{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.x86_64;

{ x86_64 (System V AMD64 ABI) backend for the native code generator.

  Emits AT&T-syntax assembly text (fed to `as`/`cc`, like QBE's .s output).

  Expression evaluation strategy (naive, correctness-first): every integer
  expression is evaluated into %eax.  Binary operators evaluate the left
  operand into %eax, push it, evaluate the right operand into %eax, pop the
  left into %ecx, then combine.  This needs no register allocator and is
  correct for arbitrary nesting; the push/pop pairs are always balanced within
  one expression, so %rsp is back to its frame-aligned position at every call
  site (SysV requires 16-byte alignment at calls).

  Milestone M2: integer literals, + - * div mod, and Write/WriteLn of integers
  (mapped to the _SysWriteInt / _SysWriteNewline runtime calls). }

interface

uses
  SysUtils, Classes, contnrs, Generics.Collections, uAST, uSymbolTable, uStrCompat,
  blaise.codegen, blaise.codegen.arcshapes, uDebugFacts,
  blaise.codegen.native.backend, blaise.codegen.target;

const
  { Per-argument hoist kinds recorded by EmitArgHoist, parallel to the
    depth list.  Kinds >= akRecCall reload a single saved 8-byte value in
    the arg loop; akOALit reloads the saved data pointer and pushes the
    high index as a second slot. }
  akNone = 0;        { not hoisted — evaluated in the normal arg loop }
  akOALit = 1;       { open-array literal: element block + saved data ptr }
  akRecCall = 2;     { record-returning call arg: sret buffer + saved ptr }
  akStrPin = 3;      { const-string pin: saved value, AddRef'd; released after }
  akStrConsume = 4;  { const-string consume: saved +1 value; released after }
  akIntfConsume = 5; { interface-returning-call arg: owned (+1) fat pointer
                       saved (itab then obj, obj on top); obj released after }

type
  { Per-call bookkeeping for hoisted call arguments — see EmitArgHoist.
    Frames nest: a call emitted while evaluating another call's arguments
    pushes its own frame. }
  TOALCallFrame = class
  public
    Depths: TList<Integer>;   { per-arg saved-slot depth; -1 = not hoisted }
    Kinds: TList<Integer>;    { per-arg hoist kind (akXxx), parallel to Depths }
    Total: Integer;           { bytes of blocks, buffers + saved slots on the stack }
    Pushed: Integer;          { bytes pushed since the hoist pre-pass }
    { The call's argument list — read by the EndCallArgs epilogue for
      record-temp field releases.  Owned by the AST, not by the frame. }
    [Unretained] Args: TObjectList;
    constructor Create;
    destructor Destroy; override;
  end;

  TX86_64Backend = class(TNativeBackend)
  protected
    FLabelCount: Integer;       { monotonic source of unique local labels }
    { OPDF debug facts (nil unless --debug-opdf): the backend records each
      function's symbol, end label, real frame-slot offsets and per-statement
      line labels here; the OPDF emitter consumes them for exact debug info.
      Owned by TCodeGenNative. }
    [Unretained] FDbgFacts: TDbgFacts;
    [Unretained] FDbgCur: TDbgFunc;   { facts entry for the function being emitted }
    FDbgSeq: Integer;                 { .Ldbg_N label counter }
    { Enclosing function while a nested proc is being emitted — lets
      DbgMarkParams resolve captured-var types from the outer var/param
      declarations.  nil for top-level functions. }
    [Unretained] FDbgOuterDecl: TMethodDecl;
    { Source file of the unit currently being emitted; stamped onto each
      TDbgFunc so per-unit line records carry the right file.  Empty while
      emitting the main program (the emitter falls back to its own file). }
    FDbgSrcFile: string;
    { Global slots to define in the .data section: program-level variables plus
      hidden for-loop end-value slots.  Insertion-ordered so EmitDataSection
      emits them in declaration order; ContainsKey gives O(1) dedup.  The value
      is the slot's static type so loads, stores, and the .data directive all
      pick the right width and signedness. }
    FDataGlobals: TOrderedDictionary<string, TTypeDesc>;
    FGlobalInits: TDictionary<string, TConstDecl>;  { global name → initialiser (var G: T = value) }
    FThreadVarGlobals: TDictionary<string, Boolean>;
    FWeakGlobals:      TDictionary<string, Boolean>;
    { Class-name string blobs already emitted to avoid duplicate label errors.
      Keyed by mangled name. }
    FClassNameEmitted: TDictionary<string, Boolean>;
    { String literal pool: unique string values in encounter order.  Each gets
      a __sN label in .rodata (12-byte ARC header + data + NUL).  The data
      pointer (str_ptr convention) is header+12. }
    FStrLits: TStringList;

    { Current function's stack frame: maps a local name (param, var, or Result)
      to its negative %rbp-relative byte offset.  nil while emitting program
      $main (whose top-level vars are globals, not frame slots).  Built once per
      function then looked up by name on every ident read and assignment — a
      key->value map, so TDictionary is the right container for the access
      pattern. }
    FFrame:     TDictionary<string, Integer>;
    { Parallel to FFrame: the static type of each frame slot, so loads and
      stores pick the right width and signedness. }
    FFrameTypes: TDictionary<string, TTypeDesc>;
    FFrameSize:  Integer;       { bytes to reserve for locals (16-aligned) }

    { Loop label stacks for break/continue: the top entry is the innermost
      loop's end-label (break) or condition-label (continue).
      Parallel FBreakExcDepths / FContinueExcDepths record FExcDepth at the
      point where the loop was entered so EmitExcUnwind knows how many frames
      to pop on a non-local exit. }
    FBreakLabels:       TStack<string>;
    FContinueLabels:    TStack<string>;
    FBreakExcDepths:    TStack<Integer>;
    FContinueExcDepths: TStack<Integer>;
    { Exit label: when non-empty, Exit jumps here (function epilogue).  Empty
      in program $main where Exit maps to a bare return. }
    FExitLabel: string;
    { True when the current function returns a record via the sret convention:
      the hidden first param (%rdi) is the caller's result buffer; Result maps
      to the pointer stored in the Result frame slot; field writes dereference
      through it; the epilogue emits a plain ret. }
    FSretFunc: Boolean;
    { ABI classification for the current record-returning function.  Set in
      BuildFrame; rcSret when FSretFunc is True; rcInt1/rcSSE1/etc. when the
      record qualifies for register return (FSretFunc is False in that case). }
    FRecRetClass: TRecReturnClass;

    { Captured outer-scope variables: when emitting a nested function, this
      holds the names of variables captured from the enclosing scope.  Each
      captured var is passed as an implicit leading pointer param and
      reads/writes are transparently redirected through that pointer.
      Nil when not inside a nested function. }
    FCapturedVars: TStringList;
    { Locals of the current function that may not be borrowed as const-string
      arguments: address-taken (explicit @ or var/out arg) plus anything
      captured by a nested procedure.  Rebuilt per function in
      EmitFunctionDef; consulted by ConstStrShape.  Mirrors the QBE
      backend's FConstArgUnsafe. }
    FConstArgUnsafe: TStringList;

    { Exception-frame accounting (per-function, reset in ClearFrame):
      FExcDepth    — number of exc frames currently live (pushed − popped).
      FExcFrameNext — index of the next pre-allocated frame slot to consume.
      FFinallyStack — parallel to FExcDepth: the finally body for each live
                      try/finally frame, or nil for a try/except frame.
                      Used by EmitExcUnwind to run finally bodies on Exit/Break/Continue.
                      Uses TList<TCompoundStmt> so nil entries are safe (no ARC release). }
    FExcDepth:     Integer;
    FExcFrameNext: Integer;
    FFinallyStack: TList<TCompoundStmt>;
    FForEndNext: Integer;
    { Stack of open-array-literal call frames; top = innermost call currently
      having its arguments pushed.  Owned (frames freed by EndCallArgs). }
    FOALFrames: TList<TOALCallFrame>;
    { Number of exc frame global slots to emit for the program main body.
      Zero when no try stmts appear in the top-level program statements. }
    FProgExcFrameCount: Integer;
    { True when the program-main body uses jumbo sets: two scratch bitmap
      buffers (_jset_scratch_0/1) are emitted as .bss globals (main has no
      frame, so set-op result/literal buffers live in static storage). }
    FProgHasJumboSet: Boolean;
    { Whole-program multi-unit guard: the system-class (TObject /
      TCustomAttribute) class-name strings, typeinfo, vtables and field-cleanup
      stubs are emitted by the FIRST class section that runs (the first unit
      that declares a class, or the program if none does).  Set True after the
      first emission so subsequent units/program do not redefine those symbols. }
    FSystemDefsEmitted: Boolean;
    { Names of dependency units that declared an initialization section, in
      AppendUnit order.  $main calls <Unit>_init for each, in order, after
      _SetArgs — mirrors the QBE backend's EmitMainHeader loop. }
    FUnitInitNames: TStringList;
    { Names of dependency units imported from cached .bif/.o in incremental /
      separate-compilation mode (SkipDepCodegen).  A global whose owning unit
      is in this set is DEFINED by that unit's own object — this program/unit
      object must only REFERENCE it (no .globl/label definition), otherwise the
      linker reports a multiple definition.  Recorded by NoteDepInitUnit for
      every imported unit regardless of whether it has an initialization
      section.  Stores raw (unmangled) unit names, matching TSymbol.OwningUnit. }
    FImportedUnits: TStringList;
    FCurrentUnitName: string;
    FProgramName: string;     { set by EmitProgram — program-scope classes keep
                                bare symbol names (no unit prefix), matching
                                uSemantic.CurrentUnitPrefix }

    { Allocate a fresh local assembly label (".L<prefix><N>"). }
    function NewLabel(const APrefix: string): string;
    { True when a catchable EDivByZero can be raised (SysUtils, which declares
      EDivByZero + _RaiseDivByZero, is in scope).  Gates the div/mod zero
      guard; without it a zero divisor traps in hardware as before. }
    function DivGuardAvailable(): Boolean;
    { Register a global integer slot of the given type (idempotent; the first
      registration's type wins).  The width and signedness drive both the
      .data directive and every load/store of the slot. }
    procedure AddGlobal(const AName: string; AType: TTypeDesc);
    procedure RegisterClassVars(AFields: TObjectList);
    procedure MarkThreadVar(const AName: string);
    procedure MarkWeakGlobal(const AName: string);
    function IsThreadVarGlobal(const AName: string): Boolean;
    function IsWeakGlobal(const AName: string): Boolean;
    { True when the global's owning unit was imported from a cached .bif/.o
      (SkipDepCodegen): the cached object DEFINES the global, so this object
      must reference it only — emitting a definition here would clash at link. }
    function IsImportedGlobal(const AName: string): Boolean;
    { The static type of a frame-local slot, or nil if AName is not a local. }
    function LocalType(const AName: string): TTypeDesc;
    { The static type of a program global, or nil if AName is not registered. }
    function GlobalType(const AName: string): TTypeDesc;
    { Emit the accumulated .data section (one slot per registered global). }
    procedure EmitDataSection;
    { Release every ARC-managed program global at program exit (string, class,
      interface obj-slot, dyn-array, and record globals' managed fields), so a
      global object's _FieldCleanup runs at program end.  Mirrors the QBE
      backend's @main_exit release pass.  Called from EmitProgram after the
      exit label. }
    procedure EmitGlobalReleases;
    { Emit all class-related data: class-name strings, published-method tables,
      typeinfo blocks, vtables, itab/impllist blocks.  Mirrors QBE backend's
      EmitTypeInfoDefs + EmitVTableDefs.  Called from EmitProgram (program type
      decls) and EmitUnit (unit interface-block type decls). }
    procedure EmitClassSection(ATypeDecls: TObjectList;
                               AGenericInstances: TObjectList;
                               ASymTable: TSymbolTable);
    function ConstElemAsmDir(const AElemType: string): string;
    procedure EmitArrayConstData(ABlock: TBlock; const APrefix: string);
    { Escape a Pascal string for use inside an AS .ascii directive. }
    function AsmEscapeString(const AStr: string): string;
    { Emit a leaq __sN+12(%rip), %rax for the string literal AValue,
      registering a new .rodata blob if not yet seen. }
    procedure EmitStrLitAddr(const AValue: string);
    { Emit an initialised global's data slot from its folded const value
      (var G: T = value).  Called from EmitDataSection inside the .data pass. }
    procedure EmitGlobalInitData(const AName: string; AType: TTypeDesc;
                                 CD: TConstDecl);
    { Emit string literal blobs in .rodata. Called from EmitDataSection. }
    procedure EmitStrLitSection;
    { Emit an immortal class-name string blob in the data section and return
      the label+12 expression that points to the character data.  ASymName
      names the data symbol; AText is the runtime-visible string content. }
    function EmitClassNameString(const ASymName, AText: string): string;
    { Emit the body of one $_FieldCleanup_<T> function.  Calls the
      destructor (if any), releases ARC-managed fields, then returns. }
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ART: TRecordTypeDesc);
    { Release every ARC-managed field of ART whose storage starts at the address
      in the callee-saved register ABaseReg (an AT&T operand such as '%rbx').
      Strings, classes, dyn-arrays and interface obj-slots are released; weak
      fields cleared; unretained fields skipped; nested record fields are
      recursed into at their offset.  ABaseReg must survive callq (caller picks
      a callee-saved register).  Used by both _FieldCleanup_<T> and record-local
      scope-exit cleanup. }
    procedure EmitRecordFieldReleases(ART: TRecordTypeDesc;
                                      const ABaseReg: string);
    { Release one ARC-managed value of type AType whose storage is at the address
      in callee-saved ABaseReg.  Scalars (string/class/intf/dynarray) are
      released directly; records recurse via EmitRecordFieldReleases; static
      arrays recurse element-by-element via EmitStaticArrayReleaseElems.  When
      AZero is set the scalar managed slot is zeroed after release (exception
      path).  ABaseReg must survive callq. }
    procedure EmitManagedReleaseAt(AType: TTypeDesc; const ABaseReg: string;
                                   AZero: Boolean);
    { Release every managed element of a static array whose inline storage starts
      at the address in callee-saved ABaseReg.  Loops the element count,
      releasing each via EmitManagedReleaseAt. }
    procedure EmitStaticArrayReleaseElems(AType: TStaticArrayTypeDesc;
                                          const ABaseReg: string; AZero: Boolean);
    procedure EmitRecordFieldRetains(ART: TRecordTypeDesc;
                                     const ABaseReg: string);
    { Emit all class/record method definitions for the given type decls plus
      the supplied generic-instance lists. }
    procedure EmitClassMethods(ATypeDecls: TObjectList;
                               AGenericInstances: TObjectList;
                               AGenericRecordInstances: TObjectList;
                               AGenericMethodInstances: TObjectList);

    { Resolve a class/interface name to its assembly symbol form, adding the
      unit prefix when the type is defined in a non-system unit.  Mirrors the
      QBE backend's ClassSymName logic. }
    function ClassSymName(const AClassName: string): string;
    { Emit a property accessor (getter/setter) call.  The receiver instance
      must already be in %rdi.  When AVSlot >= 0 the accessor is virtual and
      the call dispatches through the vtable so an overridden accessor is
      reached; otherwise it is a static call to <ClassSymName>_<method>.  The
      slot is computed by the semantic pass (PropAccessorVSlot).  Mirrors
      EmitPropAccessorCall in the QBE backend. }
    procedure EmitPropAccessorCallNative(const AOwnerType, AMethod: string;
      AVSlot: Integer);
    function IntfTypeInfoName(const AIntfName: string): string;
    { True when AName is a captured outer-scope variable in the current
      nested function (accessed via an implicit pointer param). }
    function IsCaptured(const AName: string): Boolean;
    { Load a variable's base (address or stored value) into ADstReg, handling
      local / global / nested-captured variables uniformly. }
    procedure EmitVarBaseToReg(const AName: string; AWantAddress: Boolean;
                               const ADstReg: string);
    { True when AName is a slot in the current function frame. }
    function IsLocal(const AName: string): Boolean;
    { The AT&T operand addressing AName: "-N(%rbp)" for a frame local,
      "name(%rip)" for a global. }
    function VarOperand(const AName: string): string;
    procedure EmitLeaqGlobal(const AName: string; const ADstReg: string);
    { Load the ADDRESS of a named variable into ADstReg, whether it is a stack
      local (leaq off %rbp) or a global (PC-relative, or TLS via EmitLeaqGlobal
      for a threadvar).  The local-or-global address-of-base selector that
      recurs across the field-access and method-receiver ladders. }
    procedure EmitVarAddr(const AName: string; const ADstReg: string);
    { Operands for the two halves of an interface fat pointer.  Locals occupy
      a contiguous 16-byte slot (obj at the slot base, itab 8 bytes above);
      globals are two separate .data labels, AName + '_obj'/'_itab'. }
    function IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
    function IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
    { Push the (itab, obj) pair of a named interface ident source — itab
      first so obj ends on top; leaves obj in %rax for the ARC retain that
      follows.  Handles the sret interface Result, whose slot holds a
      POINTER to the caller's 16-byte buffer rather than the fat pointer
      itself (IntfObjOperand alone would push that pointer as the obj). }
    procedure PushIntfIdentPair(AIdent: TIdentExpr);
    { Lower one interface method call (TFieldAccessExpr.IsInterfaceCall or a
      TMethodCallExpr/Stmt whose ResolvedClassType is tyInterface): load obj +
      itab, index the itab by method slot, call the loaded pointer with obj as
      Self and AArgs after it.  Result (if any) left in %rax/%xmm0.

      The receiver is normally a named interface local/global (AObjName, split
      _obj/_itab slots).  When AObjExpr is a non-nil interface-typed
      TFieldAccessExpr (the receiver is an interface stored in a record/class
      field, e.g. H.G.Greet()), obj/itab are loaded from that field's contiguous
      fat pointer instead and AObjName is ignored. }
    procedure EmitInterfaceCall(const AObjName: string; AIsGlobal: Boolean;
                                AIsVarParam: Boolean;
                                AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList;
                                AObjExpr: TASTExpr = nil;
                                ADiscardIntfRet: Boolean = False);
    procedure EmitInterfaceFieldCall(AFld: TFieldInfo; AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList;
                                ADiscardIntfRet: Boolean = False);
    { Emit typeinfo / itab / impllist blocks for interfaces and the classes
      that implement them.  Mirrors the QBE backend's EmitInterfaceDefs. }
    procedure EmitInterfaceDefs(ATypeDecls: TObjectList;
                                AGenericInstances: TObjectList;
                                AGenericIntfInstances: TObjectList;
                                ASymTable: TSymbolTable);
    { Lower an assignment whose LHS is interface-typed.  Handles the four RHS
      forms: as-cast (T as IFoo via _GetItab), direct class->interface (static
      itab), interface->interface copy, and := nil.  Strong references only;
      weak interface refs are deferred. }
    procedure EmitInterfaceAssign(AAsgn: TAssignment);
    { Store an interface expression into a record/class field's contiguous
      16-byte fat pointer (obj at ABaseReg+AOffset, itab at +8).  ABaseReg is an
      AT&T register operand (e.g. '%rcx') holding the record/object base address;
      it is copied into a callee-saved register internally so it survives the
      ARC calls.  AIntfType is the destination's declared interface type, needed
      to name the static itab when the source is a class.  Handles a class source
      (obj + static $itab_<Class>_<Interface>) and an interface source (copy
      obj+itab), retaining the new obj and releasing the old. }
    procedure EmitInterfaceToFieldSlotsAt(AExpr: TASTExpr;
      const ABaseReg: string; AOffset: Integer; AIntfType: TTypeDesc);
    { Compute the address of an interface-typed FIELD's contiguous fat pointer
      (obj at the address, itab at +8) into ADstReg (an AT&T register operand
      such as '%r15').  Handles the receiver shapes a TFieldAccessExpr can take:
      implicit-Self field, class-access (H.G), var-param/record receiver, and
      a nested receiver expression (FA.Base).  ADstReg must be free to clobber;
      callers that need it across calls pick a callee-saved register. }
    procedure EmitInterfaceFieldAddr(AFA: TFieldAccessExpr; const ADstReg: string);
    { Leave the address of an interface element of a static array in ADstReg. }
    procedure EmitIntfStaticElemAddr(ASub: TStringSubscriptExpr;
                                     const ADstReg: string);
    { True when AMethName resolves to an abstract slot on ARec (the itab entry
      must then point at _AbstractMethodError). }
    function IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                   const AMethName: string): Boolean;
    { True when the class or any ancestor implements an interface. }
    function ClassOrAncestorImplements(AClassRT: TRecordTypeDesc): Boolean;
    { Native label for a class's implementation of an interface method,
      resolved via the vtable (inherited + overridden both work). }
    function ItabMethodRefNative(AClassRT: TRecordTypeDesc;
      ATD: TTypeDecl; const AMethName: string;
      ATypeDecls: TObjectList): string;
    { Load an integer-family value from AOperand into %rax, extended to 64
      bits per AType (sign/zero-extend by width and signedness). }
    procedure EmitLoadVar(const AOperand: string; AType: TTypeDesc);
    { Store the integer-family value currently in %rax into AOperand, using
      the right-width register sub-view for AType. }
    procedure EmitStoreVar(const AOperand: string; AType: TTypeDesc);
    { Reserve an 8-byte-aligned frame slot for AName:AType, advancing AOffset. }
    procedure AddSlot(const AName: string; AType: TTypeDesc;
                      var AOffset: Integer);
    { Build FFrame for a function: assign offsets to params, Result, locals. }
    procedure BuildFrame(ADecl: TMethodDecl);
    { Tear down the current frame. }
    procedure ClearFrame;

    procedure EmitProgram(AProg: TProgram); override;
    procedure EmitUnit(AUnit: TUnit); override;
    procedure NoteDepInitUnit(const AUnitName: string;
      AHasInit: Boolean); override;
    procedure FinalizeEmit; override;
    { Emit a standalone procedure/function definition.  AExported controls
      whether the symbol gets .globl visibility (True by default).  In
      monolithic compilation, implementation-section helpers pass False so
      their labels stay local and do not collide with the RTL archive. }
    procedure EmitFunctionDef(ADecl: TMethodDecl; AExported: Boolean);
    { Spill incoming arg register AIdx into a param slot at AType's width. }
    procedure EmitSpillArg(AIdx: Integer; const AOperand: string;
                           AType: TTypeDesc);
    { Lower one statement. }
    procedure EmitStmt(AStmt: TASTStmt);
    { Lower every statement in AList (a TObjectList of TASTStmt) in order — the
      compound-body inline idiom used for try/finally/except bodies, loop
      bodies, the program block, and unit init sections.  Nil AList is a no-op. }
    procedure EmitStmtList(AList: TObjectList);
    { Given a static-array element index already in %rax, scale it to a byte
      offset: subtract the (non-zero) low bound, then multiply by the element
      size.  The read-path subscript sites all spell this the same way. }
    procedure EmitStaticElemScale(ASAT: TStaticArrayTypeDesc);
    { After an sret interface call whose argument hoist left AHoistTotal bytes
      of hoist region BELOW the 16-byte return buffer at (%rsp): reclaim the
      hoist region and leave the fat pointer (obj, itab) re-pushed at (%rsp) so
      the caller's `fat pointer at (%rsp)` contract holds.  No-op when
      AHoistTotal is 0 (nothing was hoisted, buffer already at the top). }
    procedure EmitSretBufferSlideDown(AHoistTotal: Integer);
    { Lower a Write/WriteLn call (ANewline = WriteLn). }
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    { Lower a for loop. }
    procedure EmitForStmt(AFor: TForStmt);
    { Lower a for-in loop.  Dispatches to one of five strategies depending on
      the boolean flags set by the semantic analyser: static array, dynamic
      array, string byte-iteration, set bit-scan, or class enumerator. }
    procedure EmitForInStmt(AStmt: TForInStmt);
    { Lower a case statement.  Linear comparison chain, not a jump table. }
    procedure EmitCaseStmt(AStmt: TCaseStmt);
    { Emit the element-to-loop-variable assignment for index-based for-in
      paths.  Handles ARC (string/class AddRef/Release) and width-correct
      stores.  AElemInRax is True when the element value is already in %rax. }
    procedure EmitForInAssignElem(AStmt: TForInStmt);
    { Count all try/finally and try/except statements nested inside AStmt
      (recursively) to pre-allocate exc frame slots in BuildFrame. }
    function CountTryStmts(AStmt: TASTStmt): Integer;
    function CountForStmts(AStmt: TASTStmt): Integer;
    { Unwind exception frames from FExcDepth down to ATargetDepth+1.
      For try/finally frames, emits the finally body inline.
      For try/except frames, only calls _PopExcFrame. }
    procedure EmitExcUnwind(ATargetDepth: Integer);
    { Emit the shared try-frame entry sequence: take the next pre-allocated
      512-byte exc-frame slot, _PushExcFrame, bump FExcDepth, push AFinallyBody
      onto FFinallyStack (nil for a try/except frame — keeps the stack index-
      aligned with FExcDepth), then _blaise_setjmp; branch to ALblExc on the
      longjmp return (eax<>0) or fall through to ALblTry.  Shared verbatim by
      both EmitTryFinallyStmt and EmitTryExceptStmt. }
    procedure EmitTryFramePrologue(AFinallyBody: TCompoundStmt;
      const ALblExc, ALblTry: string);
    { Emit the shared frame-pop bookkeeping triplet: _PopExcFrame, Dec(FExcDepth),
      drop the FFinallyStack top.  The Dec and the Delete must always travel with
      the pop, so they are emitted together here. }
    procedure EmitPopExcFrame;
    { Lower try/finally. }
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    { Lower try/except. }
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    { Lower raise / bare raise. }
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    { Allocate stack storage for an inline array literal [a,b,...], fill each
      element, and leave the base pointer in %rax.  Returns the number of bytes
      allocated on the stack (caller must addq that amount after the call). }
    function EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
    function EmitConstArrayLiteral(ALit: TArrayLiteralExpr): Integer;
    { Emit a direct call to a user procedure/function; result (if any) in %eax.
      ADecl is the callee's declaration (needed for var/out param handling);
      nil for type-cast calls. }
    procedure EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                       AArgs: TObjectList);
    { Emit a call to a record-returning function using the sret convention:
      ASretAddr is the AT&T operand for the destination buffer (already allocated
      by the caller), passed as the hidden first integer argument in %rdi.
      When ASretIsIndirect is True the operand holds a *pointer* to the buffer
      (sret forwarding from an outer sret function) and must be loaded with movq
      instead of leaq. }
    procedure EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                           AArgs: TObjectList; const ASretAddr: string;
                           ASretIsIndirect: Boolean);
    { Integer-register slot count of an sret call's explicit args (interface = 2). }
    function  SretUserSlots(ADecl: TMethodDecl; AArgs: TObjectList): Integer;
    { True when AExpr is a record-returning function or method call. }
    function  IsNativeRecordCall(AExpr: TASTExpr): Boolean;
    { True when AExpr is a record-method call whose receiver is exactly the
      variable AName/AIsGlobal — i.e. M := M.Method(...) would have the sret
      destination alias Self.  Such an assignment must route the result through
      a fresh temporary first. }
    function  RecordCallReceiverIsVar(AExpr: TASTExpr;
                                      const AName: string;
                                      AIsGlobal: Boolean): Boolean;
    { Sret a record-returning call (function or method) into ADest. }
    procedure EmitRecordCallSretAt(AExpr: TASTExpr; const ADest: string);
    { Sret call for a TFuncCallExpr: routes an implicit-Self method through the
      vtable-aware method-sret emitter, a free function through EmitSretCall. }
    procedure EmitFuncCallSret(AFC: TFuncCallExpr; const ADest: string;
      AIndirect: Boolean);
    procedure EmitMethodSretCall(ACall: TMethodCallExpr; const ASretAddr: string;
                                 ASretIsIndirect: Boolean;
                                 AForceStatic: Boolean = False);
    { Sret an inherited record return into ADest: an implicit-Self call
      dispatched statically to the parent's symbol.  Reuses EmitMethodSretCall
      via a transient implicit-Self method node so the sret pointer is threaded
      the same way as any other record-returning call. }
    procedure EmitInheritedRecordSret(MD: TMethodDecl; AArgs: TObjectList;
                                      const AName, ADest: string;
                                      ADestIsIndirect: Boolean);
    { Free a record-call-receiver buffer materialised by EmitMethodSretCall. }
    procedure EmitMethodSretRecvCleanup(ABytes: Integer);
    { Emit the base ADDRESS of a NAMED LOCAL record into AReg (e.g.
      '%rcx', '%rax').  Normally a stack value record, so leaq the slot.
      The one exception is the sret-function Result: its frame slot holds
      the caller's buffer POINTER, not the record, so it must be loaded
      with movq.  Every field-access receiver ladder routes its
      "IsLocal(RecordName)" leaf through here so the sret-Result
      indirection is decided in ONE place (the implicit-Result analogue of
      the implicit-Self field-access symmetry rule). }
    procedure EmitLocalRecordBase(const AName, AReg: string);
    { Compute the address of a record/class field into %rcx.  Handles
      local/global records, class fields, var-param records, chained
      access (Base <> nil), and implicit-Self fields. }
    procedure EmitFieldAddrToRcx(AFA: TFieldAccessExpr);
    { Emit the function epilogue for a reg-return record: load the local
      Result buffer into the SysV return registers (rax/rdx/xmm0/xmm1)
      according to AClass, then the caller will ret.  Only called when
      AClass <> rcSret.  VarOperand('Result') is the buffer address. }
    procedure EmitRecordReturnEpilogue(ARec: TRecordTypeDesc;
                                       AClass: TRecReturnClass);
    { Caller-side: call a record-returning function whose return class is
      AClass (non-sret).  The function is called, the return register(s)
      are stored into ADestAddr.  Args must already be set up in the SysV
      integer registers (%rdi onwards for free functions, %rsi onwards for
      methods with Self in %rdi).  Only handles the return-capture part. }
    procedure EmitRecordRegReturnCapture(const ADestAddr: string;
                                         ARec: TRecordTypeDesc;
                                         AClass: TRecReturnClass;
                                         AIsIndirect: Boolean);
    { Emit a call to a function that returns an interface via sret.  The 16-byte
      buffer (obj+itab) is left on the stack; caller is responsible for loading
      the slots and cleaning up (addq $16, %rsp). }
    procedure EmitIntfSretCall(ACall: TFuncCallExpr);
    { Interface-method call (itab dispatch) RETURNING an interface: the callee
      writes the fat pointer through a hidden sret first arg (%rdi), with the
      receiver obj as the second arg (%rsi).  Same caller contract as
      EmitIntfSretCall: the 16-byte buffer is left at (%rsp); the caller loads
      the slots and pops it (addq $16, %rsp). }
    procedure EmitIntfSretMethodCall(ACall: TMethodCallExpr);
    { Interface-method call (itab dispatch) RETURNING a RECORD: dispatch through
      the itab and write the record result into the caller-supplied ADest,
      honouring the full record-return ABI (hidden sret pointer for a
      memory-class record; register capture for a register-class one).  Mirrors
      the QBE EmitIntfSretDispatch helper.  ADestIsIndirect: ADest holds a
      pointer to the destination buffer (var/out / Result), not the buffer. }
    procedure EmitIntfRecordSretDispatch(ACall: TMethodCallExpr;
                                         const ADest: string;
                                         ADestIsIndirect: Boolean);
    { Class-receiver method call RETURNING an interface (Obj.Make() where Obj
      is class-typed): sret hidden first arg (%rdi), receiver in %rsi, static
      or vtable dispatch from the receiver's class.  Same caller contract as
      EmitIntfSretCall: the 16-byte buffer is left at (%rsp); the caller loads
      the slots and pops it (addq $16, %rsp). }
    procedure EmitClassIntfSretMethodCall(ACall: TMethodCallExpr);
    { Indirect call: load a bare function pointer from APtrOperand (an AT&T
      memory operand, e.g. "-8(%rbp)"), set up args as for EmitCall, then
      dispatch via callq *%r10.  AProcType supplies the param list for
      var-param detection; result (if any) is left in %rax. }
    procedure EmitCallIndirect(const APtrOperand: string;
                               AProcType: TProceduralTypeDesc;
                               AArgs: TObjectList);
    { Call a procedural-typed CLASS FIELD through a receiver
      (Self.FFn(args)).  The function pointer lives at [instance + Offset],
      which is not a %rbp/%rip-relative operand, so this cannot reuse
      EmitCallIndirect/EmitMethodPtrCall.  Mirrors the interface-dispatch
      shape instead: push args, then load the (call-free) receiver and the
      field's code pointer.  AResultType nil = statement call (no result
      narrowing).  Receiver shapes: a named var/global via AObjectName, a
      var/out param (AIsVarParam), or a call-free AObjExpr (an identifier or
      field access). }
    procedure EmitProcFieldCall(AObjExpr: TASTExpr; const AObjectName: string;
                                AIsVarParam: Boolean; AFieldInfo: TFieldInfo;
                                AProcType: TProceduralTypeDesc;
                                AArgs: TObjectList; AResultType: TTypeDesc);
    { Evaluate an integer expression; result left in %rax (64-bit-extended). }
    procedure EmitExprToEax(AExpr: TASTExpr);
    procedure EmitByteRhsToEax(AExpr: TASTExpr);
    { Evaluate a float expression (tyDouble or tySingle); result left in %xmm0.
      Binary ops: left → push onto int stack via subq/movsd, right → %xmm0,
      pop left → %xmm1, then addsd/subsd/mulsd/divsd. }
    procedure EmitExprToXmm0(AExpr: TASTExpr);
    function EmitFloatBuiltin(FC: TFuncCallExpr): Boolean;
    { Load a float (Double or Single) from AOperand into %xmm0. }
    procedure EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
    { Store %xmm0 into AOperand at the float type's width. }
    procedure EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
    procedure EmitXmm0WidthAdjust(ASrcType: TTypeDesc; AWantSingle: Boolean);
    { The integer-family type to use when loading the value of AExpr: the
      recorded slot type for a known local/global (authoritative), otherwise
      the node's ResolvedType. }
    function IntExprType(AExpr: TASTExpr): TTypeDesc;
    { Re-truncate and re-extend the value in %rax to AType's width and
      signedness — used after a call (whose ABI return is 32-bit) and to
      implement an explicit narrowing/widening type cast. }
    procedure EmitNarrowToType(AType: TTypeDesc);
    { Inc(x)/Dec(x) with support for simple variables, implicit-Self fields,
      var params, and field-access expressions. }
    procedure EmitLValueSlotAddr(AExpr: TASTExpr);
    { --- OPDF debug-fact hooks (no-ops when facts collection is off) --- }
    procedure SetDebugFacts(AFacts: TDbgFacts); override;
    procedure DbgBeginFunc(const ASymbol: string);
    procedure DbgRecordSlot(const AName: string; AType: TTypeDesc; AOffset: Integer);
    procedure DbgMarkParams(ADecl: TMethodDecl);
    function OuterVarType(const AName: string): TTypeDesc;
    procedure DbgStmtLabel(AStmt: TASTStmt);
    procedure DbgEndFunc;
    procedure EmitIncDec(ACall: TProcCall);
    procedure EmitIncDecAddrOp(IsInc, IsWide, HasStep: Boolean);
    { Evaluate a boolean condition and branch: if true jump ATrueLabel, else
      fall through to AFalseLabel (a jmp is emitted to it). }
    procedure EmitCondBranch(AExpr: TASTExpr;
                             const ATrueLabel, AFalseLabel: string);
    { Emit a TMethodCallExpr (class method call, with explicit receiver).
      Loads Self into %rdi and evaluates scalar args; result in %rax/%xmm0. }
    procedure EmitMethodCallExpr(ACall: TMethodCallExpr);
    { Implicit-Self regular (non-sret) method call whose register slots
      (Self + args) exceed 6: evaluate args into a stack slot block (slot 0 =
      Self), load the first six into registers and spill the rest, then dispatch
      (vtable-aware) with Self in %rdi.  Mirrors EmitMethodCallExpr's >6-slot
      branch; the implicit-Self expression path (EmitExprToEax) lacked it. }
    procedure EmitImplicitSelfCallOverflow(MD: TMethodDecl;
      AArgs: TObjectList; const ASym: string);
    { Emit a TMethodCallStmt (class method call in statement position). }
    procedure EmitMethodCallStmt(ACall: TMethodCallStmt);
    { Emit a TInheritedCallStmt (`inherited Method[(args)]`).  Direct static
      dispatch to the parent method (no vtable); Self is the current method's
      Self; a value-returning parent stores its result into the Result slot. }
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    { Shared static-dispatch sequence (Self + args + direct callq); result in
      %rax/%xmm0 on return.  Used by both inherited forms (stmt + expr). }
    procedure EmitInheritedCallSeq(MD: TMethodDecl; AArgs: TObjectList;
      const AName: string);
    { Evaluate one method-call argument and push it onto the stack.  Scalar and
      var/out params push one value; interface params push two (itab first, then
      obj — reversed so the pop loop restores them in the correct register order). }
    procedure EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
    procedure EmitVarArgAddrToRax(AArg: TASTExpr);
    { Pre-pass for call arguments (phase A of the call protocol).  Hoists
      three argument kinds into a stack region BELOW the argument slots,
      recording one (depth, kind) pair per argument (-1/akNone when not
      hoisted):

        akOALit      — open-array literals: EmitOpenArrayLiteral moves %rsp,
                       so the element block is emitted here and its data
                       pointer saved behind it.
        akRecCall    — record-returning call arguments: the callee's sret
                       buffer is materialised here (EmitExprToEax leaves it
                       at %rsp) and the buffer pointer saved.  Without the
                       hoist the buffer lands between pushed argument slots
                       and the popq sequence reads buffer words.
        akStrPin /
        akStrConsume — const-string arguments needing caller protection
                       (see blaise.codegen.arcshapes.TConstArgMode): the
                       value is evaluated and saved; pin mode AddRefs it.
                       Param const-ness comes from AParams (TMethodParam) or
                       AProcParams (TProcParamInfo); when AKnownSig is False
                       (interface dispatch) every string-typed argument is
                       protected by shape, with AVarFlags ('1'/'0' comma
                       list) marking var positions to skip.

      Returns the region bytes.  The call site reloads hoisted values in its
      arg loop and finishes with EmitHoistEpilogue AFTER the call. }
    function EmitArgHoist(AParams: TObjectList; AProcParams: TObjectList;
                          AKnownSig: Boolean; const AVarFlags: string;
                          AArgs: TObjectList;
                          ADepths: TList<Integer>; AKinds: TList<Integer>): Integer;
    { Phase C — post-call epilogue: releases pinned/consumed const-string
      values and the managed fields of hoisted record temporaries, preserving
      the call's return registers (%rax/%rdx/%xmm0/%xmm1), then reclaims
      ATotal + ABase bytes when AReclaim is True.  ABase = extra bytes (e.g.
      overflow-arg cleanup) between %rsp and the hoist region at this point. }
    procedure EmitHoistEpilogue(AArgs: TObjectList; ADepths: TList<Integer>;
                                AKinds: TList<Integer>; ATotal, ABase: Integer;
                                AReclaim: Boolean);
    { Shape classification for a const-string argument — mirror of the QBE
      backend's ConstArgMode.  APinPlainLocals forces plain locals to pin
      (var/out string sibling param, or unknown parameter types). }
    function  ConstStrShape(AArg: TASTExpr; APinPlainLocals: Boolean): TConstArgMode;
    { True when AArg is a record-returning function/method call (its
      evaluation materialises an sret buffer on the stack). }
    function  IsRecCallArg(AArg: TASTExpr): Boolean;
    { Stack bytes the sret buffer of a hoisted record-call argument occupies. }
    function  RecArgBufBytes(AArg: TASTExpr): Integer;
    function  ParamsHaveVarString(AParams: TObjectList): Boolean;
    function  ProcParamsHaveVarString(AProcParams: TObjectList): Boolean;
    { Reads the AIndex'th flag of a MethodParamVarFlagsStr-style '1'/'0'
      comma list; False when out of range or empty. }
    function  VarFlagAt(const AFlags: string; AIndex: Integer): Boolean;
    { Total of the innermost open call frame — used by sret call paths to
      address a dest pointer saved just below the hoist region. }
    function  TopFrameTotal: Integer;
    { Phase B — push the slot(s) for one argument.  Hoisted arguments reload
      their saved value from the phase-A region: the saved slot sits
      (ATotal - ADepth + APushed) bytes above the current %rsp, where
      APushed counts every byte pushed since EmitArgHoist returned. }
    procedure EmitArgPush(APar: TMethodParam; AArg: TASTExpr;
                          ATotal, ADepth, AKind: Integer; var APushed: Integer);
    { Frame-stack wrappers around EmitArgHoist/EmitArgPush for the standard
      push-loop call sites.  BeginCallArgs runs the hoist pre-pass and pushes
      a frame; PushCallArg pushes one argument's slot(s) (AIndex = position in
      the original argument list); EndCallArgs emits the post-call epilogue
      (string releases, record-temp field releases, region reclaim — place it
      where the post-call stack cleanup belongs) and pops the frame. }
    procedure BeginCallArgs(AParams: TObjectList; AArgs: TObjectList);
    procedure PushCallArg(APar: TMethodParam; AArg: TASTExpr; AIndex: Integer);
    procedure EndCallArgs;
    { Return the total number of integer register slots consumed by AParams.
      Most params = 1 slot; interface params = 2 slots (obj + itab); open-array
      params = 2 slots (ptr + high).  Used by pop loops so they count slots, not
      logical argument positions. }
    { Load a class method call's receiver instance pointer into %rax. }
    procedure EmitMethodReceiverToRax(ACall: TMethodCallExpr);
    function CountArgSlots(AParams: TObjectList): Integer;
    { Bounds-checked System V integer-arg-register accessor (raises if > 5). }
    function SysVArg64(AIndex: Integer): string;
    { Consume ASlots pushed arg slots into SysV registers from index ABase,
      spilling any overflow to the stack.  Returns overflow bytes to clean up
      after the call.  Used by the interface/class sret call emitters. }
    function EmitSretRegArgs(ASlots, ABase: Integer): Integer;
    { Pop already-pushed method-call arg slots (slot 0 pushed first, on top is
      the last slot) into the System V argument registers, routing float-family
      params to %xmm0.. and everything else to the integer registers starting
      at AIntBase (1 when only Self/%rdi is reserved).  Mirrors EmitCall's SysV
      classification so a Double/Single method or constructor argument lands in
      its xmm register instead of being mis-passed in an integer register. }
    procedure EmitPopMethodArgsToRegs(AParams, AArgs: TObjectList;
      AIntBase: Integer);
    { Append one SysV slot-class entry per logical argument to AList (1 = float
      eightbyte → xmm, 0 = integer/pointer eightbyte → integer register).  Open
      arrays and by-value interfaces occupy two integer slots; a by-value
      Double/Single occupies one xmm slot; everything else is one integer slot.
      The receiver/Self slot is NOT added here — callers prepend it as needed.
      Shared by EmitPopMethodArgsToRegs and EmitMethodOverflowLoad so the
      classification stays single-sourced. }
    procedure BuildArgSlotClasses(AParams, AArgs: TObjectList;
      AList: TList<Integer>);
    { Emit the call for a method whose receiver (Self) is already in %rdi:
      a vtable dispatch when AMD is virtual (VTableSlot >= 0) so the call
      respects polymorphism, otherwise a static callq to AStaticSym.  Used by
      the implicit-Self call paths, which must dispatch identically to an
      explicit Self.Method() call. }
    procedure EmitSelfDispatch(AMD: TMethodDecl; const AStaticSym: string);
    { As EmitSelfDispatch but with Self in an explicit register (e.g. %rsi when
      %rdi holds an sret buffer pointer). }
    procedure EmitSelfDispatchVia(AMD: TMethodDecl;
      const AStaticSym, ASelfReg: string);
    { Float-aware register load + overflow relocation for the >6-slot
      method-family layout.  The caller has stored every arg into a flat region
      whose slot I lives at offset (I+1)*8 (slot 0 is the receiver/Self) and has
      placed Self at 0(%rsp).  This loads slot 0 into %rdi and each arg slot into
      its System V register (integers from %rsi.., floats into xmm0..),
      relocates the integer-overflow slots to the top of AAllocSz and raises
      %rsp to the overflow base, returning the overflow byte count for the
      caller to reclaim after the call.  Float args never overflow (8 xmm regs).
      The store loop must already have written float slots as their 8-byte bit
      pattern (movsd %xmm0). }
    function EmitMethodOverflowLoad(AParams, AArgs: TObjectList;
      AAllocSz: Integer): Integer;
    { Store every logical argument into its 8-byte slot in the >6-slot call
      frame already allocated at (%rsp): slot I goes to (I+1)*8(%rsp) (slot 0 is
      reserved for Self).  Dispatches per arg kind — a hoisted akRecCall buffer
      is reloaded from its hoist depth, a var/out param stores its address, a
      by-value float stores the width-adjusted xmm bit pattern, and a plain
      scalar stores %rax.  AHoistDepths/AHoistKinds are the (depth, kind) vectors
      EmitArgHoist produced; AAllocSz/AHoistTotal frame the akRecCall reload
      offset.  Shared verbatim by every >6-slot method/implicit-Self/metaclass
      call path. }
    procedure EmitArgsToSlots(AArgs, AParams: TObjectList;
      AAllocSz, AHoistTotal: Integer;
      AHoistDepths, AHoistKinds: TList<Integer>);
    { True when the parameter at AIndex is a by-value float-family param (the
      caller must store its slot as an xmm bit pattern, not via %rax). }
    function OverflowArgIsFloat(AParams: TObjectList; AIndex: Integer): Boolean;
    { Emit a method-pointer (of-object) call: load Code from offset 0 and Data
      from offset 8 of the TMethod block at APtrOperand; call Code with Data as
      Self (%rdi) and the remaining args shifted. }
    procedure EmitMethodPtrCall(const APtrOperand: string;
                                AProcType: TProceduralTypeDesc;
                                AArgs: TObjectList);
    { Emit a Format(Fmt, arg1, ...) built-in call via _StringFormatN.
      Builds a temporary args array on the stack: each slot is 16 bytes
      (type tag at [0], value at [8]), matching the QBE backend's layout. }
    procedure EmitFormatCall(AArgs: TObjectList);
  public
    constructor Create(const ATarget: TTargetDesc); override;
    destructor Destroy; override;
  end;

implementation

const
  { SysV AMD64 integer argument registers (32-bit views), in order. }
  SysVArgRegs: array[0..5] of string =
    ('%edi', '%esi', '%edx', '%ecx', '%r8d', '%r9d');
  { Same registers, 64-bit views — used for Int64/UInt64 arguments. }
  SysVArgRegs64: array[0..5] of string =
    ('%rdi', '%rsi', '%rdx', '%rcx', '%r8', '%r9');
  { 8-bit and 16-bit views, for spilling a narrow incoming argument into its
    same-width param slot. }
  SysVArgRegs8: array[0..5] of string =
    ('%dil', '%sil', '%dl', '%cl', '%r8b', '%r9b');
  SysVArgRegs16: array[0..5] of string =
    ('%di', '%si', '%dx', '%cx', '%r8w', '%r9w');

constructor TOALCallFrame.Create;
begin
  inherited Create();
  Depths := TList<Integer>.Create();
  Kinds := TList<Integer>.Create();
  Total := 0;
  Pushed := 0;
  Args := nil;
end;

destructor TOALCallFrame.Destroy;
begin
  Depths.Free();
  Kinds.Free();
  inherited Destroy();
end;

{ ------------------------------------------------------------------ }
{ Integer-family width / signedness helpers                            }
{ ------------------------------------------------------------------ }

{ Byte width (1/2/4/8) of an integer-family type. Defaults to 4. }
function IntByteSize(AType: TTypeDesc): Integer;
begin
  { nil / unmapped kinds default to pointer width, mirroring the QBE
    backend's 'l' default (QbeTypeOf / PromotedQType).  A nil TypeDesc
    is typically an unresolved forward class reference — loading such a
    field with 4-byte width truncates the pointer. }
  if AType = nil then
  begin
    Exit(8);
  end;
  case AType.Kind of
    tyByte, tyBoolean:                          Result := 1;
    tySmallInt, tyWord:                         Result := 2;
    tyInteger, tyUInt32, tyEnum:                Result := 4;
    tyInt64, tyUInt64,
    tyProcedural, tyPointer, tyPChar, tyClass,
    tyString, tyMetaClass, tyDynArray,
    tyInterface:                                Result := 8;
    tyDouble:                                   Result := 8;
    tySingle:                                   Result := 4;
    tySet:
      if TSetTypeDesc(AType).IsJumbo() then
        Result := TSetTypeDesc(AType).RawSize()   { inline byte-array bitmap }
      else if TSetTypeDesc(AType).BitCount > 32 then
        Result := 8
      else
        Result := 4;
  else
    Result := 8;
  end;
end;

{ True for floating-point types supported in %xmm registers. }
function IsFloatFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind in [tyDouble, tySingle]);
end;

{ True for a JUMBO (>64-member) set: an inline byte-array bitmap aggregate
  (like a record / static array), operated on via the _Set* RTL helpers and
  passed/returned by pointer.  Sets of 64 members or fewer stay register-sized. }
function IsJumboSet(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind = tySet) and
            TSetTypeDesc(AType).IsJumbo();
end;

{ Bitmap byte count of a jumbo set (= ceil(BitCount/8), <= 32). }
function JumboSetNBytes(AType: TTypeDesc): Integer;
begin
  Result := TSetTypeDesc(AType).RawByteSize();
end;

{ SysV AMD64 XMM argument registers, in order. }
const
  SysVXmmArgRegs: array[0..7] of string =
    ('%xmm0', '%xmm1', '%xmm2', '%xmm3', '%xmm4', '%xmm5', '%xmm6', '%xmm7');

{ True for unsigned integer-family types. Byte/Word/UInt32/UInt64 are
  unsigned; Boolean and Enum hold non-negative ordinals and so are read
  zero-extended. SmallInt/Integer/Int64 are signed. }
function IsUnsignedInt(AType: TTypeDesc): Boolean;
begin
  if AType = nil then
  begin
    Exit(False);
  end;
  Result := AType.Kind in [tyByte, tyBoolean, tyWord, tyUInt32, tyUInt64, tyEnum];
end;


{ The assembly symbol for a procedure/function.  An `external name '...'`
  binding names a foreign (C/asm) symbol that must be used verbatim — never
  mangled or unit-prefixed (matching the QBE backend's ExternalName handling).
  Otherwise the semantic pass sets ResolvedQbeName for overloaded/mangled names;
  failing that use the source name. }
function FuncSymbolFromDecl(ADecl: TMethodDecl): string;
begin
  if (ADecl <> nil) and ADecl.IsExternal and (ADecl.ExternalName <> '') then
    Result := ADecl.ExternalName
  else if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ADecl.Name)
  else
    Result := '';
end;

function FuncSymbolOf(ACall: TFuncCallExpr): string;
begin
  Result := FuncSymbolFromDecl(TMethodDecl(ACall.ResolvedDecl));
  if Result = '' then
    Result := NativeMangle(ACall.Name);
end;

constructor TX86_64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
  FLabelCount          := 0;
  FDataGlobals         := TOrderedDictionary<string, TTypeDesc>.Create();
  FGlobalInits         := TDictionary<string, TConstDecl>.Create();
  FThreadVarGlobals    := TDictionary<string, Boolean>.Create();
  FWeakGlobals         := TDictionary<string, Boolean>.Create();
  FClassNameEmitted    := TDictionary<string, Boolean>.Create();
  FStrLits             := TStringList.Create();
  FBreakLabels        := TStack<string>.Create();
  FContinueLabels     := TStack<string>.Create();
  FBreakExcDepths     := TStack<Integer>.Create();
  FContinueExcDepths  := TStack<Integer>.Create();
  FFinallyStack       := TList<TCompoundStmt>.Create();
  FOALFrames          := TList<TOALCallFrame>.Create();
  FFrame          := nil;
  FFrameTypes     := nil;
  FFrameSize      := 0;
  FExitLabel      := '';
  FSretFunc       := False;
  FRecRetClass    := rcSret;
  FExcDepth           := 0;
  FExcFrameNext       := 0;
  FForEndNext         := 0;
  FProgExcFrameCount  := 0;
  FSystemDefsEmitted  := False;
  FUnitInitNames      := TStringList.Create();
  FImportedUnits      := TStringList.Create();
  FImportedUnits.CaseSensitive := False;
  FImportedUnits.Sorted := True;
  FImportedUnits.Duplicates := dupIgnore;
  FConstArgUnsafe     := TStringList.Create();
  FConstArgUnsafe.CaseSensitive := True;
  FConstArgUnsafe.Sorted := True;
  FConstArgUnsafe.Duplicates := dupIgnore;
end;

destructor TX86_64Backend.Destroy;
begin
  Self.ClearFrame();
  FConstArgUnsafe.Free();
  FImportedUnits.Free();
  FUnitInitNames.Free();
  FOALFrames.Free();
  FFinallyStack.Free();
  FContinueExcDepths.Free();
  FBreakExcDepths.Free();
  FContinueLabels.Free();
  FBreakLabels.Free();
  FClassNameEmitted.Free();
  FStrLits.Free();
  FWeakGlobals.Free();
  FThreadVarGlobals.Free();
  FGlobalInits.Free();
  FDataGlobals.Free();
  inherited Destroy();
end;

function TX86_64Backend.NewLabel(const APrefix: string): string;
begin
  Result := '.L' + APrefix + IntToStr(FLabelCount);
  Inc(FLabelCount);
end;

function TX86_64Backend.DivGuardAvailable(): Boolean;
begin
  Result := (FSymTable <> nil) and (FSymTable.Lookup('EDivByZero') <> nil);
end;

procedure TX86_64Backend.AddGlobal(const AName: string; AType: TTypeDesc);
begin
  if not FDataGlobals.ContainsKey(AName) then
    FDataGlobals.Add(AName, AType);
end;

{ Register a shared data global for every STATIC (class-level) variable in a
  class/record field list, under the mangled ClassVarEmitName stamped by the
  semantic pass.  EmitDataSection then emits a correctly-sized zero slot.  This
  covers read-only static vars that no assignment site auto-registers. }
procedure TX86_64Backend.RegisterClassVars(AFields: TObjectList);
var
  I: Integer;
  FDecl: TFieldDecl;
begin
  if AFields = nil then Exit;
  for I := 0 to AFields.Count - 1 do
  begin
    FDecl := TFieldDecl(AFields.Items[I]);
    if not FDecl.IsClassVar then Continue;
    if FDecl.ClassVarEmitName = '' then Continue;
    if FDecl.ResolvedType = nil then Continue;
    Self.AddGlobal(FDecl.ClassVarEmitName, FDecl.ResolvedType);
  end;
end;

procedure TX86_64Backend.MarkThreadVar(const AName: string);
begin
  if not FThreadVarGlobals.ContainsKey(AName) then
    FThreadVarGlobals.Add(AName, True);
end;

procedure TX86_64Backend.MarkWeakGlobal(const AName: string);
begin
  if not FWeakGlobals.ContainsKey(AName) then
    FWeakGlobals.Add(AName, True);
end;

function TX86_64Backend.IsThreadVarGlobal(const AName: string): Boolean;
var
  Dummy: Boolean;
begin
  Result := FThreadVarGlobals.TryGetValue(AName, Dummy);
end;

function TX86_64Backend.IsWeakGlobal(const AName: string): Boolean;
var
  Dummy: Boolean;
begin
  Result := FWeakGlobals.TryGetValue(AName, Dummy);
end;

function TX86_64Backend.GlobalType(const AName: string): TTypeDesc;
begin
  if not FDataGlobals.TryGetValue(AName, Result) then
    Result := nil;
end;

function TX86_64Backend.IsImportedGlobal(const AName: string): Boolean;
var
  Sym: TSymbol;
begin
  { A global whose owning unit was imported from a cached .bif/.o (incremental /
    separate compilation) is DEFINED by that unit's own object.  This object must
    only reference it (no .globl/label here), or the linker reports a multiple
    definition.  References (leaq Name(%rip)) resolve against the cached object's
    exported symbol. }
  Result := False;
  if FImportedUnits.Count = 0 then Exit;
  if FSymTable = nil then Exit;
  Sym := FSymTable.Lookup(AName);
  if Sym = nil then Exit;
  if Sym.OwningUnit = '' then Exit;
  Result := FImportedUnits.IndexOf(Sym.OwningUnit) >= 0;
end;

procedure TX86_64Backend.EmitDataSection;
var
  I, Sz:    Integer;
  Name:     string;
  Directive: string;
  IsTls:    Boolean;
  HasData, HasTbss: Boolean;
  InitCD:   TConstDecl;
begin
  if (FDataGlobals.Count = 0) and (FProgExcFrameCount = 0) and
     (not FProgHasJumboSet) then
  begin
    Self.EmitStrLitSection();
    Exit;
  end;
  HasData := False;
  HasTbss := False;
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    if Self.IsImportedGlobal(FDataGlobals.Keys[I]) then
      Continue;
    if Self.IsThreadVarGlobal(FDataGlobals.Keys[I]) then
      HasTbss := True
    else
      HasData := True;
  end;
  if FProgExcFrameCount > 0 then HasData := True;
  if FProgHasJumboSet then HasData := True;
  { Two passes: first .data globals, then .tbss threadvars. }
  if HasData then
    Self.Emit('.data');
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name  := FDataGlobals.Keys[I];
    if Self.IsImportedGlobal(Name) then Continue;
    IsTls := Self.IsThreadVarGlobal(Name);
    if IsTls then Continue;
    { Initialised global (var G: T = value): emit the folded value.  threadvars
      are excluded (they live in .tbss / always zero). }
    if FGlobalInits.TryGetValue(Name, InitCD) then
    begin
      Self.EmitGlobalInitData(Name, Self.GlobalType(Name), InitCD);
      Continue;
    end;
    { Method pointers (of-object): 16-byte Code+Data block, zero-initialised. }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyProcedural) and
       TProceduralTypeDesc(Self.GlobalType(Name)).IsMethodPtr then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.quad 0');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyInterface) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
      begin
        Self.Emit('.globl ' + Name + '_obj');
        Self.Emit('.globl ' + Name + '_itab');
      end;
      Self.Emit(Name + '_obj:');
      Self.Emit(#9'.quad 0');
      Self.Emit(Name + '_itab:');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (IsJumboSet(Self.GlobalType(Name)) or
          (Self.GlobalType(Name).Kind in [tyRecord, tyStaticArray])) then
    begin
      Sz := Self.GlobalType(Name).RawSize();
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(Format(#9'.skip %d', [Sz]));
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyDouble) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.double 0.0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tySingle) then
    begin
      Self.Emit('.balign 4');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.float 0.0');
      Continue;
    end;
    Sz := IntByteSize(Self.GlobalType(Name));
    case Sz of
      1: begin Directive := #9'.byte 0'; Self.Emit('.balign 1'); end;
      2: begin Directive := #9'.word 0'; Self.Emit('.balign 2'); end;
      8: begin Directive := #9'.quad 0'; Self.Emit('.balign 8'); end;
    else
      begin Directive := #9'.long 0'; Self.Emit('.balign 4'); end;
    end;
    if Copy(Name, 1, 2) <> '.L' then
      Self.Emit('.globl ' + Name);
    Self.Emit(Name + ':');
    Self.Emit(Directive);
  end;
  { Exception frame slots for the program-main body. }
  for I := 0 to FProgExcFrameCount - 1 do
  begin
    Self.Emit('.balign 16');
    Self.Emit('_exc_frame_' + IntToStr(I) + ':');
    Self.Emit(#9'.skip 512');
  end;
  { Jumbo-set scratch buffers for the program-main body (32 bytes each, the
    256-member maximum). }
  if FProgHasJumboSet then
  begin
    Self.Emit('.balign 8');
    Self.Emit('_jset_scratch_0:');
    Self.Emit(#9'.skip 32');
    Self.Emit('.balign 8');
    Self.Emit('_jset_scratch_1:');
    Self.Emit(#9'.skip 32');
  end;
  { Threadvar globals: emit in .tbss (zero-initialised thread-local storage). }
  if HasTbss then
  begin
    Self.Emit('.section .tbss,"awT",@nobits');
    for I := 0 to FDataGlobals.Count - 1 do
    begin
      Name := FDataGlobals.Keys[I];
      if Self.IsImportedGlobal(Name) then Continue;
      if not Self.IsThreadVarGlobal(Name) then Continue;
      if (Self.GlobalType(Name) <> nil) and
         (IsJumboSet(Self.GlobalType(Name)) or
          (Self.GlobalType(Name).Kind in [tyRecord, tyStaticArray])) then
        Sz := Self.GlobalType(Name).RawSize()
      else if (Self.GlobalType(Name) <> nil) and
              (Self.GlobalType(Name).Kind = tyDouble) then
        Sz := 8
      else
      begin
        Sz := IntByteSize(Self.GlobalType(Name));
        if Sz < 4 then Sz := 4;
      end;
      if Sz >= 8 then
        Self.Emit('.balign 8')
      else
        Self.Emit(Format('.balign %d', [Sz]));
      Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(Format(#9'.skip %d', [Sz]));
    end;
  end;
  Self.EmitStrLitSection();
end;

procedure TX86_64Backend.EmitGlobalInitData(const AName: string;
  AType: TTypeDesc; CD: TConstDecl);
var
  J:        Integer;
  ElemKind: TTypeKind;
  ElemDir:  string;
  Idx:      Integer;
  SAT:      TStaticArrayTypeDesc;
begin
  { Static array initialiser: inline element list. }
  if (AType.Kind = tyStaticArray) and CD.IsArrayConst then
  begin
    SAT := TStaticArrayTypeDesc(AType);
    { Multi-dimensional const arrays are nested static-array types; the element
      directive is governed by the INNERMOST scalar element, and the flat
      row-major ArrayElements already match the contiguous layout. }
    while SAT.ElementType.Kind = tyStaticArray do
      SAT := TStaticArrayTypeDesc(SAT.ElementType);
    ElemKind := SAT.ElementType.Kind;
    Self.Emit('.balign 8');
    if Copy(AName, 0, 2) <> '.L' then
      Self.Emit('.globl ' + AName);
    Self.Emit(AName + ':');
    if ElemKind = tyString then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      for J := 0 to CD.ArrayElements.Count - 1 do
      begin
        Idx := FStrLits.IndexOf(CD.ArrayElements[J]);
        Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
      end;
      Exit;
    end;
    case ElemKind of
      tyByte, tyBoolean:           ElemDir := #9'.byte ';
      tySmallInt, tyWord:          ElemDir := #9'.word ';
      tyInt64, tyUInt64, tyPointer, tyPChar: ElemDir := #9'.quad ';
      tyDouble:                    ElemDir := #9'.double ';
      tySingle:                    ElemDir := #9'.float ';
    else
      ElemDir := #9'.long ';
    end;
    for J := 0 to CD.ArrayElements.Count - 1 do
      Self.Emit(ElemDir + CD.ArrayElements[J]);
    Exit;
  end;

  { String scalar: point at an immortal static string header (__sN + 12). }
  if AType.IsString() then
  begin
    if FStrLits.IndexOf(CD.StrVal) < 0 then
      FStrLits.Add(CD.StrVal);
    Idx := FStrLits.IndexOf(CD.StrVal);
    Self.Emit('.balign 8');
    if Copy(AName, 0, 2) <> '.L' then
      Self.Emit('.globl ' + AName);
    Self.Emit(AName + ':');
    Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
    Exit;
  end;

  { Scalar numeric / boolean / enum / real. }
  case AType.Kind of
    tyDouble:
      begin
        Self.Emit('.balign 8');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.double %s', [CD.StrVal]));
      end;
    tySingle:
      begin
        Self.Emit('.balign 4');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.float %s', [CD.StrVal]));
      end;
    tyByte, tyBoolean:
      begin
        Self.Emit('.balign 1');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.byte %d', [CD.IntVal]));
      end;
    tySmallInt, tyWord:
      begin
        Self.Emit('.balign 2');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.word %d', [CD.IntVal]));
      end;
    tyInt64, tyUInt64, tyPointer, tyPChar:
      begin
        Self.Emit('.balign 8');
        if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
        Self.Emit(AName + ':');
        Self.Emit(Format(#9'.quad %d', [CD.IntVal]));
      end;
  else
    { Integer / UInt32 / enum — 32-bit. }
    Self.Emit('.balign 4');
    if Copy(AName, 0, 2) <> '.L' then Self.Emit('.globl ' + AName);
    Self.Emit(AName + ':');
    Self.Emit(Format(#9'.long %d', [CD.IntVal]));
  end;
end;

{ ------------------------------------------------------------------ }
{ String literal helpers (M7c)                                         }
{ ------------------------------------------------------------------ }

{ Escape a string for use in an AT&T .ascii directive.
  GNU as accepts the same escapes as C string literals. }
function TX86_64Backend.AsmEscapeString(const AStr: string): string;
var
  I, C, Hi, Lo: Integer;
begin
  Result := '';
  for I := 0 to Length(AStr) - 1 do
  begin
    C := StrAt(AStr, I);
    case C of
      34:  Result := Result + '\"';
      92:  Result := Result + '\\';
      10:  Result := Result + '\n';
      13:  Result := Result + '\r';
      9:   Result := Result + '\t';
    else
      if (C < 32) or (C > 126) then
      begin
        Hi := C shr 4;
        Lo := C and 15;
        if Hi < 10 then Hi := 48 + Hi else Hi := 55 + Hi;
        if Lo < 10 then Lo := 48 + Lo else Lo := 55 + Lo;
        Result := Result + '\x' + Chr(Hi) + Chr(Lo)
      end
      else
        Result := Result + Chr(C);
    end;
  end;
end;

procedure TX86_64Backend.EmitGlobalReleases;
var
  I:     Integer;
  Name:  string;
  Ty:    TTypeDesc;
begin
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name := FDataGlobals.Keys[I];
    Ty   := Self.GlobalType(Name);
    if Ty = nil then Continue;
    { Thread-var globals live in TLS and are not released here (matches the
      data-section split; their lifetime is per-thread, not program-global). }
    if Self.IsThreadVarGlobal(Name) then Continue;
    if Ty.IsString() then
    begin
      Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Name]));
      Self.Emit(#9'callq _StringRelease');
    end
    else if Ty.Kind = tyClass then
    begin
      if Self.IsWeakGlobal(Name) then
      begin
        Self.Emit(Format(#9'leaq %s(%%rip), %%rdi', [Name]));
        Self.Emit(#9'callq _WeakClear');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Name]));
        Self.Emit(#9'callq _ClassRelease');
      end;
    end
    else if Ty.Kind = tyDynArray then
    begin
      Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [Name]));
      Self.Emit(#9'callq _DynArrayRelease');
    end
    else if Ty.Kind = tyInterface then
    begin
      if Self.IsWeakGlobal(Name) then
      begin
        Self.Emit(Format(#9'leaq %s_obj(%%rip), %%rdi', [Name]));
        Self.Emit(#9'callq _WeakClear');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s_obj(%%rip), %%rdi', [Name]));
        Self.Emit(#9'callq _ClassRelease');
      end;
    end
    else if Ty.Kind = tyRecord then
    begin
      { Record global with managed fields: release each at exit. }
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rbx', [Name]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Ty), '%rbx');
      Self.Emit(#9'popq %rbx');
    end;
  end;
end;

{ Evaluate a string literal: register it in the pool if new, then emit
  leaq __sN+12(%rip), %rax so %rax holds the Blaise data pointer. }
{ Assembler data directive for one non-string array-const element of the named
  element type.  Honours the element's real width (Boolean/Byte -> .byte,
  Int64/pointer -> .quad, ...) so the emitted stride matches the subscript-read
  stride.  Defaults to .long (4-byte Integer) when the type is unknown. }
function TX86_64Backend.ConstElemAsmDir(const AElemType: string): string;
var
  TD: TTypeDesc;
  Sz: Integer;
begin
  { Map built-in scalar names directly so the result is correct even when
    FSymTable is unset (some callers build a codegen without a table); user
    types fall back to the table, defaulting to .long (4-byte). }
  if SameText(AElemType, 'Boolean') or SameText(AElemType, 'Byte') or
     SameText(AElemType, 'ShortInt') or SameText(AElemType, 'AnsiChar') then
    Exit(#9'.byte');
  if SameText(AElemType, 'SmallInt') or SameText(AElemType, 'Word') then
    Exit(#9'.word');
  if SameText(AElemType, 'Int64') or SameText(AElemType, 'UInt64') or
     SameText(AElemType, 'Pointer') or SameText(AElemType, 'Double') then
    Exit(#9'.quad');
  if SameText(AElemType, 'Integer') or SameText(AElemType, 'UInt32') or
     SameText(AElemType, 'LongInt') or SameText(AElemType, 'Cardinal') or
     SameText(AElemType, 'Single') then
    Exit(#9'.long');
  Sz := 4;
  if FSymTable <> nil then
  begin
    TD := FSymTable.FindType(AElemType);
    if TD <> nil then Sz := TD.RawSize();
  end;
  case Sz of
    1: Result := #9'.byte';
    2: Result := #9'.word';
    8: Result := #9'.quad';
  else
    Result := #9'.long';
  end;
end;

procedure TX86_64Backend.EmitArrayConstData(ABlock: TBlock;
  const APrefix: string);
var
  I, J, K, M: Integer;
  CD:   TConstDecl;
  TD:   TTypeDecl;
  Decl: TMethodDecl;
  Lbl:  string;
  Idx:  Integer;
  IsStr: Boolean;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    { Jumbo set constant: emit the bitmap as a byte blob under the mangled
      label (shares the const-data pass with array consts). }
    if (CD.ConstSetBytes <> nil) and (CD.ConstSetBytes.Count > 0) then
    begin
      if APrefix <> '' then
        Lbl := APrefix + '_' + CD.Name
      else if CD.ResolvedSetQbeName <> '' then
        Lbl := NativeMangle(CD.ResolvedSetQbeName)
      else
        Lbl := CD.Name;
      Self.Emit('.data');
      Self.Emit('.balign 8');
      if Copy(Lbl, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Lbl);
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ConstSetBytes.Count - 1 do
        Self.Emit(Format(#9'.byte %s', [CD.ConstSetBytes[J]]));
      Continue;
    end;
    if not CD.IsArrayConst then Continue;
    if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
    if APrefix <> '' then
      Lbl := APrefix + '_' + CD.Name
    else if CD.ResolvedQbeName <> '' then
      Lbl := NativeMangle(CD.ResolvedQbeName)
    else
      Lbl := CD.Name;
    IsStr := SameText(CD.ArrayElemType, 'string');
    if IsStr then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      Self.Emit('.data');
      Self.Emit('.balign 8');
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ArrayElements.Count - 1 do
      begin
        Idx := FStrLits.IndexOf(CD.ArrayElements[J]);
        Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
      end;
    end
    else
    begin
      Self.Emit('.data');
      Self.Emit('.balign 4');
      Self.Emit(Lbl + ':');
      for J := 0 to CD.ArrayElements.Count - 1 do
        Self.Emit(Format('%s %s',
          [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[J]]));
    end;
  end;
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.Body = nil then Continue;
    for J := 0 to Decl.Body.ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(Decl.Body.ConstDecls.Items[J]);
      if not CD.IsArrayConst then Continue;
      if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
      if CD.ResolvedQbeName <> '' then
        Lbl := NativeMangle(CD.ResolvedQbeName)
      else
        Lbl := CD.Name;
      IsStr := SameText(CD.ArrayElemType, 'string');
      if IsStr then
      begin
        for K := 0 to CD.ArrayElements.Count - 1 do
          if FStrLits.IndexOf(CD.ArrayElements[K]) < 0 then
            FStrLits.Add(CD.ArrayElements[K]);
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
        begin
          Idx := FStrLits.IndexOf(CD.ArrayElements[K]);
          Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
        end;
      end
      else
      begin
        Self.Emit('.data');
        Self.Emit('.balign 4');
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
          Self.Emit(Format('%s %s',
            [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[K]]));
      end;
    end;
  end;
  { Static (class-level) variables: register one shared global per IsClassVar
    field so EmitDataSection emits a zero-initialised slot under the mangled
    label (ClassVarEmitName).  Done for BOTH class and record types, and
    independently of any assignment (a read-only static var has no assignment to
    auto-register it via AddGlobal at the write site). }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
      RegisterClassVars(TClassTypeDef(TD.Def).Fields)
    else if TD.Def is TRecordTypeDef then
      RegisterClassVars(TRecordTypeDef(TD.Def).Fields);
  end;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    for J := 0 to TClassTypeDef(TD.Def).ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(TClassTypeDef(TD.Def).ConstDecls.Items[J]);
      if not CD.IsArrayConst then Continue;
      if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
      Lbl := TD.Name + '_' + CD.Name;
      IsStr := SameText(CD.ArrayElemType, 'string');
      if IsStr then
      begin
        for K := 0 to CD.ArrayElements.Count - 1 do
          if FStrLits.IndexOf(CD.ArrayElements[K]) < 0 then
            FStrLits.Add(CD.ArrayElements[K]);
        Self.Emit('.data');
        Self.Emit('.balign 8');
        Self.Emit('.globl ' + Lbl);
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
        begin
          Idx := FStrLits.IndexOf(CD.ArrayElements[K]);
          Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
        end;
      end
      else
      begin
        Self.Emit('.data');
        Self.Emit('.balign 4');
        Self.Emit('.globl ' + Lbl);
        Self.Emit(Lbl + ':');
        for K := 0 to CD.ArrayElements.Count - 1 do
          Self.Emit(Format('%s %s',
            [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[K]]));
      end;
    end;
    for J := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
    begin
      Decl := TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[J]);
      if Decl.Body = nil then Continue;
      for K := 0 to Decl.Body.ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(Decl.Body.ConstDecls.Items[K]);
        if not CD.IsArrayConst then Continue;
        if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
        if CD.ResolvedQbeName <> '' then
          Lbl := NativeMangle(CD.ResolvedQbeName)
        else
          Lbl := CD.Name;
        IsStr := SameText(CD.ArrayElemType, 'string');
        if IsStr then
        begin
          for M := 0 to CD.ArrayElements.Count - 1 do
            if FStrLits.IndexOf(CD.ArrayElements[M]) < 0 then
              FStrLits.Add(CD.ArrayElements[M]);
          Self.Emit('.data');
          Self.Emit('.balign 8');
          Self.Emit(Lbl + ':');
          for M := 0 to CD.ArrayElements.Count - 1 do
          begin
            Idx := FStrLits.IndexOf(CD.ArrayElements[M]);
            Self.Emit(Format(#9'.quad __s%d + 12', [Idx]));
          end;
        end
        else
        begin
          Self.Emit('.data');
          Self.Emit('.balign 4');
          Self.Emit(Lbl + ':');
          for M := 0 to CD.ArrayElements.Count - 1 do
            Self.Emit(Format('%s %s',
              [Self.ConstElemAsmDir(CD.ArrayElemType), CD.ArrayElements[M]]));
        end;
      end;
    end;
  end;
end;

procedure TX86_64Backend.EmitStrLitAddr(const AValue: string);
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Self.Emit(Format(#9'leaq __s%d + 12(%%rip), %%rax', [Idx]));
end;

{ Emit all accumulated string literal blobs to .rodata.
  Each blob: 4-byte refcnt=-1 (immortal), 4-byte length, 4-byte capacity,
  then the ASCII bytes, then a NUL terminator.
  The Blaise string data pointer convention: str_ptr = &header + 12. }
procedure TX86_64Backend.EmitStrLitSection;
var
  I:   Integer;
  Len: Integer;
begin
  if FStrLits.Count = 0 then Exit;
  Self.Emit('.section .rodata');
  for I := 0 to FStrLits.Count - 1 do
  begin
    Len := Length(FStrLits.Strings[I]);
    Self.Emit('.balign 4');
    Self.Emit(Format('__s%d:', [I]));
    Self.Emit(Format(#9'.long -1', []));       { refcnt = immortal }
    Self.Emit(Format(#9'.long %d', [Len]));    { length }
    Self.Emit(Format(#9'.long %d', [Len]));    { capacity }
    if Len > 0 then
      Self.Emit(Format(#9'.ascii "%s"', [Self.AsmEscapeString(FStrLits.Strings[I])]));
    Self.Emit(#9'.byte 0');                    { NUL terminator }
  end;
end;

{ ------------------------------------------------------------------ }
{ Class data section helpers                                           }
{ ------------------------------------------------------------------ }

{ Mangle a name for use as an assembly label: replace characters that are
  invalid in label names with underscores, matching QBE backend's QBEMangle. }
function NativeMangle(const AName: string): string;
begin
  { Delegates to the shared backend-neutral mangler in blaise.codegen
    (formerly a per-character twin of the QBE backend's QBEMangle). }
  Result := CodegenMangle(AName);
end;

function TX86_64Backend.ClassSymName(const AClassName: string): string;
var
  Sym: TSymbol;
  Owner: string;
  I: Integer;
  Ch: string;
begin
  Result := '';
  if FSymTable <> nil then
  begin
    Sym := FSymTable.Lookup(AClassName);
    if Sym <> nil then
    begin
      Owner := Sym.OwningUnit;
      { Program-scope classes keep bare names — see the QBE backend's
        ClassUnitPrefix and uSemantic.CurrentUnitPrefix. }
      if (Owner <> '') and
         not ((FProgramName <> '') and SameText(Owner, FProgramName)) and
         not SameText(Owner, 'System') and
         not ((Length(Owner) >= 4) and SameText(Copy(Owner, 0, 4), 'rtl.')) and
         not ((Length(Owner) >= 7) and SameText(Copy(Owner, 0, 7), 'blaise_')) then
      begin
        for I := 0 to Length(Owner) - 1 do
        begin
          Ch := Copy(Owner, I, 1);
          if Ch = '.' then Result := Result + '_'
          else              Result := Result + Ch;
        end;
        Result := Result + '_';
      end;
    end;
  end;
  Result := Result + NativeMangle(AClassName);
end;

procedure TX86_64Backend.EmitPropAccessorCallNative(
  const AOwnerType, AMethod: string; AVSlot: Integer);
begin
  if AVSlot >= 0 then
  begin
    { Virtual dispatch: receiver in %rdi.  Load vptr, then the function
      pointer from vtable[(Slot+1)*8] (slot 0 reserved for typeinfo). }
    Self.Emit(#9'movq (%rdi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(AVSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Self.ClassSymName(AOwnerType) + '_'
      + NativeMangle(AMethod));
end;

function TX86_64Backend.IntfTypeInfoName(const AIntfName: string): string;
begin
  if Pos('<', AIntfName) >= 0 then
    Result := NativeMangle(AIntfName)
  else
    Result := Self.ClassSymName(AIntfName);
end;

function FindMethodInClassDef(AClassDef: TClassTypeDef;
  const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  for I := 0 to AClassDef.Methods.Count - 1 do
  begin
    M := TMethodDecl(AClassDef.Methods.Items[I]);
    if SameText(M.Name, AName) then
      Exit(M);
  end;
end;

{ Compute the mangled emit name for a class method: ResolvedQbeName if set,
  else TypeName_MethodName, both passed through NativeMangle. }
function MethodEmitNameNative(ADecl: TMethodDecl; const ATypeName, AMethodName: string): string;
begin
  if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ATypeName + '_' + ADecl.Name)
  else
    Result := NativeMangle(ATypeName + '_' + AMethodName);
end;

function NativeExprOwnsRef(AExpr: TASTExpr): Boolean;
begin
  { Delegates to the shared backend-neutral predicate in blaise.codegen
    (formerly a byte-identical twin of the QBE backend's ExprOwnsRef). }
  Result := ArcExprOwnsRef(AExpr);
end;

{ Emit an immortal class-name string blob and return the label+12 reference
  (the pointer to the character data, past the 12-byte ARC/length header).
  ASymName names the data symbol (may be unit-prefixed to avoid link
  collisions); AText is the string content — the bare class/method name
  that ClassName/TestClassName must observe at runtime. }
function TX86_64Backend.EmitClassNameString(const ASymName, AText: string): string;
var
  Mangled: string;
  Len:     Integer;
begin
  Mangled := NativeMangle(ASymName);
  Result  := '__cn_' + Mangled + ' + 12';
  { Idempotent: skip if already emitted (MethodAddress and class section may
    both request the same name string). }
  if FClassNameEmitted.ContainsKey(Mangled) then
    Exit;
  FClassNameEmitted.Add(Mangled, True);
  Len := Length(AText);
  Self.Emit('.balign 4');
  Self.Emit('__cn_' + Mangled + ':');
  Self.Emit(#9'.long -1');
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.ascii "%s"', [AText]));
  Self.Emit(#9'.byte 0');
end;

procedure TX86_64Backend.EmitFieldCleanupFn(const AMangledName: string;
                                            ART: TRecordTypeDesc);
var
  Walk: TRecordTypeDesc;
  DestroyName: string;
begin
  Self.Emit('.text');
  Self.Emit('.globl _FieldCleanup_' + AMangledName);
  Self.Emit('_FieldCleanup_' + AMangledName + ':');
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  Self.Emit(#9'pushq %rbx');
  Self.Emit(#9'movq %rdi, %rbx');
  if ART <> nil then
  begin
    Walk := ART;
    while Walk <> nil do
    begin
      if Walk.HasDestroyMethod then
      begin
        if Walk.DestroyResolvedQbeName <> '' then
          DestroyName := NativeMangle(Walk.DestroyResolvedQbeName)
        else
          DestroyName := NativeMangle(Walk.Name) + '_Destroy';
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'callq ' + DestroyName);
        Break;
      end;
      Walk := Walk.Parent;
    end;
    { %rbx holds the object base and is callee-saved, so it survives the release
      calls. }
    Self.EmitRecordFieldReleases(ART, '%rbx');
  end;
  Self.Emit(#9'popq %rbx');
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.Emit('.type _FieldCleanup_' + AMangledName + ', @function');
end;

procedure TX86_64Backend.EmitRecordFieldReleases(ART: TRecordTypeDesc;
  const ABaseReg: string);
var
  I:    Integer;
  F:    TFieldInfo;
begin
  if ART = nil then Exit;
  for I := 0 to ART.Fields.Count - 1 do
  begin
    F := TFieldInfo(ART.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    { Nested record field: recurse into its managed sub-fields.  ABaseReg must
      stay pointed at the parent record (each iteration derives field addresses
      from it), so the recursion uses its own callee-saved register (%r14). }
    if F.TypeDesc.Kind = tyRecord then
    begin
      { Derive the nested record base into %r14 (callee-saved) so the recursive
        releases survive their own calls without disturbing ABaseReg. }
      Self.Emit(#9'pushq %r14');
      if F.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%s), %%r14', [F.Offset, ABaseReg]))
      else
        Self.Emit(Format(#9'movq %s, %%r14', [ABaseReg]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(F.TypeDesc), '%r14');
      Self.Emit(#9'popq %r14');
      Continue;
    end;
    { NOTE: a static-array-of-managed FIELD is intentionally NOT released here.
      EmitRecordFieldReleases must stay symmetric with EmitRecordFieldRetains /
      EmitRecordCopy, neither of which retains static-array elements; releasing
      them here without a matching retain over-releases on every record copy /
      by-value param pass and corrupts the heap.  Static-array element ARC is
      handled only for scope-exit LOCALS (the bug-#4 case).  Records with such
      fields remain a separate, latent concern. }
    if not (F.TypeDesc.IsString() or (F.TypeDesc.Kind = tyClass)
            or (F.TypeDesc.Kind = tyDynArray)
            or (F.TypeDesc.Kind = tyInterface)) then
      Continue;
    if F.IsUnretained and (F.TypeDesc.Kind = tyClass) then
      Continue;
    if F.IsWeak then
    begin
      if F.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%s), %%rdi', [F.Offset, ABaseReg]))
      else
        Self.Emit(Format(#9'movq %s, %%rdi', [ABaseReg]));
      Self.Emit(#9'callq _WeakClear');
      Continue;
    end;
    { Load the field's obj/data pointer (interface: the obj slot at +0). }
    if F.Offset > 0 then
      Self.Emit(Format(#9'movq %d(%s), %%rdi', [F.Offset, ABaseReg]))
    else
      Self.Emit(Format(#9'movq (%s), %%rdi', [ABaseReg]));
    if F.TypeDesc.IsString() then
      Self.Emit(#9'callq _StringRelease')
    else if F.TypeDesc.Kind = tyDynArray then
      Self.Emit(#9'callq _DynArrayRelease')
    else
      { tyClass and tyInterface both release the obj slot via _ClassRelease; an
        interface's itab slot at +8 is static rodata and needs no release. }
      Self.Emit(#9'callq _ClassRelease');
    if F.Offset > 0 then
      Self.Emit(Format(#9'movq $0, %d(%s)', [F.Offset, ABaseReg]))
    else
      Self.Emit(Format(#9'movq $0, (%s)', [ABaseReg]));
  end;
end;

procedure TX86_64Backend.EmitManagedReleaseAt(AType: TTypeDesc;
  const ABaseReg: string; AZero: Boolean);
begin
  if AType = nil then Exit;
  if AType.Kind = tyRecord then
  begin
    Self.EmitRecordFieldReleases(TRecordTypeDesc(AType), ABaseReg);
    Exit;
  end;
  if AType.Kind = tyStaticArray then
  begin
    Self.EmitStaticArrayReleaseElems(TStaticArrayTypeDesc(AType), ABaseReg, AZero);
    Exit;
  end;
  if not (AType.IsString() or (AType.Kind = tyClass)
          or (AType.Kind = tyDynArray) or (AType.Kind = tyInterface)) then
    Exit;
  { Load the element's obj/data pointer (interface: obj slot at +0). }
  Self.Emit(Format(#9'movq (%s), %%rdi', [ABaseReg]));
  if AType.IsString() then
    Self.Emit(#9'callq _StringRelease')
  else if AType.Kind = tyDynArray then
    Self.Emit(#9'callq _DynArrayRelease')
  else
    { tyClass and tyInterface both release the obj slot via _ClassRelease; an
      interface's itab slot at +8 is static rodata and needs no release. }
    Self.Emit(#9'callq _ClassRelease');
  if AZero then
    Self.Emit(Format(#9'movq $0, (%s)', [ABaseReg]));
end;

procedure TX86_64Backend.EmitStaticArrayReleaseElems(AType: TStaticArrayTypeDesc;
  const ABaseReg: string; AZero: Boolean);
var
  I, ElemSize: Integer;
begin
  if (AType = nil) or (AType.ElementType = nil) then Exit;
  ElemSize := AType.ElementType.RawSize();
  { Hold the array base in callee-saved %r15 and recompute each element address
    into %r14.  Both are saved/restored as a PAIR (even push count) so the
    stack stays 16-byte aligned at the per-element release callq.  Keeping the
    base in %r15 (not advancing %r14 in place) keeps the addressing correct
    under nested static arrays, whose recursive call reuses %r14. }
  Self.Emit(#9'pushq %r15');
  Self.Emit(#9'pushq %r14');
  Self.Emit(Format(#9'movq %s, %%r15', [ABaseReg]));
  for I := 0 to AType.HighBound - AType.LowBound do
  begin
    if I * ElemSize > 0 then
      Self.Emit(Format(#9'leaq %d(%%r15), %%r14', [I * ElemSize]))
    else
      Self.Emit(#9'movq %r15, %r14');
    Self.EmitManagedReleaseAt(AType.ElementType, '%r14', AZero);
  end;
  Self.Emit(#9'popq %r14');
  Self.Emit(#9'popq %r15');
end;

procedure TX86_64Backend.EmitRecordFieldRetains(ART: TRecordTypeDesc;
  const ABaseReg: string);
var
  I: Integer;
  F: TFieldInfo;
begin
  if ART = nil then Exit;
  for I := 0 to ART.Fields.Count - 1 do
  begin
    F := TFieldInfo(ART.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    if F.TypeDesc.Kind = tyRecord then
    begin
      Self.Emit(#9'pushq %r14');
      if F.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%s), %%r14', [F.Offset, ABaseReg]))
      else
        Self.Emit(Format(#9'movq %s, %%r14', [ABaseReg]));
      Self.EmitRecordFieldRetains(TRecordTypeDesc(F.TypeDesc), '%r14');
      Self.Emit(#9'popq %r14');
      Continue;
    end;
    if not (F.TypeDesc.IsString() or (F.TypeDesc.Kind = tyClass)
            or (F.TypeDesc.Kind = tyDynArray)
            or (F.TypeDesc.Kind = tyInterface)) then
      Continue;
    if F.IsUnretained and (F.TypeDesc.Kind = tyClass) then
      Continue;
    if F.IsWeak then Continue;
    if F.Offset > 0 then
      Self.Emit(Format(#9'movq %d(%s), %%rdi', [F.Offset, ABaseReg]))
    else
      Self.Emit(Format(#9'movq (%s), %%rdi', [ABaseReg]));
    if F.TypeDesc.IsString() then
      Self.Emit(#9'callq _StringAddRef')
    else if F.TypeDesc.Kind = tyDynArray then
      Self.Emit(#9'callq _DynArrayAddRef')
    else
      Self.Emit(#9'callq _ClassAddRef');
  end;
end;

procedure TX86_64Backend.EmitClassSection(ATypeDecls: TObjectList;
                                          AGenericInstances: TObjectList;
                                          ASymTable: TSymbolTable);
var
  I, J, S:   Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  CD:        TClassTypeDef;
  MD:        TMethodDecl;
  E:         TVTableEntry;
  GI:        TGenericInstance;
  MName:     string;
  CSym:      string;
  ParentStr: string;
  ImplStr:   string;
  MethStr:   string;
  AttrsStr:  string;
  PubCount:  Integer;
  Line:      string;
  EmitSys:   Boolean;
begin
  { Fixed RTL class-name strings and stubs for TObject and TCustomAttribute.
    Emitted exactly once across the whole program (the first class section that
    runs); guarded so multiple units + the program do not redefine the symbols.
    In separate-compilation (incremental unit) mode they are NOT emitted at all —
    the program object provides the single definition, so emitting them in each
    unit object would collide at link time. }
  EmitSys := (not FSystemDefsEmitted) and (not FSeparateCompile);
  Self.Emit('.data');
  if EmitSys then
  begin
    Self.EmitClassNameString('TObject', 'TObject');
    Self.EmitClassNameString('TCustomAttribute', 'TCustomAttribute');
  end;

  { User class data: name strings, method tables, typeinfo, vtables. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CD := TClassTypeDef(TD.Def);
    CSym := Self.ClassSymName(TD.Name);

    { Class-name string blob — the symbol uses the unit-prefixed name so
      __cn_ matches the typeinfo class-name reference, but the content is
      the bare class name (what ClassName must return at runtime). }
    Self.EmitClassNameString(CSym, TD.Name);

    { Published-method table: count, then (nameref, codeptr) pairs }
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
    begin
      { Emit name strings for published methods. }
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if MD.IsPublished then
          Self.EmitClassNameString(MD.Name, MD.Name);
      end;
      Self.Emit('.balign 8');
      Self.Emit('.globl methods_' + CSym);
      Self.Emit('methods_' + CSym + ':');
      Self.Emit(Format(#9'.quad %d', [PubCount]));
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if not MD.IsPublished then Continue;
        Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(MD.Name)]));
        Self.Emit(Format(#9'.quad %s', [MethodEmitNameNative(MD, TD.Name, MD.Name)]));
      end;
      MethStr := 'methods_' + CSym;
    end
    else
      MethStr := '0';
  end;

  { Generic class instances — emit class-name string blobs. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    Self.EmitClassNameString(Self.ClassSymName(GI.TypeName), GI.TypeName);
  end;

  { Typeinfo blocks — must come after all class-name strings are emitted.
    System-class typeinfo is emitted once (EmitSys). }
  if EmitSys then
  begin
    Self.Emit('.balign 8');
    { Global so separately-compiled unit objects (incremental mode) can
      reference the single program-provided system typeinfo. }
    Self.Emit('.globl typeinfo_TObject');
    Self.Emit('typeinfo_TObject:');
    Self.Emit(#9'.quad 0');          { parent = nil }
    Self.Emit(#9'.quad 0');          { impllist = nil }
    Self.Emit(#9'.quad __cn_TObject + 12');
    Self.Emit(#9'.quad 0');          { methods = nil }
    Self.Emit(#9'.quad 8');          { size = 8 (vptr only) }
    Self.Emit(#9'.quad _FieldCleanup_TObject');
    Self.Emit(#9'.quad vtable_TObject');
    Self.Emit(#9'.quad 0');          { attrs = nil }

    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_TCustomAttribute');
    Self.Emit('typeinfo_TCustomAttribute:');
    Self.Emit(#9'.quad typeinfo_TObject');
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad __cn_TCustomAttribute + 12');
    Self.Emit(#9'.quad 0');
    Self.Emit(#9'.quad 8');
    Self.Emit(#9'.quad _FieldCleanup_TCustomAttribute');
    Self.Emit(#9'.quad vtable_TCustomAttribute');
    Self.Emit(#9'.quad 0');
  end;

  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CSym := Self.ClassSymName(TD.Name);

    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + Self.ClassSymName(RT.Parent.Name)
    else
      ParentStr := '0';
    { Point at the impllist when this class OR any ancestor implements an
      interface — a descendant inherits its parent's interfaces and gets its
      own impllist (issue #130 bug3). }
    if Self.ClassOrAncestorImplements(RT) then
      ImplStr := 'impllist_' + CSym
    else
      ImplStr := '0';

    { Rebuild MethStr for typeinfo (already computed above but not stored). }
    CD := TClassTypeDef(TD.Def);
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
      MethStr := 'methods_' + CSym
    else
      MethStr := '0';

    { Class attribute RTTI table at typeinfo slot 7: a count word followed by
      one typeinfo pointer per attribute.  Referenced by _HasClassAttribute.
      Emitted before the typeinfo so the symbol is defined when slot 7
      references it; nil when the class carries no attributes.  Mirrors the
      QBE backend's attrs_<Class>. }
    if RT.ClassAttributeCount() > 0 then
    begin
      Self.Emit('.balign 8');
      Self.Emit('attrs_' + CSym + ':');
      Self.Emit(Format(#9'.quad %d', [RT.ClassAttributeCount()]));
      for J := 0 to RT.ClassAttributeCount() - 1 do
        Self.Emit(#9'.quad typeinfo_' +
          Self.ClassSymName(RT.ClassAttributeAt(J)));
      AttrsStr := 'attrs_' + CSym;
    end
    else
      AttrsStr := '0';

    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + CSym);
    Self.Emit('typeinfo_' + CSym + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(CSym)]));
    Self.Emit(#9'.quad ' + MethStr);
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize()]));
    Self.Emit(#9'.quad _FieldCleanup_' + CSym);
    Self.Emit(#9'.quad vtable_' + CSym);
    Self.Emit(#9'.quad ' + AttrsStr);   { attrs }
  end;

  { Typeinfo blocks for generic class instances. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    MName := Self.ClassSymName(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + Self.ClassSymName(RT.Parent.Name)
    else
      ParentStr := '0';
    if RT.ImplementsCount() > 0 then
      ImplStr := 'impllist_' + MName
    else
      ImplStr := '0';
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + MName);
    Self.Emit('typeinfo_' + MName + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [MName]));
    Self.Emit(#9'.quad 0');
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize()]));
    Self.Emit(#9'.quad _FieldCleanup_' + MName);
    Self.Emit(#9'.quad vtable_' + MName);
    Self.Emit(#9'.quad 0');
  end;

  { Field cleanup functions for the fixed RTL classes (once). }
  if EmitSys then
  begin
    Self.EmitFieldCleanupFn('TObject', nil);
    Self.EmitFieldCleanupFn('TCustomAttribute', nil);
  end;
  { Field cleanup for user classes. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    Self.EmitFieldCleanupFn(Self.ClassSymName(TD.Name), RT);
  end;
  { Field cleanup for generic class instances. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    Self.EmitFieldCleanupFn(Self.ClassSymName(GI.TypeName), RT);
  end;

  { Vtables — must be in .data (pointers to other data symbols). }
  Self.Emit('.data');
  if EmitSys then
  begin
    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_TObject');
    Self.Emit('vtable_TObject:');
    Self.Emit(#9'.quad typeinfo_TObject');
    Self.Emit(#9'.quad TObject_Destroy');
    Self.Emit(#9'.quad TObject_ToString');

    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_TCustomAttribute');
    Self.Emit('vtable_TCustomAttribute:');
    Self.Emit(#9'.quad typeinfo_TCustomAttribute');
    Self.Emit(#9'.quad TObject_Destroy');
    Self.Emit(#9'.quad TObject_ToString');
  end;

  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable() then Continue;
    CSym := Self.ClassSymName(TD.Name);

    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_' + CSym);
    Self.Emit('vtable_' + CSym + ':');
    Self.Emit(#9'.quad typeinfo_' + CSym);
    for S := 0 to RT.VTableCount() - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        { E.ImplName may have a '$' prefix (QBE convention) — strip it for native.
          Use StrAt for 0-based string indexing. }
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;

  { Vtables for generic class instances. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable() then Continue;
    MName := Self.ClassSymName(GI.TypeName);
    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_' + MName);
    Self.Emit('vtable_' + MName + ':');
    Self.Emit(#9'.quad typeinfo_' + MName);
    for S := 0 to RT.VTableCount() - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;

  if EmitSys then
    FSystemDefsEmitted := True;
end;

{ Lower an interface method call.  The receiver is an interface fat pointer
  (obj + itab) named AObjName; AIntf supplies the method's slot index.  The
  itab is a flat array of method-code pointers (no leading typeinfo slot, in
  contrast to a vtable), so the slot offset is MethodIndex * PtrSize.

  Calling sequence mirrors EmitMethodCallExpr: evaluate args left-to-right onto
  the stack, load the obj (Self) and the resolved code pointer into caller-saved
  scratch (%r10/%r11) that survive the pop loop, pop args into %rsi.. (shifted
  by one for Self in %rdi), set %rdi := obj, then `callq *%r11`. }
procedure TX86_64Backend.EmitInterfaceCall(const AObjName: string;
                                           AIsGlobal: Boolean;
                                           AIsVarParam: Boolean;
                                           AIntf: TInterfaceTypeDesc;
                                           const AMethName: string;
                                           AArgs: TObjectList);
var
  I, SlotOff, Ps, ArgN: Integer;
  Arg: TASTExpr;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  RecvOnStack: Boolean;
  DiscSz: Integer;
begin
  { x86_64: pointers are 8 bytes (this backend's invariant, like the rest of the
    file).  i386/arm64 backends will be separate TNativeBackend subclasses. }
  Ps := 8;
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  RecvOnStack := False;
  if (AObjExpr <> nil) and (AObjExpr is TFuncCallExpr) then
  begin
    { Function-call receiver (GetDriver().Info()): evaluate it FIRST via the
      sret convention — it is a call and would clobber pushed args.  The
      owned (+1) fat pair stays at (%rsp) until after the dispatch, then the
      obj is released. }
    Self.EmitIntfSretCall(TFuncCallExpr(AObjExpr));
    RecvOnStack := True;
  end;
  DiscSz := 0;
  if ADiscardIntfRet then
  begin
    { Throwaway sret buffer for a DISCARDED interface return: without it the
      callee would write its 16-byte fat-pointer return through %rdi. }
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
    DiscSz := 16;
  end;
  { Hoist record-call args and (shape-classified) string args — the
    implementing method's const-ness is invisible at an interface call site,
    so every string-typed value argument is protected by shape.  The var
    flags recorded on the interface type mark by-reference positions. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := AIntf.MethodParamVarFlagsStr(AIntf.MethodIndex(AMethName));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, AArgs, HD, HK);
  Pushed := 0;
  { Evaluate args left-to-right and push them.  Interface args push two values
    (obj then itab); all other args push one.  Pass nil as the TMethodParam so
    EmitMethodArgPush falls through to scalar for non-interface args. }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value. }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in interface dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    { Track bytes pushed so far — hoisted-value reloads are %rsp-relative.
      var positions always occupy one slot, even for interface-typed args. }
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Load obj (Self) into %r10 and the itab into %rax, then index the itab.
    For a field receiver the fat pointer is contiguous (obj at the field
    address, itab at +8); EmitInterfaceFieldAddr leaves that address in %r10.
    The receiver shapes that need EmitExprToEax (FA.Base) are not yet reachable
    here — args are already on the stack, so only the call-free shapes (class
    access, local/global record, var-param) are safe; reject the rest loudly. }
  if RecvOnStack then
  begin
    { Receiver fat pair sits above the discard buffer + hoist region + args. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%r10', [Pushed + HTotal + DiscSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [Pushed + HTotal + DiscSz + 8]));
  end
  else if (AObjExpr <> nil) and (AObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if (AObjExpr <> nil) and (AObjExpr is TStringSubscriptExpr) then
  begin
    { Static-array interface element receiver (Arr[I].M()): the element is a
      contiguous fat pointer (obj at the element address, itab at +8). }
    Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');   { itab }
    Self.Emit(#9'movq (%r10), %r10');    { obj }
  end
  else if AIsVarParam then
  begin
    { var/out interface param receiver: the slot holds the address of the
      caller's contiguous fat pointer — obj at +0, itab at +8. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(AObjName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.IntfObjOperand(AObjName, AIsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax', [Self.IntfItabOperand(AObjName, AIsGlobal)]));
  end;
  SlotOff := AIntf.MethodIndex(AMethName) * Ps;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Pop args into %rsi/%rdx/... (shift by 1 for %rdi = Self).
    Count slots: interface args occupy 2 slots each, except at var
    positions (one address slot). }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  if ADiscardIntfRet then
  begin
    { sret convention: %rdi = buffer, %rsi = Self, visible args from %rdx. }
    for I := SlotOff - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 2));
    Self.Emit(Format(#9'leaq %d(%%rsp), %%rdi', [HTotal]));
    Self.Emit(#9'movq %r10, %rsi');
  end
  else
  begin
    for I := SlotOff - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    Self.Emit(#9'movq %r10, %rdi');
  end;
  Self.Emit(#9'callq *%r11');
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  if ADiscardIntfRet then
  begin
    { Discarded owned return: release the obj half; statement position, so
      no live result registers to preserve. }
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'addq $16, %rsp');
  end;
  if RecvOnStack then
  begin
    { Release the owned receiver pair; preserve the dispatch result regs
      (this path also serves expression position). }
    Self.Emit(#9'subq $24, %rsp');
    Self.Emit(#9'movq %rax, 0(%rsp)');
    Self.Emit(#9'movq %rdx, 8(%rsp)');
    Self.Emit(#9'movsd %xmm0, 16(%rsp)');
    Self.Emit(#9'movq 24(%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq 0(%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rdx');
    Self.Emit(#9'movsd 16(%rsp), %xmm0');
    Self.Emit(#9'addq $40, %rsp');
  end;
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitInterfaceFieldCall(AFld: TFieldInfo;
  AIntf: TInterfaceTypeDesc; const AMethName: string; AArgs: TObjectList);
{ Dispatch an interface method call through a class field.  The fat pointer
  lives at Self + AFld.Offset (obj) and Self + AFld.Offset + 8 (itab). }
var
  I, SlotOff, ArgN: Integer;
  Arg: TASTExpr;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
begin
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  if ADiscardIntfRet then
  begin
    { Throwaway sret buffer for a DISCARDED interface return: without it the
      callee would write its 16-byte fat-pointer return through %rdi. }
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
  end;
  { Same unknown-signature hoist as EmitInterfaceCall. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := AIntf.MethodParamVarFlagsStr(AIntf.MethodIndex(AMethName));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, AArgs, HD, HK);
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value. }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in field dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    { Track bytes pushed so far — hoisted-value reloads are %rsp-relative.
      var positions always occupy one slot, even for interface-typed args. }
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Load Self and compute field base; use %r11 for base pointer. }
  Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('Self')]));
  if AFld.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %%r11', [AFld.Offset]));
  { Load obj into %r10, itab into %rax. }
  Self.Emit(#9'movq (%r11), %r10');
  Self.Emit(#9'movq 8(%r11), %rax');
  SlotOff := AIntf.MethodIndex(AMethName) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Count total slots then pop in reverse; var positions take one slot. }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  if ADiscardIntfRet then
  begin
    { sret convention: %rdi = buffer, %rsi = Self, visible args from %rdx. }
    for I := SlotOff - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 2));
    Self.Emit(Format(#9'leaq %d(%%rsp), %%rdi', [HTotal]));
    Self.Emit(#9'movq %r10, %rsi');
  end
  else
  begin
    for I := SlotOff - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    Self.Emit(#9'movq %r10, %rdi');
  end;
  Self.Emit(#9'callq *%r11');
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  if ADiscardIntfRet then
  begin
    { Discarded owned return: release the obj half (statement position). }
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'addq $16, %rsp');
  end;
  HD.Free();
  HK.Free();
end;

{ An interface method maps to one of ARec's vtable slots.  When that slot is
  abstract, the itab entry must point at _AbstractMethodError (the concrete
  symbol does not exist on an abstract base). }
function TX86_64Backend.IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                              const AMethName: string): Boolean;
var
  Slot: Integer;
begin
  Slot := ARec.FindVTableSlot(AMethName);
  if Slot < 0 then
    Result := False
  else
    Result := ARec.VTableEntryAt(Slot).IsAbstract;
end;

{ True when AClassRT or any of its ancestors implements at least one interface.
  A descendant inherits its parent's interface implementations (issue #130
  bug3), so the whole class parent chain must be scanned. }
function TX86_64Backend.ClassOrAncestorImplements(AClassRT: TRecordTypeDesc): Boolean;
var
  Walk: TRecordTypeDesc;
begin
  Walk := AClassRT;
  while Walk <> nil do
  begin
    if Walk.ImplementsCount() > 0 then Exit(True);
    Walk := Walk.Parent;
  end;
  Result := False;
end;

{ Native label for AClassRT's implementation of interface method AMethName.
  Prefers the vtable slot's resolved ImplName (so an inherited method points at
  the ancestor's body and an override at the descendant's — issue #130 bug3);
  the ImplName may carry a leading '$' (QBE convention) which is stripped, then
  NativeMangle is applied.  Falls back to the declaring-class method name. }
function TX86_64Backend.ItabMethodRefNative(AClassRT: TRecordTypeDesc;
  ATD: TTypeDecl; const AMethName: string;
  ATypeDecls: TObjectList): string;
var
  Slot:    Integer;
  E:       TVTableEntry;
  CurTD:   TTypeDecl;
  CD:      TClassTypeDef;
  MD:      TMethodDecl;
  I:       Integer;
  CurName: string;
begin
  if AClassRT <> nil then
  begin
    Slot := AClassRT.FindVTableSlot(AMethName);
    if Slot >= 0 then
    begin
      E := AClassRT.VTableEntryAt(Slot);
      if (E <> nil) and (E.ImplName <> '') then
      begin
        if StrAt(E.ImplName, 0) = 36 then   { 36 = '$' }
          Exit(NativeMangle(StrCopyTail(E.ImplName, 1)))
        else
          Exit(NativeMangle(E.ImplName));
      end;
    end;
  end;
  { No vtable slot — a non-virtual interface method.  Walk the AST class chain
    (self, then ParentName ancestors) to the nearest class that DECLARES the
    method and name $<declaringclass>_<method>; naming $<thisclass>_<method> for
    an inherited method links to a symbol that does not exist (issue #130 bug3). }
  CurTD := ATD;
  while CurTD <> nil do
  begin
    if not (CurTD.Def is TClassTypeDef) then break;
    CD := TClassTypeDef(CurTD.Def);
    MD := FindMethodInClassDef(CD, AMethName);
    if MD <> nil then
      Exit(MethodEmitNameNative(MD, CurTD.Name, AMethName));
    CurName := CD.ParentName;
    CurTD   := nil;
    if (CurName <> '') and (ATypeDecls <> nil) then
      for I := 0 to ATypeDecls.Count - 1 do
        if SameText(TTypeDecl(ATypeDecls.Items[I]).Name, CurName) then
        begin
          CurTD := TTypeDecl(ATypeDecls.Items[I]);
          break;
        end;
  end;
  Result := MethodEmitNameNative(
              FindMethodInClassDef(TClassTypeDef(ATD.Def), AMethName),
              ATD.Name, AMethName);
end;

{ Emit typeinfo / itab / impllist blocks for interfaces and implementing
  classes.  Mirrors the QBE backend's EmitInterfaceDefs:

    typeinfo_IFoo:        .quad 0            (address IS the identity token)
    itab_TFoo_IFoo:       .quad TFoo_DoIt, .quad TFoo_GetVal   (decl order)
    impllist_TFoo:        .quad typeinfo_IFoo, .quad itab_TFoo_IFoo, .quad 0

  impllist is a NULL-terminated array of (typeinfo, itab) pairs, walked by the
  _GetItab runtime helper for `as`-casts. }
procedure TX86_64Backend.EmitInterfaceDefs(ATypeDecls: TObjectList;
                                           AGenericInstances: TObjectList;
                                           AGenericIntfInstances: TObjectList;
                                           ASymTable: TSymbolTable);
var
  I, J, K:    Integer;
  TD:         TTypeDecl;
  TDesc:      TTypeDesc;
  IntfDesc:   TInterfaceTypeDesc;
  ClassRT:    TRecordTypeDesc;
  GI:         TGenericInstance;
  GII:        TGenericInterfaceInstance;
  CSym:       string;
  MName:      string;
  MethName:   string;
  MethRef:    string;
  MDecl:      TMethodDecl;
  EmitIntfs:  TObjectList;
  IntfWalk:   TInterfaceTypeDesc;
  ClassWalk:  TRecordTypeDesc;
begin
  { Typeinfo blocks for every plain interface. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    CSym := Self.ClassSymName(TD.Name);
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + CSym);
    Self.Emit('typeinfo_' + CSym + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Typeinfo blocks for generic interface instances. }
  for I := 0 to AGenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AGenericIntfInstances.Items[I]);
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + GII.InstName);
    Self.Emit('typeinfo_' + GII.InstName + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Itab and impllist blocks for each implementing class. }
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := ASymTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    { Skip only when neither this class NOR any ancestor implements an interface
      — a descendant inherits its parent's interfaces (issue #130 bug3). }
    if not Self.ClassOrAncestorImplements(ClassRT) then Continue;
    CSym := Self.ClassSymName(TD.Name);

    { Collect each implemented interface PLUS every ancestor on its parent
      chain so a class instance can narrow directly to a base interface (an
      ancestor's methods are a prefix of the descendant's itab — same impl
      pointers).  Also walk the CLASS parent chain to pick up interfaces an
      ancestor implements (issue #130 bug3).  Dedup keeps one itab per
      (class, interface). }
    EmitIntfs := TObjectList.Create(False);
    try
      ClassWalk := ClassRT;
      while ClassWalk <> nil do
      begin
        for J := 0 to ClassWalk.ImplementsCount() - 1 do
        begin
          IntfWalk := ClassWalk.ImplementsIntfAt(J);
          while IntfWalk <> nil do
          begin
            if EmitIntfs.IndexOf(IntfWalk) < 0 then EmitIntfs.Add(IntfWalk);
            IntfWalk := IntfWalk.Parent;
          end;
        end;
        ClassWalk := ClassWalk.Parent;
      end;

      { One itab per interface — a flat array of method-code ptrs in interface
        declaration order. }
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc := TInterfaceTypeDesc(EmitIntfs.Items[J]);
        Self.Emit('.balign 8');
        Self.Emit('.globl itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
        Self.Emit('itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name) + ':');
        for K := 0 to IntfDesc.MethodCount() - 1 do
        begin
          MethName := IntfDesc.MethodName(K);
          if Self.IsAbstractClassMethod(ClassRT, MethName) then
            MethRef := '_AbstractMethodError'
          else
            { Resolve via the vtable so an inherited (non-overridden) method
              points at the ancestor's body and an override at the descendant's
              (issue #130 bug3). }
            MethRef := Self.ItabMethodRefNative(ClassRT, TD, MethName, ATypeDecls);
          Self.Emit(#9'.quad ' + MethRef);
        end;
      end;

      { One impllist per class: NULL-terminated (typeinfo, itab) pairs.
        Includes ancestor interfaces so _GetItab(obj, typeinfo_IBase) resolves. }
      Self.Emit('.balign 8');
      Self.Emit('.globl impllist_' + CSym);
      Self.Emit('impllist_' + CSym + ':');
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc := TInterfaceTypeDesc(EmitIntfs.Items[J]);
        Self.Emit(#9'.quad typeinfo_' + Self.IntfTypeInfoName(IntfDesc.Name));
        Self.Emit(#9'.quad itab_' + CSym + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
      end;
      Self.Emit(#9'.quad 0');
    finally
      EmitIntfs.Free();
    end;
  end;

  { Itab and impllist for generic class instances that implement interfaces. }
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    ClassRT := TRecordTypeDesc(GI.TypeDesc);
    if ClassRT.ImplementsCount() = 0 then Continue;
    MName := Self.ClassSymName(GI.TypeName);

    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      CSym := Self.IntfTypeInfoName(IntfDesc.Name);
      Self.Emit('.balign 8');
      Self.Emit('.globl itab_' + MName + '_' + CSym);
      Self.Emit('itab_' + MName + '_' + CSym + ':');
      for K := 0 to IntfDesc.MethodCount() - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if Self.IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '_AbstractMethodError'
        else
        begin
          MDecl := FindMethodInClassDef(GI.ClassDef, MethName);
          if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
            MethRef := NativeMangle(MDecl.ResolvedQbeName)
          else
            MethRef := MName + '_' + MethName;
        end;
        Self.Emit(#9'.quad ' + MethRef);
      end;
    end;

    Self.Emit('.balign 8');
    Self.Emit('.globl impllist_' + MName);
    Self.Emit('impllist_' + MName + ':');
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit(#9'.quad typeinfo_' + Self.IntfTypeInfoName(IntfDesc.Name));
      Self.Emit(#9'.quad itab_' + MName + '_' + Self.IntfTypeInfoName(IntfDesc.Name));
    end;
    Self.Emit(#9'.quad 0');
  end;
end;

procedure TX86_64Backend.EmitInterfaceAssign(AAsgn: TAssignment);
{ Strong-reference interface assignment.  The LHS fat pointer is (obj, itab).
  In every form the obj slot co-owns the backing class instance: the new obj is
  retained and the prior obj released before the store.  The itab slot points at
  static rodata and is not refcounted. }
var
  Intf:    TInterfaceTypeDesc;
  ClassRT: TRecordTypeDesc;
  AE:      TAsExpr;
  ItabSym: string;
  ObjOp:   string;
  ItabOp:  string;
  LFail:   string;
  LEnd:    string;
  ISFld:   TFieldInfo;
begin
  Intf := TInterfaceTypeDesc(AAsgn.ResolvedLhsType);
  { Implicit Self.Field assignment: the fat pointer lives inside the object at
    Self + FieldOffset (obj) and Self + FieldOffset + 8 (itab).
    Handle entirely here rather than falling through to the ObjOp/ItabOp paths
    below (which use fixed operand strings that could be clobbered by calls). }
  if AAsgn.ImplicitSelfField <> nil then
  begin
    ISFld := TFieldInfo(AAsgn.ImplicitSelfField);
    { Compute Self + FieldOffset into %r15 (callee-saved: survives callq). }
    Self.Emit(#9'pushq %r15');
    Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
    if ISFld.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
    { Now (%r15) = obj slot, 8(%r15) = itab slot. }
    if AAsgn.Expr.ResolvedType.Kind = tyClass then
    begin
      ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
      Self.EmitExprToEax(AAsgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if AAsgn.Expr is TNilLiteral then
    begin
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq $0, (%r15)');
      Self.Emit(#9'movq $0, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TIdentExpr) then
    begin
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TFieldAccessExpr) then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AAsgn.Expr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq %rcx, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr is TFuncCallExpr) and
            (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
    begin
      { Interface-method call (itab dispatch) returning an interface — the
        callee hands back an OWNED +1 fat pointer in the sret buffer. }
      Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
    begin
      { Class-receiver method call returning an interface — sret protocol;
        the callee hands back an OWNED +1 fat pointer. }
      Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface-field assignment RHS');
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { sret interface Result: the Result slot holds a pointer to the caller's
    16-byte buffer.  Dereference it into %r15 so that (%r15)=obj, 8(%r15)=itab. }
  if (FSretFunc and SameText(AAsgn.Name, 'Result')) or AAsgn.IsVarParam then
  begin
    { Both shapes hold a POINTER to the caller's 16-byte fat-pointer block:
      the sret Result slot, or a var/out interface param slot. }
    Self.Emit(#9'pushq %r15');
    if AAsgn.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand(AAsgn.Name)]))
    else
      Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Result')]));
    ObjOp  := '(%r15)';
    ItabOp := '8(%r15)';
    if AAsgn.Expr.ResolvedType.Kind = tyClass then
    begin
      ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
      Self.EmitExprToEax(AAsgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if AAsgn.Expr is TNilLiteral then
    begin
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq $0, (%r15)');
      Self.Emit(#9'movq $0, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TIdentExpr) then
    begin
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr is TFuncCallExpr) and
            (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
            (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
    begin
      { Interface-method call (itab dispatch) returning an interface — the
        callee hands back an OWNED +1 fat pointer in the sret buffer. }
      Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else if (AAsgn.Expr is TMethodCallExpr) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
            (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
    begin
      { Class-receiver method call returning an interface — sret protocol;
        the callee hands back an OWNED +1 fat pointer. }
      Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported sret interface Result assignment RHS');
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { Register a global LHS so EmitDataSection emits its _obj/_itab labels. }
  if not Self.IsLocal(AAsgn.Name) then
  begin
    Self.AddGlobal(AAsgn.Name, AAsgn.ResolvedLhsType);
    if AAsgn.IsThreadVar then Self.MarkThreadVar(AAsgn.Name);
    if AAsgn.IsWeakLhs then Self.MarkWeakGlobal(AAsgn.Name);
  end;
  ObjOp  := Self.IntfObjOperand(AAsgn.Name, AAsgn.IsGlobal);
  ItabOp := Self.IntfItabOperand(AAsgn.Name, AAsgn.IsGlobal);

  { F := nil — release old obj, zero both slots. }
  if AAsgn.Expr is TNilLiteral then
  begin
    if AAsgn.IsWeakLhs then
      Self.Emit(Format(#9'leaq %s, %%rdi', [ObjOp]))
    else
      Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));
    if AAsgn.IsWeakLhs then
      Self.Emit(#9'callq _WeakClear')
    else
      Self.Emit(#9'callq _ClassRelease');
    Self.Emit(Format(#9'movq $0, %s', [ObjOp]));
    Self.Emit(Format(#9'movq $0, %s', [ItabOp]));
    Exit;
  end;

  { F := T as IFoo — runtime itab lookup via _GetItab(obj, typeinfo_IFoo).
    A nil result means the cast failed; raise EInvalidCast. }
  if (AAsgn.Expr is TAsExpr) and
     (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE := TAsExpr(AAsgn.Expr);
    Self.EmitExprToEax(AE.Obj);          { obj -> %rax }
    Self.Emit(#9'pushq %rax');            { keep obj on the stack across calls }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi', [Self.IntfTypeInfoName(AE.TypeName)]));
    Self.Emit(#9'callq _GetItab');         { itab -> %rax }
    Self.Emit(#9'pushq %rax');            { keep itab; stack now (itab, obj) }
    LFail := Self.NewLabel('as_fail');
    LEnd  := Self.NewLabel('as_end');
    Self.Emit(#9'testq %rax, %rax');
    Self.Emit(#9'jz ' + LFail);
    { Cast OK: addref new obj, release old, store obj + itab. }
    Self.Emit(#9'movq 8(%rsp), %rdi');     { obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %rax');              { obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'jmp ' + LEnd);
    Self.Emit(LFail + ':');
    Self.Emit(#9'addq $16, %rsp');         { discard pushed obj+itab }
    Self.Emit(#9'callq _Raise_InvalidCast');
    Self.Emit(LEnd + ':');
    Exit;
  end;

  { F := T where T is a class implementing the interface — static itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyClass) then
  begin
    ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
    ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
    Self.EmitExprToEax(AAsgn.Expr);       { new obj -> %rax }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Exit;
  end;

  { F := G where both sides are interface-typed — copy obj+itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TIdentExpr) then
  begin
    if AAsgn.IsWeakLhs then
    begin
      Self.Emit(Format(#9'movq %s, %%rsi',
        [Self.IntfObjOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(Format(#9'leaq %s, %%rdi', [ObjOp]));
      Self.Emit(#9'callq _WeakAssign');
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfItabOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    end
    else
    begin
      { Load src obj+itab; addref new obj; release old obj; store both. }
      Self.PushIntfIdentPair(TIdentExpr(AAsgn.Expr));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');              { new obj }
      Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
      Self.Emit(#9'popq %rax');              { itab }
      Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    end;
    Exit;
  end;

  { F := H.G where the RHS is an interface stored in a record/class field.  The
    fat pointer is contiguous in the field's memory (obj at the field address,
    itab at +8) — load both, addref the new obj, release the old, store both. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TFieldAccessExpr) then
  begin
    { Compute the source field's base address into %r15 (callee-saved). }
    Self.Emit(#9'pushq %r15');
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AAsgn.Expr), '%r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');             { itab }
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');             { obj; stack now (obj, itab) }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { F := Arr[I] where the RHS is an interface element of a static array.  The
    element is a contiguous fat pointer (obj at the element address, itab at +8)
    — compute the element address into %r15 and copy obj+itab with ARC, mirroring
    the field-access case above. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TStringSubscriptExpr) then
  begin
    Self.Emit(#9'pushq %r15');
    Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AAsgn.Expr), '%r15');
    Self.Emit(#9'movq 8(%r15), %rax');     { src itab }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq (%r15), %rax');      { src obj }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { F := FuncReturningInterface() — sret convention: allocate a 16-byte buffer
    on the stack, pass its address as the hidden first arg (%rdi), call the
    function (which writes obj+itab into the buffer), then move the result to
    the LHS with ARC. }
  if (AAsgn.Expr is TFuncCallExpr) and
     (TFuncCallExpr(AAsgn.Expr).ResolvedDecl <> nil) and
     (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
     (TMethodDecl(TFuncCallExpr(AAsgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyInterface) then
  begin
    Self.EmitIntfSretCall(TFuncCallExpr(AAsgn.Expr));
    { Sret buffer at (%rsp): obj at 0(%rsp), itab at 8(%rsp). }
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  { F := SomeIntf.Method(args) where Method (itab dispatch) returns an
    interface — same sret protocol; the callee hands back an OWNED +1 fat
    pointer, so release the old obj and store without an extra AddRef. }
  if (AAsgn.Expr is TMethodCallExpr) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyInterface) then
  begin
    Self.EmitIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  { F := Obj.Method() where Obj is class-typed and Method returns an
    interface — sret protocol with the receiver in %rsi; the callee hands
    back an OWNED +1 fat pointer, so release the old obj and store without
    an extra AddRef. }
  if (AAsgn.Expr is TMethodCallExpr) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AAsgn.Expr).ResolvedClassType.Kind = tyClass) then
  begin
    Self.EmitClassIntfSretMethodCall(TMethodCallExpr(AAsgn.Expr));
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));  { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'movq 8(%rsp), %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'addq $16, %rsp');
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported interface-field assignment RHS');
end;

procedure TX86_64Backend.EmitInterfaceToFieldSlotsAt(AExpr: TASTExpr;
  const ABaseReg: string; AOffset: Integer; AIntfType: TTypeDesc);
{ Store an interface RHS into a contiguous fat-pointer field.  The destination
  base address is taken from ABaseReg into the callee-saved %r15 so it survives
  the ARC calls; obj slot is (%r15), itab slot is 8(%r15). }
var
  Intf:    TInterfaceTypeDesc;
  ClassRT: TRecordTypeDesc;
  ItabSym: string;
begin
  if (AIntfType = nil) or (AIntfType.Kind <> tyInterface) then
    raise ENativeCodeGenError.Create(
      'native backend: interface-field store needs a destination interface type');
  Intf := TInterfaceTypeDesc(AIntfType);

  { Capture the destination base address in a callee-saved register. }
  Self.Emit(#9'pushq %r15');
  Self.Emit(Format(#9'movq %s, %%r15', [ABaseReg]));
  if AOffset > 0 then
    Self.Emit(Format(#9'addq $%d, %%r15', [AOffset]));
  { Now (%r15) = obj slot, 8(%r15) = itab slot. }

  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'movq (%r15), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'movq $0, (%r15)');
    Self.Emit(#9'movq $0, 8(%r15)');
  end
  else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
  begin
    ClassRT := TRecordTypeDesc(AExpr.ResolvedType);
    ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(Intf.Name);
    Self.EmitExprToEax(AExpr);
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'movq (%r15), %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');
    Self.Emit(#9'movq %rax, (%r15)');
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
    Self.Emit(#9'movq %rax, 8(%r15)');
  end
  else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyInterface) then
  begin
    { Interface source: copy obj+itab from the source's fat pointer.  A named
      interface local/global uses split _obj/_itab slots; an interface stored in
      a record/class field uses a contiguous fat pointer (obj / obj+8). }
    if AExpr is TIdentExpr then
    begin
      if TIdentExpr(AExpr).IsImplicitSelf and
         (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
        if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rax',
            [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
        Self.Emit(#9'movq 8(%rax), %rcx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'pushq %rcx');
      end
      else
        Self.PushIntfIdentPair(TIdentExpr(AExpr));
    end
    else if AExpr is TFieldAccessExpr then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AExpr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');
    end
    else if AExpr is TStringSubscriptExpr then
    begin
      { Static-array interface element source (Arr[I]): contiguous fat pointer. }
      Self.EmitIntfStaticElemAddr(TStringSubscriptExpr(AExpr), '%rax');
      Self.Emit(#9'movq 8(%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { itab }
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'pushq %rcx');           { obj on top }
    end
    else if (AExpr is TFuncCallExpr) and
            (TFuncCallExpr(AExpr).ResolvedDecl <> nil) then
    begin
      Self.EmitIntfSretCall(TFuncCallExpr(AExpr));
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'movq (%rsp), %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'movq 8(%rsp), %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
      Self.Emit(#9'addq $16, %rsp');
      Self.Emit(#9'popq %r15');
      Exit;
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface source for interface-field store');
    Self.Emit(#9'movq (%rsp), %rdi');        { new obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(#9'movq (%r15), %rdi');        { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');                { new obj }
    Self.Emit(#9'movq %rax, (%r15)');
    Self.Emit(#9'popq %rax');                { itab }
    Self.Emit(#9'movq %rax, 8(%r15)');
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: unsupported interface-field store RHS');

  Self.Emit(#9'popq %r15');
end;

procedure TX86_64Backend.EmitInterfaceFieldAddr(AFA: TFieldAccessExpr;
  const ADstReg: string);
{ Leave the address of AFA's interface field (the contiguous obj/itab fat
  pointer) in ADstReg.  Mirrors the receiver-base resolution used by the
  field-read path, but stops at the address rather than loading a value. }
begin
  if AFA.Base <> nil then
  begin
    { Nested receiver expression (e.g. Outer.Inner.G): evaluate it to the base
      address. }
    Self.EmitExprToEax(AFA.Base);
    Self.Emit(Format(#9'movq %%rax, %s', [ADstReg]));
  end
  else if AFA.IsImplicitSelf then
  begin
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Self'), ADstReg]));
    if (AFA.ImplicitBaseInfo <> nil) and (AFA.ImplicitBaseInfo.Offset > 0) then
      Self.Emit(Format(#9'addq $%d, %s', [AFA.ImplicitBaseInfo.Offset, ADstReg]));
    if AFA.IsClassAccess then
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  else if AFA.IsClassAccess then
  begin
    if Self.IsLocal(AFA.RecordName) then
      Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AFA.RecordName), ADstReg]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %s', [AFA.RecordName, ADstReg]));
    if AFA.IsVarParam then
      { var-param class: slot -> caller var -> instance }
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  else if AFA.IsVarParam then
  begin
    if Self.IsLocal(AFA.RecordName) then
      Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AFA.RecordName), ADstReg]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %s', [AFA.RecordName, ADstReg]));
  end
  else
    Self.EmitVarAddr(AFA.RecordName, ADstReg);
  { Add the field offset to reach the fat pointer's obj slot. }
  if AFA.FieldInfo.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %s', [AFA.FieldInfo.Offset, ADstReg]));
end;

procedure TX86_64Backend.EmitIntfStaticElemAddr(ASub: TStringSubscriptExpr;
  const ADstReg: string);
{ Leave the address of an interface element of a static array (the contiguous
  obj/itab fat pointer) in ADstReg.  Computes base + (idx - LowBound) * 16.
  The element-address arithmetic clobbers %rax/%rcx, so ADstReg should be a
  callee-saved register (e.g. %r15) when it must survive subsequent ARC calls. }
var
  SAT: TStaticArrayTypeDesc;
begin
  SAT := TStaticArrayTypeDesc(ASub.StrExpr.ResolvedType);
  Self.EmitExprToEax(ASub.IndexExpr);          { index -> %rax }
  Self.EmitStaticElemScale(SAT);
  { Base address of the array's inline storage into %rcx. }
  if (ASub.StrExpr is TIdentExpr) and
     TIdentExpr(ASub.StrExpr).IsImplicitSelf and
     (TIdentExpr(ASub.StrExpr).ImplicitFieldInfo <> nil) then
  begin
    { Static-array field of Self: inline storage at Self + field offset. }
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
    if TFieldInfo(TIdentExpr(ASub.StrExpr).ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx',
        [TFieldInfo(TIdentExpr(ASub.StrExpr).ImplicitFieldInfo).Offset]));
  end
  else if ASub.StrExpr is TIdentExpr then
  begin
    if Self.IsLocal(TIdentExpr(ASub.StrExpr).Name) then
      Self.Emit(Format(#9'leaq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(ASub.StrExpr).Name)]))
    else
      Self.EmitLeaqGlobal(TIdentExpr(ASub.StrExpr).Name, '%rcx');
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: unsupported interface static-array base expression');
  Self.Emit(Format(#9'addq %%rax, %%rcx', []));
  Self.Emit(Format(#9'movq %%rcx, %s', [ADstReg]));
end;

procedure TX86_64Backend.EmitClassMethods(ATypeDecls: TObjectList;
                                          AGenericInstances: TObjectList;
                                          AGenericRecordInstances: TObjectList;
                                          AGenericMethodInstances: TObjectList);
var
  I, J: Integer;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  RD:   TRecordTypeDef;
  GI:   TGenericInstance;
  GRI:  TGenericRecordInstance;
  GMI:  TGenericMethodInstance;
  Decl: TMethodDecl;
  SavedUnit: string;
begin
  for I := 0 to ATypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ATypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD := TClassTypeDef(TD.Def);
      for J := 0 to CD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(CD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        { Generic-method templates emit per instantiation, not as a template. }
        if Decl.TypeParams <> nil then Continue;
        Self.EmitFunctionDef(Decl, True);
      end;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD := TRecordTypeDef(TD.Def);
      for J := 0 to RD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(RD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        if Decl.TypeParams <> nil then Continue;
        Self.EmitFunctionDef(Decl, True);
      end;
    end;
  end;

  { Generic instance method bodies are template clones: their Line fields
    refer to the unit that DECLARES the template, so allocation-site
    tracking must report that unit, not the instantiating one. }
  SavedUnit := FCurrentUnitName;
  for I := 0 to AGenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AGenericInstances.Items[I]);
    if GI.DefUnitName <> '' then
      FCurrentUnitName := GI.DefUnitName
    else
      FCurrentUnitName := SavedUnit;
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl, True);
    end;
  end;
  FCurrentUnitName := SavedUnit;

  for I := 0 to AGenericRecordInstances.Count - 1 do
  begin
    GRI := TGenericRecordInstance(AGenericRecordInstances.Items[I]);
    for J := 0 to GRI.RecordDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl, True);
    end;
  end;

  { Generic METHOD instances (method-level <T>): each monomorphised body.  Its
    ResolvedQbeName encodes <Owner>_<Method><args> and OwnerTypeName is set, so
    EmitFunctionDef emits it with the implicit Self like any method. }
  for I := 0 to AGenericMethodInstances.Count - 1 do
  begin
    GMI := TGenericMethodInstance(AGenericMethodInstances.Items[I]);
    if GMI.MethodDecl.Body <> nil then
      Self.EmitFunctionDef(GMI.MethodDecl, True);
  end;
end;

{ ------------------------------------------------------------------ }
{ Frame model                                                          }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IsCaptured(const AName: string): Boolean;
begin
  Result := (FCapturedVars <> nil) and (FCapturedVars.IndexOf(AName) >= 0);
end;

procedure TX86_64Backend.EmitVarBaseToReg(const AName: string;
  AWantAddress: Boolean; const ADstReg: string);
{ Load the base of the variable AName into ADstReg, handling locals, globals
  and variables CAPTURED from an enclosing proc uniformly.

  AWantAddress = True  -> ADstReg receives the ADDRESS of the variable's own
                          storage (what `leaq` / EmitVarAddr would give for a
                          local; the record base for a plain-record variable).
  AWantAddress = False -> ADstReg receives the VALUE stored in the variable
                          (one dereference; e.g. the pointer held by a
                          var-param or class slot).

  A captured variable is reached through its hidden `_cap_<Name>` pointer slot,
  which holds the ADDRESS of the enclosing variable's storage — exactly the
  AWantAddress=True result.  For AWantAddress=False one further load yields the
  stored value, mirroring the local case. }
begin
  if Self.IsCaptured(AName) then
  begin
    Self.Emit(Format(#9'movq %s, %s',
      [Self.VarOperand('_cap_' + AName), ADstReg]));
    if not AWantAddress then
      Self.Emit(Format(#9'movq (%s), %s', [ADstReg, ADstReg]));
  end
  { sret Result: its slot holds the caller's record buffer POINTER, so the
    "address of the record" is the stored value, not a leaq of the slot.
    (A captured name is never Result, so this follows the capture branch.) }
  else if FSretFunc and SameText(AName, 'Result') then
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Result'), ADstReg]))
  else if AWantAddress then
    Self.EmitVarAddr(AName, ADstReg)
  else if Self.IsLocal(AName) then
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand(AName), ADstReg]))
  else
    Self.Emit(Format(#9'movq %s(%%rip), %s', [AName, ADstReg]));
end;

function TX86_64Backend.IsLocal(const AName: string): Boolean;
begin
  Result := (FFrame <> nil) and FFrame.ContainsKey(AName);
end;


function TX86_64Backend.VarOperand(const AName: string): string;
var
  Off: Integer;
begin
  if (FFrame <> nil) and FFrame.TryGetValue(AName, Off) then
  begin
    if Off > 0 then
      Result := Format('%d(%%rbp)', [Off])
    else
      Result := Format('-%d(%%rbp)', [-Off])
  end
  else if Self.IsThreadVarGlobal(AName) then
    Result := '%fs:' + AName + '@tpoff'
  else
    Result := AName + '(%rip)';
end;

procedure TX86_64Backend.EmitLeaqGlobal(const AName: string; const ADstReg: string);
begin
  if Self.IsThreadVarGlobal(AName) then
  begin
    Self.Emit(Format(#9'movq %%fs:0, %s', [ADstReg]));
    Self.Emit(Format(#9'leaq %s@tpoff(%s), %s', [AName, ADstReg, ADstReg]));
  end
  else
    Self.Emit(Format(#9'leaq %s(%%rip), %s', [AName, ADstReg]));
end;

procedure TX86_64Backend.EmitVarAddr(const AName: string; const ADstReg: string);
begin
  if Self.IsLocal(AName) then
    Self.Emit(Format(#9'leaq %s, %s', [Self.VarOperand(AName), ADstReg]))
  else
    Self.EmitLeaqGlobal(AName, ADstReg);
end;

function TX86_64Backend.LocalType(const AName: string): TTypeDesc;
begin
  if (FFrameTypes = nil) or (not FFrameTypes.TryGetValue(AName, Result)) then
    Result := nil;
end;

{ The obj half of an interface fat pointer.  Locals: the 16-byte slot base
  (VarOperand returns the low address = obj).  Globals: a dedicated label
  AName + '_obj', registered for emission in EmitDataSection. }
function TX86_64Backend.IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
    Result := Self.VarOperand(AName)
  else
    Result := AName + '_obj(%rip)';
end;

{ The itab half of an interface fat pointer.  Locals: 8 bytes above the obj
  slot (the slot base address is the obj operand, so add 8 to its rbp offset).
  Globals: a dedicated label AName + '_itab'. }
function TX86_64Backend.IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
var
  Off: Integer;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
  begin
    FFrame.TryGetValue(AName, Off);
    { Off is negative (slot base = obj). itab is 8 bytes higher in memory. }
    Result := Format('%d(%%rbp)', [Off + 8]);
  end
  else
    Result := AName + '_itab(%rip)';
end;

procedure TX86_64Backend.PushIntfIdentPair(AIdent: TIdentExpr);
begin
  if FSretFunc and SameText(AIdent.Name, 'Result') then
  begin
    { sret interface Result: the slot holds the caller-buffer address —
      dereference for obj (+0) and itab (+8). }
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]));
    Self.Emit(#9'movq 8(%rax), %rcx');
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'pushq %rax');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(AIdent.Name, AIdent.IsGlobal)]));
    Self.Emit(#9'pushq %rax');
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfObjOperand(AIdent.Name, AIdent.IsGlobal)]));
    Self.Emit(#9'pushq %rax');
  end;
end;

{ Load an integer-family value from memory into %rax, extended to the full
  64-bit register according to AType's width and signedness.  Narrower-than-
  32-bit loads use a sign/zero-extending move; 32-bit signed widens with
  movslq, 32-bit unsigned with a plain movl (which zero-extends the upper 32
  bits on x86-64); 64-bit is a straight movq. }
procedure TX86_64Backend.EmitLoadVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzbq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movsbq %s, %%rax', [AOperand]));
    2: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzwq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movswq %s, %%rax', [AOperand]));
    8: Self.Emit(Format(#9'movq %s, %%rax', [AOperand]));
  else
    { 4-byte: a movl into %eax zero-extends into %rax.  For a signed Integer
      sign-extend instead so the upper 32 bits carry the sign. }
    if IsUnsignedInt(AType) then
      Self.Emit(Format(#9'movl %s, %%eax', [AOperand]))
    else
      Self.Emit(Format(#9'movslq %s, %%rax', [AOperand]));
  end;
end;

{ Store the value in %rax to memory at the slot's natural width, using the
  matching register sub-view (%al / %ax / %eax / %rax). }
procedure TX86_64Backend.EmitStoreVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %%al, %s', [AOperand]));
    2: Self.Emit(Format(#9'movw %%ax, %s', [AOperand]));
    8: Self.Emit(Format(#9'movq %%rax, %s', [AOperand]));
  else
    Self.Emit(Format(#9'movl %%eax, %s', [AOperand]));
  end;
end;

{ Reserve a slot for AName of type AType in the current frame, advancing
  AOffset by the slot size (8 bytes for scalars/pointers; TotalSize rounded
  up to the next 8-byte boundary for records).  Stores the offset as a
  negative integer so VarOperand emits -N(%rbp). }
procedure TX86_64Backend.AddSlot(const AName: string; AType: TTypeDesc;
                                 var AOffset: Integer);
var
  Sz: Integer;
begin
  if ((AType <> nil) and (AType.Kind in [tyRecord, tyStaticArray])) or
     IsJumboSet(AType) then
    Sz := (AType.RawSize() + 7) and (-8)   { full inline aggregate slot }
  else if (AType <> nil) and (AType.Kind = tyInterface) then
    Sz := 16   { fat pointer: obj slot (+0) then itab slot (+8) }
  else if (AType <> nil) and (AType.Kind = tyProcedural) and
          TProceduralTypeDesc(AType).IsMethodPtr then
    Sz := 16   { method pointer: code slot (+0) and data/self slot (+8) }
  else
    Sz := 8;
  Inc(AOffset, Sz);
  FFrame.Add(AName, -AOffset);
  FFrameTypes.Add(AName, AType);
  Self.DbgRecordSlot(AName, AType, -AOffset);
end;

procedure TX86_64Backend.BuildFrame(ADecl: TMethodDecl);
var
  I, J, K, Offset, StackOff, TryCount, IntIdx2, XmmIdx2: Integer;
  P:    TMethodParam;
  VD:   TVarDecl;
  HasJumbo: Boolean;
begin
  Self.ClearFrame();
  FFrame      := TDictionary<string, Integer>.Create();
  FFrameTypes := TDictionary<string, TTypeDesc>.Create();
  Offset   := 0;
  StackOff := 16;  { first stack arg: +16(%rbp) — above saved %rbp and ret addr }

  { Determine sret-ness UP FRONT.  The hidden sret buffer pointer consumes an
    integer register (%rdi), which shifts where the visible params land — so the
    param-register accounting below must know this before assigning slots.  This
    classification was historically done only when allocating the Result slot
    (further down), i.e. AFTER the param loop, leaving FSretFunc stale from the
    previous function and mis-placing a stack-passed param of an sret method as
    the last register param. }
  FSretFunc := False;
  FRecRetClass := rcSret;
  if ADecl.ResolvedReturnType <> nil then
  begin
    if (ADecl.ResolvedReturnType.Kind = tyInterface) or
       IsJumboSet(ADecl.ResolvedReturnType) or
       (ADecl.ResolvedReturnType.Kind = tyStaticArray) then
      FSretFunc := True
    else if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      FRecRetClass := ClassifyRecordReturn(
        TRecordTypeDesc(ADecl.ResolvedReturnType));
      FSretFunc := FRecRetClass = rcSret;
    end;
  end;

  { Captured outer-scope variables are prepended as implicit leading pointer
    params before Self and normal params.  Each captured var gets a pointer-size
    slot named '_cap_<VarName>' in the frame. }
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
      Self.AddSlot('_cap_' + ADecl.CapturedVars.Strings[I], nil, Offset);

  { For class methods, Self is the implicit first integer param (%rdi).
    Allocate a pointer-size slot for it; normal params start at IntIdx=1.
    A `static` method takes NO implicit Self (like a class function/Java
    static), so no Self slot is reserved and the first user param occupies
    %rdi directly. }
  if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
    Self.AddSlot('Self', nil, Offset);  { nil = pointer size (8 bytes) }

  { Params: first 6 integer register slots are register-passed (spilled to
    negative slots in prologue); slots 7+ are on the stack at positive %rbp
    offsets.  Open-array params consume TWO register slots each: data ptr and
    high index.  Track IntIdx2 separately from the logical param index I. }
  begin
    IntIdx2 := 0;
    XmmIdx2 := 0;
    { Captured vars, the sret buffer pointer, and Self EACH consume one integer
      register slot, and they stack: an sret-returning class/interface method
      uses %rdi for the buffer AND %rsi for Self, so the count must include
      BOTH (not one or the other).  This mirrors the prologue spill loop, which
      sets IntIdx := 1 for sret then Inc's again for Self; the two must agree or
      a stack-passed param is mistaken for the last register param. }
    if (ADecl.CapturedVars <> nil) then
      Inc(IntIdx2, ADecl.CapturedVars.Count);
    if FSretFunc then
      Inc(IntIdx2);  { sret buffer pointer in %rdi }
    if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
      Inc(IntIdx2);  { Self in the next integer register (static methods have none) }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      P := TMethodParam(ADecl.Params.Items[I]);
      if P.IsOpenArray then
      begin
        { Two register slots: data pointer and high index. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, nil, Offset)   { nil = pointer-size (8 bytes) }
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, nil);
          Self.DbgRecordSlot(P.ParamName, nil, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName + '_high', nil, Offset)
        else
        begin
          FFrame.Add(P.ParamName + '_high', StackOff);
          FFrameTypes.Add(P.ParamName + '_high', nil);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end
      else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      begin
        { Interface param: fat pointer = two consecutive integer register slots.
          Allocate a single 16-byte slot (obj at base, itab at base+8) so that
          IntfObjOperand/IntfItabOperand can address both halves.  Two IntIdx
          increments mirror the register-passing convention. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 16);
        end;
        Inc(IntIdx2);
        { Second slot (itab): if register-passed, no separate frame entry needed
          (AddSlot already reserved 16 bytes at ParamName); if stack-passed the
          itab word sits at StackOff+8 which IntfItabOperand computes from Off+8. }
        Inc(IntIdx2);
      end
      else if (P.ResolvedType <> nil) and
              ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
               IsJumboSet(P.ResolvedType)) and
              not P.IsVarParam then
      begin
        if IntIdx2 < 6 then
        begin
          Self.AddSlot(P.ParamName, nil, Offset);
          Self.AddSlot(P.ParamName + '_data', P.ResolvedType, Offset);
        end
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, nil);
          Self.DbgRecordSlot(P.ParamName, nil, StackOff);
          Inc(StackOff, 8);
          Self.AddSlot(P.ParamName + '_data', P.ResolvedType, Offset);
        end;
        Inc(IntIdx2);
      end
      else if IsFloatFamily(P.ResolvedType) and not P.IsVarParam then
      begin
        { Float param: consumes an SSE (xmm) arg register, NOT an integer one,
          and must not advance IntIdx2 (a following integer param would
          otherwise be mis-placed onto the stack — the caller passes it in an
          integer register).  Mirrors the prologue spill loop's float branch. }
        if XmmIdx2 < 8 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(XmmIdx2);
      end
      else
      begin
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          { Stack-passed param: lives at +StackOff(%rbp), pushed by caller. }
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Self.DbgRecordSlot(P.ParamName, P.ResolvedType, StackOff);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end;
    end;
  end;
  { Result slot for a function (not a procedure).
    For a record-returning (sret) function the Result IS the caller's buffer —
    we store the incoming sret pointer (%rdi) in an 8-byte slot and dereference
    through it on every field write.  We record the slot as tyPointer so
    VarOperand returns the slot address (not the record address).
    For small POD records that qualify for register return, Result is a local
    buffer and the epilogue loads it into rax/rdx/xmm0/xmm1. }
  { FSretFunc / FRecRetClass were classified up front (see top of BuildFrame).
    Here we only allocate the Result slot: an sret return stores the incoming
    hidden buffer pointer (record/interface/jumbo-set/static-array), so the slot
    is pointer-sized; a register-returned record / scalar gets a typed slot. }
  if ADecl.ResolvedReturnType <> nil then
  begin
    if FSretFunc then
      Self.AddSlot('Result', nil, Offset)
    else
      Self.AddSlot('Result', ADecl.ResolvedReturnType, Offset);
  end;
  { Local var declarations. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        Self.AddSlot(VD.Names.Strings[J], VD.ResolvedType, Offset);
    end;
  { Pre-allocate 512-byte exception frame slots — one per try/finally or
    try/except in the function body (recursively).  Pre-allocation ensures
    frames live at static %rbp-relative addresses rather than being carved
    from %rsp inside a loop, which would grow the stack by 512 bytes per
    iteration and corrupt parent frame prev-pointers.
    Each slot name is '_exc_frame_N'; VarOperand returns the low-address
    operand (-N(%rbp)), which is what _PushExcFrame expects as the frame base. }
  if ADecl.Body <> nil then
  begin
    TryCount := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      TryCount := TryCount + Self.CountTryStmts(TASTStmt(ADecl.Body.Stmts.Items[K]));
    for K := 0 to TryCount - 1 do
    begin
      { Each frame is 512 bytes, 16-byte aligned.  We bump Offset by 512 and
        store the negative offset as the slot base (the lowest address of the
        block, matching alloc16 semantics). }
      Inc(Offset, 512);
      { Align to 16 bytes after the bump. }
      Offset := (Offset + 15) and (-16);
      FFrame.Add('_exc_frame_' + IntToStr(K), -Offset);
      FFrameTypes.Add('_exc_frame_' + IntToStr(K), nil);
    end;
  end;
  if ADecl.Body <> nil then
  begin
    TryCount := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      TryCount := TryCount + Self.CountForStmts(TASTStmt(ADecl.Body.Stmts.Items[K]));
    for K := 0 to TryCount - 1 do
      Self.AddSlot('_for_end_' + IntToStr(K), nil, Offset);
  end;
  { Jumbo-set scratch slots: a jumbo set literal, union, intersection, or
    difference produces a new bitmap that must live somewhere addressable.
    Such a value can appear deep inside any expression (e.g. 'X in [members]'
    over a >64-member enum, which is common in the compiler's own token tests),
    so rather than walk the whole body we reserve the two 32-byte scratch slots
    in every function frame.  The cost is 64 bytes per frame; correctness and
    self-host stability outweigh it.  HasJumbo is retained for future
    refinement to a body-walk-gated reservation. }
  HasJumbo := True;
  if HasJumbo then
  begin
    Inc(Offset, 32);
    Offset := (Offset + 7) and (-8);
    FFrame.Add('_jset_scratch_0', -Offset);
    FFrameTypes.Add('_jset_scratch_0', nil);
    Inc(Offset, 32);
    Offset := (Offset + 7) and (-8);
    FFrame.Add('_jset_scratch_1', -Offset);
    FFrameTypes.Add('_jset_scratch_1', nil);
  end;
  { Round the reserved size up to a 16-byte multiple (SysV alignment).
    -16 is the bitmask not(15) in two's complement (Blaise `not` is Boolean). }
  FFrameSize := (Offset + 15) and (-16);
end;

procedure TX86_64Backend.ClearFrame;
begin
  if FFrame <> nil then
  begin
    FFrame.Free();
    FFrame := nil;
  end;
  if FFrameTypes <> nil then
  begin
    FFrameTypes.Free();
    FFrameTypes := nil;
  end;
  FFrameSize    := 0;
  FSretFunc     := False;
  FRecRetClass  := rcSret;
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FForEndNext   := 0;
  FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
end;

{ ------------------------------------------------------------------ }
{ Expression lowering                                                  }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IntExprType(AExpr: TASTExpr): TTypeDesc;
var
  T: TTypeDesc;
begin
  if AExpr is TIdentExpr then
  begin
    { Prefer the slot's recorded type (local then global) over the node's
      ResolvedType: the slot type is what the memory actually holds. }
    T := Self.LocalType(TIdentExpr(AExpr).Name);
    if T = nil then
      T := Self.GlobalType(TIdentExpr(AExpr).Name);
    if T <> nil then
    begin
      Exit(T);
    end;
  end;
  Result := AExpr.ResolvedType;
end;

{ Re-narrow the value in %rax to AType, then re-extend so the register again
  holds a value consistent with that type.  Narrowing masks/truncates to the
  low N bits; widening sign- or zero-extends.  A no-op for a value already
  consistent with a 4- or 8-byte type, but harmless to apply. }
procedure TX86_64Backend.EmitNarrowToType(AType: TTypeDesc);
begin
  if AType = nil then Exit;
  { Pointer-shaped values are full 64-bit addresses — "narrowing" one (e.g.
    after a class cast TFoo(X), which routes through the type-cast call
    path) truncates the pointer to its low 32 bits. }
  if AType.Kind in [tyClass, tyMetaClass, tyInterface, tyString, tyPChar,
                    tyPointer, tyDynArray, tyOpenArray, tyRecord,
                    tyStaticArray, tyProcedural] then
    Exit;
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzbq %al, %rax')
       else
         Self.Emit(#9'movsbq %al, %rax');
    2: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzwq %ax, %rax')
       else
         Self.Emit(#9'movswq %ax, %rax');
    8: ;  { already a full 64-bit value }
  else
    { 4-byte: re-establish the upper 32 bits per signedness. }
    if IsUnsignedInt(AType) then
      Self.Emit(#9'movl %eax, %eax')    { zero-extends into %rax }
    else
      Self.Emit(#9'movslq %eax, %rax');
  end;
end;

{ Inc(x)/Dec(x) — general-purpose handler.
  Emits load-from-address / add-or-sub / store-to-address, supporting:
  - simple local/global TIdentExpr
  - implicit-Self field TIdentExpr (bare FField inside a method)
  - var-param TIdentExpr (dereference the pointer)
  - TFieldAccessExpr (Rec.Field, Obj.Field)
  - TDerefExpr (P^) }
{ Compute the ADDRESS of an L-value slot into %rdx.  Supports plain
  identifiers (locals, globals, var-params, implicit-Self fields) and
  field-access targets: R.F (inline record), C.F (class variable — slot
  holds the object pointer), implicit-Self record/class bases, var-param
  record bases, and chained Base.F (Base evaluated to an address). }
{ Evaluate the RHS of a byte-sized store into %eax.

  Chr(N) must NOT lower via the normal _Chr call — that returns a heap
  string POINTER, and the byte store would truncate to the pointer's low
  byte (the "P[I] := Chr(N)" garbage bug).  Emit the argument N directly.
  Single-char string literals get the same fold to their ordinal.
  Mirrors the QBE backend's EmitByteRhs. }
procedure TX86_64Backend.EmitByteRhsToEax(AExpr: TASTExpr);
begin
  if (AExpr is TFuncCallExpr) and
     SameText(TFuncCallExpr(AExpr).Name, 'Chr') and
     (TFuncCallExpr(AExpr).Args.Count = 1) then
  begin
    Self.EmitExprToEax(TASTExpr(TFuncCallExpr(AExpr).Args.Items[0]));
    Exit;
  end;
  if (AExpr is TStringLiteral) and
     (Length(TStringLiteral(AExpr).Value) = 1) then
  begin
    { Use StrAt (OrdAt) rather than Ord(Value[0]): the bare subscript-then-Ord
      idiom miscompiles under the self-hosted native stage (it produced a
      pointer-sized garbage immediate, surfacing as a CI-only failure of the
      S[i] := 'c' test), whereas StrAt is the stage-stable byte-read helper
      used everywhere else in this backend. }
    Self.Emit(Format(#9'movl $%d, %%eax',
      [StrAt(TStringLiteral(AExpr).Value, 0)]));
    Exit;
  end;
  Self.EmitExprToEax(AExpr);
end;

procedure TX86_64Backend.EmitLValueSlotAddr(AExpr: TASTExpr);
var
  IE:  TIdentExpr;
  FAE: TFieldAccessExpr;
  FI:  TFieldInfo;
  SlotAddrWrap: TAddrOfExpr;
begin
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil) then
    begin
      FI := TFieldInfo(IE.ImplicitFieldInfo);
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if FI.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FI.Offset]));
    end
    else if IE.ParamMode <> pmNone then
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand(IE.Name)]))
    else
      Self.EmitVarAddr(IE.Name, '%rdx');
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: L-value field access has no resolved field info');
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rdx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rdx), %rdx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { Class variable / var-param: the slot holds a POINTER — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rdx), %rdx');
    end
    else
      { Plain value record: take the address of its storage.  For an ordinary
        local the slot IS the record; for the sret Result the slot holds the
        buffer POINTER; for a nested-captured record the _cap_ slot holds the
        record's address — EmitVarBaseToReg(AWantAddress=True) handles all
        three.  Without this, SetLength(Result.DynField, N) and other l-value
        field slots in an sret function added the field offset to the address
        of the pointer slot instead of to the pointed-to record. }
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rdx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.FieldInfo.Offset]));
    Exit;
  end;
  { Array element a[i] as an l-value slot (e.g. SetLength(m[i], n) for a 2-D
    dynamic array): its address is what @a[i] computes — evaluate that into
    %rax via a transient TAddrOfExpr, then move to %rdx. }
  if AExpr is TStringSubscriptExpr then
  begin
    SlotAddrWrap := TAddrOfExpr.Create();
    try
      SlotAddrWrap.Expr := AExpr;
      Self.EmitExprToEax(SlotAddrWrap);
    finally
      SlotAddrWrap.Expr := nil;   { AExpr owned by the caller }
      SlotAddrWrap.Free();
    end;
    Self.Emit(#9'movq %rax, %rdx');
    Exit;
  end;
  raise ENativeCodeGenError.Create(
    'native backend: unsupported L-value form');
end;

procedure TX86_64Backend.SetDebugFacts(AFacts: TDbgFacts);
begin
  FDbgFacts := AFacts;
end;

procedure TX86_64Backend.DbgBeginFunc(const ASymbol: string);
begin
  if FDbgFacts = nil then Exit;
  FDbgCur := FDbgFacts.BeginFunc(ASymbol);
  FDbgCur.SourceFile := FDbgSrcFile;
end;

procedure TX86_64Backend.DbgRecordSlot(const AName: string; AType: TTypeDesc;
  AOffset: Integer);
begin
  if FDbgCur = nil then Exit;
  { Skip internal bookkeeping slots (exception frames, open-array highs).
    '_data' record-param shadows and '_cap_' capture pointers are kept —
    DbgMarkParams presents the shadow AS the parameter and a capture slot
    AS the outer variable (indirect location). }
  if AName = '' then Exit;
  if (AName[0] = '_') and (Copy(AName, 0, 5) <> '_cap_') then Exit;
  if (Length(AName) > 5) and (Copy(AName, Length(AName) - 5, 5) = '_high') then Exit;
  FDbgCur.AddVar(AName, AType, AOffset);
end;

procedure TX86_64Backend.DbgMarkParams(ADecl: TMethodDecl);
var
  I: Integer;
  P: TMethodParam;
  V: TDbgVar;
  DV: TDbgVar;
  Sym: TSymbol;
begin
  if (FDbgCur = nil) or (ADecl = nil) then Exit;
  V := FDbgCur.FindVar('Self');
  if V <> nil then
  begin
    V.IsParam := True;
    { Type Self as the owning class so the debugger can drill its fields
      (the slot holds the instance pointer; pdr derefs class types). }
    if (V.TypeDesc = nil) and (ADecl.OwnerTypeName <> '') and
       (FSymTable <> nil) then
    begin
      Sym := FSymTable.Lookup(ADecl.OwnerTypeName);
      if (Sym <> nil) and (Sym.TypeDesc <> nil) then
        V.TypeDesc := Sym.TypeDesc;
    end;
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    V := FDbgCur.FindVar(P.ParamName);
    if V = nil then Continue;
    V.IsParam := True;
    V.IsVarParam := P.IsVarParam;
    V.IsConstParam := P.IsConstParam;
    { Value record/static-array params: the named slot holds an ABI pointer;
      the callee's inline copy lives in the '_data' shadow slot.  Present
      the shadow AS the parameter — its fields are inline at known offsets,
      which is what field drilldown needs. }
    DV := FDbgCur.FindVar(P.ParamName + '_data');
    if DV <> nil then
    begin
      FDbgCur.Vars.Delete(FDbgCur.Vars.IndexOf(V));   { drop the raw pointer slot }
      DV.Name := P.ParamName;
      DV.IsParam := True;
      DV.IsVarParam := P.IsVarParam;
      DV.IsConstParam := P.IsConstParam;
    end
    else if P.IsOpenArray then
    begin
      { Open-array parameter: the named slot holds the data pointer; the
        element count is High+1, where High lives in the companion
        '<name>_high' slot.  Record the companion offset so the OPDF
        emitter can locate the length — the debugger has no heap header
        to read it from. }
      V.IsOpenArray := True;
      if not FFrame.TryGetValue(P.ParamName + '_high', V.HighRbpOffset) then
        V.HighRbpOffset := 0;
      if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
        V.TypeDesc := P.ResolvedType;
    end
    else if P.IsVarParam then
    begin
      { var/out parameter: the slot holds the ADDRESS of the caller's
        variable — indirect location, typed as the VALUE. }
      V.Indirect := True;
      if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
        V.TypeDesc := P.ResolvedType;
    end
    else if (V.TypeDesc = nil) and (P.ResolvedType <> nil) then
      V.TypeDesc := P.ResolvedType;
  end;
  { Captured outer locals: each '_cap_<Name>' slot holds a pointer to the
    outer variable.  Present it as the variable itself via the indirect
    location, typed from the enclosing function's var/param declarations
    (FDbgOuterDecl — set while nested procs are emitted). }
  if ADecl.CapturedVars <> nil then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      V := FDbgCur.FindVar('_cap_' + ADecl.CapturedVars.Strings[I]);
      if V = nil then Continue;
      V.Name := ADecl.CapturedVars.Strings[I];
      V.Indirect := True;
      if V.TypeDesc = nil then
        V.TypeDesc := Self.OuterVarType(ADecl.CapturedVars.Strings[I]);
    end;
end;

{ Resolve the type of a captured outer variable by name from the enclosing
  function's local var declarations and parameters.  Returns nil when no
  enclosing decl is recorded or the name is not found. }
function TX86_64Backend.OuterVarType(const AName: string): TTypeDesc;
var
  I, J: Integer;
  VD: TVarDecl;
  P: TMethodParam;
begin
  Result := nil;
  if FDbgOuterDecl = nil then Exit;
  if FDbgOuterDecl.Body <> nil then
    for I := 0 to FDbgOuterDecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(FDbgOuterDecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        if SameText(VD.Names.Strings[J], AName) then
          Exit(VD.ResolvedType);
    end;
  for I := 0 to FDbgOuterDecl.Params.Count - 1 do
  begin
    P := TMethodParam(FDbgOuterDecl.Params.Items[I]);
    if SameText(P.ParamName, AName) then
      Exit(P.ResolvedType);
  end;
end;

procedure TX86_64Backend.DbgStmtLabel(AStmt: TASTStmt);
var
  L: TDbgLine;
begin
  if (FDbgCur = nil) or (AStmt = nil) then Exit;
  if AStmt.Line <= 0 then Exit;
  { Structural containers re-dispatch to their children; labelling them would
    duplicate the first child's line. }
  if AStmt is TCompoundStmt then Exit;
  L := TDbgLine.Create();
  L.LabelName := Format('.Ldbg_%d', [FDbgSeq]);
  L.Line := AStmt.Line;
  L.Col := AStmt.Col;
  Inc(FDbgSeq);
  FDbgCur.Lines.Add(L);
  Self.Emit(L.LabelName + ':');
end;

procedure TX86_64Backend.DbgEndFunc;
var
  EndLbl: string;
begin
  if FDbgCur = nil then Exit;
  EndLbl := Format('.Ldbg_end_%d', [FDbgSeq]);
  Inc(FDbgSeq);
  Self.Emit(EndLbl + ':');
  FDbgCur.EndLabel := EndLbl;
  FDbgCur := nil;
end;

function TX86_64Backend.IsNativeRecordCall(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  { Interface (itab) dispatch has no ResolvedMethod — classify by the call's
    resolved return type instead, so a record-returning itab call routes
    through the sret/record-return path (EmitIntfRecordSretDispatch) like a
    direct record method call.  Mirrors the QBE IsRecordCall interface case. }
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AExpr).ResolvedClassType.Kind = tyInterface) then
  begin
    Result := (TMethodCallExpr(AExpr).ResolvedType <> nil) and
              (TMethodCallExpr(AExpr).ResolvedType.Kind = tyRecord);
    Exit;
  end;
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedMethod <> nil) and
     (TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod).ResolvedReturnType <> nil) and
     (TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
  if (AExpr is TFuncCallExpr) and
     (TFuncCallExpr(AExpr).ResolvedDecl <> nil) and
     (TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).ResolvedReturnType <> nil) and
     (TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
  if (AExpr is TInheritedCallExpr) and
     (TInheritedCallExpr(AExpr).ResolvedMethod <> nil) and
     (TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod).ResolvedReturnType <> nil) and
     (TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
    Exit(True);
end;

function TX86_64Backend.RecordCallReceiverIsVar(AExpr: TASTExpr;
  const AName: string; AIsGlobal: Boolean): Boolean;
var
  MCall: TMethodCallExpr;
  MDecl: TMethodDecl;
begin
  Result := False;
  if not (AExpr is TMethodCallExpr) then Exit;
  MCall := TMethodCallExpr(AExpr);
  if MCall.ResolvedMethod = nil then Exit;
  MDecl := TMethodDecl(MCall.ResolvedMethod);
  if not MDecl.IsRecordMethod then Exit;
  { Only a bare variable receiver (M.Method) can alias the destination var. }
  if MCall.ObjExpr <> nil then Exit;
  Result := (MCall.ObjectName = AName) and (MCall.IsGlobal = AIsGlobal);
end;

{ Emit an sret (record/jumbo-set/static-array-returning) call for a
  TFuncCallExpr.  An implicit-Self method is routed through EmitMethodSretCall
  (which passes Self and vtable-dispatches a virtual method); a free function
  goes through EmitSretCall.  Without this an implicit-Self virtual method
  returning a record would be static-dispatched (wrong override, abstract-base
  link error) and miss its Self receiver. }
procedure TX86_64Backend.EmitFuncCallSret(AFC: TFuncCallExpr;
  const ADest: string; AIndirect: Boolean);
var
  Synth: TMethodCallExpr;
begin
  if AFC.IsImplicitSelfMethod then
  begin
    Synth := TMethodCallExpr.Create();
    try
      Synth.Name           := AFC.Name;
      Synth.Args           := AFC.Args;    { borrowed — detached before Free }
      Synth.ResolvedMethod := AFC.ResolvedDecl;
      Synth.ResolvedType   := AFC.ResolvedType;
      Self.EmitMethodSretCall(Synth, ADest, AIndirect);
    finally
      Synth.Args := nil;   { do not free the borrowed arg list }
      Synth.Free();
    end;
  end
  else
    Self.EmitSretCall(FuncSymbolOf(AFC), TMethodDecl(AFC.ResolvedDecl),
      AFC.Args, ADest, AIndirect);
end;

procedure TX86_64Backend.EmitRecordCallSretAt(AExpr: TASTExpr; const ADest: string);
begin
  if (AExpr is TMethodCallExpr) and
     (TMethodCallExpr(AExpr).ResolvedClassType <> nil) and
     (TMethodCallExpr(AExpr).ResolvedClassType.Kind = tyInterface) then
    { Interface (itab) record-returning dispatch — EmitMethodSretCall raises on
      a nil ResolvedMethod, so route through the itab record-return helper. }
    Self.EmitIntfRecordSretDispatch(TMethodCallExpr(AExpr), ADest, False)
  else if AExpr is TMethodCallExpr then
    Self.EmitMethodSretCall(TMethodCallExpr(AExpr), ADest, False)
  else if AExpr is TInheritedCallExpr then
    Self.EmitInheritedRecordSret(
      TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod),
      TInheritedCallExpr(AExpr).Args,
      TInheritedCallExpr(AExpr).Name, ADest, False)
  else
    Self.EmitFuncCallSret(TFuncCallExpr(AExpr), ADest, False);
end;

procedure TX86_64Backend.EmitIncDec(ACall: TProcCall);
var
  Arg0: TASTExpr;
  IE: TIdentExpr;
  FAE: TFieldAccessExpr;
  IsInc, IsWide, HasStep: Boolean;
  FI: TFieldInfo;
begin
  IsInc := SameText(ACall.Name, 'Inc');
  Arg0 := TASTExpr(ACall.Args.Items[0]);
  HasStep := ACall.Args.Count >= 2;
  IsWide := (Arg0.ResolvedType <> nil) and
            (Arg0.ResolvedType.Kind in [tyInt64, tyUInt64, tyClass, tyPointer]);

  if Arg0 is TIdentExpr then
  begin
    IE := TIdentExpr(Arg0);
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    if IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil) then
    begin
      FI := TFieldInfo(IE.ImplicitFieldInfo);
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if FI.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FI.Offset]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep);
    end
    else if IE.ParamMode <> pmNone then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand(IE.Name)]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep);
    end
    else if Self.IsCaptured(IE.Name) then
    begin
      { Captured outer local: the _cap_ slot holds the var's ADDRESS — load it
        into %rdx and do the in-place add/sub through it. }
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('_cap_' + IE.Name)]));
      Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep);
    end
    else
    begin
      if IsWide then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(IE.Name)]))
      else
        Self.Emit(Format(#9'movl %s, %%eax', [Self.VarOperand(IE.Name)]));
      if HasStep then
      begin
        if IsWide then
        begin
          if IsInc then Self.Emit(#9'addq %rcx, %rax')
          else          Self.Emit(#9'subq %rcx, %rax');
        end
        else
        begin
          if IsInc then Self.Emit(#9'addl %ecx, %eax')
          else          Self.Emit(#9'subl %ecx, %eax');
        end;
      end
      else
      begin
        if IsWide then
        begin
          if IsInc then Self.Emit(#9'addq $1, %rax')
          else          Self.Emit(#9'subq $1, %rax');
        end
        else
        begin
          if IsInc then Self.Emit(#9'addl $1, %eax')
          else          Self.Emit(#9'subl $1, %eax');
        end;
      end;
      if IsWide then
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(IE.Name)]))
      else
        Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(IE.Name)]));

    end;
  end
  else if Arg0 is TFieldAccessExpr then
  begin
    FAE := TFieldAccessExpr(Arg0);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rdx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.ImplicitBaseInfo.Offset]));
    end
    else if FAE.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand(FAE.RecordName)]));
    end
    else
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rdx');
    end;
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdx', [FAE.FieldInfo.Offset]));
    Self.Emit(#9'pushq %rdx');
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    Self.Emit(#9'popq %rdx');
    Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep);
  end
  else if Arg0 is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(Arg0).Expr);
    Self.Emit(#9'pushq %rax');
    if HasStep then
    begin
      Self.EmitExprToEax(TASTExpr(ACall.Args.Items[1]));
      if IsWide then Self.Emit(#9'movq %rax, %rcx')
      else           Self.Emit(#9'movl %eax, %ecx');
    end;
    Self.Emit(#9'popq %rdx');
    Self.EmitIncDecAddrOp(IsInc, IsWide, HasStep);
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: Inc/Dec on unsupported expression form');
end;

procedure TX86_64Backend.EmitIncDecAddrOp(IsInc, IsWide, HasStep: Boolean);
begin
  if IsWide then
    Self.Emit(#9'movq (%rdx), %rax')
  else
    Self.Emit(#9'movl (%rdx), %eax');
  if HasStep then
  begin
    if IsWide then
    begin
      if IsInc then Self.Emit(#9'addq %rcx, %rax')
      else          Self.Emit(#9'subq %rcx, %rax');
    end
    else
    begin
      if IsInc then Self.Emit(#9'addl %ecx, %eax')
      else          Self.Emit(#9'subl %ecx, %eax');
    end;
  end
  else
  begin
    if IsWide then
    begin
      if IsInc then Self.Emit(#9'addq $1, %rax')
      else          Self.Emit(#9'subq $1, %rax');
    end
    else
    begin
      if IsInc then Self.Emit(#9'addl $1, %eax')
      else          Self.Emit(#9'subl $1, %eax');
    end;
  end;
  if IsWide then
    Self.Emit(#9'movq %rax, (%rdx)')
  else
    Self.Emit(#9'movl %eax, (%rdx)');
end;

{ Load a float value from memory into %xmm0. }
procedure TX86_64Backend.EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %s, %%xmm0', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %s, %%xmm0', [AOperand]));
end;

{ Store %xmm0 into memory. }
{ Adjust the float width of the value in %xmm0.  EmitExprToXmm0 leaves a
  SINGLE for tySingle-typed expressions and a DOUBLE for everything else
  (Double expressions, integer expressions through the int fallback, and
  integer literals).  Callers that need a specific width convert here. }
procedure TX86_64Backend.EmitXmm0WidthAdjust(ASrcType: TTypeDesc;
  AWantSingle: Boolean);
var
  SrcIsSingle: Boolean;
begin
  SrcIsSingle := (ASrcType <> nil) and (ASrcType.Kind = tySingle);
  if AWantSingle and not SrcIsSingle then
    Self.Emit(#9'cvtsd2ss %xmm0, %xmm0')
  else if SrcIsSingle and not AWantSingle then
    Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
end;

procedure TX86_64Backend.EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %%xmm0, %s', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %%xmm0, %s', [AOperand]));
end;

{ Evaluate a floating-point expression, leaving the result in %xmm0.
  Binary operators: push %xmm0 onto the stack via subq/movsd, evaluate the
  right operand into %xmm0, then pop the left into %xmm1 and combine.
  This mirrors the integer strategy (push %rax) without requiring movaps/movups
  shuffles. }
procedure TX86_64Backend.EmitExprToXmm0(AExpr: TASTExpr);
var
  FL:  TFloatLiteral;
  BE:  TBinaryExpr;
  FC:  TFuncCallExpr;
  MD:  TMethodDecl;
  Ty:  TTypeDesc;
  IsS: Boolean;
  I:   Integer;
begin
  if AExpr is TFloatLiteral then
  begin
    FL  := TFloatLiteral(AExpr);
    Ty  := AExpr.ResolvedType;
    IsS := (Ty <> nil) and (Ty.Kind = tySingle);
    { Use a .rodata constant for the immediate float — x86 has no mov-imm
      for xmm registers.  Emit a file-local label that holds the 8-byte
      (Double) or 4-byte (Single) encoding of the literal. }
    if IsS then
    begin
      Self.Emit(Format(#9'movss .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      { Defer the .rodata entry to the data section by registering a synthetic
        global with a special FP-literal tag.  We emit it directly since our
        data section is collected: just write it now in a .section .rodata block. }
      Self.Emit('.section .rodata');
      Self.Emit('.balign 4');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.float %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end
    else
    begin
      Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      Self.Emit('.section .rodata');
      Self.Emit('.balign 8');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.double %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end;
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
    Self.Emit('.section .rodata');
    Self.Emit('.balign 8');
    Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
    Self.Emit(Format(#9'.double %d.0', [TIntLiteral(AExpr).Value]));
    Self.Emit('.text');
    Inc(FLabelCount);
    Exit;
  end;

  { Integer-typed expression in a float context (e.g. Tanh(i), Power(2, n)):
    evaluate to %rax (sign-extended) and convert to double. }
  if (AExpr.ResolvedType <> nil) and IsIntFamily(AExpr.ResolvedType) then
  begin
    Self.EmitExprToEax(AExpr);
    Self.Emit(#9'cvtsi2sdq %rax, %xmm0');
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    { Implicit-Self float field read (FFloat inside a method): load from the
      Self instance at the field offset, NOT from a global symbol named after
      the field.  Without this the field reference falls through to the plain
      VarOperand path below and emits `movsd FFloat(%rip)` — an undefined
      symbol in per-unit (.o) codegen.  (The store path already handles this;
      only the read was missing it.) }
    if TIdentExpr(AExpr).IsImplicitSelf and
       (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx',
          [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
      Self.EmitLoadFloat('(%rcx)', AExpr.ResolvedType);
      Exit;
    end;
    { Float-typed named constant (const X = 6.28; ...): inline its literal
      value.  The const has no storage — its ConstString holds the source
      text — so loading from a symbol named after it (VarOperand) would
      reference an undefined label.  Emit the value via .rodata exactly as
      a TFloatLiteral does. }
    if TIdentExpr(AExpr).IsConstant and IsFloatFamily(AExpr.ResolvedType) then
    begin
      IsS := (AExpr.ResolvedType <> nil) and
             (AExpr.ResolvedType.Kind = tySingle);
      if IsS then
      begin
        Self.Emit(Format(#9'movss .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
        Self.Emit('.section .rodata');
        Self.Emit('.balign 4');
        Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
        Self.Emit(Format(#9'.float %s', [TIdentExpr(AExpr).ConstString]));
      end
      else
      begin
        Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0', [IntToStr(FLabelCount)]));
        Self.Emit('.section .rodata');
        Self.Emit('.balign 8');
        Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
        Self.Emit(Format(#9'.double %s', [TIdentExpr(AExpr).ConstString]));
      end;
      Self.Emit('.text');
      Inc(FLabelCount);
      Exit;
    end;
    Ty := AExpr.ResolvedType;
    if (Ty = nil) and Self.IsLocal(TIdentExpr(AExpr).Name) then
      Ty := Self.LocalType(TIdentExpr(AExpr).Name);
    if (Ty = nil) then
      Ty := Self.GlobalType(TIdentExpr(AExpr).Name);
    if TIdentExpr(AExpr).ParamMode <> pmNone then
    begin
      { var/out float param: the slot holds the value's address. }
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
      Self.EmitLoadFloat('(%rcx)', Ty);
    end
    else if Self.IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      { Captured outer local: the _cap_ slot holds the var's address. }
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + TIdentExpr(AExpr).Name)]));
      Self.EmitLoadFloat('(%rcx)', Ty);
    end
    else
      Self.EmitLoadFloat(Self.VarOperand(TIdentExpr(AExpr).Name), Ty);
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Self.EmitFieldAddrToRcx(TFieldAccessExpr(AExpr));
    Ty := TFieldAccessExpr(AExpr).FieldInfo.TypeDesc;
    Self.EmitLoadFloat('(%rcx)', Ty);
    Exit;
  end;

  { Pointer dereference yielding a float: P^ where P: ^Double/^Single.
    Evaluate the pointer into %rcx and load the float from (%rcx). }
  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(AExpr).Expr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.EmitLoadFloat('(%rcx)', AExpr.ResolvedType);
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    BE  := TBinaryExpr(AExpr);
    IsS := (BE.ResolvedType <> nil) and (BE.ResolvedType.Kind = tySingle);
    { left → %xmm0, push to stack via subq/movsd; right → %xmm0;
      pop left into %xmm1 via movsd/addq.  Operands whose own width differs
      from the operation width (mixed Single/Double, integer operands and
      integer literals — which EmitExprToXmm0 produces as Double) are
      converted as they arrive. }
    Self.EmitExprToXmm0(BE.Left);
    Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
    Self.Emit(#9'subq $8, %rsp');
    if IsS then
      Self.Emit(#9'movss %xmm0, (%rsp)')
    else
      Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(BE.Right);
    Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
    if IsS then
    begin
      Self.Emit(#9'movss (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addss %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subss %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulss %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divss %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomiss %xmm0, %xmm1');  { %xmm1 - %xmm0 }
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');   { below (CF set) }
              boGT: Self.Emit(#9'seta %al');   { above }
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            Self.Emit(#9'movq %rax, %xmm0');  { comparison result as int in %rax then convert? }
            { Actually we need int result for condition tests — put result in %rax,
              then caller decides if it needs to be in %xmm0.  But EmitExprToXmm0
              is for float expressions; comparisons of floats return int (Boolean).
              Fall through: return the 0/1 in %rax.  The caller (EmitCondBranch)
              actually calls EmitExprToEax and tests %rax.  So we shouldn't reach
              here for comparisons — they go through EmitCondBranch → EmitExprToEax
              which will handle float comparisons. }
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      { Result is in %xmm1, copy to %xmm0 if not a comparison. }
      if BE.Op in [boAdd, boSub, boMul, boSlash] then
        Self.Emit(#9'movaps %xmm1, %xmm0');
    end
    else
    begin
      Self.Emit(#9'movsd (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addsd %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subsd %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulsd %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divsd %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomisd %xmm0, %xmm1');
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');
              boGT: Self.Emit(#9'seta %al');
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            { Float comparisons result in integer 0/1 — return via %rax, not %xmm0. }
            Exit;
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      Self.Emit(#9'movapd %xmm1, %xmm0');
    end;
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    if Self.EmitFloatBuiltin(FC) then
      Exit;
    { Type cast Double(X) / Single(X): ResolvedDecl is nil.  Emit a real
      numeric conversion, never a bit copy. }
    if (FC.ResolvedDecl = nil) and (FC.Args.Count = 1) then
    begin
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         TASTExpr(FC.Args.Items[0]).ResolvedType.IsFloat() then
      begin
        Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
        if (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) and
           (FC.ResolvedType.Kind = tyDouble) then
          Self.Emit(#9'cvtss2sd %xmm0, %xmm0')
        else if (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyDouble) and
                (FC.ResolvedType.Kind = tySingle) then
          Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      end
      else
      begin
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        if FC.ResolvedType.Kind = tySingle then
          Self.Emit(#9'cvtsi2ssq %rax, %xmm0')
        else
          Self.Emit(#9'cvtsi2sdq %rax, %xmm0');
      end;
      Exit;
    end;
    if FC.IsImplicitSelfMethod and (FC.ResolvedDecl <> nil) then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      Self.BeginCallArgs(MD.Params, FC.Args);
      for I := 0 to FC.Args.Count - 1 do
        Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
          TASTExpr(FC.Args.Items[I]), I);
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
      for I := Self.CountArgSlots(MD.Params) - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArg64(I + 1));
      Self.Emit(#9'movq %r10, %rdi');
      Self.Emit(#9'callq ' + FuncSymbolOf(FC));
      Self.EndCallArgs();
      Exit;
    end;
    { User function call whose return type is float. }
    Self.EmitCall(FuncSymbolOf(FC), TMethodDecl(FC.ResolvedDecl), FC.Args);
    { Return value is in %xmm0 per SysV ABI. }
    Exit;
  end;

  { Qualified method call returning a float, e.g. d := Obj.GetF().  The method
    emitter performs vtable/static dispatch and the SysV ABI leaves the float
    result in %xmm0, so no further work is needed here. }
  if AExpr is TMethodCallExpr then
  begin
    Self.EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;

  { Float array element read A[I] (dynamic or static array of Double/Single).
    The element ADDRESS computation matches the integer EmitExprToEax subscript
    paths; only the final load differs — movsd/movss into %xmm0 rather than a
    GPR load.  Without this case a float element read falls through to the
    error below. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyDynArray) and
     IsFloatFamily(TDynArrayTypeDesc(
       TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TDynArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadFloat('(%rax)',
      TDynArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType);
    Exit;
  end;
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) and
     IsFloatFamily(TStaticArrayTypeDesc(
       TStringSubscriptExpr(AExpr).StrExpr.ResolvedType).ElementType) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).IndexExpr);
    Self.EmitStaticElemScale(
      TStaticArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadFloat('(%rax)',
      TStaticArrayTypeDesc(TStringSubscriptExpr(AExpr).StrExpr.ResolvedType)
        .ElementType);
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported float expression form ' + AExpr.ClassName);
end;

function TX86_64Backend.EmitFloatBuiltin(FC: TFuncCallExpr): Boolean;
var
  IsS: Boolean;
begin
  Result := True;
  { StrToDouble(S): the RTL helper takes a string pointer in %rdi and returns
    the Double in %xmm0.  It MUST be handled here in the float emitter — if it
    falls through to the integer EmitExprToEax path, the result (already in
    %xmm0) is discarded and the leftover %rax is cvtsi2sd'd into garbage. }
  if SameText(FC.Name, 'StrToDouble') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _StrToDouble');
    Exit;
  end;
  if SameText(FC.Name, 'Sqrt') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'sqrtss %xmm0, %xmm0')
    else
      Self.Emit(#9'sqrtsd %xmm0, %xmm0');
    Exit;
  end;
  if SameText(FC.Name, 'Sin') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq sinf')
    else
      Self.Emit(#9'callq sin');
    Exit;
  end;
  if SameText(FC.Name, 'Cos') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq cosf')
    else
      Self.Emit(#9'callq cos');
    Exit;
  end;
  if SameText(FC.Name, 'Tan') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq tanf')
    else
      Self.Emit(#9'callq tan');
    Exit;
  end;
  if SameText(FC.Name, 'ArcTan') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq atanf')
    else
      Self.Emit(#9'callq atan');
    Exit;
  end;
  if SameText(FC.Name, 'ArcTan2') and (FC.Args.Count = 2) then
  begin
    IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    Self.Emit(#9'subq $8, %rsp');
    if IsS then
      Self.Emit(#9'movss %xmm0, (%rsp)')
    else
      Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
    Self.Emit(#9'movaps %xmm0, %xmm1');
    if IsS then
      Self.Emit(#9'movss (%rsp), %xmm0')
    else
      Self.Emit(#9'movsd (%rsp), %xmm0');
    Self.Emit(#9'addq $8, %rsp');
    if IsS then
      Self.Emit(#9'callq atan2f')
    else
      Self.Emit(#9'callq atan2');
    Exit;
  end;
  if SameText(FC.Name, 'ArcSin') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq asinf')
    else
      Self.Emit(#9'callq asin');
    Exit;
  end;
  if SameText(FC.Name, 'ArcCos') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq acosf')
    else
      Self.Emit(#9'callq acos');
    Exit;
  end;
  if SameText(FC.Name, 'Ln') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq logf')
    else
      Self.Emit(#9'callq log');
    Exit;
  end;
  if SameText(FC.Name, 'Log2') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq log2f')
    else
      Self.Emit(#9'callq log2');
    Exit;
  end;
  if SameText(FC.Name, 'Log10') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq log10f')
    else
      Self.Emit(#9'callq log10');
    Exit;
  end;
  if SameText(FC.Name, 'Power') and (FC.Args.Count = 2) then
  begin
    IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    Self.Emit(#9'subq $8, %rsp');
    if IsS then
      Self.Emit(#9'movss %xmm0, (%rsp)')
    else
      Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
    Self.Emit(#9'movaps %xmm0, %xmm1');
    if IsS then
      Self.Emit(#9'movss (%rsp), %xmm0')
    else
      Self.Emit(#9'movsd (%rsp), %xmm0');
    Self.Emit(#9'addq $8, %rsp');
    if IsS then
      Self.Emit(#9'callq powf')
    else
      Self.Emit(#9'callq pow');
    Exit;
  end;
  if SameText(FC.Name, 'Sinh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq sinhf')
    else
      Self.Emit(#9'callq sinh');
    Exit;
  end;
  if SameText(FC.Name, 'Cosh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq coshf')
    else
      Self.Emit(#9'callq cosh');
    Exit;
  end;
  if SameText(FC.Name, 'Tanh') and (FC.Args.Count = 1) then
  begin
    Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
    if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      Self.Emit(#9'callq tanhf')
    else
      Self.Emit(#9'callq tanh');
    Exit;
  end;
  Result := False;
end;

{ Evaluate an integer-family expression, leaving a 64-bit-extended value in
  %rax.  Every value flows in the full register held sign- or zero-extended to
  its static type, so mixed-width arithmetic (e.g. Integer promoted into an
  Int64 expression) is correct without per-node width tracking; the final
  store re-narrows to the destination slot's width.  Arithmetic and
  comparisons use 64-bit ops uniformly. }
procedure TX86_64Backend.EmitExprToEax(AExpr: TASTExpr);
var
  BE:  TBinaryExpr;
  FC:  TFuncCallExpr;
  FAE: TFieldAccessExpr;
  SAE: TStringSubscriptExpr;
  MD:  TMethodDecl;
  IMD: TMethodDecl;
  Unsigned: Boolean;
  AOE: TAddrOfExpr;
  SetMask: Int64;
  SetI: Integer;
  I:   Integer;
  SetElem: TASTExpr;
  ScEndLbl: string;
  IsS: Boolean;
  DivOkLbl: string;
  SuppOut: string;
  LSuppNo: string;
  LSuppEnd: string;
  SCAT: TStaticArrayTypeDesc;
begin
  if AExpr is TNilLiteral then
  begin
    Self.Emit(#9'xorq %rax, %rax');
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    { movabsq carries the full 64-bit immediate (32-bit movq sign-extends a
      value above 2^31, which is wrong for large Int64 constants). }
    Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(TIntLiteral(AExpr).Value)]));
    Exit;
  end;

  if AExpr is TStringLiteral then
  begin
    if TStringLiteral(AExpr).IsCharCoerce then
      { Char context (e.g. S[I] = ','): the semantic pass marked this
        single-char literal for ordinal coercion — emitting the data
        pointer here would compare an address against a byte. }
      Self.Emit(Format(#9'movl $%d, %%eax',
        [TStringLiteral(AExpr).CharOrdValue]))
    else
      Self.EmitStrLitAddr(TStringLiteral(AExpr).Value);
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    if TIdentExpr(AExpr).IsMetaclassRef then
    begin
      { Bare class type identifier used as a value — the metaclass value IS
        the typeinfo address (same pointer vtable[0] holds at runtime),
        mirroring the QBE backend's `copy $typeinfo_<T>`. }
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rax',
        [Self.ClassSymName(TIdentExpr(AExpr).Name)]));
      Exit;
    end;
    if TIdentExpr(AExpr).IsImplicitSelfMethod and
       (TIdentExpr(AExpr).ImplicitMethodDecl <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
      IMD := TMethodDecl(TIdentExpr(AExpr).ImplicitMethodDecl);
      Self.Emit(Format(#9'callq %s',
        [MethodEmitNameNative(IMD, IMD.OwnerTypeName, IMD.Name)]));
      Exit;
    end;
    if TIdentExpr(AExpr).IsImplicitSelf and
       (TIdentExpr(AExpr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx',
          [TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo).Offset]));
      if (TIdentExpr(AExpr).ResolvedType <> nil) and
         (IsJumboSet(TIdentExpr(AExpr).ResolvedType) or
          (TIdentExpr(AExpr).ResolvedType.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(#9'movq %rcx, %rax')
      else if (TIdentExpr(AExpr).ResolvedType <> nil) and
              (TIdentExpr(AExpr).ResolvedType.Kind = tyClass) then
        Self.Emit(#9'movq (%rcx), %rax')
      else
        Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
      Exit;
    end;
    if (TIdentExpr(AExpr).ResolvedType <> nil) and
       (IsJumboSet(TIdentExpr(AExpr).ResolvedType) or
          (TIdentExpr(AExpr).ResolvedType.Kind in [tyRecord, tyStaticArray])) then
    begin
      if FSretFunc and (TIdentExpr(AExpr).Name = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]))
      else if Self.IsCaptured(TIdentExpr(AExpr).Name) then
        { Captured outer record/static-array: the _cap_ slot holds the address
          of the enclosing variable's storage.  For a captured plain local that
          IS the aggregate address (AWantAddress=True); for a captured var/out
          param the enclosing slot holds the caller's pointer, so one extra
          dereference (AWantAddress=False) yields the aggregate address. }
        Self.EmitVarBaseToReg(TIdentExpr(AExpr).Name,
          TIdentExpr(AExpr).ParamMode = pmNone, '%rax')
      else if Self.IsLocal(TIdentExpr(AExpr).Name) and
              (TIdentExpr(AExpr).ParamMode <> pmNone) then
        { Any param mode: the slot holds the record/array ADDRESS (value
          record/static-array params are ABI by-ref; var/out params hold
          the caller variable's address, which IS the aggregate). }
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(TIdentExpr(AExpr).Name)]))
      else if Self.IsLocal(TIdentExpr(AExpr).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand(TIdentExpr(AExpr).Name)]))
      else if TIdentExpr(AExpr).ConstArraySymbol <> '' then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TIdentExpr(AExpr).ConstArraySymbol)]))
      else
        Self.EmitLeaqGlobal(TIdentExpr(AExpr).Name, '%rax');
      Exit;
    end;
    if TIdentExpr(AExpr).IsConstant then
    begin
      if (TIdentExpr(AExpr).ResolvedType <> nil) and
         TIdentExpr(AExpr).ResolvedType.IsString() then
        Self.EmitStrLitAddr(TIdentExpr(AExpr).ConstString)
      else
        Self.Emit(Format(#9'movabsq $%s, %%rax',
          [IntToStr(TIdentExpr(AExpr).ConstValue)]));
    end
    else if TIdentExpr(AExpr).ParamMode <> pmNone then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
      Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
    end
    else if Self.IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand('_cap_' + TIdentExpr(AExpr).Name)]));
      Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
    end
    else if (TIdentExpr(AExpr).ResolvedType <> nil) and
            (TIdentExpr(AExpr).ResolvedType.Kind = tyInterface) then
    begin
      { Interface ident used as a single value (nil/identity compare): load
        the obj half of the fat pointer.  An sret Result slot holds a POINTER
        to the caller's 16-byte buffer — dereference it; locals keep obj at
        the slot base and globals use the _obj data label (a bare global
        symbol load would reference a label that does not exist). }
      if FSretFunc and SameText(TIdentExpr(AExpr).Name, 'Result') then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]));
        Self.Emit(#9'movq (%rcx), %rax');
      end
      else
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.IntfObjOperand(TIdentExpr(AExpr).Name,
              TIdentExpr(AExpr).IsGlobal)]));
    end
    else
      Self.EmitLoadVar(Self.VarOperand(TIdentExpr(AExpr).Name),
        Self.IntExprType(AExpr));
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    { MethodAddress(Instance, 'MethodName') — runtime method table lookup.
      The method name string blob (__cn_Name) must exist in the data section;
      the class section emits it for published methods.  Just reference it here
      via a forward label without re-emitting the blob. }
    if SameText(FC.Name, 'MethodAddress') and (FC.Args.Count = 2) then
    begin
      { Arg0: class instance → class pointer in %rdi }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'pushq %rdi');
      { Arg1: string data pointer for method name.  Literals reference the
        __cn_ blob directly; variable/call expressions evaluate to a managed
        string whose value is already the data pointer. }
      if TASTExpr(FC.Args.Items[1]) is TStringLiteral then
        Self.Emit(Format(#9'leaq __cn_%s + 12(%%rip), %%rsi',
          [NativeMangle(TStringLiteral(TASTExpr(FC.Args.Items[1])).Value)]))
      else
      begin
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
        Self.Emit(#9'movq %rax, %rsi');
      end;
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _MethodAddress');
      { Result = method code pointer in %rax. }
      Exit;
    end;
    { HasClassAttribute(AClass, AAttrClass): Boolean — query attribute RTTI.
      Both args are metaclass expressions that lower to typeinfo pointers.
      Pass them in %rdi/%rsi and call the runtime helper (result in %al).
      Without this the native backend never emitted the call — the result
      was the low byte of the first metaclass's typeinfo address, a layout-
      dependent false positive. }
    if FC.IsBuiltinHasClassAttr and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));   { ti_class -> %rax }
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));   { ti_attr  -> %rax }
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _HasClassAttribute');
      { Result Boolean in %al; normalise to a clean 0/1 in %rax. }
      Self.Emit(#9'movzbq %al, %rax');
      Exit;
    end;
    { SizeOf(expr) → integer literal = byte size of the resolved type. }
    if SameText(FC.Name, 'SizeOf') and (FC.Args.Count = 1) then
    begin
      Self.Emit(Format(#9'movq $%d, %%rax',
        [TASTExpr(FC.Args.Items[0]).ResolvedType.ByteSize()]));
      Exit;
    end;
    { Length/High/Low built-ins for arrays and strings. }
    if SameText(FC.Name, 'High') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]));
        tyOpenArray:
        begin
          { Load the _high slot for this open-array param. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
        end;
        tyDynArray:
        begin
          { High(A) = Length(A) - 1; delegate to RTL. }
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
        tyString:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _StringLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
      else
        { Integer/enum types: type-level High (min/max). }
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyByte:     Self.Emit(#9'movq $255, %rax');
          tyBoolean:  Self.Emit(#9'movq $1, %rax');
          tySmallInt: Self.Emit(#9'movq $32767, %rax');
          tyWord:     Self.Emit(#9'movq $65535, %rax');
          tyInteger:  Self.Emit(#9'movq $2147483647, %rax');
          tyUInt32:   Self.Emit(#9'movq $4294967295, %rax');
          tyEnum:     Self.Emit(Format(#9'movq $%d, %%rax',
            [TEnumTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).Members.Count - 1]));
        else
          Self.Emit(#9'movq $0, %rax');
        end;
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Low') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound]));
        tySmallInt: Self.Emit(#9'movq $-32768, %rax');
        tyInteger:  Self.Emit(#9'movq $-2147483648, %rax');
      else
        Self.Emit(#9'movq $0, %rax');  { 0 for all array/byte/bool/word/unsigned/open/dyn }
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Length') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
        begin
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound + 1]));
        end;
        tyOpenArray:
        begin
          { Length = High + 1: load _high slot and add 1. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
          Self.Emit(#9'incq %rax');
        end;
        tyDynArray:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
        end;
      else
        { String: delegate to RTL. }
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringLength');
        Self.Emit(#9'movslq %eax, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Pos') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringPos');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Copy') and (FC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCopy');
      Exit;
    end;
    if SameText(FC.Name, 'UpperCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringUpperCase');
      Exit;
    end;
    if SameText(FC.Name, 'LowerCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringLowerCase');
      Exit;
    end;
    if SameText(FC.Name, 'Trim') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringTrim');
      Exit;
    end;
    { GetMem(N) → _BlaiseGetMem(N) → pointer.  Size arg is Integer (32-bit). }
    if SameText(FC.Name, 'GetMem') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _BlaiseGetMem');
      Exit;
    end;
    { ReallocMem(P, N) → _BlaiseReallocMem(P, N) → pointer. }
    if SameText(FC.Name, 'ReallocMem') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _BlaiseReallocMem');
      Exit;
    end;
    if SameText(FC.Name, 'SameText') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringSameText');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Chr') and (FC.Args.Count = 1) then
    begin
      { Chr(N) returns a one-character heap String (tyString) — the data pointer
        of a freshly-allocated string.  Lower to _Chr(N), matching the QBE
        backend; the result (in %rax) is a String pointer, so it flows through
        the String ARC assignment/concat paths unchanged.  (Emitting the integer
        N here, as the missing case used to, fed a raw 66 into _StringAddRef and
        crashed.) }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _Chr');
      Exit;
    end;
    if SameText(FC.Name, 'IntToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _Int64ToStr');
      end
      else if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
              (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyUInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _UInt64ToStr');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %edi');
        Self.Emit(#9'callq _IntToStr');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StrToInt');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt64') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StrToInt64');
      Exit;
    end;
    if SameText(FC.Name, 'PChar') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      { PChar(str) is identity — the Blaise string data pointer IS the char data. }
      Exit;
    end;
    if SameText(FC.Name, 'string') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringFromPChar');
      Exit;
    end;
    { Format(Fmt, Arg1, ...) — built-in that builds an args array and calls
      _StringFormatN; handled specially because it takes a variadic args list. }
    if SameText(FC.Name, 'Format') and (FC.Args.Count >= 1) then
    begin
      Self.EmitFormatCall(FC.Args);
      Exit;
    end;
    if SameText(FC.Name, 'Ord') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyString) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(#9'callq _OrdAt');
      end;
      Exit;
    end;
    if (SameText(FC.Name, 'Succ') or SameText(FC.Name, 'Pred')) and
       (FC.Args.Count = 1) then
    begin
      { Next/previous ordinal value: +1 / -1.  Result keeps the arg's type. }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if SameText(FC.Name, 'Succ') then
        Self.Emit(#9'addl $1, %eax')
      else
        Self.Emit(#9'subl $1, %eax');
      Exit;
    end;
    if SameText(FC.Name, 'Assigned') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'testq %rax, %rax');
      Self.Emit(#9'setne %al');
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    if SameText(FC.Name, 'Int64ToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _Int64ToStr');
      Exit;
    end;
    if SameText(FC.Name, 'UInt64ToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _UInt64ToStr');
      Exit;
    end;
    if SameText(FC.Name, 'Abs') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyUInt64]) then
      begin
        Self.Emit(#9'cqto');
        Self.Emit(#9'xorq %rdx, %rax');
        Self.Emit(#9'subq %rdx, %rax');
      end
      else
      begin
        Self.Emit(#9'cltd');
        Self.Emit(#9'xorl %edx, %eax');
        Self.Emit(#9'subl %edx, %eax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'DoubleToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'callq _DoubleToStr');
      Exit;
    end;
    if SameText(FC.Name, 'SingleToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'callq _SingleToStr');
      Exit;
    end;
    if SameText(FC.Name, 'StrToDouble') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StrToDouble');
      Exit;
    end;
    if SameText(FC.Name, 'Round') and (FC.Args.Count = 1) then
    begin
      { Round half-away-from-zero, matching Delphi/FPC Round() and the QBE
        backend.  cvtsd2si/cvtss2si alone would honour the FPU rounding mode
        (round-half-to-even / banker's), which disagrees with QBE — so route
        through C99 round()/roundf() first, then truncate the integral result. }
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'callq roundf');
        Self.Emit(#9'cvttss2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq round');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Trunc') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'cvttss2si %xmm0, %rax')
      else
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Sqrt') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'sqrtss %xmm0, %xmm0')
      else
        Self.Emit(#9'sqrtsd %xmm0, %xmm0');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'CompareStr') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCompare');
      Exit;
    end;
    if SameText(FC.Name, 'CompareText') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCompareText');
      Exit;
    end;
    if SameText(FC.Name, 'PosEx') and (FC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringPosEx');
      Exit;
    end;
    if SameText(FC.Name, 'UpCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         TASTExpr(FC.Args.Items[0]).ResolvedType.IsString() then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(#9'callq _OrdAt');
      end;
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _UpCase');
      Exit;
    end;
    if SameText(FC.Name, 'ClassCreate') and (FC.Args.Count >= 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassCreate');
      { The constructor is a plain procedure (no Result) — it does NOT
        return Self in %rax.  Keep the _ClassCreate result in callee-saved
        %rbx across the ctor call, mirroring the direct constructor path. }
      if (FC.ResolvedDecl <> nil) and (FC.Args.Count > 1) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        for SetI := 1 to FC.Args.Count - 1 do
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[SetI]));
          Self.Emit(#9'pushq %rax');
        end;
        for SetI := FC.Args.Count - 1 downto 1 do
          Self.Emit(Format(#9'popq %s', [SysVArg64(SetI)]));
        Self.Emit(#9'movq %rbx, %rdi');
        if TMethodDecl(FC.ResolvedDecl).VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax',
            [(TMethodDecl(FC.ResolvedDecl).VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(Format(#9'callq %s',
            [MethodEmitNameNative(TMethodDecl(FC.ResolvedDecl),
              TMethodDecl(FC.ResolvedDecl).OwnerTypeName, 'Create')]));
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else if FC.ResolvedDecl <> nil then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.Emit(#9'movq %rax, %rdi');
        if TMethodDecl(FC.ResolvedDecl).VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax',
            [(TMethodDecl(FC.ResolvedDecl).VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(Format(#9'callq %s',
            [MethodEmitNameNative(TMethodDecl(FC.ResolvedDecl),
              TMethodDecl(FC.ResolvedDecl).OwnerTypeName, 'Create')]));
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'OrdAt') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _OrdAt');
      Exit;
    end;
    if SameText(FC.Name, 'FileExists') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _FileExists');
      Exit;
    end;
    if SameText(FC.Name, 'DirectoryExists') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _DirectoryExists');
      Exit;
    end;
    if SameText(FC.Name, 'ReadFile') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ReadFile');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFilePath') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ExtractFilePath');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileName') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ExtractFileName');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileDir') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ExtractFileDir');
      Exit;
    end;
    if SameText(FC.Name, 'ExtractFileExt') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ExtractFileExt');
      Exit;
    end;
    if SameText(FC.Name, 'ChangeFileExt') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _ChangeFileExt');
      Exit;
    end;
    if SameText(FC.Name, 'ForceDirectories') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ForceDirectories');
      Exit;
    end;
    if SameText(FC.Name, 'ExcludeTrailingPathDelimiter') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ExcludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(FC.Name, 'IncludeTrailingPathDelimiter') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _IncludeTrailingPathDelimiter');
      Exit;
    end;
    if SameText(FC.Name, 'RenameFile') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _RenameFile');
      Exit;
    end;
    if SameText(FC.Name, 'SetCurrentDir') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _SetCurrentDir');
      Exit;
    end;
    if SameText(FC.Name, 'GetCurrentDir') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetCurrentDir');
      Exit;
    end;
    if SameText(FC.Name, 'ParamStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _ParamStr');
      Exit;
    end;
    if SameText(FC.Name, 'ParamCount') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _ParamCount');
      Exit;
    end;
    if (SameText(FC.Name, 'GetEnvVar') or SameText(FC.Name, 'GetEnvironmentVariable'))
       and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _GetEnvVar');
      Exit;
    end;
    if SameText(FC.Name, 'GetProcessID') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetProcessID');
      Exit;
    end;
    if SameText(FC.Name, 'GetTempDir') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _GetTempDir');
      Exit;
    end;
    if SameText(FC.Name, 'GetTempFileName') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _GetTempFileName');
      Exit;
    end;
    if SameText(FC.Name, 'Exec') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _Exec');
      Exit;
    end;
    if SameText(FC.Name, 'CurrentExceptionMessage') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _CurrentExceptionMessage');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessCreate') and (FC.Args.Count = 0) then
    begin
      Self.Emit(#9'callq _ProcessCreate');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessRunning') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessRunning');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessReadOutput') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessReadOutput');
      Exit;
    end;
    if SameText(FC.Name, 'ProcessExitCode') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessExitCode');
      Exit;
    end;
    if SameText(FC.Name, 'FileAge') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _FileAge');
      Exit;
    end;
    if SameText(FC.Name, 'Floor') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'callq floorf');
        Self.Emit(#9'cvttss2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq floor');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Ceil') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
      begin
        Self.Emit(#9'callq ceilf');
        Self.Emit(#9'cvttss2si %xmm0, %rax');
      end
      else
      begin
        Self.Emit(#9'callq ceil');
        Self.Emit(#9'cvttsd2si %xmm0, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'IsNaN') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq __isnanf')
      else
        Self.Emit(#9'callq __isnan');
      Exit;
    end;
    if SameText(FC.Name, 'IsInfinite') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq __isinff')
      else
        Self.Emit(#9'callq __isinf');
      Exit;
    end;
    if SameText(FC.Name, 'Sin') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq sinf')
      else
        Self.Emit(#9'callq sin');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Cos') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq cosf')
      else
        Self.Emit(#9'callq cos');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Tan') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq tanf')
      else
        Self.Emit(#9'callq tan');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcTan') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq atanf')
      else
        Self.Emit(#9'callq atan');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcTan2') and (FC.Args.Count = 2) then
    begin
      IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'subq $8, %rsp');
      if IsS then
        Self.Emit(#9'movss %xmm0, (%rsp)')
      else
        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movaps %xmm0, %xmm1');
      if IsS then
        Self.Emit(#9'movss (%rsp), %xmm0')
      else
        Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      if IsS then
        Self.Emit(#9'callq atan2f')
      else
        Self.Emit(#9'callq atan2');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcSin') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq asinf')
      else
        Self.Emit(#9'callq asin');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'ArcCos') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq acosf')
      else
        Self.Emit(#9'callq acos');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Ln') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq logf')
      else
        Self.Emit(#9'callq log');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Log2') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq log2f')
      else
        Self.Emit(#9'callq log2');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Log10') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq log10f')
      else
        Self.Emit(#9'callq log10');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Power') and (FC.Args.Count = 2) then
    begin
      IsS := (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'subq $8, %rsp');
      if IsS then
        Self.Emit(#9'movss %xmm0, (%rsp)')
      else
        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movaps %xmm0, %xmm1');
      if IsS then
        Self.Emit(#9'movss (%rsp), %xmm0')
      else
        Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      if IsS then
        Self.Emit(#9'callq powf')
      else
        Self.Emit(#9'callq pow');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Sinh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq sinhf')
      else
        Self.Emit(#9'callq sinh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Cosh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq coshf')
      else
        Self.Emit(#9'callq cosh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Tanh') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToXmm0(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tySingle) then
        Self.Emit(#9'callq tanhf')
      else
        Self.Emit(#9'callq tanh');
      Self.Emit(#9'movq %xmm0, %rax');
      Exit;
    end;
    { Unqualified call to a procedural-typed field of the current class
      (implicit Self.Field) used as an expression. }
    if FC.IsProcFieldCall then
    begin
      Self.EmitProcFieldCall(nil, 'Self', False, FC.ProcFieldInfo,
        TProceduralTypeDesc(FC.ResolvedProcType), FC.Args, FC.ResolvedType);
      Exit;
    end;
    if FC.IsIndirectCall then
    begin
      { Bare function-pointer call: load the pointer from the variable slot
        and dispatch via callq *%r10.  Method pointers (of object) carry a
        16-byte TMethod block — Data (Self) must be loaded from +8 and the
        user args shifted right, exactly as in the statement path. }
      if (FC.ResolvedProcType <> nil) and
         TProceduralTypeDesc(FC.ResolvedProcType).IsMethodPtr then
        Self.EmitMethodPtrCall(
          Self.VarOperand(FC.Name),
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(FC.Name),   { local slot or global RIP-relative }
          TProceduralTypeDesc(FC.ResolvedProcType),
          FC.Args);
      { Normalise the return value width. }
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    { Type cast TypeName(Expr): ResolvedDecl is nil.  Evaluate the operand,
      then truncate/extend to the target integer-family type.  Mirrors the QBE
      backend's cast lowering. }
    if FC.ResolvedDecl = nil then
    begin
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyInterface) and
         (TASTExpr(FC.Args.Items[0]) is TIdentExpr) then
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.IntfObjOperand(TIdentExpr(TASTExpr(FC.Args.Items[0])).Name,
                               TIdentExpr(TASTExpr(FC.Args.Items[0])).IsGlobal)]))
      else
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    if (FC.ResolvedType <> nil) and (FC.ResolvedType.Kind = tyRecord) and
       (TMethodDecl(FC.ResolvedDecl).ResolvedReturnType <> nil) and
       (TMethodDecl(FC.ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      Self.Emit(Format(#9'subq $%d, %%rsp',
        [(TRecordTypeDesc(MD.ResolvedReturnType).TotalSize() + 15) and (-16)]));
      if FC.IsImplicitSelfMethod then
      begin
        Self.Emit(#9'leaq (%rsp), %r10');
        Self.Emit(#9'movq %r10, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(Format(#9'movq $%d, %%rdx',
          [TRecordTypeDesc(MD.ResolvedReturnType).TotalSize()]));
        Self.Emit(#9'callq memset');
        Self.Emit(#9'leaq (%rsp), %r10');
        Self.BeginCallArgs(MD.Params, FC.Args);
        for I := 0 to FC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(FC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, FC.Args, 2);
        Self.Emit(#9'movq %r11, %rsi');
        Self.Emit(#9'movq %r10, %rdi');
        { Virtual record-sret implicit-Self call dispatches via the vtable
          (Self in %rsi, sret buffer in %rdi). }
        Self.EmitSelfDispatchVia(MD, FuncSymbolOf(FC), '%rsi');
        Self.EndCallArgs();
      end
      else
        Self.EmitSretCall(FuncSymbolOf(FC), MD, FC.Args, '(%rsp)', False);
      Self.Emit(#9'leaq (%rsp), %rax');
      Exit;
    end;
    if FC.IsImplicitSelfMethod then
    begin
      MD := TMethodDecl(FC.ResolvedDecl);
      { Register slots = Self (%rdi) + the arg slots.  When they fit in the six
        integer registers, use the push/pop-into-registers fast path; otherwise
        spill the overflow to the stack per the SysV ABI. }
      if Self.CountArgSlots(MD.Params) + 1 <= 6 then
      begin
        Self.BeginCallArgs(MD.Params, FC.Args);
        for I := 0 to FC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(FC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, FC.Args, 1);
        Self.Emit(#9'movq %r10, %rdi');
        { Implicit-Self call to a virtual method must dispatch through the vtable
          (Self may be a more-derived instance), exactly as Self.Method() does;
          a static callq would bind to the declaring class and break
          polymorphism (and link-fail for an abstract base). }
        Self.EmitSelfDispatch(MD, FuncSymbolOf(FC));
        Self.EndCallArgs();
      end
      else
        Self.EmitImplicitSelfCallOverflow(MD, FC.Args, FuncSymbolOf(FC));
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    Self.EmitCall(FuncSymbolOf(FC), TMethodDecl(FC.ResolvedDecl), FC.Args);
    { Normalise the (32-bit-ABI) return value to the callee's return width so
      it is correctly extended in %rax before entering further arithmetic. }
    if FC.ResolvedType <> nil then
      Self.EmitNarrowToType(FC.ResolvedType);
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { Float comparison evaluated for its boolean value (0/1 in %rax).
      EmitCondBranch handles float comparisons that are themselves the
      branch condition, but when a float comparison is a sub-expression —
      nested in `and`/`or`, assigned to a Boolean, or passed as an
      argument — it reaches EmitExprToEax and must materialise the
      result.  The integer comparison path below cannot, because its
      operand emission (EmitExprToEax) has no TFloatLiteral handler. }
    if (BE.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
       (IsFloatFamily(BE.Left.ResolvedType) or
        IsFloatFamily(BE.Right.ResolvedType)) then
    begin
      IsS := (BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tySingle) and
             (BE.Right.ResolvedType <> nil) and (BE.Right.ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(BE.Left);
      Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
      Self.Emit(#9'subq $8, %rsp');
      if IsS then Self.Emit(#9'movss %xmm0, (%rsp)')
      else        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(BE.Right);
      Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
      if IsS then
      begin
        Self.Emit(#9'movss (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomiss %xmm0, %xmm1');
      end
      else
      begin
        Self.Emit(#9'movsd (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomisd %xmm0, %xmm1');
      end;
      case BE.Op of
        boEQ: Self.Emit(#9'sete %al');
        boNE: Self.Emit(#9'setne %al');
        boLT: Self.Emit(#9'setb %al');   { below (CF set) }
        boGT: Self.Emit(#9'seta %al');   { above }
        boLE: Self.Emit(#9'setbe %al');
        boGE: Self.Emit(#9'setae %al');
      end;
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    { String concatenation (boAdd on tyString): call _StringConcat(left, right). }
    if (BE.Op = boAdd) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringConcat');
      Exit;
    end;
    { String equality/inequality: content comparison via _StringEquals. }
    if (BE.Op in [boEQ, boNE]) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringEquals');
      if BE.Op = boNE then
        Self.Emit(#9'xorl $1, %eax');
      Exit;
    end;
    { String relational order via _StringCompare (strcmp-like: <0 / 0 / >0).
      Compare the result against 0 with the matching signed condition.  Without
      this, string < > <= >= fell through to the integer comparison path, which
      compared the string POINTERS (wrong answer). }
    if (BE.Op in [boLT, boGT, boLE, boGE]) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCompare');
      Self.Emit(#9'cmpl $0, %eax');
      case BE.Op of
        boLT: Self.Emit(#9'setl %al');
        boGT: Self.Emit(#9'setg %al');
        boLE: Self.Emit(#9'setle %al');
        boGE: Self.Emit(#9'setge %al');
      end;
      Self.Emit(#9'movzbl %al, %eax');
      Exit;
    end;
    { Set membership: elem in SetVar — (set >> ord(elem)) & 1 }
    if (BE.Op = boIn) and
       (BE.Right.ResolvedType <> nil) and
       (BE.Right.ResolvedType.Kind = tySet) then
    begin
      if IsJumboSet(BE.Right.ResolvedType) then
      begin
        { Jumbo: evaluate ordinal, save it, get the set's bitmap address, then
          _SetIn(rdi=set, esi=ord). }
        Self.EmitExprToEax(BE.Left);
        Self.Emit(#9'pushq %rax');           { ordinal }
        Self.EmitExprToEax(BE.Right);        { set bitmap addr -> %rax }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetIn');
        Exit;
      end;
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'movl %eax, %ecx');       { ordinal in %ecx (and %cl) }
      Self.EmitExprToEax(BE.Right);
      if TSetTypeDesc(BE.Right.ResolvedType).BitCount > 32 then
      begin
        Self.Emit(#9'shrq %cl, %rax');
        Self.Emit(#9'andq $1, %rax');
      end
      else
      begin
        Self.Emit(#9'shrl %cl, %eax');
        Self.Emit(#9'andl $1, %eax');
      end;
      { Range guard: force 0 when the ordinal is >= the set width.  The set may
        be sized to a literal's max ordinal (X in [low members]) while the
        tested element's ordinal is larger; x86 shift counts wrap mod 32/64, so
        the raw shift result for an out-of-range ordinal is meaningless and
        must be masked out.  %edx = (ord < BitCount) ? 1 : 0. }
      Self.Emit(Format(#9'cmpl $%d, %%ecx',
        [TSetTypeDesc(BE.Right.ResolvedType).BitCount]));
      Self.Emit(#9'setl %dl');
      Self.Emit(#9'movzbl %dl, %edx');
      Self.Emit(#9'andl %edx, %eax');
      Exit;
    end;
    { Set arithmetic: union (+), difference (-), intersection (*), equality. }
    if (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tySet) and
       (BE.Op in [boAdd, boSub, boMul, boEQ, boNE, boLE, boGE]) then
    begin
      if IsJumboSet(BE.Left.ResolvedType) then
      begin
        { Equality compares two bitmap addresses via _SetEqual. }
        if BE.Op in [boEQ, boNE] then
        begin
          Self.EmitExprToEax(BE.Left);
          Self.Emit(#9'pushq %rax');
          Self.EmitExprToEax(BE.Right);
          Self.Emit(#9'movq %rax, %rsi');
          Self.Emit(#9'popq %rdi');
          Self.Emit(Format(#9'movl $%d, %%edx',
            [JumboSetNBytes(BE.Left.ResolvedType)]));
          Self.Emit(#9'callq _SetEqual');
          if BE.Op = boNE then
            Self.Emit(#9'xorl $1, %eax');
          Exit;
        end;
        { Subset (<=) / superset (>=): _SetSubset(A, B) tests A subset of B.
          For >= the operands are swapped (B subset of A). }
        if BE.Op in [boLE, boGE] then
        begin
          Self.EmitExprToEax(BE.Left);
          Self.Emit(#9'pushq %rax');
          Self.EmitExprToEax(BE.Right);
          if BE.Op = boLE then
          begin
            Self.Emit(#9'movq %rax, %rsi');   { B }
            Self.Emit(#9'popq %rdi');         { A }
          end
          else
          begin
            Self.Emit(#9'movq %rax, %rdi');   { B -> A-arg }
            Self.Emit(#9'popq %rsi');         { A -> B-arg }
          end;
          Self.Emit(Format(#9'movl $%d, %%edx',
            [JumboSetNBytes(BE.Left.ResolvedType)]));
          Self.Emit(#9'callq _SetSubset');
          Exit;
        end;
        { Union/intersection/difference: write the result into a frame scratch
          slot and return its address.  The _Set helper takes rdi=dest,
          rsi=A, rdx=B, ecx=nbytes. %r12/%r13 are callee-saved across the two
          operand evaluations and the helper call. }
        Self.EmitExprToEax(BE.Left);
        Self.Emit(#9'pushq %r12');
        Self.Emit(#9'pushq %r13');
        Self.Emit(#9'movq %rax, %r12');         { A addr }
        Self.EmitExprToEax(BE.Right);
        Self.Emit(#9'movq %rax, %r13');         { B addr }
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_0')]));
        Self.Emit(#9'movq %r12, %rsi');
        Self.Emit(#9'movq %r13, %rdx');
        Self.Emit(Format(#9'movl $%d, %%ecx', [JumboSetNBytes(BE.Left.ResolvedType)]));
        case BE.Op of
          boAdd: Self.Emit(#9'callq _SetUnion');
          boMul: Self.Emit(#9'callq _SetInter');
          boSub: Self.Emit(#9'callq _SetDiff');
        end;
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand('_jset_scratch_0')]));
        Self.Emit(#9'popq %r13');
        Self.Emit(#9'popq %r12');
        Exit;
      end;
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      case BE.Op of
        boAdd: Self.Emit(#9'orq %rcx, %rax');
        boSub:
        begin
          Self.Emit(#9'notq %rcx');
          Self.Emit(#9'andq %rcx, %rax');
        end;
        boMul: Self.Emit(#9'andq %rcx, %rax');
        boEQ, boNE:
        begin
          Self.Emit(#9'cmpq %rcx, %rax');
          if BE.Op = boEQ then
            Self.Emit(#9'sete %al')
          else
            Self.Emit(#9'setne %al');
          Self.Emit(#9'movzbl %al, %eax');
        end;
        boLE, boGE:
        begin
          { subset s<=t: (s and not t)=0 ; superset s>=t: (t and not s)=0.
            %rax=s (left), %rcx=t (right).  For <= mask = s and not t; for >=
            mask = t and not s.  Then test the mask is zero. }
          if BE.Op = boLE then
          begin
            Self.Emit(#9'notq %rcx');        { ~t }
            Self.Emit(#9'andq %rcx, %rax');  { s and ~t }
          end
          else
          begin
            Self.Emit(#9'notq %rax');        { ~s }
            Self.Emit(#9'andq %rcx, %rax');  { t and ~s }
          end;
          Self.Emit(#9'testq %rax, %rax');
          Self.Emit(#9'sete %al');
          Self.Emit(#9'movzbl %al, %eax');
        end;
      end;
      Exit;
    end;
    { Short-circuit boolean and/or: evaluate LHS; skip RHS when the result
      is already determined.  For `and`, LHS=0 means result=0 (skip).
      For `or`, LHS<>0 means result=1 (skip).  When we don't skip, RHS
      is evaluated and its 0/1 value becomes the final result in %eax. }
    if ((BE.Op = boAnd) or (BE.Op = boOr)) and
       ((BE.ResolvedType = nil) or not BE.ResolvedType.IsNumeric()) then
    begin
      ScEndLbl := Self.NewLabel('sc_end');
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'testl %eax, %eax');
      if BE.Op = boAnd then
        Self.Emit(#9'jz ' + ScEndLbl)
      else
        Self.Emit(#9'jnz ' + ScEndLbl);
      Self.EmitExprToEax(BE.Right);
      Self.Emit(ScEndLbl + ':');
      Exit;
    end;
    { left -> %rax, save; right -> %rax; left -> %rcx; combine in 64 bits. }
    Self.EmitExprToEax(BE.Left);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(BE.Right);
    Self.Emit(#9'movq %rax, %rcx');   { right in %rcx }
    Self.Emit(#9'popq %rax');          { left in %rax }
    case BE.Op of
      boAdd: Self.Emit(#9'addq %rcx, %rax');
      boSub: Self.Emit(#9'subq %rcx, %rax');
      boMul: Self.Emit(#9'imulq %rcx, %rax');
      boDiv, boMod:
        begin
          { Divisor-zero guard: when SysUtils is in scope, a zero divisor
            raises a catchable EDivByZero instead of trapping (SIGFPE).
            The divisor is in %rcx; SysUtils__RaiseDivByZero longjmps and
            never returns. }
          if Self.DivGuardAvailable() then
          begin
            DivOkLbl := Self.NewLabel('divok');
            Self.Emit(#9'testq %rcx, %rcx');
            Self.Emit(#9'jne ' + DivOkLbl);
            Self.Emit(#9'callq SysUtils__RaiseDivByZero');
            Self.Emit(DivOkLbl + ':');
          end;
          { 64-bit divide.  Choose signed vs unsigned by the operand types:
            if either side is an unsigned 64-bit type, use unsigned division
            so the top bit is a magnitude bit, not a sign.  cqto sign-extends
            %rax into %rdx:%rax; for unsigned we zero %rdx instead. }
          Unsigned := IsUnsignedInt(BE.Left.ResolvedType) and
                      IsUnsignedInt(BE.Right.ResolvedType);
          if Unsigned then
          begin
            Self.Emit(#9'xorl %edx, %edx');
            Self.Emit(#9'divq %rcx');
          end
          else
          begin
            Self.Emit(#9'cqto');
            Self.Emit(#9'idivq %rcx');
          end;
          if BE.Op = boMod then
            Self.Emit(#9'movq %rdx, %rax');  { remainder in %rdx }
        end;
      { Signed integer comparisons -> boolean 0/1 in %rax.  AT&T `cmpq B, A`
        computes A - B; setcc yields 0/1, then movzbl clears the rest. }
      boAnd: Self.Emit(#9'andq %rcx, %rax');
      boOr:  Self.Emit(#9'orq %rcx, %rax');
      boXor: Self.Emit(#9'xorq %rcx, %rax');
      boShl: Self.Emit(#9'shlq %cl, %rax');
      boShr: Self.Emit(#9'shrq %cl, %rax');
      boSar: Self.Emit(#9'sarq %cl, %rax');
      boEQ, boNE, boLT, boGT, boLE, boGE:
        begin
          if (BE.Left.ResolvedType <> nil) and
             (BE.Left.ResolvedType.Kind in [tyInt64, tyUInt64, tyClass,
                tyPointer, tyInterface, tyString, tyDynArray, tyProcedural]) then
            Self.Emit(#9'cmpq %rcx, %rax')
          else
            Self.Emit(#9'cmpl %ecx, %eax');
          Unsigned := IsUnsignedInt(BE.Left.ResolvedType) or
                      IsUnsignedInt(BE.Right.ResolvedType) or
                      ((BE.Left.ResolvedType <> nil) and
                       (BE.Left.ResolvedType.Kind in [tyPointer, tyClass,
                          tyInterface, tyString, tyDynArray, tyProcedural]));
          if Unsigned then
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');
              boGT: Self.Emit(#9'seta %al');
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end
          else
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setl %al');
              boGT: Self.Emit(#9'setg %al');
              boLE: Self.Emit(#9'setle %al');
              boGE: Self.Emit(#9'setge %al');
            end;
          Self.Emit(#9'movzbl %al, %eax');  { 0/1 in %rax (movzbl zero-extends) }
        end;
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported binary operator in integer expression');
    end;
    Exit;
  end;

  { Open-array element read: A[I] where A is an open-array parameter.
    The data pointer lives in the _var_A slot (not _var_A_high). }
  { Indexed/default property read: Obj.Items[I] or Obj[I] (default property) —
    semantic has folded the index into StrExpr (a TFieldAccessExpr with PropRead
    + PropIndexExpr), leaving AExpr.IndexExpr nil.  Delegate to the StrExpr. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead <> nil) then
  begin
    Self.EmitExprToEax(TStringSubscriptExpr(AExpr).StrExpr);
    Exit;
  end;

  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TIdentExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyOpenArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.VarOperand(TIdentExpr(SAE.StrExpr).Name)]));
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record elements evaluate to their address — records are by-value via
      pointer; loading 8 bytes here would read the first field instead. }
    if TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind <> tyRecord then
      Self.EmitLoadVar('(%rax)',
        TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Dynamic-array element read: A[I] where A is a dynamic array variable.
    Data pointer is stored directly in the variable slot. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyDynArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record elements evaluate to their address — records are by-value via
      pointer; loading 8 bytes here would read the first field instead. }
    if TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind <> tyRecord then
      Self.EmitLoadVar('(%rax)',
        TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Static array element read: A[I] where A: array[L..H] of T.
    Uses TStringSubscriptExpr (the parser's postfix-bracket node). }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.EmitStaticElemScale(TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType));
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    { Record and nested static-array elements evaluate to their address —
      records are by-value via pointer; a nested array is inline storage that
      a further subscript A[I][J] indexes into.  Loading 8 bytes here would
      read the first field/element instead of yielding the aggregate address. }
    if not (TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.Kind in
            [tyRecord, tyStaticArray]) then
      Self.EmitLoadVar('(%rax)',
        TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { PChar element read: P[I] where P: PChar.  The pointer lives directly in
    the variable slot; load one (zero-extended) byte at base + I. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyPChar) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbl (%rax), %eax');
    Exit;
  end;

  { String subscript S[I]: calls _OrdAt(str_ptr, index) -> byte value as Integer. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyString) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(#9'movl %eax, %esi');
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'callq _OrdAt');
    Self.Emit(#9'movslq %eax, %rax');
    Exit;
  end;

  { Zero-arg interface method call: G.GetVal where G: IFoo.  Dispatched through
    the itab; result (if any) in %rax. }
  { Class const accessed via the type name (TThing.MaxCount): semantic marks
    the field-access node IsConstant with the value inlined — no storage to
    load, mirror the IDENT-const path. }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsConstant then
  begin
    FAE := TFieldAccessExpr(AExpr);
    { Class-level const ARRAY element access (T.Days[I]): semantic folds the
      subscript into the field-access node, setting ConstArraySymbol (the global
      data label), ConstArrayType (the static-array type) and PropIndexExpr (the
      index).  Compute base + (idx - LowBound)*ElemSize and load — mirrors the
      QBE EmitSupportsExpr/IsConstant ConstArraySymbol path.  Without this the
      access fell through to the scalar-string branch and read an empty literal. }
    if (FAE.ConstArraySymbol <> '') and (FAE.PropIndexExpr <> nil) and
       (FAE.ConstArrayType <> nil) then
    begin
      SCAT := TStaticArrayTypeDesc(FAE.ConstArrayType);
      Self.EmitExprToEax(FAE.PropIndexExpr);          { index -> %rax }
      Self.EmitStaticElemScale(SCAT);
      Self.Emit(Format(#9'leaq %s(%%rip), %%rcx',
        [NativeMangle(FAE.ConstArraySymbol)]));
      Self.Emit(#9'addq %rcx, %rax');
      if (SCAT.ElementType <> nil) and IsFloatFamily(SCAT.ElementType) then
        Self.EmitLoadFloat('(%rax)', SCAT.ElementType)
      else if (SCAT.ElementType <> nil) and SCAT.ElementType.IsString() then
        Self.Emit(#9'movq (%rax), %rax')
      else
      begin
        Self.Emit(#9'movq (%rax), %rax');
        Self.EmitNarrowToType(SCAT.ElementType);
      end;
      Exit;
    end;
    { Bare class-const array reference (no subscript): the data label address. }
    if FAE.ConstArraySymbol <> '' then
    begin
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [NativeMangle(FAE.ConstArraySymbol)]));
      Exit;
    end;
    if (FAE.ResolvedType <> nil) and FAE.ResolvedType.IsString() then
      Self.EmitStrLitAddr(FAE.ConstString)
    else
      Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(FAE.ConstValue)]));
    Exit;
  end;

  { Static var read: TypeName.StaticVar — a plain global load of the mangled
    label resolved by the semantic pass (no Self, no instance). }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsClassVarRead then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Self.Emit(Format(#9'movq %s(%%rip), %%rax',
      [NativeMangle(FAE.ClassVarEmitName)]));
    if (FAE.ResolvedType <> nil) and IsIntFamily(FAE.ResolvedType) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  { Static property read: TypeName.StaticProp — call the static getter (no Self
    argument); result in %rax. }
  if (AExpr is TFieldAccessExpr) and TFieldAccessExpr(AExpr).IsStaticPropGet then
  begin
    FAE := TFieldAccessExpr(AExpr);
    MD  := TMethodDecl(FAE.ResolvedMethod);
    Self.Emit(#9'callq ' +
      MethodEmitNameNative(MD,
        TRecordTypeDesc(FAE.ResolvedClassType).Name, MD.Name));
    if (FAE.ResolvedType <> nil) and IsIntFamily(FAE.ResolvedType) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsInterfaceCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Self.EmitInterfaceCall(FAE.RecordName, FAE.IsGlobal, FAE.IsVarParam,
      TInterfaceTypeDesc(FAE.ResolvedClassType), FAE.FieldName, nil);
    if (FAE.ResolvedType <> nil) and
       not (FAE.ResolvedType.Kind in [tyInt64, tyUInt64, tyPointer, tyClass,
                                      tyString, tyPChar, tyInterface]) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  { Built-in: Obj.ClassName — instance → vtable[0] → typeinfo[0] → name at +16 }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsClassNameAccess then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq 16(%rax), %rax');
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { Built-in: Obj.ClassType — instance → vtable[0] → typeinfo[0] }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsClassTypeAccess then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
    Self.Emit(#9'movq (%rax), %rax');
    Self.Emit(#9'movq (%rax), %rax');
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { Method-backed property read: Obj.Prop or Obj.Prop[I].
    Load the receiver (Self pointer) into %rdi, optional index into %rsi,
    then call the getter method.  Covers chained (Base <> nil), implicit-Self,
    and plain variable receivers. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).PropRead <> nil) and
     (TFieldAccessExpr(AExpr).PropRead.ReadMethod <> '') then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rdi', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rdi), %rdi');
    end
    else
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdi');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rdi), %rdi');
    end;
    if FAE.FieldInfo <> nil then
    begin
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdi', [FAE.FieldInfo.Offset]));
      Self.Emit(#9'movq (%rdi), %rdi');
    end;
    if FAE.PropIndexExpr <> nil then
    begin
      Self.Emit(#9'pushq %rdi');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'movq %rax, %rsi');
    end;
    Self.EmitPropAccessorCallNative(FAE.PropOwnerType, FAE.PropRead.ReadMethod,
      FAE.PropAccessorVSlot);
    if (FAE.ResolvedType <> nil) and
       not IsIntFamily(FAE.ResolvedType) and
       not IsFloatFamily(FAE.ResolvedType) and
       (FAE.ResolvedType.Kind <> tyString) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { String field subscript read: R.Field[I] (0-based char access).
    Same receiver ladder as the array path, then load the string data
    pointer from the field slot and read byte I. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsCharAccess and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rcx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
    Self.Emit(#9'movq (%rcx), %rcx');      { string data pointer }
    Self.Emit(#9'pushq %rcx');
    Self.EmitExprToEax(FAE.PropIndexExpr);
    Self.Emit(#9'popq %rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbq (%rax), %rax');
    Exit;
  end;

  { Array field subscript read: R.Arr[I] where Arr is an array-typed field.
    Compute the record base address, add FieldInfo.Offset to reach the array
    field, then index into the array (static, dynamic, or open). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsArrayAccess and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.Base <> nil then
    begin
      { Chained receiver (c.N.Arr[I]): the base expression evaluates to the
        record/object address. }
      Self.EmitExprToEax(FAE.Base);
      Self.Emit(#9'movq %rax, %rcx');
    end
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else if FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { Class variable / var-param: the slot holds a POINTER to the object
        or record — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
    if FAE.FieldInfo.TypeDesc.Kind = tyDynArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
      Self.Emit(#9'addq %rcx, %rax');
      if TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
    begin
      Self.Emit(#9'pushq %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.EmitStaticElemScale(TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc));
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'addq %rcx, %rax');
      if TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyOpenArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
      Self.Emit(#9'addq %rcx, %rax');
      if TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else
      raise ENativeCodeGenError.Create(Format(
        'IsArrayAccess on non-array field ''%s'' (kind %d) at line %d',
        [FAE.FieldName, Ord(FAE.FieldInfo.TypeDesc.Kind), FAE.Line]));
    Exit;
  end;

  { Chained field access: Base.Field where Base is another expression.
    Recursively emit the base (returns address for records), then add offset. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     not TFieldAccessExpr(AExpr).IsMethodCall and
     not TFieldAccessExpr(AExpr).IsConstructorCall and
     (TFieldAccessExpr(AExpr).Base <> nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    { When the base is a record-returning call, EmitExprToEax materialises an
      sret buffer with `subq $N,%rsp` and never frees it — fine for a
      standalone expression (the frame epilogue reclaims it), but inside an
      argument push/pop sequence that stray allocation shifts %rsp and
      corrupts the other already-pushed arguments (e.g. a const-string arg
      reloaded by %rsp offset).  Allocate the buffer here, read the scalar
      field out of it, then FREE it so this expression nets zero stack change.
      Only safe for scalar fields — a record/static-array field returns an
      address INTO the buffer, so its lifetime must outlive this read and the
      buffer cannot be freed here. }
    if Self.IsNativeRecordCall(FAE.Base) and
       not (IsJumboSet(FAE.FieldInfo.TypeDesc) or
            (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
    begin
      Self.Emit(Format(#9'subq $%d, %%rsp', [Self.RecArgBufBytes(FAE.Base)]));
      Self.EmitRecordCallSretAt(FAE.Base, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rcx');
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rcx', [FAE.FieldInfo.Offset]));
      Self.EmitLoadVar('(%rcx)', FAE.FieldInfo.TypeDesc);
      Self.Emit(Format(#9'addq $%d, %%rsp', [Self.RecArgBufBytes(FAE.Base)]));
      Exit;
    end;
    Self.EmitExprToEax(FAE.Base);
    if NativeExprOwnsRef(FAE.Base) then
      Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rcx');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'leaq %d(%%rcx), %%rcx', [FAE.FieldInfo.Offset]));
    if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
      Self.Emit(#9'movq %rcx, %rax')
    else
      Self.EmitLoadVar('(%rcx)', FAE.FieldInfo.TypeDesc);
    if NativeExprOwnsRef(FAE.Base) then
    begin
      { The loaded field value is borrowed from the transient base we are about
        to release.  If that value is itself a managed class reference, it
        aliases INTO the transient's owned object graph: releasing the transient
        runs _FieldCleanup on it, which releases (and frees) the very object the
        loaded pointer designates — leaving the result dangling for the rest of
        the chain (e.g. MakeIt().A.B.Method(): freeing the MakeIt() transient
        frees A, whose cleanup frees B, before B's method runs).  Pin the result
        with an AddRef first so the cleanup's matching release nets out and the
        object survives the chain.  This intentionally leaks +1 on the result
        (the same deep-chain transient leak the QBE backend has — see bugs.txt);
        a crash is the worse failure, so correctness wins until the chain gains
        a deferred-release mechanism. }
      if FAE.FieldInfo.TypeDesc.Kind in [tyClass, tyInterface] then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'popq %rax');
      end;
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { Record/class field read: Rec.Field or Class.Field.
    Handles local/global record bases and class (pointer-deref) bases. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     not TFieldAccessExpr(AExpr).IsMethodCall and
     not TFieldAccessExpr(AExpr).IsConstructorCall and
     (TFieldAccessExpr(AExpr).Base = nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rcx), %rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsClassAccess then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rcx), %rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsVarParam then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]))
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end
    else if (not Self.IsCaptured(FAE.RecordName)) and
            (not (FSretFunc and SameText(FAE.RecordName, 'Result'))) and
            (not Self.IsLocal(FAE.RecordName)) and
            (FAE.FieldInfo.Offset = 0) and
            (not (IsJumboSet(FAE.FieldInfo.TypeDesc) or
                  (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray]))) and
            (not Self.IsThreadVarGlobal(FAE.RecordName)) then
      { Non-threadvar offset-0 fast path: read the field directly off the
        PC-relative global.  Only applies to a genuine global (not local, not
        captured, not sret Result, not threadvar). }
      Self.EmitLoadVar(FAE.RecordName + '(%rip)', FAE.FieldInfo.TypeDesc)
    else
    begin
      { Compute the record base into %rcx, handling local / global / sret-Result
        / nested-captured uniformly, then read or address the field.  Aggregate
        fields (record/static array/jumbo set) yield an ADDRESS in %rax; scalar
        fields are loaded by value. }
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      if (IsJumboSet(FAE.FieldInfo.TypeDesc) or
         (FAE.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray])) then
      begin
        if FAE.FieldInfo.Offset = 0 then
          Self.Emit(#9'movq %rcx, %rax')
        else
          Self.Emit(Format(#9'leaq %d(%%rcx), %%rax', [FAE.FieldInfo.Offset]));
      end
      else
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
    end;
    Exit;
  end;

  { Zero-arg method call on a variable: B.GetVal or H.GetValue.
    For class variables Self is the loaded pointer; for record variables Self
    is the address of the record storage. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsMethodCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.ResolvedMethod = nil then
      raise ENativeCodeGenError.Create(
        'native backend: zero-arg method call has no ResolvedMethod');
    MD := TMethodDecl(FAE.ResolvedMethod);
    if FAE.Base <> nil then
    begin
      Self.EmitExprToEax(FAE.Base);
      if NativeExprOwnsRef(FAE.Base) then
        Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
    end
    else if MD.IsRecordMethod and FAE.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]))
    else if MD.IsRecordMethod then
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, True, '%rdi');
    end
    else if FAE.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]));
      Self.Emit(#9'movq (%rdi), %rdi');
    end
    else
    begin
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rdi');
    end;
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        MD, MD.OwnerTypeName, FAE.FieldName));
    if (MD.ResolvedReturnType <> nil) and
       not IsIntFamily(MD.ResolvedReturnType) and
       not IsFloatFamily(MD.ResolvedReturnType) and
       (MD.ResolvedReturnType.Kind <> tyString) then
      Self.EmitNarrowToType(MD.ResolvedReturnType);
    if (FAE.Base <> nil) and NativeExprOwnsRef(FAE.Base) then
    begin
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
    end;
    Exit;
  end;

  { ── TAddrOfExpr: @Expr ── }
  if AExpr is TAddrOfExpr then
  begin
    AOE := TAddrOfExpr(AExpr);

    { @Array[I] — address of array element.  The inner expression is
      TStringSubscriptExpr (the parser's postfix-bracket node).  Compute
      base + index * elemSize without the final load. }
    if AOE.Expr is TStringSubscriptExpr then
    begin
      SAE := TStringSubscriptExpr(AOE.Expr);
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyStaticArray) then
      begin
        Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.EmitStaticElemScale(TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyOpenArray) then
      begin
        if (SAE.StrExpr is TIdentExpr) then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(SAE.StrExpr).Name)]))
        else
          Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
      if (SAE.StrExpr.ResolvedType <> nil) and
         (SAE.StrExpr.ResolvedType.Kind = tyDynArray) then
      begin
        Self.EmitExprToEax(SAE.StrExpr);
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(SAE.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
        Exit;
      end;
    end;

    { @FuncName — load the function's code address into %rax. }
    if (AOE.Expr is TIdentExpr) and
       (TIdentExpr(AOE.Expr).ResolvedType <> nil) and
       (TIdentExpr(AOE.Expr).ResolvedType.Kind = tyProcedural) then
    begin
      if AOE.ResolvedFreeRoutine <> nil then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TMethodDecl(AOE.ResolvedFreeRoutine).ResolvedQbeName)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [TIdentExpr(AOE.Expr).Name]));
      Exit;
    end;

    { @VarParam — the variable's slot holds a pointer to the caller's data;
      load that pointer value (not the slot address). }
    if (AOE.Expr is TIdentExpr) and (TIdentExpr(AOE.Expr).ParamMode <> pmNone) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AOE.Expr).Name)]));
      Exit;
    end;

    { @ImplicitSelfField — field of Self accessed by bare name inside a method. }
    if (AOE.Expr is TIdentExpr) and
       TIdentExpr(AOE.Expr).IsImplicitSelf and
       (TIdentExpr(AOE.Expr).ImplicitFieldInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AOE.Expr).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax',
          [TFieldInfo(TIdentExpr(AOE.Expr).ImplicitFieldInfo).Offset]));
      Exit;
    end;

    { @Variable — take the address of a local or global variable. }
    if AOE.Expr is TIdentExpr then
    begin
      if Self.IsLocal(TIdentExpr(AOE.Expr).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax',
          [Self.VarOperand(TIdentExpr(AOE.Expr).Name)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [TIdentExpr(AOE.Expr).Name]));
      Exit;
    end;

    { @Rec.Arr[I] — address of array-field element.  The field access has
      IsArrayAccess set by semantic and PropIndexExpr holds the subscript. }
    if (AOE.Expr is TFieldAccessExpr) and
       TFieldAccessExpr(AOE.Expr).IsArrayAccess then
    begin
      FAE := TFieldAccessExpr(AOE.Expr);
      if FAE.Base <> nil then
      begin
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FAE.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
        if FAE.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
        if FAE.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      end;
      if FAE.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
      if FAE.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        Self.Emit(#9'movq (%rcx), %rcx');
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end
      else if FAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.EmitStaticElemScale(TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end
      else
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.PropIndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax',
          [TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize()]));
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'addq %rcx, %rax');
      end;
      Exit;
    end;

    { @Obj.MethodName — method-pointer construction is handled at statement
      level (TAssignment) to write directly into the 16-byte destination slot. }
    if (AOE.Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(AOE.Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(AOE.Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(AOE.Expr).ResolvedType).IsMethodPtr then
      raise ENativeCodeGenError.Create(
        'native backend: @Obj.Method must be used in assignment context');

    { @Rec.Field — address of a record/class field (non-array). }
    if AOE.Expr is TFieldAccessExpr then
    begin
      FAE := TFieldAccessExpr(AOE.Expr);
      if FAE.Base <> nil then
      begin
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FAE.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.ImplicitBaseInfo.Offset]));
        if FAE.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rcx');
        if FAE.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FAE.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, True, '%rcx');
      end;
      if (FAE.FieldInfo <> nil) and (FAE.FieldInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
      Self.Emit(#9'movq %rcx, %rax');
      Exit;
    end;

    raise ENativeCodeGenError.Create(
      'native backend: unsupported TAddrOfExpr form (' +
      AOE.Expr.ClassName + ')');
  end;

  { P^ — pointer dereference read.  Load the pointer into %rcx, then load
    the pointed-to value into %rax through (%rcx). }
  { Set literal [EnumA, EnumC, ...] — compute bitmask at compile time. }
  if (AExpr is TArrayLiteralExpr) and
     (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tySet) then
  begin
    { Jumbo set literal: build the bitmap in the scratch_1 slot — memset 0,
      then _SetInclude per element (elements may be non-constant).  Return the
      buffer address.  scratch_1 (not scratch_0) so a surrounding set-op
      assignment, which uses scratch_0, is not clobbered. }
    if IsJumboSet(AExpr.ResolvedType) then
    begin
      Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_1')]));
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(Format(#9'movl $%d, %%edx', [TSetTypeDesc(AExpr.ResolvedType).RawSize()]));
      Self.Emit(#9'callq memset');
      for SetI := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      begin
        SetElem := TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[SetI]);
        Self.EmitExprToEax(SetElem);
        Self.Emit(#9'movl %eax, %esi');     { ordinal }
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand('_jset_scratch_1')]));
        Self.Emit(#9'callq _SetInclude');
      end;
      Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand('_jset_scratch_1')]));
      Exit;
    end;
    SetMask := 0;
    for SetI := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
    begin
      SetElem := TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[SetI]);
      if SetElem is TIntLiteral then
        SetMask := SetMask or (Int64(1) shl TIntLiteral(SetElem).Value)
      else if (SetElem is TIdentExpr) and TIdentExpr(SetElem).IsConstant then
        SetMask := SetMask or (Int64(1) shl TIdentExpr(SetElem).ConstValue);
    end;
    if TSetTypeDesc(AExpr.ResolvedType).BitCount > 32 then
      Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(SetMask)]))
    else
      Self.Emit(Format(#9'movl $%s, %%eax', [IntToStr(SetMask)]));
    Exit;
  end;

  if AExpr is TDerefExpr then
  begin
    Self.EmitExprToEax(TDerefExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (IsJumboSet(AExpr.ResolvedType) or
       (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray])) then
    begin
      { Pointer-to-record/array: the pointer value IS the record address.
        Callers (field access, assignment) work with addresses for records. }
    end
    else
    begin
      Self.Emit(#9'movq %rax, %rcx');
      Self.EmitLoadVar('(%rcx)', AExpr.ResolvedType);
    end;
    Exit;
  end;

  { not Expr — logical or bitwise NOT. }
  if AExpr is TNotExpr then
  begin
    Self.EmitExprToEax(TNotExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind = tyBoolean) then
      Self.Emit(#9'xorl $1, %eax')
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      Self.Emit(#9'notq %rax')
    else
      Self.Emit(#9'notl %eax');
    Exit;
  end;

  { TypeName.Create — allocate a new class instance.
    Returns the instance pointer in %rax.  Does NOT do ARC (caller's job). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsConstructorCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if (FAE.ResolvedType = nil) or not (FAE.ResolvedType is TRecordTypeDesc) then
      raise ENativeCodeGenError.Create('native backend: constructor call has no class type');
    { _ClassAlloc(size, fieldcleanup_fn): returns zeroed instance ptr (after header). }
    Self.Emit(Format(#9'movq $%d, %%rdi',
      [TRecordTypeDesc(FAE.ResolvedType).TotalSize()]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi',
      [Self.ClassSymName(FAE.ResolvedType.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    { Store vtable pointer at offset 0 if the class has virtual methods. }
    if TRecordTypeDesc(FAE.ResolvedType).HasVTable() then
    begin
      Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx',
        [Self.ClassSymName(FAE.ResolvedType.Name)]));
      Self.Emit(#9'movq %rcx, (%rax)');
    end;
    if FDebugMode then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'movq %rax, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(Format(#9'movq typeinfo_%s+16(%%rip), %%rsi',
        [Self.ClassSymName(FAE.ResolvedType.Name)]));
      SetI := FStrLits.IndexOf(FCurrentUnitName);
      if SetI < 0 then SetI := FStrLits.Add(FCurrentUnitName);
      Self.Emit(Format(#9'leaq __s%d+12(%%rip), %%rdx', [SetI]));
      Self.Emit(Format(#9'movq $%d, %%rcx', [FAE.Line]));
      Self.Emit(#9'callq _LeakTrackerRegister');
      Self.Emit(#9'movq %rbx, %rax');
      Self.Emit(#9'popq %rbx');
    end;
    { Call user-defined zero-arg Create body if present. }
    if FAE.ResolvedMethod <> nil then
    begin
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        TMethodDecl(FAE.ResolvedMethod), FAE.ResolvedType.Name, FAE.FieldName));
      Self.Emit(#9'popq %rax');
    end;
    { %rax = new instance pointer. }
    Exit;
  end;

  { Class method call: C.Method() or C.Method(args) returning a scalar. }
  if AExpr is TMethodCallExpr then
  begin
    Self.EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;

  { Indirect function call expression: FuncPtrExpr(args) returning a value.
    Evaluate the callee expression, save the function pointer on the stack
    (arg evaluation may invoke callq which clobbers caller-saved regs), push
    args, pop them into registers, load the saved func ptr into %r10, and
    dispatch via callq *%r10. }
  if AExpr is TIndirectFuncCallExpr then
  begin
    Self.EmitExprToEax(TIndirectFuncCallExpr(AExpr).CalleeExpr);
    Self.Emit(#9'pushq %rax');
    for SetI := 0 to TIndirectFuncCallExpr(AExpr).Args.Count - 1 do
    begin
      Self.EmitExprToEax(TASTExpr(TIndirectFuncCallExpr(AExpr).Args.Items[SetI]));
      Self.Emit(#9'pushq %rax');
    end;
    for SetI := TIndirectFuncCallExpr(AExpr).Args.Count - 1 downto 0 do
      Self.Emit(Format(#9'popq %s', [SysVArg64(SetI)]));
    Self.Emit(#9'popq %r10');
    Self.Emit(#9'callq *%r10');
    Exit;
  end;

  { `inherited Method(args)` in expression position — static dispatch to the
    parent slot; result lands in %rax / %xmm0 (the EmitExprToEax contract). }
  if AExpr is TInheritedCallExpr then
  begin
    Self.EmitInheritedCallSeq(
      TMethodDecl(TInheritedCallExpr(AExpr).ResolvedMethod),
      TInheritedCallExpr(AExpr).Args,
      TInheritedCallExpr(AExpr).Name);
    Exit;
  end;

  { X is TFoo — class type test via _IsInstance / _ImplementsInterface.
    Result: 0/1 in %eax. }
  if AExpr is TIsExpr then
  begin
    Self.EmitExprToEax(TIsExpr(AExpr).Obj);
    Self.Emit(#9'movq %rax, %rdi');
    if (TIsExpr(AExpr).ResolvedTargetType <> nil) and
       (TIsExpr(AExpr).ResolvedTargetType.Kind = tyInterface) then
    begin
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.ClassSymName(TIsExpr(AExpr).TypeName)]));
      Self.Emit(#9'callq _ImplementsInterface');
    end
    else
    begin
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.ClassSymName(TIsExpr(AExpr).TypeName)]));
      Self.Emit(#9'callq _IsInstance');
    end;
    Exit;
  end;

  { X as TFoo — checked downcast.  Calls _IsInstance; raises EInvalidCast on
    failure; result = original object pointer (class-to-class). }
  if AExpr is TAsExpr then
  begin
    ScEndLbl := Self.NewLabel('as_ok');
    Self.EmitExprToEax(TAsExpr(AExpr).Obj);
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.ClassSymName(TAsExpr(AExpr).TypeName)]));
    Self.Emit(#9'callq _IsInstance');
    Self.Emit(#9'testl %eax, %eax');
    Self.Emit(#9'jnz ' + ScEndLbl);
    Self.Emit(#9'callq _Raise_InvalidCast');
    Self.Emit(ScEndLbl + ':');
    Self.Emit(#9'popq %rax');
    Exit;
  end;

  { Supports(Obj, IFoo[, OutVar]) — interface query via _ImplementsInterface.
    Result: 0/1 in %eax.  The 3-arg form additionally populates OutVar's fat
    pointer (obj+itab) on success, with ARC retain/release, mirroring the QBE
    EmitSupportsExpr path. }
  if AExpr is TSupportsExpr then
  begin
    SuppOut := TSupportsExpr(AExpr).OutVarName;
    Self.EmitExprToEax(TSupportsExpr(AExpr).Obj);
    if SuppOut = '' then
    begin
      { 2-arg form: boolean result only. }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
      Self.Emit(#9'callq _ImplementsInterface');
      Exit;
    end;
    { 3-arg form.  Keep obj on the stack across the helper calls. }
    Self.Emit(#9'pushq %rax');               { (obj) }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
    Self.Emit(#9'callq _ImplementsInterface');
    LSuppNo  := Self.NewLabel('supports_no');
    LSuppEnd := Self.NewLabel('supports_end');
    Self.Emit(#9'testl %eax, %eax');
    Self.Emit(#9'jz ' + LSuppNo);
    { Success: register the out-var (if global) so its _obj/_itab labels are
      emitted, then store the new fat pointer with ARC. }
    if not Self.IsLocal(SuppOut) then
      Self.AddGlobal(SuppOut, TSupportsExpr(AExpr).ResolvedIntfType);
    Self.Emit(#9'movq (%rsp), %rdi');        { obj }
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
      [Self.IntfTypeInfoName(TSupportsExpr(AExpr).IntfTypeName)]));
    Self.Emit(#9'callq _GetItab');           { itab -> %rax }
    Self.Emit(#9'pushq %rax');               { (itab, obj) }
    { ARC: retain new obj, release the out-var's old obj slot. }
    Self.Emit(#9'movq 8(%rsp), %rdi');       { obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi',
      [Self.IntfObjOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');                { itab }
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.IntfItabOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'popq %rax');                { obj }
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.IntfObjOperand(SuppOut, TSupportsExpr(AExpr).OutVarIsGlobal)]));
    Self.Emit(#9'movl $1, %eax');
    Self.Emit(#9'jmp ' + LSuppEnd);
    Self.Emit(LSuppNo + ':');
    Self.Emit(#9'addq $8, %rsp');            { discard saved obj }
    Self.Emit(#9'movl $0, %eax');
    Self.Emit(LSuppEnd + ':');
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    Format('native backend: unsupported expression form %s at line %d col %d in %s',
      [AExpr.ClassName, AExpr.Line, AExpr.Col, FCurrentUnitName]));
end;

{ Emit a class method call: load Self into %rdi, then scalar args starting at
  %rsi/%rdx/etc.  The method symbol is OwnerTypeName_MethodName. }
procedure TX86_64Backend.EmitMethodCallExpr(ACall: TMethodCallExpr);
var
  I:          Integer;
  SetI:       Integer;
  MD:         TMethodDecl;
  Sym:        string;
  Arg:        TASTExpr;
  RT:         TRecordTypeDesc;
  UserSlots:     Integer;
  TotalSlots:    Integer;
  AllocSz:       Integer;
  SlotOff:       Integer;
  CleanUp:       Integer;
  OverflowSlots: Integer;
  Dest:          Integer;
  HD:            TList<Integer>;
  HK:            TList<Integer>;
  HTotal:        Integer;
  RecvBufBytes:  Integer;
begin
  { Interface method dispatch: receiver is an interface fat pointer; route
    through the itab rather than a static method symbol. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    { When the receiver is an expression (an interface stored in a field, e.g.
      H.G.Greet()), ACall.ObjectName is empty — pass ACall.ObjExpr so the obj/
      itab are loaded from the field's fat pointer rather than bogus _obj/_itab
      operands. }
    Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam,
      TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
      ACall.ObjExpr);
    Exit;
  end;

  { Constructor call with args: TypeName.Create(args).
    Allocate the instance, save it in %r10, push args, pop into registers,
    call the constructor body, then return the instance in %rax. }
  if ACall.IsConstructorCall then
  begin
    RT := TRecordTypeDesc(ACall.ResolvedClassType);
    if ACall.IsMetaclassDispatch then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'callq _ClassCreate');
    end
    else
    begin
      Self.Emit(Format(#9'movq $%d, %%rdi', [RT.TotalSize()]));
      Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi', [Self.ClassSymName(RT.Name)]));
      Self.Emit(#9'callq _ClassAlloc');
      if RT.HasVTable() then
      begin
        Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx', [Self.ClassSymName(RT.Name)]));
        Self.Emit(#9'movq %rcx, (%rax)');
      end;
    end;
    if FDebugMode then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'movq %rax, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(Format(#9'movq typeinfo_%s+16(%%rip), %%rsi',
        [Self.ClassSymName(RT.Name)]));
      SetI := FStrLits.IndexOf(FCurrentUnitName);
      if SetI < 0 then SetI := FStrLits.Add(FCurrentUnitName);
      Self.Emit(Format(#9'leaq __s%d+12(%%rip), %%rdx', [SetI]));
      Self.Emit(Format(#9'movq $%d, %%rcx', [ACall.Line]));
      Self.Emit(#9'callq _LeakTrackerRegister');
      Self.Emit(#9'movq %rbx, %rax');
      Self.Emit(#9'popq %rbx');
    end;
    MD := TMethodDecl(ACall.ResolvedMethod);
    if MD <> nil then
    begin
      UserSlots  := Self.CountArgSlots(MD.Params);
      TotalSlots := UserSlots + 1;
      Sym := MethodEmitNameNative(MD, RT.Name, ACall.Name);

      if TotalSlots <= 6 then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.BeginCallArgs(MD.Params, ACall.Args);
        for I := 0 to ACall.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(ACall.Args.Items[I]), I);
        Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
        Self.Emit(#9'movq %rbx, %rdi');
        if ACall.IsMetaclassDispatch and (MD.VTableSlot >= 0) then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EndCallArgs();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        HD := TList<Integer>.Create();
        HK := TList<Integer>.Create();
        HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
        OverflowSlots := TotalSlots - 6;
        AllocSz := ((TotalSlots * 8 + 15) and (-16));
        Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
        Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);
        Self.Emit(Format(#9'movq %%rbx, 0(%%rsp)', []));
        CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
        if ACall.IsMetaclassDispatch and (MD.VTableSlot >= 0) then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
        HD.Free();
        HK.Free();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
    end;
    Exit;
  end;

  { Built-in TObject.InheritsFrom(C): _InheritsFrom(self_typeinfo, arg_typeinfo)
    → Boolean in %eax.  A class-instance receiver carries its typeinfo at
    vtable[0] = *( *obj ); the argument is a class-of value that EmitExprToEax
    lowers to a typeinfo pointer (mirrors the QBE path). }
  if ACall.IsBuiltinInheritsFrom then
  begin
    Self.EmitMethodReceiverToRax(ACall);     { instance ptr -> %rax }
    if (ACall.ResolvedClassType <> nil) and
       (ACall.ResolvedClassType.Kind = tyClass) then
    begin
      Self.Emit(#9'movq (%rax), %rax');       { vtable }
      Self.Emit(#9'movq (%rax), %rax');       { typeinfo = vtable[0] }
    end;
    Self.Emit(#9'pushq %rax');                { save self typeinfo }
    Self.EmitExprToEax(TASTExpr(ACall.Args.Items[0]));  { arg typeinfo -> %rax }
    Self.Emit(#9'movq %rax, %rsi');
    Self.Emit(#9'popq %rdi');                 { self typeinfo }
    Self.Emit(#9'callq _InheritsFrom');
    Exit;
  end;

  { Built-in TObject.ToString: virtual dispatch through vtable slot 2 (offset 16:
    [0]=typeinfo, [8]=Destroy, [16]=ToString).  Returns a string in %rax. }
  if ACall.IsBuiltinToString then
  begin
    Self.EmitMethodReceiverToRax(ACall);     { instance ptr -> %rax }
    Self.Emit(#9'movq %rax, %rdi');           { Self }
    Self.Emit(#9'movq (%rdi), %rax');         { vtable }
    Self.Emit(#9'movq 16(%rax), %rax');       { vtable[2] = ToString }
    Self.Emit(#9'callq *%rax');
    Exit;
  end;

  { Procedural-typed field call used as an expression: Result := Self.FFn(S).
    Dispatch through the (Code, Data) pair stored in the field; the result is
    left in %rax. }
  if ACall.IsProcFieldCall then
  begin
    Self.EmitProcFieldCall(ACall.ObjExpr, ACall.ObjectName, ACall.IsVarParam,
      ACall.ProcFieldInfo, TProceduralTypeDesc(ACall.ResolvedProcType),
      ACall.Args, ACall.ResolvedType);
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallExpr has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method call (TypeName.StaticMethod(args)): NO implicit Self — the
    callee shifts every parameter down one register (first user arg in %rdi).
    A value-returning static method is exactly a plain function call to the
    method's mangled symbol, so route it through EmitCall, which marshals args
    into %rdi.. with no receiver.  Record-returning static factories use the
    sret ABI and are handled in EmitMethodSretCall. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    Self.EmitCall(Sym, MD, ACall.Args);
    Exit;
  end;

  UserSlots  := Self.CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;

  if TotalSlots <= 6 then
  begin
    { Record-returning-call receiver (e.g. A.Plus(B).Val()): the receiver is a
      transient record value with no home, but a record method needs Self as an
      ADDRESS.  Materialise the call result into a stack buffer FIRST (before any
      args are pushed) and carry its address in callee-saved %rbx, which survives
      the arg push/pop sequence.  %rbx is saved/restored around the whole call. }
    RecvBufBytes := 0;
    if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
       Self.IsNativeRecordCall(ACall.ObjExpr) then
    begin
      RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
      Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rbx');     { receiver address -> callee-saved }
    end;

    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%r10');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%r10), %r10');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%r10', [ACall.ObjectName]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %r10')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %r10');
    end
    else
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));

    Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
    Self.Emit(#9'movq %r10, %rdi');
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
    if RecvBufBytes > 0 then
    begin
      { Free the receiver buffer and restore %rbx (does not touch the return
        registers %rax/%rdx/%xmm0/%xmm1). }
      Self.Emit(Format(#9'addq $%d, %%rsp', [RecvBufBytes]));
      Self.Emit(#9'popq %rbx');
    end;
  end
  else
  begin
    { Record-returning-call receiver on the >6-slot path: materialise the result
      into a stack buffer and carry its address in callee-saved %rbx (immune to
      the hoist/alloc %rsp movement below).  See the <=6 path for the rationale. }
    RecvBufBytes := 0;
    if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
       Self.IsNativeRecordCall(ACall.ObjExpr) then
    begin
      RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
      Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
      Self.Emit(#9'movq %rsp, %rbx');
    end;
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rax), %rax');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rax', [ACall.ObjectName]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));

    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
    if RecvBufBytes > 0 then
    begin
      Self.Emit(Format(#9'addq $%d, %%rsp', [RecvBufBytes]));
      Self.Emit(#9'popq %rbx');
    end;
  end;
end;

procedure TX86_64Backend.EmitImplicitSelfCallOverflow(MD: TMethodDecl;
  AArgs: TObjectList; const ASym: string);
var
  I, AllocSz, CleanUp, Dest: Integer;
  Arg: TASTExpr;
  HD, HK: TList<Integer>;
  HTotal: Integer;
begin
  { Slot block: slot 0 = Self, slots 1.. = one per logical arg (matching
    EmitMethodOverflowLoad's reader).  16-aligned. }
  AllocSz := (((Self.CountArgSlots(MD.Params) + 1) * 8 + 15) and (-16));
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', AArgs, HD, HK);
  Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
  Self.EmitArgsToSlots(AArgs, MD.Params, AllocSz, HTotal, HD, HK);
  { Self into slot 0. }
  Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
  Self.Emit(#9'movq %rax, 0(%rsp)');
  { Load slot 0 -> %rdi (Self) and the arg slots into %rsi.. / %xmm0.., spilling
    the >6th integer slot to the stack; returns bytes to reclaim after the call. }
  CleanUp := Self.EmitMethodOverflowLoad(MD.Params, AArgs, AllocSz);
  { Self is now in %rdi — dispatch (vtable-aware) exactly like Self.Method(). }
  Self.EmitSelfDispatch(MD, ASym);
  Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  HD.Free();
  HK.Free();
end;

{ Leave the ADDRESS of a var/out argument in %rax.  Shared by every
  call-emission path that passes a var param — loading the variable's
  VALUE here (the old EmitSretCall behaviour) hands the callee a garbage
  pointer. }
procedure TX86_64Backend.EmitVarArgAddrToRax(AArg: TASTExpr);
var
  FAE: TFieldAccessExpr;
  SubAddrWrap: TAddrOfExpr;
begin
  if (AArg is TIdentExpr) and (TIdentExpr(AArg).ParamMode <> pmNone) then
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.VarOperand(TIdentExpr(AArg).Name)]))
  else if (AArg is TIdentExpr) and TIdentExpr(AArg).IsImplicitSelf
          and (TIdentExpr(AArg).ImplicitFieldInfo <> nil) then
  begin
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    if TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax',
        [TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset]));
  end
  else if (AArg is TIdentExpr) and Self.IsLocal(TIdentExpr(AArg).Name) then
    Self.Emit(Format(#9'leaq %s, %%rax',
      [Self.VarOperand(TIdentExpr(AArg).Name)]))
  else if (AArg is TIdentExpr) and (TIdentExpr(AArg).ConstArraySymbol <> '') then
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
      [NativeMangle(TIdentExpr(AArg).ConstArraySymbol)]))
  else if (AArg is TIdentExpr) and (AArg.ResolvedType <> nil) and
          (AArg.ResolvedType.Kind = tyInterface) then
    { Global interface: there is no bare Name symbol — the 16-byte fat
      pointer block starts at the Name_obj label. }
    Self.Emit(Format(#9'leaq %s_obj(%%rip), %%rax', [TIdentExpr(AArg).Name]))
  else if AArg is TIdentExpr then
    Self.EmitLeaqGlobal(TIdentExpr(AArg).Name, '%rax')
  else if AArg is TFieldAccessExpr then
  begin
    { Record/class field as var argument (including fields of the sret
      Result record).  Compute the field's address. }
    FAE := TFieldAccessExpr(AArg);
    if FAE.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: var/out field argument has no resolved field info');
    if FAE.Base <> nil then
      Self.EmitExprToEax(FAE.Base)
    else if FAE.IsImplicitSelf then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if (FAE.ImplicitBaseInfo <> nil) and (FAE.ImplicitBaseInfo.Offset > 0) then
        Self.Emit(Format(#9'addq $%d, %%rax', [FAE.ImplicitBaseInfo.Offset]));
      if FAE.IsClassAccess then
        Self.Emit(#9'movq (%rax), %rax');
    end
    else if (FSretFunc and SameText(FAE.RecordName, 'Result'))
            or FAE.IsClassAccess or FAE.IsVarParam then
    begin
      { The slot holds a POINTER (sret Result, class instance, var-param
        record) — load it. }
      Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
      if FAE.IsClassAccess and FAE.IsVarParam then
        { var-param class: slot -> caller var -> instance }
        Self.Emit(#9'movq (%rax), %rax');
    end
    else Self.EmitVarBaseToReg(FAE.RecordName, True, '%rax');
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax', [FAE.FieldInfo.Offset]));
  end
  else if AArg is TStringSubscriptExpr then
  begin
    { Array element a[i] as a var/out actual.  Its address is what @a[i]
      computes, so evaluate a transient TAddrOfExpr (leaves the element
      address in %rax). }
    SubAddrWrap := TAddrOfExpr.Create();
    try
      SubAddrWrap.Expr := AArg;
      Self.EmitExprToEax(SubAddrWrap);
    finally
      SubAddrWrap.Expr := nil;   { AArg owned by the caller }
      SubAddrWrap.Free();
    end;
  end
  else
    raise ENativeCodeGenError.Create(
      'native backend: var/out argument must be a variable or field');
end;

procedure TX86_64Backend.EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
var
  ClassRT: TRecordTypeDesc;
  IntfDesc: TInterfaceTypeDesc;
  ItabSym: string;
begin
  if (APar <> nil) and APar.IsVarParam then
  begin
    Self.EmitVarArgAddrToRax(AArg);
    Self.Emit(#9'pushq %rax');
  end
  else if (APar <> nil) and (APar.ResolvedType <> nil) and
          (APar.ResolvedType.Kind = tyInterface) then
  begin
    { Interface param: push obj first (lower register slot), then itab (higher
      register slot).  The pop loop runs high-to-low, so itab (pushed last) is
      popped first into the higher register, obj (pushed first) into the lower. }
    IntfDesc := TInterfaceTypeDesc(APar.ResolvedType);
    if AArg.ResolvedType.Kind = tyClass then
    begin
      { Class expression → interface: emit obj, look up static itab. }
      ClassRT := TRecordTypeDesc(AArg.ResolvedType);
      ItabSym := 'itab_' + Self.ClassSymName(ClassRT.Name) + '_' + Self.IntfTypeInfoName(IntfDesc.Name);
      Self.EmitExprToEax(AArg);          { obj -> %rax }
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'pushq %rax');         { push itab }
    end
    else if AArg is TAsExpr then
    begin
      { T as IFoo: runtime itab lookup. }
      Self.EmitExprToEax(TAsExpr(AArg).Obj);
      Self.Emit(#9'pushq %rax');         { save obj for push below }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [Self.IntfTypeInfoName(TAsExpr(AArg).TypeName)]));
      Self.Emit(#9'callq _GetItab');
      Self.Emit(#9'pushq %rax');         { itab on top; obj below }
      { Stack top: itab, below: obj — but we need obj first (lower slot).
        Swap: pop itab into %rcx, leave obj on stack, push itab back. }
      Self.Emit(#9'popq %rcx');          { rcx = itab }
      { %rax is still obj (was saved before callq). Re-load from stack: }
      Self.Emit(#9'movq (%rsp), %rax'); { rax = obj (already on stack) }
      { Stack already has obj; push itab on top. }
      Self.Emit(#9'pushq %rcx');         { itab on top, obj below ✓ }
    end
    else if (AArg is TIdentExpr) and
            TIdentExpr(AArg).IsImplicitSelf and
            (TIdentExpr(AArg).ImplicitFieldInfo <> nil) then
    begin
      { Implicit Self.field of interface type: load from object layout. }
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax',
          [TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset]));
      Self.Emit(#9'movq (%rax), %rcx');  { obj }
      Self.Emit(#9'movq 8(%rax), %rdx'); { itab }
      Self.Emit(#9'pushq %rcx');         { push obj }
      Self.Emit(#9'pushq %rdx');         { push itab }
    end
    else if AArg is TFieldAccessExpr then
    begin
      Self.EmitInterfaceFieldAddr(TFieldAccessExpr(AArg), '%rax');
      Self.Emit(#9'movq (%rax), %rcx');
      Self.Emit(#9'movq 8(%rax), %rdx');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'pushq %rdx');
    end
    else if AArg is TIdentExpr then
    begin
      { Interface variable: load both halves. }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfObjOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.IntfItabOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(#9'pushq %rcx');         { push itab }
    end
    else if ((AArg is TFuncCallExpr) or (AArg is TMethodCallExpr)) and
            (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyInterface) then
    begin
      { Interface-returning call result passed positionally, e.g.
        Show(MakeFoo(42)).  EmitIntfSretCall leaves the owned (+1) fat pointer
        at (%rsp): obj at 0, itab at 8.  Load both halves and push in the
        arg-slot order (obj first, itab on top), then drop the sret buffer.
        The pushed obj keeps the +1 ref; the callee borrows it for the call. }
      if AArg is TFuncCallExpr then
        Self.EmitIntfSretCall(TFuncCallExpr(AArg))
      else
        Self.EmitIntfSretMethodCall(TMethodCallExpr(AArg));
      Self.Emit(#9'movq (%rsp), %rax');   { obj }
      Self.Emit(#9'movq 8(%rsp), %rcx');  { itab }
      Self.Emit(#9'addq $16, %rsp');      { drop the sret buffer }
      Self.Emit(#9'pushq %rax');          { push obj }
      Self.Emit(#9'pushq %rcx');          { push itab }
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface argument expression');
  end
  else if (APar <> nil) and APar.IsOpenArray then
  begin
    if AArg is TArrayLiteralExpr then
      { An open-array literal emitted here would subq its element block in the
        middle of the slot-push sequence and break the caller's popq order.
        Call sites must hoist literals via HoistOALitArgs and push them with
        EmitArgPush. }
      raise ENativeCodeGenError.Create(
        'native backend: open-array literal argument reached EmitMethodArgPush'
        + ' — call site must hoist it via HoistOALitArgs')
    else if (AArg is TIdentExpr) and
            (TIdentExpr(AArg).ResolvedType <> nil) and
            (TIdentExpr(AArg).ResolvedType.Kind = tyStaticArray) then
    begin
      if Self.IsLocal(TIdentExpr(AArg).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax',
          [Self.VarOperand(TIdentExpr(AArg).Name)]))
      else if TIdentExpr(AArg).ConstArraySymbol <> '' then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [NativeMangle(TIdentExpr(AArg).ConstArraySymbol)]))
      else
        Self.EmitLeaqGlobal(TIdentExpr(AArg).Name, '%rax');
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'pushq $%d',
        [TStaticArrayTypeDesc(TIdentExpr(AArg).ResolvedType).HighBound -
         TStaticArrayTypeDesc(TIdentExpr(AArg).ResolvedType).LowBound]));
    end
    else if (AArg.ResolvedType <> nil) and
            (AArg.ResolvedType.Kind = tyDynArray) then
    begin
      { Dynamic array coerced to open-array: push data ptr + (length - 1). }
      Self.EmitExprToEax(AArg);          { data ptr -> %rax }
      Self.Emit(#9'pushq %rax');         { push ptr }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _DynArrayLength');
      Self.Emit(#9'movslq %eax, %rax');
      Self.Emit(#9'decq %rax');          { high = length - 1 }
      Self.Emit(#9'pushq %rax');         { push high }
    end
    else
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name + '_high')]));
      Self.Emit(#9'pushq %rax');
    end;
  end
  else if (APar <> nil) and IsFloatFamily(APar.ResolvedType) then
  begin
    { Float scalar argument: materialise to %xmm0 (handles literals via the
      .LF constant path, variables, expressions), adjust to the param's width,
      and push its 8-byte bit pattern onto the stack as one slot.  The pop loop
      (EmitPopMethodArgsToRegs) routes this slot into an xmm argument register
      per the SysV ABI instead of an integer register. }
    Self.EmitExprToXmm0(AArg);
    Self.EmitXmm0WidthAdjust(AArg.ResolvedType,
      APar.ResolvedType.Kind = tySingle);
    Self.Emit(#9'subq $8, %rsp');
    Self.Emit(#9'movsd %xmm0, 0(%rsp)');
  end
  else
  begin
    Self.EmitExprToEax(AArg);
    Self.Emit(#9'pushq %rax');
  end;
end;

{ Count total integer register slots consumed by a parameter list.
  Most params = 1 slot; interface params = 2 (obj + itab); open-array = 2.
  Used by pop loops so they iterate over slots, not logical arg positions. }
function TX86_64Backend.SysVArg64(AIndex: Integer): string;
{ Bounds-checked accessor for the 6 System V integer argument registers.  An
  index > 5 means a call-emission slot loop tried to use more than the 6
  available integer registers (args + sret/Self offset overflowed) — a latent
  codegen bug that previously read past SysVArgRegs64[0..5] and returned an
  adjacent data-section value (garbage pointer -> _StringConcat crash).  Raise
  loudly so the offending call path is named instead of silently miscompiling. }
begin
  if (AIndex < 0) or (AIndex > 5) then
    raise ENativeCodeGenError.Create(Format(
      'native backend: System V integer arg register index %d out of range ' +
      '[0..5] — a call has more register-passed slots than the ABI allows ' +
      '(sret/Self offset + args); this path must spill to the stack', [AIndex]));
  Result := SysVArgRegs64[AIndex];
end;

{ Load the receiver object pointer of a class method call into %rax.  Covers an
  expression receiver, a named local/global instance, and implicit Self.  Used by
  the TObject builtins (InheritsFrom, ToString) which only need the instance
  pointer, not the record/var-param address handling of the full call path. }
procedure TX86_64Backend.EmitMethodReceiverToRax(ACall: TMethodCallExpr);
begin
  if ACall.ObjExpr <> nil then
    Self.EmitExprToEax(ACall.ObjExpr)
  else if ACall.ObjectName <> '' then
  begin
    if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%rax', [ACall.ObjectName]));
  end
  else
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
end;

function TX86_64Backend.CountArgSlots(AParams: TObjectList): Integer;
var
  I: Integer;
  P: TMethodParam;
begin
  Result := 0;
  if AParams = nil then Exit;
  for I := 0 to AParams.Count - 1 do
  begin
    P := TMethodParam(AParams.Items[I]);
    if P.IsOpenArray then
      Inc(Result, 2)
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      Inc(Result, 2)
    else
      Inc(Result);
  end;
end;

{ Consume ASlots argument slots already pushed onto the stack (slot 0 pushed
  first, so slot 0 is at the highest address and slot ASlots-1 is on top) into
  the System V integer argument registers starting at register index ABase
  (ABase = 1 when only %rdi is pre-reserved for the sret buffer, ABase = 2 when
  %rdi=sret buffer and %rsi=receiver/Self are both pre-reserved).

  The first (6 - ABase) slots map to the remaining integer registers; any
  further slots overflow onto the stack per the System V ABI.

  Stack geometry (offsets from %rsp on entry, all in bytes):
    slot i lives at (ASlots-1-i)*8.  So the RegSlots register-mapped slots
    (i = 0..RegSlots-1) occupy the HIGH offsets and the overflow slots
    (i = RegSlots..ASlots-1) occupy the LOW offsets — but in reverse order
    (slot ASlots-1 at offset 0).  System V wants the lowest-indexed overflow
    slot at the lowest address at call time.

  Strategy: load the register slots with `movq` (not pop).  Then relocate the
  overflow slots into the HIGH part of the region (just below the sret buffer)
  in ascending index order, and raise %rsp past the vacated register-slot
  space so the overflow ends up at 0(%rsp).., slot RegSlots first.  The
  relocation runs highest-target-first so a target never overwrites an
  as-yet-unmoved source.

  Returns the number of stack bytes occupied by overflow arguments at call time;
  the caller must `addq` this back after the call (before any sret-buffer slide).
  For ASlots <= (6 - ABase) the result is 0 and the stack is fully consumed. }
function TX86_64Backend.EmitSretRegArgs(ASlots, ABase: Integer): Integer;
var
  RegSlots, OverflowSlots, K, SrcOff, DstOff: Integer;
begin
  RegSlots := 6 - ABase;
  if RegSlots < 0 then RegSlots := 0;
  if ASlots <= RegSlots then
  begin
    { Fast path: everything fits in registers — pop top-down as before. }
    for K := ASlots - 1 downto 0 do
      Self.Emit(#9'popq ' + Self.SysVArg64(K + ABase));
    Result := 0;
    Exit;
  end;
  OverflowSlots := ASlots - RegSlots;
  { Load the register-mapped slots (slots 0 .. RegSlots-1). }
  for K := 0 to RegSlots - 1 do
    Self.Emit(Format(#9'movq %d(%%rsp), %s',
      [(ASlots - 1 - K) * 8, Self.SysVArg64(K + ABase)]));
  { Relocate overflow slot (RegSlots + K) from its source offset to its final
    offset (RegSlots + K)*8.  Highest target first so live low-offset sources
    are not clobbered. }
  for K := OverflowSlots - 1 downto 0 do
  begin
    SrcOff := (ASlots - 1 - (RegSlots + K)) * 8;
    DstOff := (RegSlots + K) * 8;
    if SrcOff <> DstOff then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [SrcOff]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [DstOff]));
    end;
  end;
  { Raise %rsp past the vacated register-slot space; overflow now sits at
    0(%rsp).. with slot RegSlots first. }
  if RegSlots > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [RegSlots * 8]));
  Result := OverflowSlots * 8;
end;

procedure TX86_64Backend.EmitSelfDispatch(AMD: TMethodDecl;
  const AStaticSym: string);
begin
  Self.EmitSelfDispatchVia(AMD, AStaticSym, '%rdi');
end;

procedure TX86_64Backend.EmitSelfDispatchVia(AMD: TMethodDecl;
  const AStaticSym, ASelfReg: string);
begin
  if (AMD <> nil) and (AMD.VTableSlot >= 0) then
  begin
    Self.Emit(Format(#9'movq (%s), %%rax', [ASelfReg]));
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(AMD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + AStaticSym);
end;

procedure TX86_64Backend.BuildArgSlotClasses(AParams, AArgs: TObjectList;
  AList: TList<Integer>);
var
  I, NParams: Integer;
  P: TMethodParam;
  PT: TTypeDesc;
begin
  { Determine the param backing each logical arg.  AParams may be nil (no
    declared params): then every arg is a plain integer slot. }
  NParams := 0;
  if AParams <> nil then NParams := AParams.Count;

  for I := 0 to AArgs.Count - 1 do
  begin
    P := nil;
    if I < NParams then P := TMethodParam(AParams.Items[I]);
    PT := nil;
    if P <> nil then PT := P.ResolvedType;
    if (PT = nil) and (TASTExpr(AArgs.Items[I]).ResolvedType <> nil) then
      PT := TASTExpr(AArgs.Items[I]).ResolvedType;
    if (P <> nil) and P.IsOpenArray then
    begin
      AList.Add(0);  AList.Add(0);   { ptr + high }
    end
    else if (PT <> nil) and (PT.Kind = tyInterface) and
            ((P = nil) or not P.IsVarParam) then
    begin
      AList.Add(0);  AList.Add(0);   { obj + itab }
    end
    else if IsFloatFamily(PT) and ((P = nil) or
            (not P.IsVarParam and not P.IsOpenArray)) then
      AList.Add(1)                   { float scalar -> xmm }
    else
      AList.Add(0);                  { integer/ptr scalar }
  end;
end;

procedure TX86_64Backend.EmitPopMethodArgsToRegs(AParams, AArgs: TObjectList;
  AIntBase: Integer);
var
  I, IntIdx, XmmIdx: Integer;
  IsFloatSlot: TList<Integer>;  { 1 = float (xmm) slot, 0 = integer slot,
                                  in stack-slot order (slot 0 pushed first) }
  Dest: TStringList;            { target register per slot, parallel to above }
  Slots: Integer;
begin
  IsFloatSlot := TList<Integer>.Create();
  Dest := TStringList.Create();
  try
    { Forward pass: one entry per stack slot, in push order (slot 0 first). }
    Self.BuildArgSlotClasses(AParams, AArgs, IsFloatSlot);

    { Assign a register to each slot in forward order: integers consume the
      SysV integer registers from AIntBase, floats consume xmm0.. — the two
      sequences advance independently, per SysV. }
    IntIdx := AIntBase;
    XmmIdx := 0;
    for I := 0 to IsFloatSlot.Count - 1 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        Dest.Add(SysVXmmArgRegs[XmmIdx]);
        Inc(XmmIdx);
      end
      else
      begin
        Dest.Add(Self.SysVArg64(IntIdx));
        Inc(IntIdx);
      end;
    end;

    { Reverse pass: the top of the stack is the LAST slot.  Pop from the last
      slot down to slot 0, moving each into its precomputed register.  Every
      slot is 8 bytes and consumed in turn, so the current slot is always at
      0(%rsp) — a float reads it then raises %rsp by 8, an integer pops it. }
    Slots := IsFloatSlot.Count;
    for I := Slots - 1 downto 0 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        Self.Emit(Format(#9'movsd 0(%%rsp), %s', [Dest.Strings[I]]));
        Self.Emit(#9'addq $8, %rsp');
      end
      else
        Self.Emit(#9'popq ' + Dest.Strings[I]);
    end;
  finally
    Dest.Free();
    IsFloatSlot.Free();
  end;
end;

function TX86_64Backend.OverflowArgIsFloat(AParams: TObjectList;
  AIndex: Integer): Boolean;
var
  P: TMethodParam;
begin
  Result := False;
  if (AParams = nil) or (AIndex >= AParams.Count) then Exit;
  P := TMethodParam(AParams.Items[AIndex]);
  Result := IsFloatFamily(P.ResolvedType) and not P.IsVarParam and
            not P.IsOpenArray;
end;

procedure TX86_64Backend.EmitArgsToSlots(AArgs, AParams: TObjectList;
  AAllocSz, AHoistTotal: Integer;
  AHoistDepths, AHoistKinds: TList<Integer>);
var
  I, Dest: Integer;
  Arg: TASTExpr;
begin
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Dest := (I + 1) * 8;
    if AHoistKinds.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [AAllocSz + AHoistTotal - AHoistDepths.Get(I)]));
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end
    else if TMethodParam(AParams.Items[I]).IsVarParam then
    begin
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end
    else if Self.OverflowArgIsFloat(AParams, I) then
    begin
      Self.EmitExprToXmm0(Arg);
      Self.EmitXmm0WidthAdjust(Arg.ResolvedType,
        TMethodParam(AParams.Items[I]).ResolvedType.Kind = tySingle);
      Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [Dest]));
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [Dest]));
    end;
  end;
end;

function TX86_64Backend.EmitMethodOverflowLoad(AParams, AArgs: TObjectList;
  AAllocSz: Integer): Integer;
var
  I, IntIdx, XmmIdx, SlotOff: Integer;
  IsFloatSlot: TList<Integer>;   { per flat slot (slot 0 = Self): 1 = xmm }
  OverflowOffs: TList<Integer>;  { source offsets of integer-overflow slots }
  RK, RSrc, RDst, OverflowBytes: Integer;
begin
  IsFloatSlot := TList<Integer>.Create();
  OverflowOffs := TList<Integer>.Create();
  try
    { Slot 0 = Self/receiver — always integer.  The per-arg slots follow. }
    IsFloatSlot.Add(0);
    Self.BuildArgSlotClasses(AParams, AArgs, IsFloatSlot);

    { Load register-bound slots; record integer-overflow slot offsets.  Self is
      integer register 0 (%rdi); arg integers continue from index 1. }
    IntIdx := 0;
    XmmIdx := 0;
    SlotOff := 0;
    for I := 0 to IsFloatSlot.Count - 1 do
    begin
      if IsFloatSlot.Get(I) = 1 then
      begin
        if XmmIdx < 8 then
          Self.Emit(Format(#9'movsd %d(%%rsp), %s',
            [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        if IntIdx < 6 then
          Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]))
        else
          OverflowOffs.Add(SlotOff);
        Inc(IntIdx);
      end;
      Inc(SlotOff, 8);
    end;

    if OverflowOffs.Count = 0 then
    begin
      Self.Emit(Format(#9'addq $%d, %%rsp', [AAllocSz]));
      Result := 0;
      Exit;
    end;

    { Relocate overflow to the top of the allocation (16-aligned region) so the
      call sees a 16-aligned %rsp with the lowest-indexed overflow arg first. }
    OverflowBytes := ((OverflowOffs.Count * 8 + 15) and (-16));
    for RK := OverflowOffs.Count - 1 downto 0 do
    begin
      RSrc := OverflowOffs.Get(RK);
      RDst := (AAllocSz - OverflowBytes) + RK * 8;
      if RSrc <> RDst then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [RSrc]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [RDst]));
      end;
    end;
    if AAllocSz > OverflowBytes then
      Self.Emit(Format(#9'addq $%d, %%rsp', [AAllocSz - OverflowBytes]));
    Result := OverflowBytes;
  finally
    OverflowOffs.Free();
    IsFloatSlot.Free();
  end;
end;

{ Emit a TMethodCallStmt (class method call in statement position).
  Same as EmitMethodCallExpr but for statement nodes. }
procedure TX86_64Backend.EmitMethodCallStmt(ACall: TMethodCallStmt);
var
  I:        Integer;
  MD:       TMethodDecl;
  Sym:      string;
  Arg:      TASTExpr;
  UserSlots, TotalSlots, AllocSz, SlotOff, CleanUp: Integer;
  OverflowSlots, Dest: Integer;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  RT:       TRecordTypeDesc;
  IsSretDiscard: Boolean;
  SretBufSize:   Integer;
  SretRT:        TRecordTypeDesc;
  SretShim:      TMethodCallExpr;
begin
  { Metaclass-var constructor dispatch in statement position: C.Create(args)
    where C is a 'class of' variable and the result is discarded.  Only the
    expression-position path (EmitExpr) allocated the instance and dispatched
    the ctor through the vtable; without this branch the generic dispatch
    below loads the metaclass typeinfo pointer as the object and calls a
    garbage vtable slot — crashing at runtime.  (A non-metaclass ctor as a
    statement, TFoo.Create();, is rejected by the semantic pass as 'not a
    variable', so only the metaclass shape reaches here.)  The instance comes
    back from _ClassCreate at refcount 1; the result is discarded, so we
    release it once afterwards to free rather than leak it. }
  if ACall.IsConstructorCall and ACall.IsMetaclassDispatch then
  begin
    RT := TRecordTypeDesc(ACall.ResolvedClassType);
    MD := TMethodDecl(ACall.ResolvedMethod);
    Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'callq _ClassCreate');
    if MD <> nil then
    begin
      UserSlots  := Self.CountArgSlots(MD.Params);
      TotalSlots := UserSlots + 1;
      Sym := MethodEmitNameNative(MD, RT.Name, ACall.Name);
      if TotalSlots <= 6 then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.BeginCallArgs(MD.Params, ACall.Args);
        for I := 0 to ACall.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(ACall.Args.Items[I]), I);
        Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
        Self.Emit(#9'movq %rbx, %rdi');
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EndCallArgs();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        HD := TList<Integer>.Create();
        HK := TList<Integer>.Create();
        HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
        OverflowSlots := TotalSlots - 6;
        AllocSz := ((TotalSlots * 8 + 15) and (-16));
        Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
        Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);
        Self.Emit(Format(#9'movq %%rbx, 0(%%rsp)', []));
        CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
        if MD.VTableSlot >= 0 then
        begin
          Self.Emit(#9'movq (%rdi), %rax');
          Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
          Self.Emit(#9'callq *%rax');
        end
        else
          Self.Emit(#9'callq ' + Sym);
        Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
        HD.Free();
        HK.Free();
        Self.Emit(#9'movq %rbx, %rax');
        Self.Emit(#9'popq %rbx');
      end;
    end;
    { Discarded result: free the rc=1 instance. }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassRelease');
    Exit;
  end;

  { Discarded interface (itab) method call returning a RECORD: the callee
    follows the record-return ABI (sret pointer for a memory-class record,
    register return for a register-class one).  The plain EmitInterfaceCall
    path below treats the return as a scalar / fat pointer and hands the callee
    no sret buffer, so an sret record is written over caller memory.  Allocate
    a zeroed throwaway buffer, dispatch into it, then release its managed
    fields.  Mirrors the QBE EmitMethodCall record-discard branch. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) and
     (ACall.ResolvedReturnTypeDesc <> nil) and
     (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) then
  begin
    SretRT := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
    SretBufSize := (SretRT.TotalSize() + 15) and (-16);
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'movq %rsp, %rbx');
    { Zero the buffer so EmitRecordFieldReleases sees nil managed fields if the
      callee leaves any unset. }
    Self.Emit(#9'movq %rbx, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [SretRT.TotalSize()]));
    Self.Emit(#9'callq memset');
    { EmitIntfRecordSretDispatch takes the expression form; build a transient
      TMethodCallExpr view of this statement node (the relevant fields are the
      same).  Args are borrowed and detached before Free. }
    SretShim := TMethodCallExpr.Create();
    try
      SretShim.ObjectName       := ACall.ObjectName;
      SretShim.Name             := ACall.Name;
      SretShim.Args             := ACall.Args;
      SretShim.ObjExpr          := ACall.ObjExpr;
      SretShim.ResolvedClassType := ACall.ResolvedClassType;
      SretShim.ResolvedType     := ACall.ResolvedReturnTypeDesc;
      SretShim.IsGlobal         := ACall.IsGlobal;
      SretShim.IsVarParam       := ACall.IsVarParam;
      Self.EmitIntfRecordSretDispatch(SretShim, '(%rbx)', False);
    finally
      SretShim.Args    := nil;   { borrowed — do not free }
      SretShim.ObjExpr := nil;   { borrowed — do not free }
      SretShim.Free();
    end;
    { The dispatch may clobber %rbx during arg evaluation; %rsp is balanced and
      still points at the buffer, so re-derive the buffer address. }
    Self.Emit(#9'movq %rsp, %rbx');
    Self.EmitRecordFieldReleases(SretRT, '%rbx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'popq %rbx');
    Exit;
  end;

  { Interface method dispatch (statement position): route through the itab.
    Pass ObjExpr so receivers that are interface-typed fields (H.S.Note())
    load obj/itab from the field's fat pointer instead of bogus _obj/_itab
    operands built from an empty ObjectName. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
      Self.EmitInterfaceFieldCall(ACall.ImplicitBaseInfo,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
        (ACall.ResolvedReturnTypeDesc <> nil) and
        (ACall.ResolvedReturnTypeDesc.Kind = tyInterface))
    else
      Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args,
        ACall.ObjExpr,
        (ACall.ResolvedReturnTypeDesc <> nil) and
        (ACall.ResolvedReturnTypeDesc.Kind = tyInterface));
    Exit;
  end;

  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    if ACall.IsImplicitSelf then
    begin
      Self.Emit(#9'movq ' + Self.VarOperand('Self') + ', %rax');
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'leaq %d(%%rax), %%rax', [ACall.ImplicitBaseInfo.Offset]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%rax), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq $0, (%rax)');
    end
    else if ACall.ObjExpr <> nil then
    begin
      if (ACall.ObjExpr is TFieldAccessExpr) or (ACall.ObjExpr is TIdentExpr) then
      begin
        { L-value receiver (Def.ClassDef.Free()): release AND nil the slot.
          A stale pointer left here aliases the next allocation of the same
          size class, and the following ARC field store double-releases it —
          the QBE lowering nils the slot, so must we. }
        Self.EmitLValueSlotAddr(ACall.ObjExpr);
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'movq $0, (%rdx)');
      end
      else
      begin
        Self.EmitExprToEax(ACall.ObjExpr);
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassRelease');
      end;
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq (%rax), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq $0, (%rax)');
    end
    else
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [ACall.ObjectName]));
      Self.Emit(#9'callq _ClassRelease');
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq $0, %s(%%rip)', [ACall.ObjectName]));
    end;
    Exit;
  end;

  { Procedural-typed field call as a statement: Self.FFn(args).  Dispatch
    through the (Code, Data) pair stored in the field; no result is wanted. }
  if ACall.IsProcFieldCall then
  begin
    Self.EmitProcFieldCall(ACall.ObjExpr, ACall.ObjectName, ACall.IsVarParam,
      ACall.ProcFieldInfo, TProceduralTypeDesc(ACall.ResolvedProcType),
      ACall.Args, nil);
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallStmt has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method call in statement position (TypeName.StaticMethod(args), result
    discarded): NO implicit Self.  A void/scalar-returning static method is a
    plain function call (EmitCall marshals args into %rdi.., result ignored).  A
    record-returning static factory whose result is discarded needs a throwaway
    sret buffer, dispatched via EmitSretCall, with its managed fields released. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    if (ACall.ResolvedReturnTypeDesc <> nil) and
       (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) then
    begin
      SretRT      := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
      SretBufSize := (SretRT.TotalSize() + 15) and (-16);
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'movq %rsp, %rbx');
      Self.EmitSretCall(Sym, MD, ACall.Args, '(%rbx)', False);
      { EmitSretCall may have clobbered %rbx during arg evaluation; %rsp still
        points at the buffer, so re-derive its address before releasing. }
      Self.Emit(#9'movq %rsp, %rbx');
      if not Self.IsRecordManagedClean(SretRT) then
        Self.EmitRecordFieldReleases(SretRT, '%rbx');
      Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'popq %rbx');
    end
    else
      Self.EmitCall(Sym, MD, ACall.Args);
    Exit;
  end;

  IsSretDiscard := (ACall.ResolvedReturnTypeDesc <> nil) and
    (ACall.ResolvedReturnTypeDesc.Kind = tyRecord) and
    (ClassifyRecordReturn(TRecordTypeDesc(ACall.ResolvedReturnTypeDesc)) = rcSret);
  SretBufSize := 0;
  SretRT      := nil;
  if IsSretDiscard then
  begin
    SretRT      := TRecordTypeDesc(ACall.ResolvedReturnTypeDesc);
    SretBufSize := (SretRT.TotalSize() + 15) and (-16);
  end;

  UserSlots  := Self.CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;

  if TotalSlots <= 6 then
  begin
    { ≤6 total slots: push/pop strategy (Self in %rdi, args in %rsi..%r9).
      When IsSretDiscard is set, %rdi holds the throwaway buffer and Self
      shifts to %rsi, so user args start at %rdx (IntBase = 2). }
    if IsSretDiscard then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'subq $%d, %%rsp', [SretBufSize]));
      Self.Emit(#9'movq %rsp, %rbx');
      Self.Emit(#9'movq %rbx, %rdi');
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(Format(#9'movq $%d, %%rdx', [SretRT.TotalSize()]));
      Self.Emit(#9'callq memset');
    end;

    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%r10', [ACall.ImplicitBaseInfo.Offset]));
      if ACall.ImplicitBaseInfo.TypeDesc.Kind <> tyRecord then
        Self.Emit(#9'movq (%r10), %r10');
    end
    else if MD.IsRecordMethod and ACall.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else if MD.IsRecordMethod then
    begin
      if FSretFunc and SameText(ACall.ObjectName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Result')]))
      else
        Self.EmitVarAddr(ACall.ObjectName, '%r10');
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%r10), %r10');
    end
    else if ACall.ObjectName <> '' then
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%r10', [ACall.ObjectName]));
    end
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %r10');
    end
    else
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));

    if IsSretDiscard then
    begin
      Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 2);
      Self.Emit(#9'movq %r10, %rsi');
      Self.Emit(#9'movq %rbx, %rdi');
    end
    else
    begin
      Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 1);
      Self.Emit(#9'movq %r10, %rdi');
    end;
  end
  else
  begin
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    Self.EmitArgsToSlots(ACall.Args, MD.Params, AllocSz, HTotal, HD, HK);

    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax', [ACall.ImplicitBaseInfo.Offset]));
      if ACall.ImplicitBaseInfo.TypeDesc.Kind <> tyRecord then
        Self.Emit(#9'movq (%rax), %rax');
    end
    else if MD.IsRecordMethod and ACall.IsVarParam then
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
    else if MD.IsRecordMethod then
    begin
      if FSretFunc and SameText(ACall.ObjectName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Result')]))
      else
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
    end
    else if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else if ACall.ObjectName <> '' then
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [ACall.ObjectName]));
    end
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));

    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, ACall.Args, AllocSz);
  end;

  if MD.VTableSlot >= 0 then
  begin
    if IsSretDiscard then
      Self.Emit(#9'movq (%rsi), %rax')
    else
      Self.Emit(#9'movq (%rdi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Sym);

  if TotalSlots > 6 then
  begin
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end
  else
    Self.EndCallArgs();

  if IsSretDiscard then
  begin
    if not Self.IsRecordManagedClean(SretRT) then
      Self.EmitRecordFieldReleases(SretRT, '%rbx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [SretBufSize]));
    Self.Emit(#9'popq %rbx');
  end;
end;

{ Shared static-dispatch call sequence for both inherited forms.  Marshals
  Self + args and emits the direct callq to the parent method; on return the
  result (if any) is in %rax / %xmm0 per the SysV ABI.  AMD/AArgs/AName come
  from either TInheritedCallStmt or TInheritedCallExpr. }
procedure TX86_64Backend.EmitInheritedCallSeq(MD: TMethodDecl;
  AArgs: TObjectList; const AName: string);
var
  I:   Integer;
  Sym: string;
  Par: TMethodParam;
  UserSlots, TotalSlots, OverflowSlots, AllocSz, CleanUp, Dest, HTotal: Integer;
  Arg: TASTExpr;
  HD, HK: TList<Integer>;
begin
  Sym        := MethodEmitNameNative(MD, MD.OwnerTypeName, AName);
  UserSlots  := CountArgSlots(MD.Params);
  TotalSlots := UserSlots + 1;   { + Self }

  if TotalSlots <= 6 then
  begin
    { All of Self + args fit in the 6 integer arg registers: push then pop. }
    Self.BeginCallArgs(MD.Params, AArgs);
    for I := 0 to AArgs.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Self.PushCallArg(Par, TASTExpr(AArgs.Items[I]), I);
    end;
    { Self is the current method's Self slot. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    Self.EmitPopMethodArgsToRegs(MD.Params, AArgs, 1);
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
  end
  else
  begin
    { More than 6 register slots (Self + args): the surplus must spill to the
      stack.  Build the 6 register slots + overflow region in one frame, place
      Self in slot 0, evaluate each arg into its slot, load regs 0..5, drop the
      6-register prefix so the overflow sits at the callee's [rsp+0..], then
      static-dispatch to the parent.  Mirrors EmitMethodCallStmt's >6 path
      (the inherited call is always a direct callq, never vtable). }
    OverflowSlots := TotalSlots - 6;
    AllocSz := ((TotalSlots * 8 + 15) and (-16));
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', AArgs, HD, HK);
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.EmitArgsToSlots(AArgs, MD.Params, AllocSz, HTotal, HD, HK);
    { Self into slot 0 (the implicit first integer arg). }
    Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 0(%%rsp)', []));
    CleanUp := Self.EmitMethodOverflowLoad(MD.Params, AArgs, AllocSz);
    Self.Emit(#9'callq ' + Sym);
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end;
end;

procedure TX86_64Backend.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  MD: TMethodDecl;
begin
  { `inherited` on TObject (no parent body) is a no-op. }
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then Exit;

  { A record-returning parent uses the sret ABI, not a %rax value: route it
    through the sret path writing straight into the current Result slot (the
    statement form sets Result).  For an sret function that slot holds the
    buffer ADDRESS (indirect); for a register-returned record it is the buffer
    itself.  Without this the scalar store below would treat %rax as the record
    and corrupt the heap. }
  if (MD.ResolvedReturnType <> nil) and
     (MD.ResolvedReturnType.Kind = tyRecord) then
  begin
    Self.EmitInheritedRecordSret(MD, ACall.Args, ACall.Name,
      Self.VarOperand('Result'), Self.FSretFunc);
    Exit;
  end;

  Self.EmitInheritedCallSeq(MD, ACall.Args, ACall.Name);

  { A value-returning parent stores its result into the current Result slot,
    so `Result := ...` is unnecessary for `inherited F;` to set Result. }
  if (MD.ResolvedReturnType <> nil) and (MD.ResolvedReturnType.Kind <> tyVoid) then
  begin
    if IsFloatFamily(MD.ResolvedReturnType) then
      Self.EmitStoreFloat(Self.VarOperand('Result'), MD.ResolvedReturnType)
    else
      Self.EmitStoreVar(Self.VarOperand('Result'), MD.ResolvedReturnType);
  end;
end;

procedure TX86_64Backend.EmitCondBranch(AExpr: TASTExpr;
                                        const ATrueLabel, AFalseLabel: string);
var
  BE: TBinaryExpr;
  IsS: Boolean;
begin
  { Float comparison: ucomisd/ucomiss sets CF/ZF directly; use conditional
    jumps that map CF/ZF to the comparison operator.  The result is a direct
    branch without materialising a 0/1 in %rax. }
  if (AExpr is TBinaryExpr) then
  begin
    BE  := TBinaryExpr(AExpr);
    if IsFloatFamily(BE.Left.ResolvedType) or IsFloatFamily(BE.Right.ResolvedType) then
    begin
      IsS := (BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tySingle) and
             (BE.Right.ResolvedType <> nil) and (BE.Right.ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(BE.Left);
      Self.EmitXmm0WidthAdjust(BE.Left.ResolvedType, IsS);
      Self.Emit(#9'subq $8, %rsp');
      if IsS then Self.Emit(#9'movss %xmm0, (%rsp)')
      else        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(BE.Right);
      Self.EmitXmm0WidthAdjust(BE.Right.ResolvedType, IsS);
      if IsS then
      begin
        Self.Emit(#9'movss (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomiss %xmm0, %xmm1');
      end
      else
      begin
        Self.Emit(#9'movsd (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomisd %xmm0, %xmm1');
      end;
      { ucomisd %xmm0, %xmm1 computes xmm1 - xmm0 conceptually for flags.
        CF=1 means xmm1 < xmm0.  ZF=1 means equal. }
      case BE.Op of
        boEQ: begin Self.Emit(#9'je '  + ATrueLabel); end;
        boNE: begin Self.Emit(#9'jne ' + ATrueLabel); end;
        boLT: begin Self.Emit(#9'jb '  + ATrueLabel); end;  { below: CF }
        boGT: begin Self.Emit(#9'ja '  + ATrueLabel); end;  { above: ~CF & ~ZF }
        boLE: begin Self.Emit(#9'jbe ' + ATrueLabel); end;
        boGE: begin Self.Emit(#9'jae ' + ATrueLabel); end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float comparison operator');
      end;
      Self.Emit(#9'jmp ' + AFalseLabel);
      Exit;
    end;
  end;

  { Integer condition: evaluate to a 0/1 (or any nonzero=true) value in %eax. }
  Self.EmitExprToEax(AExpr);
  Self.Emit(#9'testq %rax, %rax');
  Self.Emit(#9'jne ' + ATrueLabel);
  Self.Emit(#9'jmp ' + AFalseLabel);
end;

{ ------------------------------------------------------------------ }
{ Statement lowering                                                   }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  I:        Integer;
  StartIdx: Integer;
  FdLit:    string;
  ArgExpr:  TASTExpr;
  K:        TTypeKind;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
    begin
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteNewline');
    end;
    Exit;
  end;

  StartIdx := 0;
  FdLit    := '$1';
  ArgExpr  := TASTExpr(ACall.Args.Items[0]);
  if (ArgExpr is TIdentExpr) and SameText(TIdentExpr(ArgExpr).Name, 'StdErr') then
  begin
    StartIdx := 1;
    FdLit    := '$2';
  end;

  if StartIdx >= ACall.Args.Count then
  begin
    if ANewline then
    begin
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteNewline');
    end;
    Exit;
  end;

  for I := StartIdx to ACall.Args.Count - 1 do
  begin
    ArgExpr := TASTExpr(ACall.Args.Items[I]);
    if ArgExpr.ResolvedType <> nil then
      K := ArgExpr.ResolvedType.Kind
    else
      K := tyInteger;
    if K in [tyString, tyPChar] then
    begin
      Self.EmitExprToEax(ArgExpr);
      { A string argument that OWNS its reference (a call/concat result that
        returned a fresh +1 string) is borrowed by _SysWriteStr and nothing
        else holds it — release the transient after the write, or it leaks
        once per Write/WriteLn.  Stash the pointer across the call, then
        release.  Plain variables / literals / PChars are borrowed and are
        not released. }
      if (K = tyString) and NativeExprOwnsRef(ArgExpr) then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteStr');
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'callq _StringRelease');
      end
      else
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteStr');
      end;
    end
    else if K = tyDouble then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteDouble');
    end
    else if K = tySingle then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteSingle');
    end
    else if K = tyBoolean then
    begin
      Self.EmitExprToEax(ArgExpr);
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
      Self.Emit(#9'callq _SysWriteBool');
    end
    else
    begin
      Self.EmitExprToEax(ArgExpr);
      if K = tyUInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else if K = tyInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteInt64');
      end
      else if K in [tyUInt32, tyWord] then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %esi');
        Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
        Self.Emit(#9'callq _SysWriteInt');
      end;
    end;
  end;
  if ANewline then
  begin
    Self.Emit(Format(#9'movl %s, %%edi', [FdLit]));
    Self.Emit(#9'callq _SysWriteNewline');
  end;
end;

procedure TX86_64Backend.EmitForStmt(AFor: TForStmt);
var
  VarOp, EndSlot:              string;
  LCond, LBody, LNext, LEnd:  string;
  VarType:                     TTypeDesc;
begin
  if Self.IsLocal(AFor.VarName) then
    VarType := Self.LocalType(AFor.VarName)
  else
  begin
    VarType := AFor.StartExpr.ResolvedType;
    Self.AddGlobal(AFor.VarName, VarType);
  end;
  VarOp   := Self.VarOperand(AFor.VarName);
  if (FFrame <> nil) and FFrame.ContainsKey('_for_end_' + IntToStr(FForEndNext)) then
  begin
    EndSlot := Self.VarOperand('_for_end_' + IntToStr(FForEndNext));
    Inc(FForEndNext);
  end
  else
  begin
    EndSlot := Self.NewLabel('forend');
    Self.AddGlobal(EndSlot, VarType);
    EndSlot := EndSlot + '(%rip)';
  end;
  LCond := Self.NewLabel('fcond');
  LBody := Self.NewLabel('fbody');
  LNext := Self.NewLabel('fnext');
  LEnd  := Self.NewLabel('fend');

  Self.EmitExprToEax(AFor.StartExpr);
  Self.EmitStoreVar(VarOp, VarType);
  Self.EmitExprToEax(AFor.EndExpr);
  Self.EmitStoreVar(EndSlot, VarType);

  Self.Emit(LCond + ':');
  Self.EmitLoadVar(VarOp, VarType);
  Self.Emit(#9'pushq %rax');
  Self.EmitLoadVar(EndSlot, VarType);
  Self.Emit(#9'movq %rax, %rcx');
  Self.Emit(#9'popq %rax');
  Self.Emit(#9'cmpq %rcx, %rax');
  if AFor.IsDownTo then
    Self.Emit(#9'jge ' + LBody)
  else
    Self.Emit(#9'jle ' + LBody);
  Self.Emit(#9'jmp ' + LEnd);

  Self.Emit(LBody + ':');
  FBreakLabels.Push(LEnd);
  FBreakExcDepths.Push(FExcDepth);
  FContinueLabels.Push(LNext);
  FContinueExcDepths.Push(FExcDepth);
  Self.EmitStmt(AFor.Body);
  FContinueExcDepths.Pop();
  FContinueLabels.Pop();
  FBreakExcDepths.Pop();
  FBreakLabels.Pop();

  Self.Emit(LNext + ':');
  Self.EmitLoadVar(VarOp, VarType);
  if AFor.IsDownTo then
    Self.Emit(#9'subq $1, %rax')
  else
    Self.Emit(#9'addq $1, %rax');
  Self.EmitStoreVar(VarOp, VarType);
  Self.Emit(#9'jmp ' + LCond);
  Self.Emit(LEnd + ':');
end;

{ ------------------------------------------------------------------ }
{ For-in and Case statements                                           }
{ ------------------------------------------------------------------ }

{ Assign the element value (already in %rax) to the for-in loop variable,
  with ARC handling for strings and classes. }
procedure TX86_64Backend.EmitForInAssignElem(AStmt: TForInStmt);
var
  VarOp: string;
begin
  if AStmt.VarIsGlobal then
    VarOp := AStmt.VarName + '(%rip)'
  else
    VarOp := Self.VarOperand(AStmt.VarName);
  if AStmt.ResolvedVarType.IsString() then
  begin
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _StringAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [VarOp]));
    Self.Emit(#9'callq _StringRelease');
    Self.Emit(#9'popq %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [VarOp]));
  end
  else if AStmt.ResolvedVarType.Kind = tyClass then
  begin
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [VarOp]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');
    Self.Emit(Format(#9'movq %%rax, %s', [VarOp]));
  end
  else
    Self.EmitStoreVar(VarOp, AStmt.ResolvedVarType);
end;

procedure TX86_64Backend.EmitForInStmt(AStmt: TForInStmt);
var
  LCond, LBody, LNext, LEnd: string;
  IdxOp:     string;
  SAT:       TStaticArrayTypeDesc;
  DAT:       TDynArrayTypeDesc;
  ElemSize:  Integer;
  GetEDecl, MNDecl, CurDecl: TMethodDecl;
  EnumOp, Sym: string;
  SlotOff:   Integer;
begin
  if AStmt.IsArrayIter then
  begin
    { ---- Static array iteration ----
      idx runs ArrayLow..ArrayHigh (inclusive).  Element address =
      base + (idx - ArrayLow) * ElemSize. }
    SAT      := TStaticArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize();
    IdxOp    := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    { Initialise index to ArrayLow }
    Self.Emit(Format(#9'movl $%d, %%eax', [AStmt.ArrayLow]));
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'cmpl $%d, %%eax', [AStmt.ArrayHigh]));
    Self.Emit(#9'jle ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Compute element address: base + (idx - ArrayLow) * ElemSize }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    if AStmt.ArrayLow <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax', [AStmt.ArrayLow]));
    Self.Emit(Format(#9'imulq $%d, %%rax, %%rax', [ElemSize]));
    Self.Emit(#9'addq %rcx, %rax');
    { Load element from (%rax) }
    case ElemSize of
      1: if IsUnsignedInt(SAT.ElementType) then
           Self.Emit(#9'movzbq (%rax), %rax')
         else
           Self.Emit(#9'movsbq (%rax), %rax');
      2: if IsUnsignedInt(SAT.ElementType) then
           Self.Emit(#9'movzwq (%rax), %rax')
         else
           Self.Emit(#9'movswq (%rax), %rax');
      4: Self.Emit(#9'movslq (%rax), %rax');
    else
      Self.Emit(#9'movq (%rax), %rax');
    end;
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsDynArrayIter then
  begin
    { ---- Dynamic array iteration ----
      idx runs 0.._DynArrayLength(ptr)-1.  Element address =
      data_ptr + idx * ElemSize. }
    DAT      := TDynArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := DAT.ElementType.RawSize();
    IdxOp    := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    { Get length via _DynArrayLength }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _DynArrayLength');
    Self.Emit(#9'movl %eax, %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Element address: data_ptr + idx * ElemSize }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    Self.Emit(Format(#9'imulq $%d, %%rax, %%rax', [ElemSize]));
    Self.Emit(#9'addq %rcx, %rax');
    case ElemSize of
      1: if IsUnsignedInt(DAT.ElementType) then
           Self.Emit(#9'movzbq (%rax), %rax')
         else
           Self.Emit(#9'movsbq (%rax), %rax');
      2: if IsUnsignedInt(DAT.ElementType) then
           Self.Emit(#9'movzwq (%rax), %rax')
         else
           Self.Emit(#9'movswq (%rax), %rax');
      4: Self.Emit(#9'movslq (%rax), %rax');
    else
      Self.Emit(#9'movq (%rax), %rax');
    end;
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsCodePointIter then
  begin
    { ---- String codepoint-iteration ----
      Calls _Utf8DecodeAt(strptr, byteIdx) which returns packed Int64:
        low 32 bits = codepoint, high 32 bits = byte advance (1-4).
      Advance is stored in a synthetic __adv_N slot to survive the body. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movl -8(%rax), %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'movl %s, %%esi', [IdxOp]));
    Self.Emit(#9'callq _Utf8DecodeAt');
    Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(AStmt.VarName)]));
    Self.Emit(#9'shrq $32, %rax');
    Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(AStmt.AdvVarName)]));

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'addl %s, %%eax', [Self.VarOperand(AStmt.AdvVarName)]));
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsStringIter then
  begin
    { ---- String byte-iteration ----
      String data pointer layout: [data...]
      Length at data_ptr - 8 (4-byte integer).
      idx runs 0..length-1.  Element = byte at data_ptr + idx. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    { Load string length from data_ptr - 8 }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movl -8(%rax), %ecx');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'cmpl %ecx, %eax');
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Load byte at data_ptr + idx }
    Self.EmitExprToEax(AStmt.CollExpr);
    Self.Emit(#9'movq %rax, %rcx');
    Self.Emit(Format(#9'movslq %s, %%rax', [IdxOp]));
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movzbq (%rax), %rax');
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt.IsSetIter then
  begin
    { ---- Set iteration ----
      Evaluate set expression once into mask slot.  Iterate bit positions
      0..SetBitCount-1.  For each set bit, assign the ordinal to the loop
      variable and run the body. }
    IdxOp := Self.VarOperand(AStmt.IdxVarName);
    LCond := Self.NewLabel('ficond');
    LBody := Self.NewLabel('fibody');
    LNext := Self.NewLabel('finext');
    LEnd  := Self.NewLabel('fiend');

    { Evaluate set expression once }
    Self.EmitExprToEax(AStmt.CollExpr);
    if AStmt.SetBitCount > 32 then
    begin
      Self.Emit(Format(#9'movq %%rax, %s',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
    end
    else
    begin
      Self.Emit(Format(#9'movl %%eax, %s',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
    end;
    Self.Emit(Format(#9'movl $0, %s', [IdxOp]));

    Self.Emit(LCond + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(Format(#9'cmpl $%d, %%eax', [AStmt.SetBitCount]));
    Self.Emit(#9'jl ' + LBody);
    Self.Emit(#9'jmp ' + LEnd);

    Self.Emit(LBody + ':');
    { Test bit: jumbo via _SetIn(set_addr, idx); else (mask >> idx) & 1 }
    if AStmt.SetIsJumbo then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.VarOperand(AStmt.SetMaskVarName)]));   { set bitmap addr }
      Self.Emit(Format(#9'movl %s, %%esi', [IdxOp]));
      Self.Emit(#9'callq _SetIn');
      Self.Emit(#9'testl %eax, %eax');
    end
    else if AStmt.SetBitCount > 32 then
    begin
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
      Self.Emit(Format(#9'movl %s, %%ecx', [IdxOp]));
      Self.Emit(#9'shrq %cl, %rax');
      Self.Emit(#9'andq $1, %rax');
      Self.Emit(#9'testq %rax, %rax');
    end
    else
    begin
      Self.Emit(Format(#9'movl %s, %%eax',
        [Self.VarOperand(AStmt.SetMaskVarName)]));
      Self.Emit(Format(#9'movl %s, %%ecx', [IdxOp]));
      Self.Emit(#9'shrl %cl, %eax');
      Self.Emit(#9'andl $1, %eax');
      Self.Emit(#9'testl %eax, %eax');
    end;
    Self.Emit(#9'jne ' + LBody + '_yes');
    Self.Emit(#9'jmp ' + LNext);
    Self.Emit(LBody + '_yes:');

    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LNext);
    FContinueExcDepths.Push(FExcDepth);

    { Assign ordinal (idx) to loop variable }
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.EmitForInAssignElem(AStmt);

    Self.EmitStmt(AStmt.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();

    Self.Emit(LNext + ':');
    Self.Emit(Format(#9'movl %s, %%eax', [IdxOp]));
    Self.Emit(#9'addl $1, %eax');
    Self.Emit(Format(#9'movl %%eax, %s', [IdxOp]));
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  { ---- Class enumerator protocol ----
    GetEnumerator → enumerator object (ARC'd).
    while MoveNext do LoopVar := Current. }
  LCond := Self.NewLabel('ficond');
  LBody := Self.NewLabel('fibody');
  LEnd  := Self.NewLabel('fiend');
  GetEDecl := TMethodDecl(AStmt.GetEnumDecl);
  MNDecl   := TMethodDecl(AStmt.MoveNextDecl);
  CurDecl  := TMethodDecl(AStmt.CurrentDecl);
  EnumOp   := Self.VarOperand(AStmt.EnumVarName);

  { Call GetEnumerator on the collection }
  Self.EmitExprToEax(AStmt.CollExpr);
  Self.Emit(#9'movq %rax, %rdi');
  Sym := MethodEmitNameNative(GetEDecl, GetEDecl.OwnerTypeName, GetEDecl.Name);
  if GetEDecl.VTableSlot >= 0 then
  begin
    SlotOff := (GetEDecl.VTableSlot + 1) * 8;
    Self.Emit(#9'movq (%rdi), %rcx');
    Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
    Self.Emit(#9'callq *%r10');
  end
  else
    Self.Emit(#9'callq ' + Sym);

  { Move the enumerator into the synthetic slot.  GetEnumerator's
    result is an owned +1 (constructor/call result) — transfer it;
    an extra AddRef here leaks one enumerator per loop because the
    function epilogue releases the slot exactly once. }
  Self.Emit(#9'pushq %rax');
  Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
  Self.Emit(#9'callq _ClassRelease');
  Self.Emit(#9'popq %rax');
  Self.Emit(Format(#9'movq %%rax, %s', [EnumOp]));

  { Condition: call MoveNext }
  Self.Emit(LCond + ':');
  Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
  Sym := MethodEmitNameNative(MNDecl, MNDecl.OwnerTypeName, MNDecl.Name);
  if MNDecl.VTableSlot >= 0 then
  begin
    SlotOff := (MNDecl.VTableSlot + 1) * 8;
    Self.Emit(#9'movq (%rdi), %rcx');
    Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
    Self.Emit(#9'callq *%r10');
  end
  else
    Self.Emit(#9'callq ' + Sym);
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jne ' + LBody);
  Self.Emit(#9'jmp ' + LEnd);

  { Body: read Current, assign to loop var }
  Self.Emit(LBody + ':');
  FBreakLabels.Push(LEnd);
  FBreakExcDepths.Push(FExcDepth);
  FContinueLabels.Push(LCond);
  FContinueExcDepths.Push(FExcDepth);

  Self.Emit(Format(#9'movq %s, %%rdi', [EnumOp]));
  Sym := MethodEmitNameNative(CurDecl, CurDecl.OwnerTypeName, CurDecl.Name);
  if CurDecl.VTableSlot >= 0 then
  begin
    SlotOff := (CurDecl.VTableSlot + 1) * 8;
    Self.Emit(#9'movq (%rdi), %rcx');
    Self.Emit(Format(#9'movq %d(%%rcx), %%r10', [SlotOff]));
    Self.Emit(#9'callq *%r10');
  end
  else
    Self.Emit(#9'callq ' + Sym);
  Self.EmitForInAssignElem(AStmt);

  Self.EmitStmt(AStmt.Body);
  FContinueExcDepths.Pop();
  FContinueLabels.Pop();
  FBreakExcDepths.Pop();
  FBreakLabels.Pop();

  Self.Emit(#9'jmp ' + LCond);
  Self.Emit(LEnd + ':');
end;

procedure TX86_64Backend.EmitCaseStmt(AStmt: TCaseStmt);
var
  EndLbl, ElseLbl, BranchLbl, NextLbl: string;
  Branch:       TCaseBranch;
  I, J:         Integer;
  BranchLabels: TStringList;
begin
  { Evaluate selector once, keep in %rax, save to %r10 (caller-saved scratch). }
  Self.EmitExprToEax(AStmt.Selector);
  Self.Emit(#9'movq %rax, %r10');

  EndLbl  := Self.NewLabel('csend');
  ElseLbl := Self.NewLabel('cselse');

  BranchLabels := TStringList.Create();
  for I := 0 to AStmt.Branches.Count - 1 do
    BranchLabels.Add(Self.NewLabel('csbr'));

  { Dispatch block: linear chain of comparisons.  For each branch, test all
    its values; on any match, jump to that branch body.  On no match for
    any branch, fall through to the else block. }
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch    := TCaseBranch(AStmt.Branches.Items[I]);
    BranchLbl := BranchLabels.Strings[I];
    for J := 0 to Branch.Values.Count - 1 do
    begin
      NextLbl := Self.NewLabel('csnxt');
      if TASTExpr(Branch.Values.Items[J]) is TSetRangeExpr then
      begin
        { Range label lo..hi: match when (sel >= lo) and (sel <= hi).  Signed
          ordinal comparison; selector stays in %r10 across both bound evals. }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TSetRangeExpr(Branch.Values.Items[J]).LowExpr);
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'jl ' + NextLbl);        { sel < lo -> no match }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TSetRangeExpr(Branch.Values.Items[J]).HighExpr);
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'jg ' + NextLbl);        { sel > hi -> no match }
        Self.Emit(#9'jmp ' + BranchLbl);
      end
      else if AStmt.IsStringCase then
      begin
        { String comparison: call _StringEquals(selector, value) }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TASTExpr(Branch.Values.Items[J]));
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'movq %r10, %rdi');
        Self.Emit(#9'pushq %r10');
        Self.Emit(#9'callq _StringEquals');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'testl %eax, %eax');
        Self.Emit(#9'jne ' + BranchLbl);
        Self.Emit(#9'jmp ' + NextLbl);
      end
      else
      begin
        { Integer/enum comparison }
        Self.Emit(#9'pushq %r10');
        Self.EmitExprToEax(TASTExpr(Branch.Values.Items[J]));
        Self.Emit(#9'movl %eax, %ecx');
        Self.Emit(#9'popq %r10');
        Self.Emit(#9'cmpl %ecx, %r10d');
        Self.Emit(#9'je ' + BranchLbl);
        Self.Emit(#9'jmp ' + NextLbl);
      end;
      Self.Emit(NextLbl + ':');
    end;
  end;
  Self.Emit(#9'jmp ' + ElseLbl);

  { Branch bodies }
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch    := TCaseBranch(AStmt.Branches.Items[I]);
    BranchLbl := BranchLabels.Strings[I];
    Self.Emit(BranchLbl + ':');
    Self.EmitStmt(Branch.Stmt);
    Self.Emit(#9'jmp ' + EndLbl);
  end;

  { Else block }
  Self.Emit(ElseLbl + ':');
  if AStmt.ElseStmt <> nil then
    Self.EmitStmt(AStmt.ElseStmt);
  Self.Emit(#9'jmp ' + EndLbl);

  Self.Emit(EndLbl + ':');
  BranchLabels.Free();
end;

{ ------------------------------------------------------------------ }
{ Exception handling                                                   }
{ ------------------------------------------------------------------ }

function TX86_64Backend.CountTryStmts(AStmt: TASTStmt): Integer;
var
  I:    Integer;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  RepS: TRepeatStmt;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    Result := 1;
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := 1;
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + Self.CountTryStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + Self.CountTryStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Exit(Self.CountTryStmts(IfS.ThenStmt) + Self.CountTryStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(Self.CountTryStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(Self.CountTryStmts(ForS.Body));
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TForInStmt then
    Exit(Self.CountTryStmts(TForInStmt(AStmt).Body));
  if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      Result := Result + Self.CountTryStmts(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
    Result := Result + Self.CountTryStmts(TCaseStmt(AStmt).ElseStmt);
    Exit;
  end;
end;

function TX86_64Backend.CountForStmts(AStmt: TASTStmt): Integer;
var
  I:    Integer;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  RepS: TRepeatStmt;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + Self.CountForStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + Self.CountForStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Exit(Self.CountForStmts(IfS.ThenStmt) + Self.CountForStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(Self.CountForStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(1 + Self.CountForStmts(ForS.Body));
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + Self.CountForStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TForInStmt then
    Exit(Self.CountForStmts(TForInStmt(AStmt).Body));
  if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      Result := Result + Self.CountForStmts(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt);
    Result := Result + Self.CountForStmts(TCaseStmt(AStmt).ElseStmt);
    Exit;
  end;
end;

{ Unwind exception frames from FExcDepth down to ATargetDepth+1.
  For each frame: pop it; if it is a try/finally frame, also emit the
  finally body inline.  try/except frames have a nil FFinallyStack entry. }
procedure TX86_64Backend.EmitExcUnwind(ATargetDepth: Integer);
var
  I, J:    Integer;
  FinBody: TCompoundStmt;
begin
  for I := FExcDepth downto ATargetDepth + 1 do
  begin
    Self.Emit(#9'callq _PopExcFrame');
    if I - 1 < FFinallyStack.Count then
    begin
      FinBody := FFinallyStack.Get(I - 1);
      if FinBody <> nil then
        Self.EmitStmtList(FinBody.Stmts);
    end;
  end;
end;

procedure TX86_64Backend.EmitTryFramePrologue(AFinallyBody: TCompoundStmt;
  const ALblExc, ALblTry: string);
var
  FrameSlot: string;
begin
  { Use the next pre-allocated 512-byte frame slot from BuildFrame. }
  FrameSlot := '_exc_frame_' + IntToStr(FExcFrameNext);
  Inc(FExcFrameNext);

  { _PushExcFrame wants the frame base address in %rdi. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _PushExcFrame');
  Inc(FExcDepth);
  FFinallyStack.Add(AFinallyBody);

  { _blaise_setjmp(frame): returns 0 on normal entry, 1 on exception longjmp. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _blaise_setjmp');
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jnz ' + ALblExc);
  Self.Emit(#9'jmp ' + ALblTry);
end;

procedure TX86_64Backend.EmitPopExcFrame;
begin
  Self.Emit(#9'callq _PopExcFrame');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
end;

procedure TX86_64Backend.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
begin
  LblTry    := Self.NewLabel('try_body');
  LblFinExc := Self.NewLabel('fin_exc');
  LblEnd    := Self.NewLabel('fin_end');

  Self.EmitTryFramePrologue(AStmt.FinallyBody, LblFinExc, LblTry);

  { Normal path: run try body, pop frame, run finally, done. }
  Self.Emit(LblTry + ':');
  Self.EmitStmtList(AStmt.TryBody.Stmts);
  Self.EmitPopExcFrame();
  Self.EmitStmtList(AStmt.FinallyBody.Stmts);
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: capture exception, pop frame, run finally, re-raise.
    Restore FExcDepth to the try-entry level so the exception-path codegen
    sees the same depth as the normal path (both paths execute at codegen time
    even though only one runs at runtime). }
  Inc(FExcDepth);
  FFinallyStack.Add(AStmt.FinallyBody);
  Self.Emit(LblFinExc + ':');
  Self.Emit(#9'callq _CurrentException');
  Self.Emit(#9'pushq %rax');   { save exception pointer across finally body }
  Self.EmitPopExcFrame();
  Self.EmitStmtList(AStmt.FinallyBody.Stmts);
  Self.Emit(#9'popq %rdi');    { restore saved exception }
  Self.Emit(#9'callq _Reraise');
  Self.Emit(#9'jmp ' + LblEnd);  { unreachable; satisfies assembler block exit }

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  LblBody:   string;
  LblNext:   string;
  I:         Integer;
  H:         TExceptHandlerClause;
begin
  LblTry    := Self.NewLabel('try_body');
  LblExcept := Self.NewLabel('except_handler');
  LblEnd    := Self.NewLabel('except_end');

  { Push nil so FFinallyStack stays index-aligned with FExcDepth.
    A non-local exit crossing a try/except frame only pops it — no body to run. }
  Self.EmitTryFramePrologue(nil, LblExcept, LblTry);

  { Normal path: run try body, pop frame on clean exit. }
  Self.Emit(LblTry + ':');
  Self.EmitStmtList(AStmt.TryBody.Stmts);
  Self.EmitPopExcFrame();
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: dispatch handlers.
    Restore codegen-time FExcDepth/FFinallyStack to the try-entry level so
    the exception path sees the same bookkeeping state (both paths execute at
    codegen time even though only one runs at runtime). }
  Inc(FExcDepth);
  FFinallyStack.Add(nil);
  Self.Emit(LblExcept + ':');

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while our frame is still on the stack. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'pushq %rax');   { save exception across _PopExcFrame }
    Self.EmitPopExcFrame();
    Self.Emit(#9'popq %r15');    { exception in %r15 (callee-saved — survives handler bodies) }

    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers[I]);
      LblBody := Self.NewLabel('exc_handler_body');
      LblNext := Self.NewLabel('exc_handler_next');

      { _IsInstance(obj, typeinfo): returns non-zero if obj is an instance of the type. }
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'leaq typeinfo_' + Self.ClassSymName(H.TypeName) + '(%rip), %rsi');
      Self.Emit(#9'callq _IsInstance');
      Self.Emit(#9'testl %eax, %eax');
      Self.Emit(#9'jnz ' + LblBody);
      Self.Emit(#9'jmp ' + LblNext);

      Self.Emit(LblBody + ':');
      if H.VarName <> '' then
      begin
        { Retain the exception to balance the scope-exit release (the handler
          var is a class local; EmitFunctionDef will emit a release at epilogue
          only for string vars, but we retain here to match QBE backend ARC).
          Release any PRIOR binding first — the slot is shared by every
          same-named handler in the function.
          The handler var slot is a pre-declared local: assign %r15 into it. }
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        if Self.IsLocal(H.VarName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(H.VarName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [H.VarName]));
        Self.Emit(#9'callq _ClassRelease');
        if Self.IsLocal(H.VarName) then
          Self.Emit(Format(#9'movq %%r15, %s', [Self.VarOperand(H.VarName)]))
        else
          Self.Emit(Format(#9'movq %%r15, %s(%%rip)', [H.VarName]));
      end;
      Self.EmitStmtList(H.Body.Stmts);
      Self.Emit(#9'jmp ' + LblEnd);

      Self.Emit(LblNext + ':');
    end;

    { No handler matched: run else body if any, otherwise re-raise. }
    if AStmt.ElseBody <> nil then
    begin
      Self.EmitStmtList(AStmt.ElseBody.Stmts);
      Self.Emit(#9'jmp ' + LblEnd);
    end
    else
    begin
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'callq _Reraise');
      Self.Emit(#9'jmp ' + LblEnd);
    end;
  end
  else
  begin
    { Plain catch-all except body. }
    Self.EmitPopExcFrame();
    Self.EmitStmtList(AStmt.ExceptBody.Stmts);
    Self.Emit(#9'jmp ' + LblEnd);
  end;

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitRaiseStmt(AStmt: TRaiseStmt);
begin
  if AStmt.Expr <> nil then
  begin
    Self.EmitExprToEax(AStmt.Expr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Raise');
  end
  else
  begin
    { Bare re-raise: retrieve the current exception then re-raise it. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Reraise');
  end;
end;

procedure TX86_64Backend.EmitStmtList(AList: TObjectList);
var
  I: Integer;
begin
  if AList = nil then Exit;
  for I := 0 to AList.Count - 1 do
    Self.EmitStmt(TASTStmt(AList.Items[I]));
end;

procedure TX86_64Backend.EmitStaticElemScale(ASAT: TStaticArrayTypeDesc);
begin
  if ASAT.LowBound <> 0 then
    Self.Emit(Format(#9'subq $%d, %%rax', [ASAT.LowBound]));
  Self.Emit(Format(#9'imulq $%d, %%rax', [ASAT.ElementType.RawSize()]));
end;

procedure TX86_64Backend.EmitSretBufferSlideDown(AHoistTotal: Integer);
begin
  if AHoistTotal > 0 then
  begin
    Self.Emit(#9'movq (%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rcx');
    Self.Emit(Format(#9'addq $%d, %%rsp', [16 + AHoistTotal]));
    Self.Emit(#9'pushq %rcx');
    Self.Emit(#9'pushq %rax');
  end;
end;

procedure TX86_64Backend.EmitStmt(AStmt: TASTStmt);
var
  PC:    TProcCall;
  Comp:  TCompoundStmt;
  IfS:   TIfStmt;
  WhileS: TWhileStmt;
  RepS:  TRepeatStmt;
  Asgn:  TAssignment;
  FA:    TFieldAssignment;
  CVStore: TAssignment;
  FAE:   TFieldAccessExpr;
  SSA:   TStaticSubscriptAssign;
  MD:    TMethodDecl;
  DAElemType: TTypeDesc;
  I:     Integer;
  LThen, LElse, LEnd:    string;
  LCond, LBody:          string;
  FDynArgName: string;
  FDynElemSz:  Integer;
  ISFld:   TFieldInfo;
  IntfArgs: TObjectList;
  PCUserSlots, PCTotalSlots, PCOverflow, PCCleanUp, PCAllocSz, PCDest: Integer;
  PCHD, PCHK: TList<Integer>;
  PCHTotal: Integer;
  AliasBuf: Integer;
begin
  { An empty statement (e.g. the body of `for x := 0 to N do;`) parses to a nil
    statement — the parser's convention for "no statement here".  It is a valid,
    do-nothing body, so emit nothing.  Without this guard the unsupported-
    statement fallback at the tail dereferences AStmt.ClassName and segfaults. }
  if AStmt = nil then
    Exit;
  Self.DbgStmtLabel(AStmt);
  if AStmt is TAsmStmt then
  begin
    { Inline assembler: emit the verbatim block.  The internal/external
      assembler parses it; the front end never did. }
    Self.Emit(TAsmStmt(AStmt).Code);
    Exit;
  end;
  if AStmt is TAssignment then
  begin
    Asgn := TAssignment(AStmt);
    { Implicit-Self field assignment (bare `FName := x` inside a method) must be
      resolved as a field of Self, NOT as a variable named FName — otherwise the
      managed-type branches below would treat it as a global/local and write to
      the wrong slot.  Interface fields are excluded here: EmitInterfaceAssign
      (reached via the tyInterface branch) already handles ImplicitSelfField. }
    if (Asgn.ImplicitSelfField <> nil) and
       (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind <> tyInterface) then
    begin
      ISFld := TFieldInfo(Asgn.ImplicitSelfField);
      { ARC-managed implicit-Self field: retain the new value (unless the RHS
        already owns +1) and release the old before overwriting.  %r15
        (callee-saved) holds the slot address across the ARC calls. }
      if ISFld.IsUnretained or ISFld.IsWeak then
      begin
        { Non-owning fields keep plain/weak store semantics. }
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
        if ISFld.IsWeak then
        begin
          Self.Emit(#9'movq %rax, %rsi');
          Self.Emit(#9'movq %rcx, %rdi');
          Self.Emit(#9'callq _WeakAssign');
        end
        else
          Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Asgn.ResolvedLhsType.IsString()
           or (Asgn.ResolvedLhsType.Kind = tyClass)
           or (Asgn.ResolvedLhsType.Kind = tyDynArray) then
      begin
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %r15');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
        Self.Emit(#9'pushq %rax');
        { String/dyn-array: elide the retain when the RHS already owns +1 (a
          call result), else the buffer leaks one ref per store.  Class: the
          retain stays unconditional — some method calls return a borrowed class
          reference that NativeExprOwnsRef reports as owning, so eliding it would
          release a reference the field never acquired (a use-after-free).  This
          mirrors the deliberate asymmetry in the QBE backend (96514ee). }
        if not NativeExprOwnsRef(Asgn.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          if Asgn.ResolvedLhsType.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if Asgn.ResolvedLhsType.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(#9'movq (%r15), %rdi');     { old value }
        if Asgn.ResolvedLhsType.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if Asgn.ResolvedLhsType.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, (%r15)');
        Self.Emit(#9'popq %r15');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TMethodCallExpr) and
              (TMethodCallExpr(Asgn.Expr).ResolvedClassType <> nil) and
              (TMethodCallExpr(Asgn.Expr).ResolvedClassType.Kind = tyInterface) and
              (TMethodCallExpr(Asgn.Expr).ResolvedType <> nil) and
              (TMethodCallExpr(Asgn.Expr).ResolvedType.Kind = tyRecord) then
      begin
        { Interface (itab) record-returning dispatch into an implicit-Self
          field — EmitRecordCallSretAt routes the itab case to the record-
          return helper. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitIntfRecordSretDispatch(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TMethodCallExpr) and
              (TMethodCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
              (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
              (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind = tyRecord) and
              (Asgn.Expr is TFuncCallExpr) and
              (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
              (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
              (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rbx', [ISFld.Offset]));
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr), '(%rbx)', False);
        Self.Emit(#9'popq %rbx');
      end
      else if IsJumboSet(Asgn.ResolvedLhsType) then
      begin
        { Jumbo set into an implicit-Self field: plain bitmap memcpy (a set has
          no managed fields, so no retain/release). }
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');         { source bitmap addr }
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rdi', [ISFld.Offset]));
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
      end
      else if (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) then
      begin
        Self.EmitExprToEax(Asgn.Expr);
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'movq %rax, %rbx');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
        if ISFld.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
        Self.EmitRecordFieldRetains(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%r15');
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'popq %r15');
      end
      else
      begin
        { Non-managed implicit-Self field (integer, float, enum, etc.). }
        if IsFloatFamily(Asgn.ResolvedLhsType) then
        begin
          Self.EmitExprToXmm0(Asgn.Expr);
          { Narrow a Double/integer RHS to Single before the movss store
            (see the TFieldAssignment float path). }
          Self.EmitXmm0WidthAdjust(Asgn.Expr.ResolvedType,
            Asgn.ResolvedLhsType.Kind = tySingle);
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if ISFld.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
          Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
        end
        else
        begin
          Self.EmitExprToEax(Asgn.Expr);
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if ISFld.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [ISFld.Offset]));
          Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
        end;
      end;
      Exit;
    end;
    { Method-pointer assignment from @Obj.Method: directly store the
      [CodePtr, ObjPtr] pair into the destination's 16-byte slot. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       (TProceduralTypeDesc(Asgn.ResolvedLhsType).IsMethodPtr) and
       (Asgn.Expr is TAddrOfExpr) and
       (TAddrOfExpr(Asgn.Expr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr).ResolvedType).IsMethodPtr then
    begin
      FAE := TFieldAccessExpr(TAddrOfExpr(Asgn.Expr).Expr);
      MD  := TMethodDecl(FAE.ResolvedMethod);
      { Destination address → %rcx }
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(Asgn.Name)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [Asgn.Name]));
      { Store code pointer at offset 0 }
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
      Self.Emit(#9'movq %rax, (%rcx)');
      { Store object pointer at offset 8 }
      if FAE.Base <> nil then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
      Exit;
    end;
    { Method-pointer (of-object) assignment from a TMethod/TAddProc cast:
      P := TAddProc(M) — both sides are 16-byte Code+Data blocks.
      Emit as memcpy(dest, src, 16). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       (TProceduralTypeDesc(Asgn.ResolvedLhsType).IsMethodPtr) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl = nil) and
       (TFuncCallExpr(Asgn.Expr).Args.Count = 1) then
    begin
      { Destination address → %rdi }
      Self.EmitVarAddr(Asgn.Name, '%rdi');
      { Source address: the cast argument (a TMethod record or another method ptr). }
      if TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0]) is TIdentExpr then
      begin
        if Self.IsLocal(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name) then
          Self.Emit(Format(#9'leaq %s, %%rsi',
            [Self.VarOperand(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rsi',
            [TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name]));
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: method-ptr cast source must be a simple variable');
      Self.Emit(#9'movq $16, %rdx');
      Self.Emit(#9'callq memcpy');
      Exit;
    end;
    { sret assignment: LHS is a record (or jumbo set) variable; RHS is a
      record/jumbo-set-returning call.  Pass the destination buffer address as
      the hidden first arg (%rdi). }
    if (Asgn.ResolvedLhsType <> nil) and
       ((Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) or
        IsJumboSet(Asgn.ResolvedLhsType)) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
       (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
       ((TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) or
        IsJumboSet(TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType)) then
    begin
      { For a local jumbo set the dest is leaq'd; EmitSretCall's caller passes
        the operand and a 'by-ref' flag.  Mirror the record dispatch below. }
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitFuncCallSret(TFuncCallExpr(Asgn.Expr),
          Asgn.Name + '(%rip)', False);
      end;
      Exit;
    end;
    { sret assignment: interface (itab) method call returning a record.  The
      itab call has no ResolvedMethod, so it is classified by ResolvedClassType
      = interface + ResolvedType = record.  EmitIntfRecordSretDispatch writes
      the record straight into the destination, honouring the record-return ABI
      (hidden sret pointer for a memory-class record; register capture for a
      register-class one).  Mirrors the QBE EmitIntfSretDispatch path. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyRecord) and
       (Asgn.Expr is TMethodCallExpr) and
       (TMethodCallExpr(Asgn.Expr).ResolvedClassType <> nil) and
       (TMethodCallExpr(Asgn.Expr).ResolvedClassType.Kind = tyInterface) and
       (TMethodCallExpr(Asgn.Expr).ResolvedType <> nil) and
       (TMethodCallExpr(Asgn.Expr).ResolvedType.Kind = tyRecord) then
    begin
      { Release the destination's prior managed fields before overwriting it,
        then dispatch.  The dispatch writes the constructed record (which owns
        its managed fields +1) over the dest, so ownership transfers cleanly. }
      Self.Emit(#9'pushq %rbx');
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if Asgn.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitLeaqGlobal(Asgn.Name, '%rbx');
      end;
      Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
      Self.EmitIntfRecordSretDispatch(TMethodCallExpr(Asgn.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { sret assignment: method call returning a record (or jumbo set).
      %rdi = sret ptr, %rsi = Self, %rdx.. = user args. }
    if (Asgn.ResolvedLhsType <> nil) and
       ((Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) or
        IsJumboSet(Asgn.ResolvedLhsType)) and
       (Asgn.Expr is TMethodCallExpr) and
       (TMethodCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       ((TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) or
        IsJumboSet(TMethodDecl(TMethodCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType)) then
    begin
      { Self-assigned record method (M := M.Method(...)): the sret destination
        would alias the receiver, so the callee would clobber Self while still
        reading it.  Route the call through a fresh zeroed stack buffer (address
        held in callee-saved %r14), then move the result into the destination
        (release old fields, raw memcpy — ownership of the constructed managed
        fields transfers). }
      if (Asgn.ResolvedLhsType.Kind = tyRecord) and
         Self.RecordCallReceiverIsVar(Asgn.Expr, Asgn.Name, Asgn.IsGlobal) then
      begin
        AliasBuf := (TRecordTypeDesc(Asgn.ResolvedLhsType).TotalSize() + 15) and (-16);
        Self.Emit(#9'pushq %r14');
        Self.Emit(Format(#9'subq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'movq %rsp, %r14');
        Self.Emit(#9'movq %r14, %rdi');
        Self.Emit(#9'xorl %esi, %esi');
        Self.Emit(Format(#9'movq $%d, %%rdx',
          [TRecordTypeDesc(Asgn.ResolvedLhsType).TotalSize()]));
        Self.Emit(#9'callq memset');
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr), '(%r14)', False);
        { %r14 still holds the temp buffer address (callee-saved across the call).
          Resolve the destination address into %rbx, release its old managed
          fields, then memcpy the constructed result over it. }
        Self.Emit(#9'pushq %rbx');
        if Asgn.IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(Asgn.Name)]))
        else
          Self.EmitVarAddr(Asgn.Name, '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.Emit(#9'movq %rbx, %rdi');
        Self.Emit(#9'movq %r14, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx',
          [TRecordTypeDesc(Asgn.ResolvedLhsType).TotalSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %rbx');
        Self.Emit(Format(#9'addq $%d, %%rsp', [AliasBuf]));
        Self.Emit(#9'popq %r14');
        Exit;
      end;
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitMethodSretCall(TMethodCallExpr(Asgn.Expr),
          Asgn.Name + '(%rip)', False);
      end;
      Exit;
    end;
    { sret assignment: `<rec> := inherited M(...)` — static dispatch to the
      parent, same destination selection as the method/func branches above. }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray]) and
       (Asgn.Expr is TInheritedCallExpr) and
       (TInheritedCallExpr(Asgn.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       (TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod).ResolvedReturnType.Kind in
          [tyRecord, tyStaticArray]) then
    begin
      if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand('Result'), True)
      else if Asgn.IsVarParam then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand(Asgn.Name), True)
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Self.VarOperand(Asgn.Name), False)
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitInheritedRecordSret(
          TMethodDecl(TInheritedCallExpr(Asgn.Expr).ResolvedMethod),
          TInheritedCallExpr(Asgn.Expr).Args, TInheritedCallExpr(Asgn.Expr).Name,
          Asgn.Name + '(%rip)', False);
      end;
      Exit;
    end;
    if IsFloatFamily(Asgn.ResolvedLhsType) then
    begin
      { Float assignment: value → %xmm0, then store. }
      Self.EmitExprToXmm0(Asgn.Expr);
      { Adjust the value to the LHS width: Double/integer RHS into a Single
        LHS narrows (cvtsd2ss); a Single RHS into a Double LHS widens
        (cvtss2sd). }
      Self.EmitXmm0WidthAdjust(Asgn.Expr.ResolvedType,
        Asgn.ResolvedLhsType.Kind = tySingle);
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.EmitStoreFloat('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitStoreFloat(Self.VarOperand(Asgn.Name), Self.LocalType(Asgn.Name))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitStoreFloat(Self.VarOperand(Asgn.Name), Asgn.ResolvedLhsType);
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyString) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyDynArray) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyInterface) then
    begin
      Self.EmitInterfaceAssign(Asgn);
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyClass) and
            (Asgn.Expr is TNilLiteral) then
    begin
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq $0, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq $0, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'callq _ClassRelease');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq $0, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyClass) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      { Elide the retain when the RHS already owns +1 (a call result): a
        function/method returning a class leaves Result at +1 (the callee's
        `Result := x` AddRef'd and the epilogue did not release it), so the
        assignment consumes that transferred reference.  AddRef'ing again leaks
        one ref per call.  This matches the tyString/tyDynArray branches above
        and the QBE backend's ExprOwnsRef elision. }
      if not NativeExprOwnsRef(Asgn.Expr) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
      end;
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        { Captured outer local: the _cap_ slot holds the var's address. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.Emit(#9'movq %rax, (%rcx)');
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (IsJumboSet(Asgn.ResolvedLhsType) or
             (Asgn.ResolvedLhsType.Kind in [tyRecord, tyStaticArray])) then
    begin
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'movq %rax, %rsi');
      if Asgn.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(Asgn.Name)]))
      else if Self.IsCaptured(Asgn.Name) then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('_cap_' + Asgn.Name)]))
      else if FSretFunc and SameText(Asgn.Name, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Result')]))
      else if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        Self.EmitLeaqGlobal(Asgn.Name, '%rdi');
      end;
      { Record with managed fields (string / class / interface / dyn-array, or
        nested record thereof): a bare memcpy would make the copy share the
        source's references at the same refcount, so mutating either side later
        drops a shared buffer to 0 and frees it under the other (use-after-free
        / double-free).  Release the destination's prior fields, and — unless the
        source already transferred ownership (+1, e.g. a record-returning
        property getter / call whose Result owns its fields) — retain the
        source's managed fields so the copy owns its own references.  Mirrors the
        string/dyn-array assignment paths' NativeExprOwnsRef guard and the
        record-field-store copy path. }
      if (Asgn.ResolvedLhsType.Kind = tyRecord) and
         not RecretManagedClean(TRecordTypeDesc(Asgn.ResolvedLhsType)) then
      begin
        { %rsi = source addr, %rdi = dest addr — preserve both across the ARC
          calls in callee-saved registers (%rbx = source, %r15 = dest). }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'movq %rsi, %rbx');
        Self.Emit(#9'movq %rdi, %r15');
        if not NativeExprOwnsRef(Asgn.Expr) then
          Self.EmitRecordFieldRetains(TRecordTypeDesc(Asgn.ResolvedLhsType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(Asgn.ResolvedLhsType), '%r15');
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
      end
      else
      begin
        Self.Emit(Format(#9'movq $%d, %%rdx', [Asgn.ResolvedLhsType.RawSize()]));
        Self.Emit(#9'callq memcpy');
      end;
    end
    else
    begin
      Self.EmitExprToEax(Asgn.Expr);
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.VarOperand(Asgn.Name)]));
        Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Self.IsCaptured(Asgn.Name) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.VarOperand('_cap_' + Asgn.Name)]));
        Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else
      begin
        if not Self.IsLocal(Asgn.Name) then
        begin
          Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
          if Asgn.IsThreadVar then Self.MarkThreadVar(Asgn.Name);
        end;
        Self.EmitStoreVar(Self.VarOperand(Asgn.Name),
          Asgn.ResolvedLhsType);
      end;
    end;
    Exit;
  end;

  if AStmt is TForStmt then
  begin
    Self.EmitForStmt(TForStmt(AStmt));
    Exit;
  end;

  if AStmt is TForInStmt then
  begin
    Self.EmitForInStmt(TForInStmt(AStmt));
    Exit;
  end;

  if AStmt is TCaseStmt then
  begin
    Self.EmitCaseStmt(TCaseStmt(AStmt));
    Exit;
  end;

  if AStmt is TProcCall then
  begin
    PC := TProcCall(AStmt);
    if SameText(PC.Name, 'WriteLn') then
    begin
      Self.EmitWrite(PC, True);
      Exit;
    end;
    if SameText(PC.Name, 'Write') then
    begin
      Self.EmitWrite(PC, False);
      Exit;
    end;
    { FreeMem(P) → _BlaiseFreeMem(P).  Pointer arg in %rdi. }
    if SameText(PC.Name, 'FreeMem') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _BlaiseFreeMem');
      Exit;
    end;
    { Delete(S, Idx, Count): S := _StringDelete(S, Idx, Count) with ARC. }
    if SameText(PC.Name, 'Delete') and (PC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringDelete');
      { Assign result back: addref new, release old, store. }
      if TASTExpr(PC.Args.Items[0]) is TIdentExpr then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
      end;
      Exit;
    end;
    { SetLength(A, N) for dynamic arrays: A := _DynArraySetLength(A, N, ElemSize). }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyDynArray) then
    begin
      if (TASTExpr(PC.Args.Items[0]) is TIdentExpr) and
         not TIdentExpr(TASTExpr(PC.Args.Items[0])).IsImplicitSelf and
         (TIdentExpr(TASTExpr(PC.Args.Items[0])).ParamMode = pmNone) then
      begin
        FDynArgName := TIdentExpr(TASTExpr(PC.Args.Items[0])).Name;
        FDynElemSz :=
          TDynArrayTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).ElementType.RawSize();
        { Evaluate the new-length expression FIRST.  It may itself emit a call
          (e.g. SetLength(Result, Length(A)) lowers Length(A) to a
          _DynArrayLength call) which clobbers %rdi, so the array pointer must
          be loaded into %rdi only after this expression is fully evaluated. }
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'movl %eax, %esi');
        { Load current data ptr into %rdi (after N is evaluated). }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [FDynArgName]));
        { Element size into %edx. }
        Self.Emit(Format(#9'movl $%d, %%edx', [FDynElemSz]));
        Self.Emit(#9'callq _DynArraySetLength');
        { Store new data ptr back. }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)', [FDynArgName]));
      end
      else
      begin
        { Field receiver (R.A / C.A / chained): compute the slot address,
          call through it, store the new data pointer back. }
        FDynElemSz :=
          TDynArrayTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).ElementType.RawSize();
        Self.EmitLValueSlotAddr(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'pushq %rdx');
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'subq $8, %rsp');   { keep calls 16-byte aligned }
        Self.Emit(#9'movl %eax, %esi');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(Format(#9'movl $%d, %%edx', [FDynElemSz]));
        Self.Emit(#9'callq _DynArraySetLength');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'movq %rax, (%rdx)');
      end;
      Exit;
    end;
    { SetLength(S, N): S := _StringSetLength(S, N) with ARC. }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringSetLength');
      if (TASTExpr(PC.Args.Items[0]) is TIdentExpr) and
         not TIdentExpr(TASTExpr(PC.Args.Items[0])).IsImplicitSelf and
         (TIdentExpr(TASTExpr(PC.Args.Items[0])).ParamMode = pmNone) then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
      end
      else
      begin
        { Field receiver: new string is in %rax — retain it, release the old
          field value, store through the slot address. }
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        Self.EmitLValueSlotAddr(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'pushq %rdx');
        Self.Emit(#9'movq (%rdx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rdx');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, (%rdx)');
      end;
      Exit;
    end;
    { Inc(x) / Inc(x,n) / Dec(x) / Dec(x,n) — in-place add/sub.
      Supports TIdentExpr (local, global, implicit-Self field, var param)
      and TFieldAccessExpr (record/class field). }
    if (SameText(PC.Name, 'Inc') or SameText(PC.Name, 'Dec')) and
       (PC.Args.Count >= 1) and (PC.Args.Count <= 2) then
    begin
      Self.EmitIncDec(PC);
      Exit;
    end;
    { Include(S, elem): S := S or (1 shl ord(elem)) }
    if SameText(PC.Name, 'Include') and (PC.Args.Count = 2) then
    begin
      { Jumbo set: address of the set, ordinal, then _SetInclude. Handles any
        lvalue shape (var, field, element), not just a bare ident. }
      if IsJumboSet(TASTExpr(PC.Args.Items[0]).ResolvedType) then
      begin
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'pushq %rax');           { ordinal }
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));  { set addr -> %rax }
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetInclude');
        Exit;
      end;
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %ecx');
      FDynArgName := TIdentExpr(TASTExpr(PC.Args.Items[0])).Name;
      if (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
         (TSetTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).BitCount > 32) then
      begin
        Self.Emit(#9'movq $1, %rax');
        Self.Emit(#9'shlq %cl, %rax');
        if Self.IsLocal(FDynArgName) then
        begin
          Self.Emit(Format(#9'orq %%rax, %s', [Self.VarOperand(FDynArgName)]));
        end
        else
          Self.Emit(Format(#9'orq %%rax, %s(%%rip)', [FDynArgName]));
      end
      else
      begin
        Self.Emit(#9'movl $1, %eax');
        Self.Emit(#9'shll %cl, %eax');
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'orl %%eax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'orl %%eax, %s(%%rip)', [FDynArgName]));
      end;
      Exit;
    end;
    { Exclude(S, elem): S := S and (not (1 shl ord(elem))) }
    if SameText(PC.Name, 'Exclude') and (PC.Args.Count = 2) then
    begin
      { Jumbo set: address of the set, ordinal, then _SetExclude. }
      if IsJumboSet(TASTExpr(PC.Args.Items[0]).ResolvedType) then
      begin
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'popq %rsi');
        Self.Emit(#9'callq _SetExclude');
        Exit;
      end;
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %ecx');
      FDynArgName := TIdentExpr(TASTExpr(PC.Args.Items[0])).Name;
      if (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
         (TSetTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).BitCount > 32) then
      begin
        Self.Emit(#9'movq $1, %rax');
        Self.Emit(#9'shlq %cl, %rax');
        Self.Emit(#9'notq %rax');
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'andq %%rax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'andq %%rax, %s(%%rip)', [FDynArgName]));
      end
      else
      begin
        Self.Emit(#9'movl $1, %eax');
        Self.Emit(#9'shll %cl, %eax');
        Self.Emit(#9'notl %eax');
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'andl %%eax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'andl %%eax, %s(%%rip)', [FDynArgName]));
      end;
      Exit;
    end;
    if SameText(PC.Name, 'Halt') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq exit');
      Exit;
    end;
    if SameText(PC.Name, 'ZeroMem') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rdx');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'xorl %esi, %esi');
      Self.Emit(#9'callq memset');
      Exit;
    end;
    if SameText(PC.Name, 'Sleep') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movl %eax, %edi');
      Self.Emit(#9'callq _Sleep');
      Exit;
    end;
    if SameText(PC.Name, 'DeleteFile') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _DeleteFile');
      Exit;
    end;
    if SameText(PC.Name, 'RemoveDir') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _RemoveDir');
      Exit;
    end;
    if SameText(PC.Name, 'ForceDirectories') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ForceDirectories');
      Exit;
    end;
    if SameText(PC.Name, 'WriteFile') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _WriteFile');
      Exit;
    end;
    if SameText(PC.Name, 'AppendFile') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _AppendFile');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessSetExe') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _ProcessSetExe');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessAddArg') and (PC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _ProcessAddArg');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessExecute') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessExecute');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessWaitOnExit') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessWaitOnExit');
      Exit;
    end;
    if SameText(PC.Name, 'ProcessFree') and (PC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ProcessFree');
      Exit;
    end;
    { Unqualified call to a procedural-typed field of the current class
      (implicit Self.Field) used as a statement. }
    if PC.IsProcFieldCall then
    begin
      Self.EmitProcFieldCall(nil, 'Self', False, PC.ProcFieldInfo,
        TProceduralTypeDesc(PC.ResolvedProcType), PC.Args, nil);
      Exit;
    end;
    if PC.IsIndirectCall then
    begin
      if (PC.ResolvedProcType <> nil) and
         TProceduralTypeDesc(PC.ResolvedProcType).IsMethodPtr then
        Self.EmitMethodPtrCall(Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType), PC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType),
          PC.Args);
      Exit;
    end;
    if PC.IsImplicitSelfMethod and (PC.ResolvedDecl <> nil) then
    begin
      MD := TMethodDecl(PC.ResolvedDecl);
      { Self occupies %rdi, leaving %rsi..%r9 (5 registers) for arguments.  The
        push/pop-into-registers fast path is only valid when every argument
        slot fits a register — i.e. Self + args <= 6 total.  When the call has
        more slots, the surplus must go on the stack; otherwise the pop loop
        indexes SysVArg64 past %r9 (the OOB that crashed _StringConcat). }
      if Self.CountArgSlots(MD.Params) + 1 <= 6 then
      begin
        Self.BeginCallArgs(MD.Params, PC.Args);
        for I := 0 to PC.Args.Count - 1 do
          Self.PushCallArg(TMethodParam(MD.Params.Items[I]),
            TASTExpr(PC.Args.Items[I]), I);
        Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
        Self.EmitPopMethodArgsToRegs(MD.Params, PC.Args, 1);
        Self.Emit(#9'movq %r10, %rdi');
        { Virtual implicit-Self call dispatches through the vtable. }
        Self.EmitSelfDispatch(MD, FuncSymbolFromDecl(MD));
        Self.EndCallArgs();
        Exit;
      end;
      { >6 slots: stack-spill path (mirrors EmitMethodCallStmt).  Reserve a
        6-register staging area plus overflow space; slot 0 = Self -> %rdi,
        slots 1..5 -> %rsi..%r9, surplus slots stay on the stack. }
      PCUserSlots := Self.CountArgSlots(MD.Params);
      PCTotalSlots := PCUserSlots + 1;
      PCOverflow := PCTotalSlots - 6;
      PCAllocSz := ((PCTotalSlots * 8 + 15) and (-16));
      PCHD := TList<Integer>.Create();
      PCHK := TList<Integer>.Create();
      PCHTotal := Self.EmitArgHoist(MD.Params, nil, True, '', PC.Args, PCHD, PCHK);
      Self.Emit(Format(#9'subq $%d, %%rsp', [PCAllocSz]));
      Self.EmitArgsToSlots(PC.Args, MD.Params, PCAllocSz, PCHTotal, PCHD, PCHK);
      { Self into slot 0 -> %rdi. }
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      Self.Emit(#9'movq %rax, 0(%rsp)');
      PCCleanUp := Self.EmitMethodOverflowLoad(MD.Params, PC.Args, PCAllocSz);
      Self.EmitSelfDispatch(MD, FuncSymbolFromDecl(MD));
      Self.EmitHoistEpilogue(PC.Args, PCHD, PCHK, PCHTotal, PCCleanUp, True);
      PCHD.Free();
      PCHK.Free();
      Exit;
    end;
    { User procedure call (result, if any, ignored in statement position). }
    Self.EmitCall(FuncSymbolFromDecl(TMethodDecl(PC.ResolvedDecl)),
      TMethodDecl(PC.ResolvedDecl), PC.Args);
    Exit;
  end;

  if AStmt is TCompoundStmt then
  begin
    Comp := TCompoundStmt(AStmt);
    Self.EmitStmtList(Comp.Stmts);
    Exit;
  end;

  if AStmt is TIfStmt then
  begin
    IfS   := TIfStmt(AStmt);
    LThen := Self.NewLabel('then');
    LEnd  := Self.NewLabel('ifend');
    if IfS.ElseStmt <> nil then
      LElse := Self.NewLabel('else')
    else
      LElse := LEnd;
    Self.EmitCondBranch(IfS.Condition, LThen, LElse);
    Self.Emit(LThen + ':');
    Self.EmitStmt(IfS.ThenStmt);
    Self.Emit(#9'jmp ' + LEnd);
    if IfS.ElseStmt <> nil then
    begin
      Self.Emit(LElse + ':');
      Self.EmitStmt(IfS.ElseStmt);
      Self.Emit(#9'jmp ' + LEnd);
    end;
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TTryFinallyStmt then
  begin
    Self.EmitTryFinallyStmt(TTryFinallyStmt(AStmt));
    Exit;
  end;

  if AStmt is TTryExceptStmt then
  begin
    Self.EmitTryExceptStmt(TTryExceptStmt(AStmt));
    Exit;
  end;

  if AStmt is TRaiseStmt then
  begin
    Self.EmitRaiseStmt(TRaiseStmt(AStmt));
    Exit;
  end;

  if AStmt is TWhileStmt then
  begin
    WhileS := TWhileStmt(AStmt);
    LCond  := Self.NewLabel('wcond');
    LBody  := Self.NewLabel('wbody');
    LEnd   := Self.NewLabel('wend');
    Self.Emit(LCond + ':');
    Self.EmitCondBranch(WhileS.Condition, LBody, LEnd);
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    Self.EmitStmt(WhileS.Body);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TRepeatStmt then
  begin
    RepS  := TRepeatStmt(AStmt);
    LBody := Self.NewLabel('rbody');
    LCond := Self.NewLabel('rcond');
    LEnd  := Self.NewLabel('rend');
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    Self.EmitStmtList(RepS.Body.Stmts);
    FContinueExcDepths.Pop();
    FContinueLabels.Pop();
    FBreakExcDepths.Pop();
    FBreakLabels.Pop();
    Self.Emit(LCond + ':');
    Self.EmitCondBranch(RepS.Condition, LEnd, LBody);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ENativeCodeGenError.Create('break outside loop');
    Self.EmitExcUnwind(FBreakExcDepths.Peek());
    Self.Emit(#9'jmp ' + FBreakLabels.Peek());
    Exit;
  end;

  if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ENativeCodeGenError.Create('continue outside loop');
    Self.EmitExcUnwind(FContinueExcDepths.Peek());
    Self.Emit(#9'jmp ' + FContinueLabels.Peek());
    Exit;
  end;

  if AStmt is TExitStmt then
  begin
    if TExitStmt(AStmt).ResultAssign <> nil then
      Self.EmitStmt(TExitStmt(AStmt).ResultAssign);
    Self.EmitExcUnwind(0);
    if FExitLabel <> '' then
      Self.Emit(#9'jmp ' + FExitLabel)
    else
    begin
      Self.Emit(#9'movl $0, %eax');
      Self.Emit(#9'leave');
      Self.Emit(#9'ret');
    end;
    Exit;
  end;

  if AStmt is TMethodCallStmt then
  begin
    { Class method call in statement position (result discarded). }
    Self.EmitMethodCallStmt(TMethodCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TInheritedCallStmt then
  begin
    Self.EmitInheritedCall(TInheritedCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TFieldAssignment then
  begin
    FA := TFieldAssignment(AStmt);
    { Qualified STATIC var write 'TFoo.X := V': lower exactly like a bare global
      store to the shared slot.  Delegate to the TAssignment path via a borrowed
      synthetic node (Expr nilled before Free so the shared expression is not
      released twice) — reuses the scalar / class-ARC / interface store logic. }
    if FA.IsClassVarWrite then
    begin
      CVStore := TAssignment.Create();
      try
        CVStore.Name            := FA.ClassVarEmitName;
        CVStore.IsGlobal        := True;
        CVStore.ResolvedLhsType := FA.ClassVarLhsType;
        CVStore.Expr            := FA.Expr;
        Self.EmitStmt(CVStore);
      finally
        CVStore.Expr := nil;
        CVStore.Free();
      end;
      Exit;
    end;
    { Interface property write: I.Prop := V — FieldName holds the SETTER
      (rewritten by semantic); dispatch through the itab with V as the
      single argument. }
    if FA.IntfWriteDesc <> nil then
    begin
      IntfArgs := TObjectList.Create(False);
      try
        IntfArgs.Add(FA.Expr);
        Self.EmitInterfaceCall(FA.RecordName, FA.IsGlobal, FA.IsVarParam,
          TInterfaceTypeDesc(FA.IntfWriteDesc), FA.FieldName, IntfArgs);
      finally
        IntfArgs.Free();
      end;
      Exit;
    end;
    if FA.PropWriteInfo <> nil then
    begin
      Self.EmitExprToEax(FA.Expr);
      Self.Emit(#9'pushq %rax');
      if FA.ObjExpr <> nil then
      begin
        { Receiver is an arbitrary expression (default-property write through a
          property/field result): its value is the object pointer. }
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rdi');
      end
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rdi', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rdi');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rdi), %rdi');
      end;
      if FA.PropIndexExpr <> nil then
      begin
        Self.Emit(#9'pushq %rdi');
        Self.EmitExprToEax(FA.PropIndexExpr);
        Self.Emit(#9'popq %rdi');
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'popq %rdx');
      end
      else
        Self.Emit(#9'popq %rsi');
      Self.EmitPropAccessorCallNative(FA.PropOwnerType,
        FA.PropWriteInfo.WriteMethod, FA.PropAccessorVSlot);
      Exit;
    end;
    if FA.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: field assignment has no resolved field info');
    { Element write into an array-typed field: Receiver.Field[Idx] := V.
      Evaluate the value, the scaled index, then the field slot address;
      for a dynamic array deref the slot to reach the data pointer; store
      by ELEMENT type with the same ARC rules as plain subscript writes. }
    if FA.IsElemWrite then
    begin
      if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
        DAElemType := TDynArrayTypeDesc(FA.FieldInfo.TypeDesc).ElementType
      else
        DAElemType := TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).ElementType;
      if DAElemType.Kind in [tyByte, tyBoolean] then
        Self.EmitByteRhsToEax(FA.Expr)
      else
        Self.EmitExprToEax(FA.Expr);
      Self.Emit(#9'pushq %rax');           { value (or record src addr) }
      Self.EmitExprToEax(FA.PropIndexExpr);
      if (FA.FieldInfo.TypeDesc.Kind = tyStaticArray) and
         (TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound <> 0) then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(FA.FieldInfo.TypeDesc).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      Self.Emit(#9'pushq %rax');           { scaled element offset }
      { Field slot address → %rdx, per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rdx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rdx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rdx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rdx), %rdx');
      end
      else if FA.IsClassAccess or FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rdx');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rdx), %rdx');
      end
      else
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rdx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rdx', [FA.FieldInfo.Offset]));
      if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
        Self.Emit(#9'movq (%rdx), %rdx');  { data pointer }
      Self.Emit(#9'popq %rax');            { scaled offset }
      Self.Emit(#9'addq %rax, %rdx');
      Self.Emit(#9'movq %rdx, %rcx');      { element address }
      if DAElemType.Kind = tyRecord then
      begin
        { Record element: ARC-aware copy (retain src fields, release dest
          fields, memcpy).  Source record address is on the stack. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'subq $8, %rsp');
        Self.Emit(#9'movq %rcx, %r15');      { dest element addr }
        Self.Emit(#9'movq 24(%rsp), %rbx');  { src record addr }
        Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15');
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'addq $8, %rsp');        { drop saved src addr }
        Exit;
      end;
      if DAElemType.Kind = tyString then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _StringAddRef');
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
      end
      else if DAElemType.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
      end;
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', DAElemType);
      Exit;
    end;
    { Interface-typed field: store a two-slot fat pointer (obj + itab), not a
      single value.  Compute the destination record/object base into %rcx for
      each receiver shape, then hand off to EmitInterfaceToFieldSlotsAt (which
      evaluates the RHS itself and applies ARC on the obj slot). }
    if FA.FieldInfo.TypeDesc.Kind = tyInterface then
    begin
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      Self.EmitInterfaceToFieldSlotsAt(FA.Expr, '%rcx', FA.FieldInfo.Offset,
        FA.FieldInfo.TypeDesc);
      Exit;
    end;
    { Method-pointer (of object) field assignment from @Obj.Method: store the
      [CodePtr, ObjPtr] pair into the field's 16-byte slot.  Mirrors the
      simple-variable case in EmitAssignment; the only difference is that the
      destination is a field, so its containing-object base is computed per
      receiver shape (exactly as the interface-field store above does). }
    if (FA.FieldInfo.TypeDesc.Kind = tyProcedural) and
       TProceduralTypeDesc(FA.FieldInfo.TypeDesc).IsMethodPtr and
       (FA.Expr is TAddrOfExpr) and
       (TAddrOfExpr(FA.Expr).Expr is TFieldAccessExpr) and
       (TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType <> nil) and
       (TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType.Kind = tyProcedural) and
       TProceduralTypeDesc(TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr).ResolvedType).IsMethodPtr then
    begin
      FAE := TFieldAccessExpr(TAddrOfExpr(FA.Expr).Expr);
      MD  := TMethodDecl(FAE.ResolvedMethod);
      { Destination field's containing-object base → %rcx, per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      { Store the code pointer at offset 0. }
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
        [MethodEmitNameNative(MD, MD.OwnerTypeName, FAE.FieldName)]));
      Self.Emit(#9'movq %rax, (%rcx)');
      { Store the captured object pointer at offset 8. }
      if FAE.Base <> nil then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.EmitExprToEax(FAE.Base);
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end
      else
      begin
        Self.EmitVarBaseToReg(FAE.RecordName, False, '%rax');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
      Exit;
    end;
    { Field := MethodCall() where the method returns a record via sret.
      Compute the field address into %rbx (callee-saved), release managed
      fields of the old record, then call with %rbx as the sret destination. }
    if (FA.FieldInfo.TypeDesc.Kind = tyRecord) and
       (FA.Expr is TMethodCallExpr) and
       (TMethodCallExpr(FA.Expr).ResolvedMethod <> nil) and
       (TMethodDecl(TMethodCallExpr(FA.Expr).ResolvedMethod).ResolvedReturnType <> nil) and
       (TMethodDecl(TMethodCallExpr(FA.Expr).ResolvedMethod).ResolvedReturnType.Kind = tyRecord) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitMethodSretCall(TMethodCallExpr(FA.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { Field := FuncCall() where the function returns a record via sret. }
    if (FA.FieldInfo.TypeDesc.Kind = tyRecord) and
       (FA.Expr is TFuncCallExpr) and
       (TFuncCallExpr(FA.Expr).ResolvedDecl <> nil) and
       (TMethodDecl(TFuncCallExpr(FA.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
       (TMethodDecl(TFuncCallExpr(FA.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
    begin
      Self.Emit(#9'pushq %rbx');
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rbx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rbx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else if FA.IsClassAccess then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rbx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rbx), %rbx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rbx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rbx', [FA.FieldInfo.Offset]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitFuncCallSret(TFuncCallExpr(FA.Expr), '(%rbx)', False);
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    if IsFloatFamily(FA.FieldInfo.TypeDesc) then
    begin
      Self.EmitExprToXmm0(FA.Expr);
      { An integer RHS (and any Double sub-expression) lands in %xmm0 as a
        DOUBLE; a Single field needs it narrowed (cvtsd2ss) before the movss
        store, else only the low 32 bits of the double are written — garbage.
        Mirrors the QBE swtof/truncd field-store conversion. }
      Self.EmitXmm0WidthAdjust(FA.Expr.ResolvedType,
        FA.FieldInfo.TypeDesc.Kind = tySingle);
      if FA.ObjExpr <> nil then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FA.IsClassAccess then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else if FA.IsVarParam then
      begin
        Self.Emit(#9'subq $8, %rsp');
        Self.EmitStoreFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        Self.EmitLoadFloat('(%rsp)', FA.FieldInfo.TypeDesc);
        Self.Emit(#9'addq $8, %rsp');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      end;
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      Self.EmitStoreFloat('(%rcx)', FA.FieldInfo.TypeDesc);
      Exit;
    end;
    { Record-typed field := record value: full copy with ARC (retain the
      source's managed fields, release the destination's, then memcpy).
      The scalar tail below would store just the source ADDRESS — an
      8-byte pointer write masquerading as a record copy. }
    if FA.FieldInfo.TypeDesc.Kind = tyRecord then
    begin
      Self.EmitExprToEax(FA.Expr);       { source record address }
      Self.Emit(#9'pushq %rax');
      { Destination field address -> %rcx per receiver shape. }
      if FA.ObjExpr <> nil then
      begin
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
      end
      else if FSretFunc and (FA.RecordName = 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]))
      else if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if FA.IsClassAccess or FA.IsVarParam then
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsClassAccess and FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [FA.FieldInfo.Offset]));
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r15');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movq %rcx, %r15');      { dest field addr }
      Self.Emit(#9'movq 24(%rsp), %rbx');  { src record addr }
      Self.EmitRecordFieldRetains(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%rbx');
      Self.EmitRecordFieldReleases(TRecordTypeDesc(FA.FieldInfo.TypeDesc), '%r15');
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'movq %rbx, %rsi');
      Self.Emit(Format(#9'movq $%d, %%rdx',
        [FA.FieldInfo.TypeDesc.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'popq %r15');
      Self.Emit(#9'popq %rbx');
      Self.Emit(#9'addq $8, %rsp');        { drop saved src addr }
      Exit;
    end;
    Self.EmitExprToEax(FA.Expr);
    { Chained field assignment: ObjExpr is the receiver expression (e.g. DT.Date
      or H.R.Obj).  Emit the receiver to get the base address, then store at the
      field offset — with ARC for managed fields (interface fields are handled by
      the unified block above and never reach here). }
    if FA.ObjExpr <> nil then
    begin
      if FA.FieldInfo.TypeDesc.IsString()
         or (FA.FieldInfo.TypeDesc.Kind = tyClass)
         or (FA.FieldInfo.TypeDesc.Kind = tyDynArray) then
      begin
        { Managed field: retain new (string/dyn-array only when the RHS does not
          already own +1; class stays unconditional — see the IsClassAccess
          branch), release old, store.  %r15 (callee-saved, preserved) holds the
          receiver base across the ARC calls; the new value sits on the stack. }
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rax');            { new value }
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %r15');       { receiver base }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq (%rsp), %rdi');   { new value }
          if FA.FieldInfo.TypeDesc.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(Format(#9'movq %d(%%r15), %%rdi', [FA.FieldInfo.Offset]));
        if FA.FieldInfo.TypeDesc.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');             { new value }
        Self.Emit(#9'movq %r15, %rcx');
        Self.Emit(#9'popq %r15');             { restore caller's %r15 }
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'pushq %rax');
        Self.EmitExprToEax(FA.ObjExpr);
        Self.Emit(#9'movq %rax, %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end
    else if FSretFunc and (FA.RecordName = 'Result') then
    begin
      if FA.FieldInfo.TypeDesc.IsString()
         or (FA.FieldInfo.TypeDesc.Kind = tyClass)
         or (FA.FieldInfo.TypeDesc.Kind = tyDynArray) then
      begin
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'pushq %rax');
        Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Result')]));
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          if FA.FieldInfo.TypeDesc.IsString() then
            Self.Emit(#9'callq _StringAddRef')
          else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
            Self.Emit(#9'callq _DynArrayAddRef')
          else
            Self.Emit(#9'callq _ClassAddRef');
        end;
        Self.Emit(Format(#9'movq %d(%%r15), %%rdi', [FA.FieldInfo.Offset]));
        if FA.FieldInfo.TypeDesc.IsString() then
          Self.Emit(#9'callq _StringRelease')
        else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
          Self.Emit(#9'callq _DynArrayRelease')
        else
          Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %r15, %rcx');
        Self.Emit(#9'popq %r15');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]));
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end
    else if FA.IsClassAccess or FA.IsImplicitSelf then
    begin
      Self.Emit(#9'pushq %rax');
      if FA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if (FA.ImplicitBaseInfo <> nil) and (FA.ImplicitBaseInfo.Offset > 0) then
          Self.Emit(Format(#9'addq $%d, %%rcx', [FA.ImplicitBaseInfo.Offset]));
        if FA.IsClassAccess then
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else
      begin
        Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
        if FA.IsVarParam then
          { var-param class: slot -> caller var -> instance }
          Self.Emit(#9'movq (%rcx), %rcx');
      end;
      if FA.FieldInfo.IsUnretained and (FA.FieldInfo.TypeDesc.Kind = tyClass) then
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
        if NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _ClassRelease');
        end;
      end
      else if FA.FieldInfo.IsWeak then
      begin
        Self.Emit(#9'popq %rax');
        Self.Emit(Format(#9'leaq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'callq _WeakAssign');
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        { ARC: addref(new) unless the RHS already owns +1 (call results
          transfer ownership), release(old), store new. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _ClassAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.IsString() then
      begin
        { When the RHS already owns +1 (a call result), the field consumes that
          transferred reference and must NOT AddRef again — otherwise the buffer
          leaks one ref per store.  The old field contents are released
          unconditionally. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        { Dynamic-array field: same ARC shape as String — retain new buffer,
          release the old, store.  Skip the retain when the RHS already owns +1. }
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end
    else if FA.IsVarParam then
    begin
      Self.Emit(#9'pushq %rax');
      Self.EmitVarBaseToReg(FA.RecordName, False, '%rcx');
      if FA.FieldInfo.TypeDesc.IsString() then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'popq %rcx');
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end
    else
    begin
      Self.Emit(#9'pushq %rax');
      Self.EmitVarBaseToReg(FA.RecordName, True, '%rcx');
      if FA.FieldInfo.TypeDesc.IsString() then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _StringAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'popq %rcx');
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else if FA.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        if not NativeExprOwnsRef(FA.Expr) then
        begin
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'movq 8(%rsp), %rdi');
          Self.Emit(#9'callq _DynArrayAddRef');
          Self.Emit(#9'popq %rcx');
        end;
        Self.Emit(Format(#9'movq %d(%%rcx), %%rdi', [FA.FieldInfo.Offset]));
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'callq _DynArrayRelease');
        Self.Emit(#9'popq %rcx');
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end
      else
      begin
        Self.Emit(#9'popq %rax');
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
      end;
    end;
    Exit;
  end;

  if AStmt is TStaticSubscriptAssign then
  begin
    SSA := TStaticSubscriptAssign(AStmt);
    { Default array property write: Obj[I] := V lowered to a setter call.
      Args: receiver %rdi, index %rsi, value %rdx (System V).  Evaluate value
      and index first (they clobber registers), stash on the stack, then load
      the receiver and reload the args. }
    if SSA.PropWriteInfo <> nil then
    begin
      Self.EmitExprToEax(SSA.ValueExpr);       { value }
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);       { index }
      Self.Emit(#9'pushq %rax');
      if SSA.IsImplicitSelf then
      begin
        { Self.Field[I] := V — load Self, reach the field slot, deref to the
          field's class object (the setter receiver). }
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rdi', [SSA.ImplicitFieldInfo.Offset]));
        Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rdi');
        if SSA.IsVarParam then
          Self.Emit(#9'movq (%rdi), %rdi');      { var-param: slot -> instance }
      end;
      Self.Emit(#9'popq %rsi');                { index }
      Self.Emit(#9'popq %rdx');                { value }
      Self.EmitPropAccessorCallNative(SSA.PropOwnerType,
        TPropertyInfo(SSA.PropWriteInfo).WriteMethod, SSA.PropAccessorVSlot);
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind = tyString) then
    begin
      { String subscript write S[I] := ch with copy-on-write.  %rbx holds the
        address of the slot that stores the string's data pointer (a
        local/global slot directly, or the caller's variable address for a
        var/out param).  _StringUnique returns a uniquely-owned writable
        pointer (releasing the old one when it copies); store it back so the
        slot keeps exactly one owned reference, then storeb into it.  Without
        the COW, writing a literal-backed string would hit read-only memory. }
      Self.EmitByteRhsToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');                  { [rsp] = byte value }
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.Emit(#9'pushq %rax');                  { [rsp] = index }
      { Preserve %rbx and keep %rsp 16-aligned across the call: pushing %rbx
        alone (3rd push) would misalign, so reserve a paired 8-byte pad. }
      Self.Emit(#9'pushq %rbx');                  { preserve %rbx }
      Self.Emit(#9'subq $8, %rsp');               { align to 16 }
      { %rbx := address of the slot holding the data pointer. }
      Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rbx');
      if SSA.IsVarParam then
        { var/out param: slot holds the caller variable's address; that is
          where the string pointer actually lives. }
        Self.Emit(#9'movq (%rbx), %rbx');
      Self.Emit(#9'movq (%rbx), %rdi');           { old data pointer }
      Self.Emit(#9'callq _StringUnique');         { %rax = unique pointer }
      Self.Emit(#9'movq %rax, (%rbx)');           { write back to slot }
      Self.Emit(#9'movq %rax, %rcx');             { %rcx = unique base }
      Self.Emit(#9'addq $8, %rsp');               { drop alignment pad }
      Self.Emit(#9'popq %rbx');                   { restore %rbx }
      Self.Emit(#9'popq %rax');                   { index }
      Self.Emit(#9'addq %rax, %rcx');
      Self.Emit(#9'popq %rax');                   { byte value }
      Self.Emit(#9'movb %al, (%rcx)');
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind = tyPChar) then
    begin
      { PChar subscript write: P[I] := byte — storeb at base + I.  PChar is a
        raw pointer with no ARC header (the slot holds it directly). }
      Self.EmitByteRhsToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx');
      if SSA.IsVarParam then
        { var/out param: slot -> caller var -> char pointer. }
        Self.Emit(#9'movq (%rcx), %rcx');
      Self.Emit(#9'addq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movb %al, (%rcx)');
      Exit;
    end;
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind in [tyDynArray, tyOpenArray]) then
    begin
      { Open arrays share the dynamic-array element-write path: both address the
        element as data_ptr + I*elemsize.  The one difference is the var-param
        deref below — an open-array param slot already holds the data pointer
        directly, so it must NOT be dereferenced a second time (issue #130
        bug5). }
      if SSA.ResolvedArrayType.Kind = tyOpenArray then
        DAElemType := TOpenArrayTypeDesc(SSA.ResolvedArrayType).ElementType
      else
      DAElemType := TDynArrayTypeDesc(SSA.ResolvedArrayType).ElementType;
      { Chained / multi-dimensional write A[I][J] := V where the inner array
        is itself a dynamic array: BaseExpr (A[I]) evaluates to the inner
        dynarray value — its data pointer.  Stash it on the stack so index
        and value evaluation below can clobber registers freely; the
        base-resolve steps then reload it instead of a named slot. }
      if SSA.BaseExpr <> nil then
      begin
        Self.EmitExprToEax(SSA.BaseExpr);
        Self.Emit(#9'pushq %rax');             { stack: [baseptr] }
      end;
      { Record-returning call as the RHS: sret directly into the element —
        EmitExprToEax cannot evaluate a record call (the callee writes its
        Result through the hidden sret pointer, which would be garbage). }
      if (DAElemType.Kind = tyRecord) and Self.IsNativeRecordCall(SSA.ValueExpr) then
      begin
        Self.Emit(#9'pushq %rbx');
        Self.EmitExprToEax(SSA.IndexExpr);
        Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
        if SSA.BaseExpr <> nil then
          { Base ptr pushed before %rbx: now at 8(%rsp). }
          Self.Emit(#9'movq 8(%rsp), %rcx')
        else if SSA.IsImplicitSelf then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
          if SSA.ImplicitFieldInfo.Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
          Self.Emit(#9'movq (%rcx), %rcx');
        end
        else if Self.IsLocal(SSA.ArrayName) then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]));
          if SSA.IsVarParam then
            { var/out param: slot -> caller var -> data pointer. }
            Self.Emit(#9'movq (%rcx), %rcx');
        end
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [SSA.ArrayName]));
        Self.Emit(#9'addq %rcx, %rax');
        Self.Emit(#9'movq %rax, %rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%rbx');
        Self.EmitRecordCallSretAt(SSA.ValueExpr, '(%rbx)');
        Self.Emit(#9'popq %rbx');
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      { Float element: evaluate the RHS into %xmm0, coerce to the element's
        width, then spill the bit pattern through %rax onto the stack (x86 has
        no push for xmm regs).  EmitExprToEax cannot evaluate a float
        expression; the integer store path (movq) would store garbage. }
      if IsFloatFamily(DAElemType) then
      begin
        Self.EmitExprToXmm0(SSA.ValueExpr);
        Self.EmitXmm0WidthAdjust(SSA.ValueExpr.ResolvedType,
                                 DAElemType.Kind = tySingle);
        Self.Emit(#9'movq %xmm0, %rax');
      end
      else if DAElemType.Kind in [tyByte, tyBoolean] then
        Self.EmitByteRhsToEax(SSA.ValueExpr)
      else
        Self.EmitExprToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.BaseExpr <> nil then
        { Base ptr pushed before the value: value is on top, so the base
          sits at 8(%rsp). }
        Self.Emit(#9'movq 8(%rsp), %rcx')
      else if SSA.IsImplicitSelf then
      begin
        { ArrayName is a dyn-array field of Self: Self + offset holds the
          data pointer. }
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
        Self.Emit(#9'movq (%rcx), %rcx');
      end
      else if Self.IsLocal(SSA.ArrayName) then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]));
        { An open-array param slot already holds the data pointer, so it is NOT
          dereferenced again (a var dynamic-array slot holds the caller-var
          address and does need the extra load). }
        if SSA.IsVarParam and (SSA.ResolvedArrayType.Kind <> tyOpenArray) then
          { var/out param: slot -> caller var -> data pointer. }
          Self.Emit(#9'movq (%rcx), %rcx');
      end
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [SSA.ArrayName]));
      Self.Emit(#9'addq %rcx, %rax');
      Self.Emit(#9'movq %rax, %rcx');
      if IsFloatFamily(DAElemType) then
      begin
        { Float store: reload the spilled value into %xmm0, store at the
          element address with the element's width. }
        Self.Emit(#9'popq %rax');
        Self.Emit(#9'movq %rax, %xmm0');
        Self.EmitStoreFloat('(%rcx)', DAElemType);
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      if DAElemType.Kind = tyRecord then
      begin
        { Record element: ARC-aware copy of the record contents (retain the
          source's managed fields, release the destination's, then memcpy).
          The source record address was pushed above; %rcx holds the element
          address.  Push count stays even so calls remain 16-byte aligned. }
        Self.Emit(#9'pushq %rbx');
        Self.Emit(#9'pushq %r15');
        Self.Emit(#9'subq $8, %rsp');
        Self.Emit(#9'movq %rcx, %r15');        { dest element addr }
        Self.Emit(#9'movq 24(%rsp), %rbx');    { src record addr }
        Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
        Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15');
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'movq %rbx, %rsi');
        Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
        Self.Emit(#9'callq memcpy');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'popq %r15');
        Self.Emit(#9'popq %rbx');
        Self.Emit(#9'addq $8, %rsp');          { drop saved src addr }
        if SSA.BaseExpr <> nil then
          Self.Emit(#9'addq $8, %rsp');         { drop stashed base ptr }
        Exit;
      end;
      if DAElemType.Kind = tyString then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _StringAddRef');
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rcx');
      end
      else if DAElemType.Kind = tyClass then
      begin
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'movq 8(%rsp), %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        Self.Emit(#9'movq (%rsp), %rcx');
        Self.Emit(#9'movq (%rcx), %rdi');
        Self.Emit(#9'callq _ClassRelease');
        Self.Emit(#9'popq %rcx');
      end;
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', DAElemType);
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');           { drop stashed base ptr }
      Exit;
    end;
    { Static array element write. }
    if (SSA.ResolvedArrayType = nil) or
       (SSA.ResolvedArrayType.Kind <> tyStaticArray) then
      raise ENativeCodeGenError.Create(
        'native backend: static subscript assign on non-static-array');
    DAElemType := TStaticArrayTypeDesc(SSA.ResolvedArrayType).ElementType;
    { Interface element write (Arr[I] := V): the element is a contiguous 16-byte
      fat pointer (obj at +0, itab at +8).  A plain EmitStoreVar would store only
      the 8-byte obj and leave the itab garbage, so a later dispatch/read faults.
      Compute the element address into a callee-saved register (it must survive
      the helper's ARC calls) and delegate to EmitInterfaceToFieldSlotsAt, which
      stores obj+itab with ARC for nil / class-instance / interface sources. }
    if DAElemType.Kind = tyInterface then
    begin
      Self.Emit(#9'pushq %r14');
      { Build a TStringSubscriptExpr-equivalent address: reuse the SSA fields.
        EmitIntfStaticElemAddr expects StrExpr/IndexExpr, but here the array is
        named by SSA — compute the element address inline (base + idx*16). }
      Self.EmitExprToEax(SSA.IndexExpr);
      if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%r14', [SSA.ImplicitFieldInfo.Offset]));
      end
      else if SSA.IsVarParam then
        { var-param array: the slot holds the array POINTER (AWantAddress=False).
          For a captured var-param the _cap_ slot holds the address of that
          pointer slot, so EmitVarBaseToReg(False) loads it and derefs once. }
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%r14')
      else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%r14', [Self.VarOperand(SSA.ArrayName)]))
      else
        Self.EmitVarBaseToReg(SSA.ArrayName, True, '%r14');
      Self.Emit(#9'addq %rax, %r14');          { %r14 = element address }
      Self.EmitInterfaceToFieldSlotsAt(SSA.ValueExpr, '%r14', 0, DAElemType);
      Self.Emit(#9'popq %r14');
      Exit;
    end;
    { Record-returning call RHS: sret directly into the element (see the
      dyn-array branch above). }
    if (DAElemType.Kind = tyRecord) and Self.IsNativeRecordCall(SSA.ValueExpr) then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.EmitExprToEax(SSA.IndexExpr);
      if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
      if SSA.IsImplicitSelf then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
        if SSA.ImplicitFieldInfo.Offset > 0 then
          Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
      end
      else if SSA.IsVarParam then
        Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx')
      else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
      else
        Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rcx');
      Self.Emit(#9'addq %rcx, %rax');
      Self.Emit(#9'movq %rax, %rbx');
      Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%rbx');
      Self.EmitRecordCallSretAt(SSA.ValueExpr, '(%rbx)');
      Self.Emit(#9'popq %rbx');
      Exit;
    end;
    { Chained / multi-dimensional write A[I][J] := V: evaluate BaseExpr (the
      inner-array address) first and stash it on the stack so the index
      evaluation below can clobber registers freely; the base-resolve step
      then pops it instead of loading from a named slot. }
    if SSA.BaseExpr <> nil then
    begin
      Self.EmitExprToEax(SSA.BaseExpr);
      Self.Emit(#9'pushq %rax');             { stack: [baseaddr] }
    end;
    { Float element: evaluate into %xmm0, coerce to the element width, then
      spill through %rax (see the dyn-array float branch above). }
    if IsFloatFamily(DAElemType) then
    begin
      Self.EmitExprToXmm0(SSA.ValueExpr);
      Self.EmitXmm0WidthAdjust(SSA.ValueExpr.ResolvedType,
                               DAElemType.Kind = tySingle);
      Self.Emit(#9'movq %xmm0, %rax');
    end
    else if DAElemType.Kind in [tyByte, tyBoolean] then
      Self.EmitByteRhsToEax(SSA.ValueExpr)
    else
      Self.EmitExprToEax(SSA.ValueExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SSA.IndexExpr);
    if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax',
        [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
    Self.Emit(Format(#9'imulq $%d, %%rax', [DAElemType.RawSize()]));
    if SSA.BaseExpr <> nil then
    begin
      { Base address was pushed before the value: it now sits at 8(%rsp)
        (the value is on top).  Load it without disturbing the value. }
      Self.Emit(#9'movq 8(%rsp), %rcx');
    end
    else if SSA.IsImplicitSelf then
    begin
      { ArrayName is a static-array field of Self: the inline storage
        starts at Self + field offset. }
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      if SSA.ImplicitFieldInfo.Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rcx', [SSA.ImplicitFieldInfo.Offset]));
    end
    else if SSA.IsVarParam then
      Self.EmitVarBaseToReg(SSA.ArrayName, False, '%rcx')
    else if FSretFunc and SameText(SSA.ArrayName, 'Result') then
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
    else
      Self.EmitVarBaseToReg(SSA.ArrayName, True, '%rcx');
    Self.Emit(#9'addq %rcx, %rax');
    Self.Emit(#9'movq %rax, %rcx');
    if IsFloatFamily(DAElemType) then
    begin
      { Float store: reload the spilled value into %xmm0 and store with the
        element width. }
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, %xmm0');
      Self.EmitStoreFloat('(%rcx)', DAElemType);
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');           { drop stashed base address }
      Exit;
    end;
    if DAElemType.Kind = tyRecord then
    begin
      { Record element: ARC-aware copy — same scheme as the dyn-array
        record branch above. }
      Self.Emit(#9'pushq %rbx');
      Self.Emit(#9'pushq %r15');
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movq %rcx, %r15');        { dest element addr }
      Self.Emit(#9'movq 24(%rsp), %rbx');    { src record addr }
      Self.EmitRecordFieldRetains(TRecordTypeDesc(DAElemType), '%rbx');
      Self.EmitRecordFieldReleases(TRecordTypeDesc(DAElemType), '%r15');
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'movq %rbx, %rsi');
      Self.Emit(Format(#9'movq $%d, %%rdx', [DAElemType.RawSize()]));
      Self.Emit(#9'callq memcpy');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'popq %r15');
      Self.Emit(#9'popq %rbx');
      Self.Emit(#9'addq $8, %rsp');          { drop saved src addr }
      if SSA.BaseExpr <> nil then
        Self.Emit(#9'addq $8, %rsp');         { drop stashed base address }
      Exit;
    end;
    if DAElemType.Kind = tyString then
    begin
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq 8(%rsp), %rdi');
      Self.Emit(#9'callq _StringAddRef');
      Self.Emit(#9'movq (%rsp), %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'callq _StringRelease');
      Self.Emit(#9'popq %rcx');
    end
    else if DAElemType.Kind = tyClass then
    begin
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'movq 8(%rsp), %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%rsp), %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rcx');
    end;
    Self.Emit(#9'popq %rax');
    Self.EmitStoreVar('(%rcx)', DAElemType);
    if SSA.BaseExpr <> nil then
      Self.Emit(#9'addq $8, %rsp');           { drop stashed base address }
    Exit;
  end;

  { P^ := Value — pointer dereference write.  Evaluate value into %rax,
    save it, evaluate pointer into %rcx, then store through (%rcx). }
  if AStmt is TPointerWriteStmt then
  begin
    if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
       TPointerWriteStmt(AStmt).BaseTy.IsString() then
    begin
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'callq _StringRelease');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringAddRef');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'movq %rax, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyClass) then
    begin
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movq (%rcx), %rdi');
      Self.Emit(#9'pushq %rcx');
      Self.Emit(#9'callq _ClassRelease');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'movq %rax, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tyDouble) then
    begin
      Self.EmitExprToXmm0(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movsd (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'movsd %xmm0, (%rcx)');
    end
    else if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
            (TPointerWriteStmt(AStmt).BaseTy.Kind = tySingle) then
    begin
      Self.EmitExprToXmm0(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'movss %xmm0, (%rsp)');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'movss (%rsp), %xmm0');
      Self.Emit(#9'addq $8, %rsp');
      Self.Emit(#9'movss %xmm0, (%rcx)');
    end
    else
    begin
      if (TPointerWriteStmt(AStmt).BaseTy <> nil) and
         (TPointerWriteStmt(AStmt).BaseTy.Kind in [tyByte, tyBoolean]) then
        Self.EmitByteRhsToEax(TPointerWriteStmt(AStmt).ValExpr)
      else
        Self.EmitExprToEax(TPointerWriteStmt(AStmt).ValExpr);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TPointerWriteStmt(AStmt).PtrExpr);
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', TPointerWriteStmt(AStmt).BaseTy);
    end;
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported statement ' + AStmt.ClassName);
end;

{ ------------------------------------------------------------------ }
{ Calls and function definitions                                       }
{ ------------------------------------------------------------------ }

{ Allocate stack storage for an inline open-array literal, fill elements in
  order, and leave a pointer to element 0 in %rax.  Returns the bytes allocated
  on the stack; caller must addq that after the call to reclaim them. }
function TX86_64Backend.EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
var
  OAType:   TOpenArrayTypeDesc;
  ElemType: TTypeDesc;
  ElemSize: Integer;
  TotalSz:  Integer;
  I:        Integer;
begin
  { 'array of const' literal: each element is a 16-byte TVarRec (VType at +0,
    VValue at +8). }
  if ALit.IsConstArray then
    Exit(Self.EmitConstArrayLiteral(ALit));

  OAType   := TOpenArrayTypeDesc(ALit.ResolvedType);
  ElemType := OAType.ElementType;
  ElemSize := ElemType.RawSize();
  TotalSz  := ALit.Elements.Count * ElemSize;
  if TotalSz < 1 then TotalSz := 1;
  { Align to 16 bytes for ABI compliance. }
  TotalSz := (TotalSz + 15) and (-16);
  Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSz]));
  Self.Emit(#9'movq %rsp, %rax');  { %rax = base of element storage }
  for I := 0 to ALit.Elements.Count - 1 do
  begin
    Self.EmitExprToEax(TASTExpr(ALit.Elements.Items[I]));
    case ElemSize of
      1: Self.Emit(Format(#9'movb %%al, %d(%%rsp)', [I * ElemSize]));
      2: Self.Emit(Format(#9'movw %%ax, %d(%%rsp)', [I * ElemSize]));
      4: Self.Emit(Format(#9'movl %%eax, %d(%%rsp)', [I * ElemSize]));
    else
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * ElemSize]));
    end;
  end;
  { Re-load %rax with the base ptr (EmitExprToEax may have clobbered it). }
  Self.Emit(#9'movq %rsp, %rax');
  Exit(TotalSz);
end;

function TX86_64Backend.EmitConstArrayLiteral(ALit: TArrayLiteralExpr): Integer;
{ Build an 'array of const' temporary on the stack: one 16-byte TVarRec per
  element (VType byte at +0, pointer-sized VValue at +8).  Borrow semantics —
  strings/objects are stored without an AddRef.  Doubles are heap-boxed (a
  PDouble in the slot) since a double does not fit the integer value slot.
  Returns the bytes subtracted from %rsp (caller restores), with %rax = base. }
var
  Count, TotalSz, I, Tag, Off: Integer;
  Elem: TASTExpr;
  EK:   TTypeKind;
begin
  Count := ALit.Elements.Count;
  if Count < 1 then
  begin
    { Empty [] — no storage; null data pointer, callee sees high = -1. }
    Self.Emit(#9'xorq %rax, %rax');
    Exit(0);
  end;
  TotalSz := Count * 16;
  TotalSz := (TotalSz + 15) and (-16);   { 16-byte ABI alignment }
  Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSz]));
  { %rbx holds the stable block base across element evaluation (callee-saved). }
  Self.Emit(#9'pushq %rbx');
  Self.Emit(#9'leaq 8(%rsp), %rbx');     { base = rsp + 8 (skip saved rbx) }
  for I := 0 to Count - 1 do
  begin
    Elem := TASTExpr(ALit.Elements.Items[I]);
    EK   := Elem.ResolvedType.Kind;
    Off  := I * 16;
    case EK of
      tyDouble, tySingle:
        begin
          Tag := 3;   { vtExtended — heap-box the double }
          Self.EmitExprToXmm0(Elem);
          Self.Emit(#9'subq $8, %rsp');
          Self.Emit(#9'movsd %xmm0, (%rsp)');   { stash the double }
          Self.Emit(#9'movl $8, %edi');
          Self.Emit(#9'callq _BlaiseGetMem');   { ptr in %rax }
          Self.Emit(#9'movsd (%rsp), %xmm0');
          Self.Emit(#9'addq $8, %rsp');
          Self.Emit(#9'movsd %xmm0, (%rax)');   { *box = double }
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyBoolean:
        begin
          Tag := 1;
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movzbl %al, %eax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyInteger, tyUInt32, tyByte, tySmallInt, tyWord:
        begin
          Tag := 0;   { vtInteger }
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movslq %eax, %rax');     { sign-extend to 64 bits }
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyEnum:
        begin
          Tag := 24;  { vtEnum }
          Self.EmitExprToEax(Elem);
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyInt64, tyUInt64:
        begin
          Tag := 16;  { vtInt64 }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyString:
        begin
          Tag := 20;  { vtAnsiString — borrow the string data pointer }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
      tyClass, tyMetaClass:
        begin
          Tag := 7;   { vtObject — borrow the object pointer }
          Self.EmitExprToEax(Elem);
          Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
        end;
    else
      Tag := 5;       { vtPointer }
      Self.EmitExprToEax(Elem);
      Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [Off + 8]));
    end;
    { Store the tag byte at slot +0. }
    Self.Emit(Format(#9'movb $%d, %d(%%rbx)', [Tag, Off]));
  end;
  Self.Emit(#9'movq %rbx, %rax');   { base pointer to the TVarRec block }
  Self.Emit(#9'popq %rbx');
  Exit(TotalSz);
end;

function TX86_64Backend.ConstStrShape(AArg: TASTExpr;
  APinPlainLocals: Boolean): TConstArgMode;
var
  IE: TIdentExpr;
begin
  Result := camPin;
  if AArg = nil then Exit;
  if AArg is TStringLiteral then
    Exit(camBorrowed);
  if AArg is TIdentExpr then
  begin
    IE := TIdentExpr(AArg);
    if IE.IsImplicitSelfMethod then
      Exit(camConsume);   { bare zero-arg method call — +1 owned return }
    if IE.IsConstant then
      Exit(camBorrowed);  { named string const — immortal literal data }
    if (not IE.IsGlobal) and (IE.ParamMode = pmNone) and
       (IE.ImplicitFieldInfo = nil) and not Self.IsCaptured(IE.Name) and
       (FConstArgUnsafe.IndexOf(IE.Name) < 0) then
    begin
      { Plain local / by-value or const param: the frame's own reference
        outlives the call — unless an alias can defeat that (var/out string
        sibling param in the same signature, or unknown parameter types). }
      if APinPlainLocals then
        Exit(camPin);
      Exit(camBorrowed);
    end;
    Exit(camPin);         { global, var-param read, implicit-Self field,
                            address-taken or nested-captured local }
  end;
  if NativeExprOwnsRef(AArg) then
    Exit(camConsume);     { function/method/getter return — +1 owned temp }
end;

function TX86_64Backend.IsRecCallArg(AArg: TASTExpr): Boolean;
begin
  Result := False;
  if (AArg = nil) or (AArg.ResolvedType = nil) then Exit;
  if AArg.ResolvedType.Kind <> tyRecord then Exit;
  if (AArg is TFuncCallExpr) and (TFuncCallExpr(AArg).ResolvedDecl <> nil) then
    Exit(True);
  if (AArg is TMethodCallExpr) and
     not TMethodCallExpr(AArg).IsConstructorCall then
    Exit(True);
end;

function TX86_64Backend.RecArgBufBytes(AArg: TASTExpr): Integer;
begin
  Result := (TRecordTypeDesc(AArg.ResolvedType).TotalSize() + 15) and (-16);
end;

function TX86_64Backend.ParamsHaveVarString(AParams: TObjectList): Boolean;
var
  I: Integer;
  P: TMethodParam;
begin
  Result := False;
  if AParams = nil then Exit;
  for I := 0 to AParams.Count - 1 do
  begin
    P := TMethodParam(AParams.Items[I]);
    if P.IsVarParam and (P.ResolvedType <> nil) and
       P.ResolvedType.IsString() then
      Exit(True);
  end;
end;

function TX86_64Backend.ProcParamsHaveVarString(AProcParams: TObjectList): Boolean;
var
  I: Integer;
  P: TProcParamInfo;
begin
  Result := False;
  if AProcParams = nil then Exit;
  for I := 0 to AProcParams.Count - 1 do
  begin
    P := TProcParamInfo(AProcParams.Items[I]);
    if P.IsVarParam and (P.TypeDesc <> nil) and P.TypeDesc.IsString() then
      Exit(True);
  end;
end;

function TX86_64Backend.VarFlagAt(const AFlags: string; AIndex: Integer): Boolean;
var
  I, Idx: Integer;
begin
  Result := False;
  if AFlags = '' then Exit;
  Idx := 0;
  for I := 0 to Length(AFlags) - 1 do
  begin
    if AFlags[I] = ',' then
      Idx := Idx + 1
    else if Idx = AIndex then
      Exit(AFlags[I] = '1');
  end;
end;

function TX86_64Backend.TopFrameTotal: Integer;
begin
  Result := TOALCallFrame(FOALFrames.Get(FOALFrames.Count - 1)).Total;
end;

function TX86_64Backend.EmitArgHoist(AParams: TObjectList;
  AProcParams: TObjectList; AKnownSig: Boolean; const AVarFlags: string;
  AArgs: TObjectList;
  ADepths: TList<Integer>; AKinds: TList<Integer>): Integer;
var
  I: Integer;
  Par: TMethodParam;
  PP: TProcParamInfo;
  Arg: TASTExpr;
  IsVarPos: Boolean;
  ConstStr: Boolean;
  PinPlain: Boolean;
  Mode: TConstArgMode;
begin
  Result := 0;
  if AArgs = nil then Exit;
  { One var/out string sibling param pins plain locals; unknown parameter
    types (interface dispatch) pin them too unless the var flags prove the
    signature has no var params at all. }
  if AParams <> nil then
    PinPlain := Self.ParamsHaveVarString(AParams)
  else if AProcParams <> nil then
    PinPlain := Self.ProcParamsHaveVarString(AProcParams)
  else
    PinPlain := Pos('1', AVarFlags) >= 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Par := nil;
    PP := nil;
    if (AParams <> nil) and (I < AParams.Count) then
      Par := TMethodParam(AParams.Items[I]);
    if (AProcParams <> nil) and (I < AProcParams.Count) then
      PP := TProcParamInfo(AProcParams.Items[I]);
    IsVarPos := ((Par <> nil) and Par.IsVarParam) or
                ((PP <> nil) and PP.IsVarParam) or
                Self.VarFlagAt(AVarFlags, I);

    { Open-array literal: element block + saved data pointer. }
    if (Par <> nil) and Par.IsOpenArray and (Arg is TArrayLiteralExpr) then
    begin
      Result := Result + Self.EmitOpenArrayLiteral(TArrayLiteralExpr(Arg));
      Self.Emit(#9'pushq %rax');
      Result := Result + 8;
      ADepths.Add(Result);
      AKinds.Add(akOALit);
      Continue;
    end;

    { Record-returning call: materialise the sret buffer here and save the
      buffer pointer.  Evaluated mid-loop it would land between pushed
      argument slots and corrupt the popq sequence. }
    if (not IsVarPos) and Self.IsRecCallArg(Arg) then
    begin
      if Arg is TMethodCallExpr then
      begin
        { EmitExprToEax routes a method call through EmitMethodCallExpr, which
          has no sret-buffer path — it would leave %rax pointing at nothing.
          Allocate the buffer and drive the sret call directly, mirroring the
          TFuncCallExpr path in EmitExprToEax. }
        Self.Emit(Format(#9'subq $%d, %%rsp', [Self.RecArgBufBytes(Arg)]));
        Self.EmitMethodSretCall(TMethodCallExpr(Arg), '(%rsp)', False);
        Self.Emit(#9'leaq (%rsp), %rax');
      end
      else
        Self.EmitExprToEax(Arg);        { buffer at %rsp, pointer in %rax }
      { The buffer (RecArgBufBytes, 16-aligned) plus the 8-byte saved pointer
        would leave the hoist region 8 bytes off 16-alignment.  Reserve a
        16-byte slot for the pointer (push + 8-byte pad) so the total stays a
        multiple of 16 — otherwise a later call in this argument list (or the
        callee, e.g. a libm routine using `movdqa`) faults on a misaligned %rsp.
        The pad sits ABOVE the saved pointer, so the reload offset (which uses
        Result - depth) is unchanged. }
      Self.Emit(#9'subq $8, %rsp');
      Self.Emit(#9'pushq %rax');
      Result := Result + Self.RecArgBufBytes(Arg) + 16;
      ADepths.Add(Result);
      AKinds.Add(akRecCall);
      Continue;
    end;

    { Interface-returning call argument (Show(MakeFoo(42))): the callee hands
      back an OWNED (+1) fat pointer that the borrowing parameter does not
      release.  Hoist it here so EmitHoistEpilogue can release the obj after the
      call (mirrors akStrConsume).  EmitIntfSretCall leaves the fat pointer at
      (%rsp) over a 16-byte buffer: obj@0, itab@8.  Save it as a contiguous
      16-byte pair (itab pushed first, obj on top); depth records the obj. }
    if (not IsVarPos) and
       ((Arg is TFuncCallExpr) or (Arg is TMethodCallExpr)) and
       (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TFuncCallExpr then
        Self.EmitIntfSretCall(TFuncCallExpr(Arg))
      else
        Self.EmitIntfSretMethodCall(TMethodCallExpr(Arg));
      Self.Emit(#9'movq (%rsp), %rax');     { obj }
      Self.Emit(#9'movq 8(%rsp), %rcx');    { itab }
      Self.Emit(#9'addq $16, %rsp');        { drop the sret buffer }
      Self.Emit(#9'pushq %rcx');            { save itab }
      Self.Emit(#9'pushq %rax');            { save obj (on top) }
      Result := Result + 16;
      ADepths.Add(Result);
      AKinds.Add(akIntfConsume);
      Continue;
    end;

    { Const-string argument needing caller protection. }
    ConstStr := False;
    if Par <> nil then
      ConstStr := Par.IsConstParam and (Par.ResolvedType <> nil) and
                  (Par.ResolvedType.Kind = tyString)
    else if PP <> nil then
      ConstStr := PP.IsConstParam and (PP.TypeDesc <> nil) and
                  (PP.TypeDesc.Kind = tyString)
    else if not AKnownSig then
      { Unknown signature: the implementing method's const-ness is invisible,
        so protect every string-typed value argument by shape.  Pin/consume
        are safe for value params too (the callee pair nets to zero on top). }
      ConstStr := (not IsVarPos) and (Arg.ResolvedType <> nil) and
                  (Arg.ResolvedType.Kind = tyString);
    if ConstStr then
    begin
      Mode := Self.ConstStrShape(Arg, PinPlain);
      if Mode <> camBorrowed then
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
        if Mode = camPin then
        begin
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _StringAddRef');
        end;
        Result := Result + 8;
        ADepths.Add(Result);
        if Mode = camPin then
          AKinds.Add(akStrPin)
        else
          AKinds.Add(akStrConsume);
        Continue;
      end;
    end;

    ADepths.Add(-1);
    AKinds.Add(akNone);
  end;
end;

procedure TX86_64Backend.EmitHoistEpilogue(AArgs: TObjectList;
  ADepths: TList<Integer>; AKinds: TList<Integer>; ATotal, ABase: Integer;
  AReclaim: Boolean);
var
  I, K, Off: Integer;
  HasWork: Boolean;
begin
  HasWork := False;
  for I := 0 to AKinds.Count - 1 do
    if AKinds.Get(I) >= akRecCall then
      HasWork := True;
  if HasWork then
  begin
    { Preserve the call's return registers across the release calls:
      %rax/%rdx (int and two-reg record returns), %xmm0/%xmm1 (float and
      SSE-class record returns).  %rbx is the record-release scratch. }
    Self.Emit(#9'subq $40, %rsp');
    Self.Emit(#9'movq %rax, 0(%rsp)');
    Self.Emit(#9'movq %rdx, 8(%rsp)');
    Self.Emit(#9'movq %rbx, 16(%rsp)');
    Self.Emit(#9'movsd %xmm0, 24(%rsp)');
    Self.Emit(#9'movsd %xmm1, 32(%rsp)');
    for I := 0 to AKinds.Count - 1 do
    begin
      K := AKinds.Get(I);
      if K < akRecCall then Continue;
      Off := 40 + ABase + ATotal - ADepths.Get(I);
      if (K = akStrPin) or (K = akStrConsume) then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Off]));
        Self.Emit(#9'callq _StringRelease');
      end
      else if K = akIntfConsume then
      begin
        { Release the owned (+1) obj of a hoisted interface-call argument. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Off]));
        Self.Emit(#9'callq _ClassRelease');
      end
      else
      begin
        { Hoisted record temp: release its managed fields; the buffer
          itself is stack memory reclaimed below. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rbx', [Off]));
        Self.EmitRecordFieldReleases(
          TRecordTypeDesc(TASTExpr(AArgs.Items[I]).ResolvedType), '%rbx');
      end;
    end;
    Self.Emit(#9'movq 0(%rsp), %rax');
    Self.Emit(#9'movq 8(%rsp), %rdx');
    Self.Emit(#9'movq 16(%rsp), %rbx');
    Self.Emit(#9'movsd 24(%rsp), %xmm0');
    Self.Emit(#9'movsd 32(%rsp), %xmm1');
    Self.Emit(#9'addq $40, %rsp');
  end;
  if AReclaim and (ATotal + ABase > 0) then
    Self.Emit(Format(#9'addq $%d, %%rsp', [ATotal + ABase]));
end;

procedure TX86_64Backend.EmitArgPush(APar: TMethodParam; AArg: TASTExpr;
  ATotal, ADepth, AKind: Integer; var APushed: Integer);
begin
  if AKind = akOALit then
  begin
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));
    Self.Emit(#9'pushq %rax');
    Self.Emit(Format(#9'pushq $%d',
      [TArrayLiteralExpr(AArg).Elements.Count - 1]));
    APushed := APushed + 16;
    Exit;
  end;
  if AKind = akIntfConsume then
  begin
    { Hoisted interface-returning-call argument: the saved 16-byte fat pointer
      has obj on top (at depth) and itab just below.  Push both as the two
      interface arg slots (obj first, itab on top), matching the layout
      EmitMethodArgPush emits for an interface argument. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));         { obj }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rcx',
      [ATotal - ADepth + APushed + 8]));     { itab }
    Self.Emit(#9'pushq %rax');               { push obj }
    Self.Emit(#9'pushq %rcx');               { push itab }
    APushed := APushed + 16;
    Exit;
  end;
  if AKind >= akRecCall then
  begin
    { Hoisted record-call or const-string argument: reload the saved value. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
      [ATotal - ADepth + APushed]));
    Self.Emit(#9'pushq %rax');
    APushed := APushed + 8;
    Exit;
  end;
  Self.EmitMethodArgPush(APar, AArg);
  if (APar <> nil) and (APar.IsOpenArray or
     ((APar.ResolvedType <> nil) and (APar.ResolvedType.Kind = tyInterface))) then
    APushed := APushed + 16
  else
    APushed := APushed + 8;
end;

procedure TX86_64Backend.BeginCallArgs(AParams: TObjectList; AArgs: TObjectList);
var
  F: TOALCallFrame;
begin
  F := TOALCallFrame.Create();
  F.Args := AArgs;
  F.Total := Self.EmitArgHoist(AParams, nil, True, '', AArgs, F.Depths, F.Kinds);
  FOALFrames.Add(F);
end;

procedure TX86_64Backend.PushCallArg(APar: TMethodParam; AArg: TASTExpr;
  AIndex: Integer);
var
  F: TOALCallFrame;
  Depth: Integer;
  Kind: Integer;
  Pushed: Integer;
begin
  F := FOALFrames.Get(FOALFrames.Count - 1);
  if AIndex < F.Depths.Count then
  begin
    Depth := F.Depths.Get(AIndex);
    Kind := F.Kinds.Get(AIndex);
  end
  else
  begin
    Depth := -1;
    Kind := akNone;
  end;
  Pushed := F.Pushed;
  Self.EmitArgPush(APar, AArg, F.Total, Depth, Kind, Pushed);
  F.Pushed := Pushed;
end;

procedure TX86_64Backend.EndCallArgs;
var
  F: TOALCallFrame;
begin
  F := FOALFrames.Get(FOALFrames.Count - 1);
  FOALFrames.Delete(FOALFrames.Count - 1);
  Self.EmitHoistEpilogue(F.Args, F.Depths, F.Kinds, F.Total, 0, True);
  F.Free();
end;

{ Emit a direct call.  SysV AMD64: integer args in rdi/rsi/rdx/rcx/r8/r9;
  float args in xmm0..xmm5 (independent counters).  Stack args (args 7+ in
  total, after registers are exhausted) go right-to-left.  For M6 the common
  cases are:
    - all-integer params: existing push/pop strategy (up to 8 args).
    - all-float params: evaluate left-to-right into %xmm0..%xmmN directly.
    - mixed int+float params (e.g. _SysWriteDouble): evaluate left-to-right;
      integer args push to stack then pop to int regs; float args evaluated
      directly into xmm regs.  All args must fit in registers (≤6 each). }
procedure TX86_64Backend.EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                                  AArgs: TObjectList);
var
  I:              Integer;
  Arg:            TASTExpr;
  IsVar:          Boolean;
  IsOA:           Boolean;
  ParamType:      TTypeDesc;
  HasFloat:       Boolean;
  SlotCount:      Integer;
  IntIdx, XmmIdx: Integer;
  AllocSz, SlotOff: Integer;
  OverflowBytes:  Integer;
  CleanUp:        Integer;
  OALD:           TList<Integer>;
  OALK:           TList<Integer>;
  OALTotal:       Integer;
  OALPushed:      Integer;
  OverflowOffs:   TList<Integer>;  { source offsets of integer-overflow slots,
                                     in ascending arg order, for relocation }
  RK, RSrc, RDst: Integer;
begin
  { Detect whether any arg is float-typed.
    Also compute SlotCount: open-array args expand to 2 register slots each. }
  HasFloat  := False;
  SlotCount := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsOA := (ADecl <> nil) and (I < ADecl.Params.Count) and
            TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    ParamType := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := Arg.ResolvedType;
    if IsFloatFamily(ParamType) and not IsVar then
      HasFloat := True;
    if IsOA or ((not IsVar) and (ParamType <> nil) and
                (ParamType.Kind = tyInterface)) then
      Inc(SlotCount, 2)
    else
      Inc(SlotCount);
  end;

  { Count implicit captured-var pointer args (prepended before normal args). }
  if (ADecl <> nil) and (ADecl.CapturedVars <> nil) then
    Inc(SlotCount, ADecl.CapturedVars.Count);

  OverflowBytes := 0;

  { Hoist open-array literal blocks, record-call argument buffers and
    pinned const-string values before any slot push / slot store (see
    EmitArgHoist).  EmitHoistEpilogue after the call releases and reclaims. }
  OALD := TList<Integer>.Create();
  OALK := TList<Integer>.Create();
  OverflowOffs := TList<Integer>.Create();
  if ADecl <> nil then
    OALTotal := Self.EmitArgHoist(ADecl.Params, nil, True, '', AArgs, OALD, OALK)
  else
    OALTotal := Self.EmitArgHoist(nil, nil, True, '', AArgs, OALD, OALK);
  OALPushed := 0;

  if (not HasFloat) and (SlotCount <= 6) then
  begin
    { Pure integer call with ≤6 slots: push/pop strategy.
      Open-array arg A pushes: data ptr first, then high index.
      SlotCount counts register slots after expansion. }

    { Push captured-var addresses as implicit leading args. }
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) and
       (ADecl.CapturedVars.Count > 0) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if Self.IsCaptured(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'pushq %s',
            [Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]))
        else if Self.IsLocal(ADecl.CapturedVars.Strings[I]) then
        begin
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(ADecl.CapturedVars.Strings[I])]));
          Self.Emit(#9'pushq %rax');
        end
        else
        begin
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [ADecl.CapturedVars.Strings[I]]));
          Self.Emit(#9'pushq %rax');
        end;
        OALPushed := OALPushed + 8;
      end;

    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      IsOA  := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      { Recompute the param type per argument — the counting loop above
        leaves ParamType holding the LAST argument's type. }
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if (not IsOA) and (OALK.Get(I) = akIntfConsume) then
      begin
        { Hoisted interface-returning-call argument — reload the saved 16-byte
          fat pointer (obj on top at depth, itab just below) and push both as
          the two interface arg slots (obj first, itab on top). }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [OALTotal - OALD.Get(I) + OALPushed]));        { obj }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rcx',
          [OALTotal - OALD.Get(I) + OALPushed + 8]));    { itab }
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'pushq %rcx');
      end
      else if (not IsOA) and (OALK.Get(I) >= akRecCall) then
      begin
        { Hoisted record-call or const-string argument — reload the saved
          value from the pre-pass region. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [OALTotal - OALD.Get(I) + OALPushed]));
        Self.Emit(#9'pushq %rax');
      end
      else if IsOA then
      begin
        if Arg is TArrayLiteralExpr then
        begin
          { Hoisted in the pre-pass — reload the saved data pointer. }
          Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
            [OALTotal - OALD.Get(I) + OALPushed]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TArrayLiteralExpr(Arg).Elements.Count - 1]));
        end
        else if (Arg is TIdentExpr) and
                (TIdentExpr(Arg).ResolvedType <> nil) and
                (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
        begin
          if Self.IsLocal(TIdentExpr(Arg).Name) then
            Self.Emit(Format(#9'leaq %s, %%rax',
              [Self.VarOperand(TIdentExpr(Arg).Name)]))
          else if TIdentExpr(Arg).ConstArraySymbol <> '' then
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [NativeMangle(TIdentExpr(Arg).ConstArraySymbol)]))
          else
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [TIdentExpr(Arg).Name]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound]));
        end
        else if (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyDynArray) then
        begin
          { Dynamic array coerced to open-array: push data ptr +
            (runtime length - 1) as the high index. }
          Self.EmitExprToEax(Arg);          { data ptr -> %rax }
          Self.Emit(#9'pushq %rax');         { push ptr }
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');          { high = length - 1 }
          Self.Emit(#9'pushq %rax');         { push high }
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
          Self.Emit(#9'pushq %rax');
        end;
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(#9'pushq %rax');
      end
      else if (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        if (ADecl <> nil) and (I < ADecl.Params.Count) then
          Self.EmitMethodArgPush(TMethodParam(ADecl.Params.Items[I]), Arg)
        else if Arg is TFieldAccessExpr then
        begin
          Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else if Arg is TIdentExpr then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end
        else
          raise ENativeCodeGenError.Create(
            'native backend: unsupported interface arg expression in EmitCall');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
      { Track bytes pushed so far — hoisted-literal reloads above are
        %rsp-relative.  Mirrors the slot widths of the branches. }
      if IsOA or ((not IsVar) and (ParamType <> nil) and
                  (ParamType.Kind = tyInterface)) then
        OALPushed := OALPushed + 16
      else
        OALPushed := OALPushed + 8;
    end;

    for I := SlotCount - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I));
  end
  else
  begin
    { >6 integer slots or mixed int/float call.  Pre-allocate strategy:
      1. Allocate SC×8 bytes on the stack (16-byte aligned).
      2. Evaluate each arg left-to-right into slot[I] at I×8(%rsp).
      3. Load the first 6 int args into SysV int regs, first 8 float args
         into xmm regs; overflow int args stay on the stack.
      4. Adjust %rsp so the overflow args sit at the top. }

    AllocSz := ((SlotCount * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    { Evaluate captured-var addresses into the first slots. }
    SlotOff := 0;
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) and
       (ADecl.CapturedVars.Count > 0) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if Self.IsCaptured(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]))
        else if Self.IsLocal(ADecl.CapturedVars.Strings[I]) then
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(ADecl.CapturedVars.Strings[I])]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [ADecl.CapturedVars.Strings[I]]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end;

    { Evaluate each arg left-to-right into its slot. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      IsOA  := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;

      if (not IsOA) and (OALK.Get(I) >= akRecCall) then
      begin
        { Hoisted record-call or const-string argument — reload the saved
          value from above the slot block. }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + OALTotal - OALD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end
      else if IsOA then
      begin
        if Arg is TArrayLiteralExpr then
        begin
          { Hoisted in the pre-pass — the saved data pointer sits above the
            slot block allocated by the subq just before this loop. }
          Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
            [AllocSz + OALTotal - OALD.Get(I)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq $%d, %d(%%rsp)',
            [TArrayLiteralExpr(Arg).Elements.Count - 1, SlotOff]));
          Inc(SlotOff, 8);
        end
        else if (Arg is TIdentExpr) and
                (TIdentExpr(Arg).ResolvedType <> nil) and
                (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
        begin
          if Self.IsLocal(TIdentExpr(Arg).Name) then
            Self.Emit(Format(#9'leaq %s, %%rax',
              [Self.VarOperand(TIdentExpr(Arg).Name)]))
          else if TIdentExpr(Arg).ConstArraySymbol <> '' then
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [NativeMangle(TIdentExpr(Arg).ConstArraySymbol)]))
          else
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [TIdentExpr(Arg).Name]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq $%d, %d(%%rsp)',
            [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound,
             SlotOff]));
          Inc(SlotOff, 8);
        end
        else if (Arg.ResolvedType <> nil) and
                (Arg.ResolvedType.Kind = tyDynArray) then
        begin
          { Dynamic array coerced to open-array: store data ptr +
            (runtime length - 1) as the high index. }
          Self.EmitExprToEax(Arg);          { data ptr -> %rax }
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');          { high = length - 1 }
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end;
      end
      else if IsFloatFamily(ParamType) and not IsVar then
      begin
        Self.EmitExprToXmm0(Arg);
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
        begin
          if (Arg.ResolvedType = nil) or (Arg.ResolvedType.Kind <> tySingle) then
            Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [SlotOff]));
        end
        else
        begin
          if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tySingle) then
            Self.Emit(#9'cvtss2sd %xmm0, %xmm0');
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [SlotOff]));
        end;
        Inc(SlotOff, 8);
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end
      else if (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        if (ADecl <> nil) and (I < ADecl.Params.Count) then
        begin
          Self.EmitExprToEax(Arg);
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          { Interface itab — for a simple ident, load from itab slot. }
          if Arg is TIdentExpr then
            Self.Emit(Format(#9'movq %s, %%rax',
              [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]))
          else
            Self.Emit(#9'xorq %rax, %rax');
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else if Arg is TFieldAccessExpr then
        begin
          Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(Format(#9'movq %%rcx, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(#9'movq 8(%rax), %rcx');
          Self.Emit(Format(#9'movq %%rcx, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else if Arg is TIdentExpr then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
          Inc(SlotOff, 8);
        end
        else
          raise ENativeCodeGenError.Create(
            'native backend: unsupported interface arg expression in EmitCall');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
        Inc(SlotOff, 8);
      end;
    end;

    { Pass 2: load from slots into registers.  Integer args use separate
      IntIdx (0..5 → registers, ≥6 → leave on stack), float args use
      XmmIdx (0..7 → xmm registers).  We read slots in order and load
      the register-bound ones; overflow int args must end up at (%rsp)
      in forward order after we remove the register-bound region. }

    { First, load the register-bound args.  Captured vars occupy the
      first slots; normal args follow. }
    IntIdx := 0;
    XmmIdx := 0;
    SlotOff := 0;
    if (ADecl <> nil) and (ADecl.CapturedVars <> nil) then
      for I := 0 to ADecl.CapturedVars.Count - 1 do
      begin
        if IntIdx < 6 then
        begin
          Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
          Inc(IntIdx);
        end;
        Inc(SlotOff, 8);
      end;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      IsOA := (ADecl <> nil) and (I < ADecl.Params.Count) and
              TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;

      if IsFloatFamily(ParamType) and not IsOA and not IsVar then
      begin
        if XmmIdx < 8 then
        begin
          if (ParamType <> nil) and (ParamType.Kind = tySingle) then
            Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
          else
            Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
          Inc(XmmIdx);
        end;
        Inc(SlotOff, 8);
      end
      else
      begin
        if IsOA then
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end
        else if (ParamType <> nil) and (ParamType.Kind = tyInterface) and
                not IsVar then
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end
        else
        begin
          if IntIdx < 6 then
          begin
            Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
            Inc(IntIdx);
          end
          else
            OverflowOffs.Add(SlotOff);
          Inc(SlotOff, 8);
        end;
      end;
    end;

    { If nothing overflowed, reclaim the entire pre-allocated area.  Otherwise
      relocate the integer-overflow slots to the TOP of the region (highest
      offsets, just below the hoist area) in ascending arg order, then raise
      %rsp past the vacated low space so the call sees the overflow at
      0(%rsp).. with the lowest-indexed overflow arg first (System V order).
      Relocation runs highest-target-first so a target never clobbers a source
      that has not been moved yet.  Float args never overflow (they always take
      an xmm register, of which there are 8), so only integer slots appear here.

      This replaces a former `addq $48` shortcut that assumed exactly the first
      six contiguous slots were register-bound; with floats interspersed fewer
      integer slots precede the overflow, so that shortcut placed the overflow
      at the wrong address and crashed the callee. }
    if OverflowOffs.Count = 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [AllocSz]))
    else
    begin
      { Reserve a 16-byte-aligned overflow region at the top of the allocation
        so that, after raising %rsp to its base, the call sees a 16-aligned
        %rsp (System V requires it at the call site).  The overflow args
        occupy the low Count*8 bytes of that region. }
      OverflowBytes := ((OverflowOffs.Count * 8 + 15) and (-16));
      for RK := OverflowOffs.Count - 1 downto 0 do
      begin
        RSrc := OverflowOffs.Get(RK);
        RDst := (AllocSz - OverflowBytes) + RK * 8;
        if RSrc <> RDst then
        begin
          Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [RSrc]));
          Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [RDst]));
        end;
      end;
      if AllocSz > OverflowBytes then
        Self.Emit(Format(#9'addq $%d, %%rsp', [AllocSz - OverflowBytes]));
    end;
  end;

  Self.Emit(#9'callq ' + AFuncSym);
  Self.EmitHoistEpilogue(AArgs, OALD, OALK, OALTotal, OverflowBytes, True);
  OALD.Free();
  OALK.Free();
  OverflowOffs.Free();
end;

{ Spill the incoming argument register at index AIdx into the param slot
  AOperand, using the register sub-view matching the param's width. }
procedure TX86_64Backend.EmitSpillArg(AIdx: Integer; const AOperand: string;
                                      AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %s, %s', [SysVArgRegs8[AIdx],  AOperand]));
    2: Self.Emit(Format(#9'movw %s, %s', [SysVArgRegs16[AIdx], AOperand]));
    8: Self.Emit(Format(#9'movq %s, %s', [SysVArg64(AIdx), AOperand]));
  else
    Self.Emit(Format(#9'movl %s, %s', [SysVArgRegs[AIdx], AOperand]));
  end;
end;

{ Emit a call through a bare function pointer held in APtrOperand (an AT&T
  memory operand).  Loads the pointer into %r10 (caller-saved scratch, not
  clobbered by arg evaluation in %rax), sets up args exactly as EmitCall does,
  then dispatches via `callq *%r10`.  AProcType supplies the param signature
  for var/out param detection; nil means all value params. }
procedure TX86_64Backend.EmitCallIndirect(const APtrOperand: string;
                                          AProcType: TProceduralTypeDesc;
                                          AArgs: TObjectList);
var
  I:        Integer;
  Arg:      TASTExpr;
  IsVar:    Boolean;
  AllocSz:  Integer;
  SlotOff:  Integer;
  CleanUp:  Integer;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  PParams:  TObjectList;
begin
  PParams := nil;
  if AProcType <> nil then
    PParams := AProcType.Params;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(nil, PParams, True, '', AArgs, HD, HK);
  { The function pointer is loaded into %r10 only AFTER all argument
    evaluation: %r10 is caller-saved, so any call emitted while evaluating
    an argument (or the hoist pre-pass above) would clobber it.
    APtrOperand is %rbp- or %rip-relative, never %rsp-relative. }

  if AArgs.Count <= 6 then
  begin
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (AProcType <> nil) and (I < AProcType.Params.Count) and
               TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [HTotal - HD.Get(I) + I * 8]));
        Self.Emit(#9'pushq %rax');
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(#9'pushq %rax');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;
    for I := AArgs.Count - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I));
    Self.Emit(Format(#9'movq %s, %%r10', [APtrOperand]));
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { >6 args: pre-allocate strategy with %r10 holding the function ptr. }
    AllocSz := ((AArgs.Count * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    SlotOff := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (AProcType <> nil) and (I < AProcType.Params.Count) and
               TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else if IsVar then
        Self.EmitVarArgAddrToRax(Arg)
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
      Inc(SlotOff, 8);
    end;
    for I := 0 to 5 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [I * 8, SysVArg64(I)]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    CleanUp := AllocSz - 6 * 8;
    Self.Emit(Format(#9'movq %s, %%r10', [APtrOperand]));
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end;
  HD.Free();
  HK.Free();
end;

{ Call a procedural-typed class field through a receiver — emits:
    <push each arg>
    movq <receiver>, %rax ; addq $Offset, %rax   ; %rax = field slot
    movq 8(%rax), %rdi   (of object only: Data -> first arg)
    movq (%rax), %r10    ; code pointer
    popq <arg regs>      ; callq *%r10 }
procedure TX86_64Backend.EmitProcFieldCall(AObjExpr: TASTExpr;
  const AObjectName: string; AIsVarParam: Boolean; AFieldInfo: TFieldInfo;
  AProcType: TProceduralTypeDesc; AArgs: TObjectList; AResultType: TTypeDesc);
var
  I:       Integer;
  Arg:     TASTExpr;
  IsVar:   Boolean;
  IsMeth:  Boolean;
  Slots:   Integer;
  HD:      TList<Integer>;
  HK:      TList<Integer>;
  HTotal:  Integer;
begin
  IsMeth := (AProcType <> nil) and AProcType.IsMethodPtr;
  { A method pointer consumes %rdi for the captured Data (Self), leaving five
    argument registers; a plain function pointer leaves all six.  Anything
    larger would need the stack-overflow argument strategy — fail loudly
    rather than emit a silently wrong call. }
  if IsMeth then Slots := AArgs.Count + 1 else Slots := AArgs.Count;
  if Slots > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: procedural-field call with >6 argument slots is not supported');

  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  try
    HTotal := Self.EmitArgHoist(nil, AProcType.Params, True, '', AArgs, HD, HK);
    { Evaluate args left-to-right and push them.  var/out positions push the
      argument's address; record-call/string args are reloaded from the hoist
      region. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (I < AProcType.Params.Count) and
               TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [HTotal - HD.Get(I) + I * 8]));
        Self.Emit(#9'pushq %rax');
      end
      else if IsVar then
      begin
        Self.EmitVarArgAddrToRax(Arg);
        Self.Emit(#9'pushq %rax');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;

    { Load the receiver instance pointer into %rax.  This must be call-free so
      it cannot clobber the already-pushed arguments. }
    if AObjExpr <> nil then
    begin
      if (AObjExpr is TIdentExpr) or (AObjExpr is TFieldAccessExpr) then
        Self.EmitExprToEax(AObjExpr)
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported receiver expression in procedural-field call');
    end
    else if AIsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(AObjectName)]));
      Self.Emit(#9'movq (%rax), %rax');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(AObjectName)]));

    { %rax now holds the instance pointer; advance to the field slot (the code
      pointer for a plain function pointer, or the 16-byte (Code, Data) block
      for a method pointer). }
    if AFieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rax', [AFieldInfo.Offset]));

    if IsMeth then
    begin
      Self.Emit(#9'movq 8(%rax), %rdi');   { Data (Self) -> first argument }
      Self.Emit(#9'movq (%rax), %r10');    { Code pointer }
      for I := AArgs.Count - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArg64(I + 1));
    end
    else
    begin
      Self.Emit(#9'movq (%rax), %r10');    { Code pointer }
      for I := AArgs.Count - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArg64(I));
    end;
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  finally
    HD.Free();
    HK.Free();
  end;

  { Normalise the (32-bit-ABI) return value to the field signature's return
    width.  Statement calls pass nil and need no result. }
  if AResultType <> nil then
    Self.EmitNarrowToType(AResultType);
end;

procedure TX86_64Backend.EmitLocalRecordBase(const AName, AReg: string);
begin
  if FSretFunc and SameText(AName, 'Result') then
    { sret Result: the slot holds the caller's buffer POINTER. }
    Self.Emit(Format(#9'movq %s, %s', [Self.VarOperand('Result'), AReg]))
  else
    { Ordinary local value record: the slot IS the record. }
    Self.Emit(Format(#9'leaq %s, %s', [Self.VarOperand(AName), AReg]));
end;

procedure TX86_64Backend.EmitFieldAddrToRcx(AFA: TFieldAccessExpr);
begin
  if AFA.Base <> nil then
  begin
    Self.EmitExprToEax(AFA.Base);
    Self.Emit(#9'movq %rax, %rcx');
  end
  else if AFA.IsImplicitSelf then
  begin
    Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
    if (AFA.ImplicitBaseInfo <> nil) and (AFA.ImplicitBaseInfo.Offset > 0) then
      Self.Emit(Format(#9'addq $%d, %%rcx', [AFA.ImplicitBaseInfo.Offset]));
    if AFA.IsClassAccess then
      Self.Emit(#9'movq (%rcx), %rcx');
  end
  else if AFA.IsClassAccess then
  begin
    Self.EmitVarBaseToReg(AFA.RecordName, False, '%rcx');
    if AFA.IsVarParam then
      { var-param class: slot -> caller var -> instance }
      Self.Emit(#9'movq (%rcx), %rcx');
  end
  else if AFA.IsVarParam then
  begin
    Self.EmitVarBaseToReg(AFA.RecordName, False, '%rcx');
  end
  else Self.EmitVarBaseToReg(AFA.RecordName, True, '%rcx');
  if AFA.FieldInfo.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %%rcx', [AFA.FieldInfo.Offset]));
end;

{ Emit a call to a record-returning function using the sret convention.
  ASretAddr is the AT&T operand for the destination buffer already allocated
  by the caller.  Strategy:
    1. leaq ASretAddr → %r10  (save addr before arg eval clobbers %rax/%rdi)
    2. Evaluate each normal arg (push/pop strategy for integer args)
    3. Pop into %rsi/%rdx/... (index 1..N)
    4. movq %r10, %rdi  (hidden first arg = sret ptr)
    5. callq AFuncSym
  All args must be integer-family value params (≤5 since %rdi is taken by sret). }

procedure TX86_64Backend.EmitRecordReturnEpilogue(ARec: TRecordTypeDesc;
  AClass: TRecReturnClass);
var
  ResOp: string;
  Sz: Integer;
begin
  ResOp := Self.VarOperand('Result');
  Sz := ARec.TotalSize();
  case AClass of
    rcInt1:
      begin
        Self.Emit(Format(#9'leaq %s, %%rax', [ResOp]));
        case Sz of
          1: Self.Emit(#9'movzbl (%rax), %eax');
          2: Self.Emit(#9'movzwl (%rax), %eax');
          4: Self.Emit(#9'movl (%rax), %eax');
          8: Self.Emit(#9'movq (%rax), %rax');
        end;
      end;
    rcInt2:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movq (%rcx), %rax');
        Self.Emit(#9'movq 8(%rcx), %rdx');
      end;
    rcSSE1:
      begin
        if Sz = 4 then
          Self.Emit(Format(#9'movss %s, %%xmm0', [ResOp]))
        else
          Self.Emit(Format(#9'movsd %s, %%xmm0', [ResOp]));
      end;
    rcSSE2:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movsd (%rcx), %xmm0');
        Self.Emit(#9'movsd 8(%rcx), %xmm1');
      end;
    rcIntSSE:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movq (%rcx), %rax');
        Self.Emit(#9'movsd 8(%rcx), %xmm0');
      end;
    rcSSEInt:
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [ResOp]));
        Self.Emit(#9'movsd (%rcx), %xmm0');
        Self.Emit(#9'movq 8(%rcx), %rax');
      end;
  end;
end;

procedure TX86_64Backend.EmitRecordRegReturnCapture(const ADestAddr: string;
  ARec: TRecordTypeDesc; AClass: TRecReturnClass; AIsIndirect: Boolean);
var
  Sz:      Integer;
  LoadOp:  string;
begin
  Sz := ARec.TotalSize();
  if AIsIndirect then
    LoadOp := 'movq'
  else
    LoadOp := 'leaq';
  case AClass of
    rcInt1:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        case Sz of
          1: Self.Emit(#9'movb %al, (%rcx)');
          2: Self.Emit(#9'movw %ax, (%rcx)');
          4: Self.Emit(#9'movl %eax, (%rcx)');
          8: Self.Emit(#9'movq %rax, (%rcx)');
        end;
      end;
    rcInt2:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movq %rax, (%rcx)');
        Self.Emit(#9'movq %rdx, 8(%rcx)');
      end;
    rcSSE1:
      begin
        if AIsIndirect then
        begin
          Self.Emit(Format(#9'movq %s, %%rcx', [ADestAddr]));
          if Sz = 4 then
            Self.Emit(#9'movss %xmm0, (%rcx)')
          else
            Self.Emit(#9'movsd %xmm0, (%rcx)');
        end
        else
        begin
          if Sz = 4 then
            Self.Emit(Format(#9'movss %%xmm0, %s', [ADestAddr]))
          else
            Self.Emit(Format(#9'movsd %%xmm0, %s', [ADestAddr]));
        end;
      end;
    rcSSE2:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movsd %xmm0, (%rcx)');
        Self.Emit(#9'movsd %xmm1, 8(%rcx)');
      end;
    rcIntSSE:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movq %rax, (%rcx)');
        Self.Emit(#9'movsd %xmm0, 8(%rcx)');
      end;
    rcSSEInt:
      begin
        Self.Emit(Format(#9'%s %s, %%rcx', [LoadOp, ADestAddr]));
        Self.Emit(#9'movsd %xmm0, (%rcx)');
        Self.Emit(#9'movq %rax, 8(%rcx)');
      end;
  end;
end;

{ Number of integer-register SLOTS the explicit args of an sret free-function
  call occupy, expanding interface params to two (obj + itab).  Used to pick the
  register vs stack-spill path and to drive the pop loop. }
function TX86_64Backend.SretUserSlots(ADecl: TMethodDecl;
                                      AArgs: TObjectList): Integer;
var
  I: Integer;
  PT: TTypeDesc;
  IsVar: Boolean;
begin
  Result := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    PT := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      PT := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if PT = nil then
      PT := TASTExpr(AArgs.Items[I]).ResolvedType;
    if (not IsVar) and (PT <> nil) and (PT.Kind = tyInterface) then
      Inc(Result, 2)
    else
      Inc(Result);
  end;
end;

procedure TX86_64Backend.EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                                      AArgs: TObjectList; const ASretAddr: string;
                                      ASretIsIndirect: Boolean);
var
  I:        Integer;
  Arg:      TASTExpr;
  IsVar:    Boolean;
  AllocSz:  Integer;
  CleanUp:  Integer;
  RC:       TRecReturnClass;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  HasFloat: Boolean;
  ParamType: TTypeDesc;
  IntIdx, XmmIdx, SlotOff: Integer;
  ArgPushed: Integer;
begin
  { Check if the callee returns a small POD record via registers. }
  RC := rcSret;
  if (ADecl <> nil) and (ADecl.ResolvedReturnType <> nil) and
     (ADecl.ResolvedReturnType.Kind = tyRecord) then
    RC := ClassifyRecordReturn(TRecordTypeDesc(ADecl.ResolvedReturnType));
  if RC <> rcSret then
  begin
    { Reg-return: zero the dest buffer, call without hidden sret param,
      capture return registers into the dest buffer. }
    if ASretIsIndirect then
      Self.Emit(Format(#9'movq %s, %%r10', [ASretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%r10', [ASretAddr]));
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [TRecordTypeDesc(ADecl.ResolvedReturnType).TotalSize()]));
    Self.Emit(#9'callq memset');
    Self.EmitCall(AFuncSym, ADecl, AArgs);
    Self.EmitRecordRegReturnCapture(ASretAddr,
      TRecordTypeDesc(ADecl.ResolvedReturnType), RC, ASretIsIndirect);
    Exit;
  end;
  { Save the destination address on the stack, below the hoist region:
    no caller-saved register survives argument evaluation, and a
    %rsp-relative ASretAddr (e.g. '(%rsp)') would drift once the region is
    live.  When ASretIsIndirect the operand holds a pointer to the buffer
    (sret forwarding) — load it with movq. }
  if ASretIsIndirect then
    Self.Emit(Format(#9'movq %s, %%rax', [ASretAddr]))
  else
    Self.Emit(Format(#9'leaq %s, %%rax', [ASretAddr]));
  Self.Emit(#9'pushq %rax');
  { Zero the destination buffer via memset(dest, 0, size), mirroring the QBE
    backend.  The return type is a record or a jumbo set here; RawSize covers
    both (TotalSize for a record, the bitmap byte count for a jumbo set). }
  if (ADecl <> nil) and (ADecl.ResolvedReturnType <> nil) then
  begin
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [ADecl.ResolvedReturnType.RawSize()]));
    Self.Emit(#9'callq memset');
  end;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  if ADecl <> nil then
    HTotal := Self.EmitArgHoist(ADecl.Params, nil, True, '', AArgs, HD, HK)
  else
    HTotal := Self.EmitArgHoist(nil, nil, True, '', AArgs, HD, HK);
  { Detect a float-typed by-value argument: the integer push/pop path below
    cannot carry one (it would route the float through %rax and an integer arg
    register).  When present, use the slot-based scheme that places each float
    arg in an %xmm register per the SysV ABI (mirrors EmitCall's float path). }
  HasFloat := False;
  for I := 0 to AArgs.Count - 1 do
  begin
    ParamType := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
    if IsFloatFamily(ParamType) and not IsVar then
      HasFloat := True;
  end;

  if HasFloat then
  begin
    { Slot-based: sret = slot 0 (%rdi), explicit args = slots 1..Count.  Each
      arg is evaluated into its 8-byte slot (float via movsd/movss, integer via
      movq), then int slots load into %rsi.. and float slots into %xmm0.., each
      stream counted independently.  Args beyond the 5 int / 8 xmm registers
      would need stack spill — record-returning functions with that many float
      args do not occur yet, so guard the integer overflow loudly via SysVArg64. }
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    { Reload the saved sret dest (pushed just below the hoist region). }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
      end
      else if IsFloatFamily(ParamType) and not IsVar then
      begin
        Self.EmitExprToXmm0(Arg);
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [(I + 1) * 8]))
        else
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [(I + 1) * 8]));
      end
      else
      begin
        if IsVar then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
      end;
    end;
    { Load sret ptr into %rdi, then int args into %rsi.. and float args into
      %xmm0.., each stream advancing its own register index. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    IntIdx := 1;   { %rdi consumed by sret }
    XmmIdx := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      SlotOff := (I + 1) * 8;
      if IsFloatFamily(ParamType) and not IsVar then
      begin
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
        Inc(IntIdx);
      end;
    end;
    { %al = number of vector registers used (SysV varargs/AL convention; the
      callee ignores it for a fixed prototype but the ABI requires it set). }
    Self.Emit(Format(#9'movb $%d, %%al', [XmmIdx]));
    { Drop the (Count+1) register-bound slots so any overflow sits at the top;
      with <=5 args there is no overflow, so this reclaims the whole region
      except the alignment padding. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [(AArgs.Count + 1) * 8]));
    Self.Emit(#9'callq ' + AFuncSym);
    CleanUp := AllocSz - (AArgs.Count + 1) * 8;
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end
  else if Self.SretUserSlots(ADecl, AArgs) <= 5 then
  begin
    { Push each arg's register slot(s) — an interface arg is a fat pointer that
      occupies TWO slots (obj then itab on top), so the push count is the SLOT
      count, not the arg count.  ArgPushed tracks bytes pushed so far so the
      hoisted-value reloads stay correct as %rsp moves. }
    ArgPushed := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if (not IsVar) and (HK.Get(I) = akIntfConsume) then
      begin
        { Hoisted interface-returning-call arg: reload the saved 16-byte fat
          pointer (obj, then itab) and push both slots (obj first, itab on top). }
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + ArgPushed]));
        Self.Emit(Format(#9'movq %d(%%rsp), %%rcx', [HTotal - HD.Get(I) + ArgPushed + 8]));
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'pushq %rcx');
        ArgPushed := ArgPushed + 16;
      end
      else if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + ArgPushed]));
        Self.Emit(#9'pushq %rax');
        ArgPushed := ArgPushed + 8;
      end
      else if (not IsVar) and (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        { Direct interface arg (variable / field): push obj then itab. }
        Self.EmitMethodArgPush(TMethodParam(ADecl.Params.Items[I]), Arg);
        ArgPushed := ArgPushed + 16;
      end
      else
      begin
        if IsVar then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
        ArgPushed := ArgPushed + 8;
      end;
    end;
    { Pop one register per pushed SLOT into %rsi onwards (%rdi is the sret ptr,
      loaded below).  ArgPushed/8 = total slots; topmost slot -> highest reg. }
    for I := (ArgPushed div 8) - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    { The saved dest sits just below the hoist region. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [HTotal]));
    Self.Emit(#9'callq ' + AFuncSym);
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { >5 explicit args + sret: pre-allocate (Count+1) slots (sret = slot 0,
      explicit args = slots 1..Count).  Evaluate, load regs, leave overflow.
      This overflow path assumes one slot per logical arg; an interface arg
      (two slots) is not yet handled here.  Fail loudly rather than silently
      mis-place registers — the <=5-slot path above covers interface args. }
    for I := 0 to AArgs.Count - 1 do
    begin
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(AArgs.Items[I]).ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if (not IsVar) and (ParamType <> nil) and (ParamType.Kind = tyInterface) then
        raise ENativeCodeGenError.Create('native backend: interface argument in ' +
          'an sret call with more than 5 register slots is not yet supported');
    end;
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else if IsVar then
        Self.EmitVarArgAddrToRax(Arg)
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
    end;
    { Load sret ptr into %rdi, first 5 explicit args into %rsi..%r9. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    { Shift %rsp past the 6 register-bound slots (sret + 5 args). }
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    Self.Emit(#9'callq ' + AFuncSym);
    CleanUp := AllocSz - 6 * 8;
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end;
  { Reclaim the saved dest slot. }
  Self.Emit(#9'addq $8, %rsp');
  HD.Free();
  HK.Free();
end;

{ Free a record-call-receiver buffer materialised by EmitMethodSretCall (see
  the RecvBufBytes prologue there).  No-op when ABytes = 0.  Does not touch the
  sret destination (written via its own pointer) nor any return register. }
procedure TX86_64Backend.EmitMethodSretRecvCleanup(ABytes: Integer);
begin
  if ABytes > 0 then
  begin
    { Mirror the prologue's pushes: subq buffer, pushq %rbx, pushq %r14
      (in that order) -> free buffer, popq %rbx, popq %r14. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [ABytes]));
    Self.Emit(#9'popq %rbx');
    Self.Emit(#9'popq %r14');
  end;
end;

{ Emit a method call that returns a record via the sret convention.
  Register layout: %rdi = sret ptr, %rsi = Self, %rdx.. = user args.
  The destination buffer is at ASretAddr (AT&T operand, already allocated). }
procedure TX86_64Backend.EmitMethodSretCall(ACall: TMethodCallExpr;
                                            const ASretAddr: string;
                                            ASretIsIndirect: Boolean;
                                            AForceStatic: Boolean);
var
  I:        Integer;
  MD:       TMethodDecl;
  Sym:      string;
  Arg:      TASTExpr;
  AllocSz:  Integer;
  CleanUp:  Integer;
  RC:       TRecReturnClass;
  HD:       TList<Integer>;
  HK:       TList<Integer>;
  HTotal:   Integer;
  HasFloat: Boolean;
  ParamType: TTypeDesc;
  IntIdx, XmmIdx, SlotOff: Integer;
  RecvBufBytes: Integer;
  LSretAddr: string;
  LSretIndirect: Boolean;
  UserSlots: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: method-sret call has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Record-returning static factory (TypeName.Make(args): TRec): NO implicit
    Self, so it follows the plain record-return ABI exactly — sret buffer in
    %rdi, user args in %rsi.. — which is what EmitSretCall (the free-function
    record-return emitter) already produces.  Delegate to it with the method's
    mangled symbol; the Self-threading code below is for instance methods only. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    Self.EmitSretCall(Sym, MD, ACall.Args, ASretAddr, ASretIsIndirect);
    Exit;
  end;

  { Record-returning-call receiver (e.g. A.Plus(B).Scale(2), where the OUTER
    method Scale itself returns a record via sret): materialise the inner call
    result into a stack buffer up front and carry its address in callee-saved
    %rbx, which survives all the arg-evaluation %rsp movement below.  Every
    ObjExpr-receiver site loads %rbx instead of evaluating the call value as a
    pointer; the buffer + %rbx are freed at each exit (EmitMethodSretCleanup).

    Because this prologue moves %rsp, a caller-supplied %rsp-relative ASretAddr
    (the recursive EmitRecordCallSretAt('(%rsp)') case in a nested chain like
    A.Plus(B).Plus(A)) would drift.  Resolve the destination to an ABSOLUTE
    pointer FIRST, save it in callee-saved %r14, and re-express the rest of the
    routine as an indirect store through %r14. }
  RecvBufBytes := 0;
  LSretAddr := ASretAddr;
  LSretIndirect := ASretIsIndirect;
  if (ACall.ObjExpr <> nil) and MD.IsRecordMethod and
     Self.IsNativeRecordCall(ACall.ObjExpr) then
  begin
    RecvBufBytes := Self.RecArgBufBytes(ACall.ObjExpr);
    { Resolve the destination to an absolute pointer BEFORE pushing anything —
      a %rsp-relative ASretAddr (the recursive EmitRecordCallSretAt('(%rsp)')
      case) must be read while %rsp still has its caller value. }
    if ASretIsIndirect then
      Self.Emit(Format(#9'movq %s, %%rax', [ASretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%rax', [ASretAddr]));
    Self.Emit(#9'pushq %r14');
    Self.Emit(#9'movq %rax, %r14');
    { %r14 now HOLDS the destination address.  Express it as a non-indirect
      operand so consumers do `leaq (%r14), %reg` (i.e. %reg := %r14), not a
      double dereference. }
    LSretAddr := '(%r14)';
    LSretIndirect := False;
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [RecvBufBytes]));
    Self.EmitRecordCallSretAt(ACall.ObjExpr, '(%rsp)');
    Self.Emit(#9'movq %rsp, %rbx');
  end;

  { Check for register-return: no hidden sret param, Self goes in %rdi,
    args in %rsi onwards. }
  RC := rcSret;
  if (MD.ResolvedReturnType <> nil) and
     (MD.ResolvedReturnType.Kind = tyRecord) then
    RC := ClassifyRecordReturn(TRecordTypeDesc(MD.ResolvedReturnType));
  if RC <> rcSret then
  begin
    if LSretIndirect then
      Self.Emit(Format(#9'movq %s, %%r10', [LSretAddr]))
    else
      Self.Emit(Format(#9'leaq %s, %%r10', [LSretAddr]));
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [TRecordTypeDesc(MD.ResolvedReturnType).TotalSize()]));
    Self.Emit(#9'callq memset');
    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;
    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rdi');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rdi), %rdi');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [ACall.ObjectName]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rdi')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %rdi');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand('Self')]));
    { Pop one register per SLOT (interface args take two) into %rsi onwards;
      Self occupies %rdi (slot index 0), so user slots start at index 1. }
    for I := Self.CountArgSlots(MD.Params) - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
    Self.EmitRecordRegReturnCapture(LSretAddr,
      TRecordTypeDesc(MD.ResolvedReturnType), RC, LSretIndirect);
    Self.EmitMethodSretRecvCleanup(RecvBufBytes);
    Exit;
  end;

  { Save the destination address below the hoist region — no caller-saved
    register survives argument evaluation, and a %rsp-relative ASretAddr
    would drift once the region is live. }
  if LSretIndirect then
    Self.Emit(Format(#9'movq %s, %%rax', [LSretAddr]))
  else
    Self.Emit(Format(#9'leaq %s, %%rax', [LSretAddr]));
  Self.Emit(#9'pushq %rax');
  if (MD.ResolvedReturnType <> nil) then
  begin
    Self.Emit(#9'movq (%rsp), %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [MD.ResolvedReturnType.RawSize()]));
    Self.Emit(#9'callq memset');
  end;

  { Detect a float-typed by-value argument.  The integer push/pop path below
    cannot carry one to an %xmm register, so route the whole call through a
    slot-based scheme: sret = slot 0 (%rdi), Self = slot 1 (%rsi), explicit
    args = slots 2..Count+1, int args load into %rdx.. and float args into
    %xmm0.. per the SysV ABI. }
  HasFloat := False;
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ParamType := nil;
    if I < MD.Params.Count then
      ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
    if IsFloatFamily(ParamType) and
       not ((I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam) then
      HasFloat := True;
  end;

  if HasFloat then
  begin
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    AllocSz := (((ACall.Args.Count + 2) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    { sret into slot 0. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    { Evaluate each explicit arg into slot I+2 (float kept in its slot for the
      xmm load below; int/record-ptr via movq). }
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      ParamType := nil;
      if I < MD.Params.Count then
        ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
      end
      else if IsFloatFamily(ParamType) and
              not ((I < MD.Params.Count) and
                   TMethodParam(MD.Params.Items[I]).IsVarParam) then
      begin
        Self.EmitExprToXmm0(Arg);
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [(I + 2) * 8]))
        else
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [(I + 2) * 8]));
      end
      else
      begin
        if (I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam then
          Self.EmitVarArgAddrToRax(Arg)
        else
          Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
      end;
    end;
    { Self pointer into slot 1. }
    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rax');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rax), %rax');
      end
      else if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [ACall.ObjectName]));
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 8(%%rsp)', []));
    { Load registers: %rdi = sret, %rsi = Self, then int args into %rdx.. and
      float args into %xmm0.. }
    Self.Emit(#9'movq 0(%rsp), %rdi');
    Self.Emit(#9'movq 8(%rsp), %rsi');
    IntIdx := 2;   { %rdi (sret), %rsi (Self) consumed }
    XmmIdx := 0;
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ParamType := nil;
      if I < MD.Params.Count then
        ParamType := TMethodParam(MD.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
      SlotOff := (I + 2) * 8;
      if IsFloatFamily(ParamType) and
         not ((I < MD.Params.Count) and TMethodParam(MD.Params.Items[I]).IsVarParam) then
      begin
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArg64(IntIdx)]));
        Inc(IntIdx);
      end;
    end;
    Self.Emit(Format(#9'movb $%d, %%al', [XmmIdx]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [(ACall.Args.Count + 2) * 8]));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'movq (%rsi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      { %al was clobbered by the vtable load; for a fixed prototype the callee
        ignores it, so this is benign. }
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    CleanUp := AllocSz - (ACall.Args.Count + 2) * 8;
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
    Self.Emit(#9'addq $8, %rsp');   { reclaim the saved dest slot }
    Self.EmitMethodSretRecvCleanup(RecvBufBytes);
    Exit;
  end;

  { Register-path guard is on SLOTS, not logical args: an interface argument is
    a fat pointer occupying TWO integer registers, so a 2-arg call can need more
    registers than 2.  sret (%rdi) + Self (%rsi) consume two; the user args must
    fit in the remaining four. }
  UserSlots := Self.CountArgSlots(MD.Params);
  if UserSlots + 2 <= 6 then
  begin
    Self.BeginCallArgs(MD.Params, ACall.Args);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      Self.PushCallArg(TMethodParam(MD.Params.Items[I]), Arg, I);
    end;

    if ACall.ObjectName <> '' then
    begin
      if MD.IsRecordMethod and ACall.IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]))
      else if MD.IsRecordMethod then
      begin
        Self.EmitVarAddr(ACall.ObjectName, '%rsi');
      end
      else if ACall.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]));
        Self.Emit(#9'movq (%rsi), %rsi');
      end
      else
      begin
        if Self.IsLocal(ACall.ObjectName) then
          Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(ACall.ObjectName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rsi', [ACall.ObjectName]));
      end;
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rsi')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
    begin
      Self.EmitExprToEax(ACall.ObjExpr);
      Self.Emit(#9'movq %rax, %rsi');
    end
    else
      Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand('Self')]));

    { Pop one register per SLOT (interface args occupy two), into the integer
      registers after %rdi (sret) and %rsi (Self): %rdx, %rcx, %r8, %r9. }
    Self.EmitPopMethodArgsToRegs(MD.Params, ACall.Args, 2);
    { The saved dest sits just below the call frame's hoist region. }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [Self.TopFrameTotal()]));
    if (MD.VTableSlot >= 0) and not AForceStatic then
    begin
      Self.Emit(#9'pushq %rdi');
      Self.Emit(#9'movq (%rsi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
      Self.Emit(#9'popq %rax');
    end
    else
      Self.Emit(#9'callq ' + Sym);
    Self.EndCallArgs();
  end
  else
  begin
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    AllocSz := (((ACall.Args.Count + 2) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [AllocSz + HTotal]));
    Self.Emit(#9'movq %rax, 0(%rsp)');
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 2) * 8]));
    end;
    if ACall.ObjectName <> '' then
    begin
      if Self.IsLocal(ACall.ObjectName) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(ACall.ObjectName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [ACall.ObjectName]));
    end
    else if (ACall.ObjExpr <> nil) and (RecvBufBytes > 0) then
      Self.Emit(#9'movq %rbx, %rax')      { record-call receiver address }
    else if ACall.ObjExpr <> nil then
      Self.EmitExprToEax(ACall.ObjExpr)
    else
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
    Self.Emit(Format(#9'movq %%rax, 8(%%rsp)', []));
    Self.Emit(#9'movq 0(%rsp), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    Self.Emit(#9'callq ' + Sym);
    CleanUp := AllocSz - 6 * 8;
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, CleanUp, True);
    HD.Free();
    HK.Free();
  end;
  { Reclaim the saved dest slot. }
  Self.Emit(#9'addq $8, %rsp');
  Self.EmitMethodSretRecvCleanup(RecvBufBytes);
end;

{ Sret an inherited record return: build a transient implicit-Self method node
  carrying the parent method + the inherited call's args and emit it
  force-static, so EmitMethodSretCall threads the sret pointer / register-return
  capture the same way every other record-returning call does (instead of a
  second copy of the sret sequence).  The Args list is borrowed and detached
  before Free so the caller's node keeps ownership. }
procedure TX86_64Backend.EmitInheritedRecordSret(MD: TMethodDecl;
  AArgs: TObjectList; const AName, ADest: string; ADestIsIndirect: Boolean);
var
  Shim: TMethodCallExpr;
begin
  { An inherited call is an implicit-Self call (ObjectName = '' and ObjExpr =
    nil, so EmitMethodSretCall loads the receiver from the current Self slot)
    dispatched STATICALLY to the parent's method. }
  Shim := TMethodCallExpr.Create();
  Shim.ResolvedMethod := MD;
  Shim.Name := AName;
  Shim.Args := AArgs;
  Self.EmitMethodSretCall(Shim, ADest, ADestIsIndirect, True);
  Shim.Args := nil;
  Shim.Free();
end;

{ Emit a standalone function call that returns an interface via sret.
  Allocates a 16-byte buffer on the stack, passes its address as the first
  hidden arg (%rdi), calls the function, and leaves the buffer on the stack
  (caller loads obj at 0(%rsp) and itab at 8(%rsp), then addq $16, %rsp). }
procedure TX86_64Backend.EmitIntfSretCall(ACall: TFuncCallExpr);
var
  I:      Integer;
  MD:     TMethodDecl;
  FSym:   string;
  Arg:    TASTExpr;
  ArgCnt: Integer;
  Par:    TMethodParam;
  HD:     TList<Integer>;
  HK:     TList<Integer>;
  HTotal: Integer;
  Pushed: Integer;
  OverflowBytes: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedDecl);
  FSym := FuncSymbolOf(ACall);
  ArgCnt := ACall.Args.Count;
  { Hoist region BELOW the sret buffer: the buffer must sit exactly at %rsp
    when the call is made, so the region cannot live between buffer and call.
    After the call the buffer is relocated down over the region so callers
    keep their `fat pointer at (%rsp), addq $16` contract. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
  { Allocate the 16-byte sret buffer on the stack and zero it. }
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  if ACall.IsImplicitSelfMethod then
  begin
    { Open-array literal args raise in EmitMethodArgPush — unsupported for
      interface-sret calls. }
    Pushed := 0;
    for I := 0 to ArgCnt - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]));
        Self.Emit(#9'pushq %rax');
        Pushed := Pushed + 8;
      end
      else
      begin
        Self.EmitMethodArgPush(Par, Arg);
        if Par.IsOpenArray or
           ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
          Pushed := Pushed + 16
        else
          Pushed := Pushed + 8;
      end;
    end;
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    { Consume args (base 2: %rdi = sret buffer, %rsi = Self); spill overflow. }
    OverflowBytes := Self.EmitSretRegArgs(Self.CountArgSlots(MD.Params), 2);
    Self.Emit(#9'movq %r10, %rsi');
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    { Virtual implicit-Self interface-sret call dispatches through the vtable
      (Self is in %rsi here; %rdi holds the sret buffer). }
    Self.EmitSelfDispatchVia(MD, FSym, '%rsi');
  end
  else
  begin
    Pushed := 0;
    for I := 0 to ArgCnt - 1 do
    begin
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
      Pushed := Pushed + 8;
    end;
    { Consume args (base 1: %rdi = sret buffer); spill overflow. }
    OverflowBytes := Self.EmitSretRegArgs(ArgCnt, 1);
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    Self.Emit(#9'callq ' + FSym);
  end;
  { Reclaim overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values (the 16-byte buffer sits between %rsp
    and the region), then slide the buffer down over the region so the
    caller's contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitIntfSretMethodCall(ACall: TMethodCallExpr);
var
  I, SlotOff, ArgN: Integer;
  Arg: TASTExpr;
  IntfD: TInterfaceTypeDesc;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  IE: TIdentExpr;
  OverflowBytes: Integer;
begin
  IntfD := TInterfaceTypeDesc(ACall.ResolvedClassType);
  ArgN := 0;
  if ACall.Args <> nil then ArgN := ACall.Args.Count;
  { Same unknown-signature hoist as EmitInterfaceCall; the region sits BELOW
    the sret buffer (see EmitIntfSretCall for the layout rationale). }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := IntfD.MethodParamVarFlagsStr(IntfD.MethodIndex(ACall.Name));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, ACall.Args, HD, HK);
  { Allocate and zero the 16-byte sret buffer. }
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      { Hoisted record-call or string argument — reload the saved value
        (+16 for the sret buffer between %rsp and the hoist region). }
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [16 + HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      { var/out position: pass the slot ADDRESS — same rule as direct
        calls; covers managed types (string, dynarray) the callee rebinds. }
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in sret interface dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Resolve the receiver: obj into %r10, itab into %rax. }
  if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(ACall.ObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) and
          TIdentExpr(ACall.ObjExpr).IsImplicitSelf and
          (TIdentExpr(ACall.ObjExpr).ImplicitFieldInfo <> nil) then
  begin
    { Interface field of Self as receiver: fat pointer at Self + offset. }
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    if TFieldInfo(IE.ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r10',
        [TFieldInfo(IE.ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(IE.Name, IE.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(IE.Name, IE.IsGlobal)]));
  end
  else if ACall.ObjExpr <> nil then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported receiver expression in sret interface dispatch')
  else if ACall.IsVarParam then
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(ACall.ObjectName, ACall.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(ACall.ObjectName, ACall.IsGlobal)]));
  end;
  SlotOff := IntfD.MethodIndex(ACall.Name) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Pop args shifted by 2: %rdi = sret buffer, %rsi = receiver obj.
    var positions take one slot. }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  { Consume args (base 2: %rdi = sret buffer, %rsi = receiver obj); spill
    overflow slots beyond the 4 remaining registers to the stack. }
  OverflowBytes := Self.EmitSretRegArgs(SlotOff, 2);
  Self.Emit(#9'movq %r10, %rsi');
  Self.Emit(#9'movq %rsp, %rdi');
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
  Self.Emit(#9'callq *%r11');
  { Reclaim overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values, then slide the buffer down over the
    hoist region so the caller's `fat pointer at (%rsp)` contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

procedure TX86_64Backend.EmitIntfRecordSretDispatch(ACall: TMethodCallExpr;
  const ADest: string; ADestIsIndirect: Boolean);
var
  I, SlotOff, ArgN, Slots: Integer;
  Arg: TASTExpr;
  IntfD: TInterfaceTypeDesc;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal, Pushed: Integer;
  VFlags: string;
  IE: TIdentExpr;
  OverflowBytes, ABase: Integer;
  RC: TRecReturnClass;
  RetRec: TRecordTypeDesc;
begin
  IntfD := TInterfaceTypeDesc(ACall.ResolvedClassType);
  RetRec := TRecordTypeDesc(ACall.ResolvedType);
  RC := ClassifyRecordReturn(RetRec);
  ArgN := 0;
  if ACall.Args <> nil then ArgN := ACall.Args.Count;

  { Resolve the destination to an ABSOLUTE pointer FIRST, in callee-saved %r14,
    before any %rsp movement (arg pushes / overflow spill) can drift a
    %rsp-relative ADest. }
  Self.Emit(#9'pushq %r14');
  if ADestIsIndirect then
    Self.Emit(Format(#9'movq %s, %%r14', [ADest]))
  else
    Self.Emit(Format(#9'leaq %s, %%r14', [ADest]));

  { Same unknown-signature hoist as EmitIntfSretMethodCall; the region sits
    BELOW any sret buffer space we reserve. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  VFlags := IntfD.MethodParamVarFlagsStr(IntfD.MethodIndex(ACall.Name));
  HTotal := Self.EmitArgHoist(nil, nil, False, VFlags, ACall.Args, HD, HK);
  Pushed := 0;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax', [HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
    end
    else if Self.VarFlagAt(VFlags, I) then
    begin
      Self.EmitVarArgAddrToRax(Arg);
      Self.Emit(#9'pushq %rax');
    end
    else if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        if TIdentExpr(Arg).IsImplicitSelf and
           (TIdentExpr(Arg).ImplicitFieldInfo <> nil) then
        begin
          Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
          if TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset > 0 then
            Self.Emit(Format(#9'addq $%d, %%rax',
              [TFieldInfo(TIdentExpr(Arg).ImplicitFieldInfo).Offset]));
          Self.Emit(#9'movq (%rax), %rcx');
          Self.Emit(#9'movq 8(%rax), %rdx');
          Self.Emit(#9'pushq %rcx');
          Self.Emit(#9'pushq %rdx');
        end
        else
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end;
      end
      else if Arg is TFieldAccessExpr then
      begin
        Self.EmitInterfaceFieldAddr(TFieldAccessExpr(Arg), '%rax');
        Self.Emit(#9'movq (%rax), %rcx');
        Self.Emit(#9'movq 8(%rax), %rdx');
        Self.Emit(#9'pushq %rcx');
        Self.Emit(#9'pushq %rdx');
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in sret interface record dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
    if (HK.Get(I) < akRecCall) and (not Self.VarFlagAt(VFlags, I)) and
       (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Pushed := Pushed + 16
    else
      Pushed := Pushed + 8;
  end;
  { Resolve the receiver: obj into %r10, itab into %rax. }
  if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TFieldAccessExpr) then
  begin
    Self.EmitInterfaceFieldAddr(TFieldAccessExpr(ACall.ObjExpr), '%r10');
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) and
          TIdentExpr(ACall.ObjExpr).IsImplicitSelf and
          (TIdentExpr(ACall.ObjExpr).ImplicitFieldInfo <> nil) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
    if TFieldInfo(IE.ImplicitFieldInfo).Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r10',
        [TFieldInfo(IE.ImplicitFieldInfo).Offset]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else if (ACall.ObjExpr <> nil) and (ACall.ObjExpr is TIdentExpr) then
  begin
    IE := TIdentExpr(ACall.ObjExpr);
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(IE.Name, IE.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(IE.Name, IE.IsGlobal)]));
  end
  else if ACall.ObjExpr <> nil then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported receiver expression in sret interface record dispatch')
  else if ACall.IsVarParam then
  begin
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
    Self.Emit(#9'movq 8(%r10), %rax');
    Self.Emit(#9'movq (%r10), %r10');
  end
  else
  begin
    Self.Emit(Format(#9'movq %s, %%r10',
      [Self.IntfObjOperand(ACall.ObjectName, ACall.IsGlobal)]));
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(ACall.ObjectName, ACall.IsGlobal)]));
  end;
  SlotOff := IntfD.MethodIndex(ACall.Name) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));

  { Count the arg SLOTS (var positions one slot; interface args two). }
  Slots := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    if (not Self.VarFlagAt(VFlags, I)) and (Arg.ResolvedType <> nil) and
       (Arg.ResolvedType.Kind = tyInterface) then
      Inc(Slots, 2)
    else
      Inc(Slots);
  end;

  if RC = rcSret then
  begin
    { Memory-class record: hidden sret pointer in %rdi, receiver obj in %rsi,
      visible args from %rdx (base index 2).  The dest buffer is %r14. }
    Self.Emit(#9'movq %r14, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx', [RetRec.TotalSize()]));
    Self.Emit(#9'pushq %r10');           { preserve receiver obj across memset }
    Self.Emit(#9'pushq %r11');           { preserve fptr across memset }
    Self.Emit(#9'callq memset');
    Self.Emit(#9'popq %r11');
    Self.Emit(#9'popq %r10');
    ABase := 2;
    OverflowBytes := Self.EmitSretRegArgs(Slots, ABase);
    Self.Emit(#9'movq %r10, %rsi');
    Self.Emit(#9'movq %r14, %rdi');
    Self.Emit(#9'callq *%r11');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { Register-class record: NO hidden sret arg.  Receiver obj in %rdi,
      visible args from %rsi (base index 1).  Capture the register return
      into the dest buffer (%r14). }
    ABase := 1;
    OverflowBytes := Self.EmitSretRegArgs(Slots, ABase);
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'callq *%r11');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    { %r14 still holds the dest pointer (callee-saved across the call). }
    Self.EmitRecordRegReturnCapture('%r14', RetRec, RC, True);
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 0, True);
  end;
  HD.Free();
  HK.Free();
  Self.Emit(#9'popq %r14');
end;

procedure TX86_64Backend.EmitClassIntfSretMethodCall(ACall: TMethodCallExpr);
var
  I: Integer;
  MD: TMethodDecl;
  Sym: string;
  Arg: TASTExpr;
  Par: TMethodParam;
  UserSlots: Integer;
  HD: TList<Integer>;
  HK: TList<Integer>;
  HTotal: Integer;
  Pushed: Integer;
  OverflowBytes: Integer;
begin
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: class sret interface call has no ResolvedMethod (' +
      ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Static method returning an interface (TypeName.GetIt: IFoo): there is NO
    receiver, so the call follows the plain free-function interface-sret ABI —
    sret buffer in %rdi, user args from %rsi (base 1), and a direct callq to the
    mangled static symbol.  Without this branch the code below would treat the
    bare TypeName (ACall.ObjectName) as a global Self and emit a load of an
    undefined `TypeName` symbol.  Mirrors the non-Self `else` arm of
    EmitIntfSretCall. }
  if ACall.IsStaticCall then
  begin
    Sym := MethodEmitNameNative(MD,
             TRecordTypeDesc(ACall.ResolvedClassType).Name, ACall.Name);
    UserSlots := Self.CountArgSlots(MD.Params);
    HD := TList<Integer>.Create();
    HK := TList<Integer>.Create();
    HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
    Self.Emit(#9'subq $16, %rsp');
    Self.Emit(#9'movq $0, (%rsp)');
    Self.Emit(#9'movq $0, 8(%rsp)');
    Pushed := 0;
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MD.Params.Items[I]);
      Arg := TASTExpr(ACall.Args.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [16 + HTotal - HD.Get(I) + Pushed]));
        Self.Emit(#9'pushq %rax');
        Pushed := Pushed + 8;
      end
      else
      begin
        Self.EmitMethodArgPush(Par, Arg);
        if Par.IsOpenArray or
           ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
          Pushed := Pushed + 16
        else
          Pushed := Pushed + 8;
      end;
    end;
    { Base 1: %rdi = sret buffer, user args from %rsi; no Self register. }
    OverflowBytes := Self.EmitSretRegArgs(UserSlots, 1);
    Self.Emit(#9'movq %rsp, %rdi');
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
    Self.Emit(#9'callq ' + Sym);
    if OverflowBytes > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
    Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
    Self.EmitSretBufferSlideDown(HTotal);
    HD.Free();
    HK.Free();
    Exit;
  end;

  UserSlots := Self.CountArgSlots(MD.Params);
  { %rdi = sret buffer, %rsi = Self leave four integer arg registers; further
    slots spill to the stack via EmitSretRegArgs (ABase = 2). }
  { Hoist region BELOW the sret buffer — same layout rationale as
    EmitIntfSretCall. }
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(MD.Params, nil, True, '', ACall.Args, HD, HK);
  Self.Emit(#9'subq $16, %rsp');
  Self.Emit(#9'movq $0, (%rsp)');
  Self.Emit(#9'movq $0, 8(%rsp)');
  Pushed := 0;
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MD.Params.Items[I]);
    Arg := TASTExpr(ACall.Args.Items[I]);
    if HK.Get(I) >= akRecCall then
    begin
      Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
        [16 + HTotal - HD.Get(I) + Pushed]));
      Self.Emit(#9'pushq %rax');
      Pushed := Pushed + 8;
    end
    else
    begin
      Self.EmitMethodArgPush(Par, Arg);
      if Par.IsOpenArray or
         ((Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface)) then
        Pushed := Pushed + 16
      else
        Pushed := Pushed + 8;
    end;
  end;
  { Receiver into %r10 — mirrors EmitMethodCallExpr's resolution for
    class-typed receivers. }
  if ACall.ObjectName <> '' then
  begin
    if ACall.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]));
      Self.Emit(#9'movq (%r10), %r10');
    end
    else if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%r10', [ACall.ObjectName]));
  end
  else if ACall.ObjExpr <> nil then
  begin
    Self.EmitExprToEax(ACall.ObjExpr);
    Self.Emit(#9'movq %rax, %r10');
  end
  else
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
  { Consume args into registers (shifted by 2: %rdi = sret buffer,
    %rsi = receiver); slots beyond the 4 remaining registers spill. }
  OverflowBytes := Self.EmitSretRegArgs(UserSlots, 2);
  Self.Emit(#9'movq %r10, %rsi');
  Self.Emit(#9'movq %rsp, %rdi');
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rdi', [OverflowBytes]));
  if MD.VTableSlot >= 0 then
  begin
    { Virtual dispatch through the receiver's vtable (slot 0 is the
      typeinfo pointer, hence +1). }
    Self.Emit(#9'movq (%rsi), %rax');
    Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
    Self.Emit(#9'callq *%rax');
  end
  else
    Self.Emit(#9'callq ' + Sym);
  { Reclaim any overflow stack args before touching the sret buffer. }
  if OverflowBytes > 0 then
    Self.Emit(Format(#9'addq $%d, %%rsp', [OverflowBytes]));
  { Post-call: release hoisted values, then slide the buffer down over the
    hoist region so the caller's `fat pointer at (%rsp)` contract holds. }
  Self.EmitHoistEpilogue(ACall.Args, HD, HK, HTotal, 16, False);
  Self.EmitSretBufferSlideDown(HTotal);
  HD.Free();
  HK.Free();
end;

{ Emit a method-pointer (of-object) call through a TMethod block.
  APtrOperand is the AT&T memory operand for the 16-byte Code+Data block.
  Load Code into %r10, Data into %rdi, push/pop other args, then callq *%r10. }
procedure TX86_64Backend.EmitMethodPtrCall(const APtrOperand: string;
                                           AProcType: TProceduralTypeDesc;
                                           AArgs: TObjectList);
var
  I:       Integer;
  Arg:     TASTExpr;
  AllocSz: Integer;
  CleanUp: Integer;
  HD:      TList<Integer>;
  HK:      TList<Integer>;
  HTotal:  Integer;
  PParams: TObjectList;
begin
  PParams := nil;
  if AProcType <> nil then
    PParams := AProcType.Params;
  HD := TList<Integer>.Create();
  HK := TList<Integer>.Create();
  HTotal := Self.EmitArgHoist(nil, PParams, True, '', AArgs, HD, HK);
  { Code/Data are loaded into %r10/%r11 only AFTER all argument evaluation:
    both are caller-saved, so any call emitted while evaluating an argument
    (or the hoist pre-pass above) would clobber them.  APtrOperand is %rbp-
    or %rip-relative, never %rsp-relative. }

  if AArgs.Count <= 5 then
  begin
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if HK.Get(I) >= akRecCall then
      begin
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [HTotal - HD.Get(I) + I * 8]));
        Self.Emit(#9'pushq %rax');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;
    for I := AArgs.Count - 1 downto 0 do
      Self.Emit(#9'popq ' + SysVArg64(I + 1));
    Self.Emit(Format(#9'leaq %s, %%rcx', [APtrOperand]));
    Self.Emit(#9'movq (%rcx), %r10');
    Self.Emit(#9'movq 8(%rcx), %rdi');
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, 0, True);
  end
  else
  begin
    { >5 explicit args: pre-allocate (Count+1) slots (slot 0 unused, args=1..N). }
    AllocSz := (((AArgs.Count + 1) * 8 + 15) and (-16));
    Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      if HK.Get(I) >= akRecCall then
        Self.Emit(Format(#9'movq %d(%%rsp), %%rax',
          [AllocSz + HTotal - HD.Get(I)]))
      else
        Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [(I + 1) * 8]));
    end;
    Self.Emit(Format(#9'leaq %s, %%rcx', [APtrOperand]));
    Self.Emit(#9'movq (%rcx), %r10');
    Self.Emit(#9'movq 8(%rcx), %rdi');
    for I := 0 to 4 do
      Self.Emit(Format(#9'movq %d(%%rsp), %s', [(I + 1) * 8, SysVArg64(I + 1)]));
    Self.Emit(Format(#9'addq $%d, %%rsp', [6 * 8]));
    CleanUp := AllocSz - 6 * 8;
    Self.Emit(#9'callq *%r10');
    Self.EmitHoistEpilogue(AArgs, HD, HK, HTotal, CleanUp, True);
  end;
  HD.Free();
  HK.Free();
end;

{ True when AType is an integer-family type the backend can place in a
  general-purpose register (Byte..Int64).  Floats, records, strings, etc. are
  not yet handled and must fail loudly. }
function IsIntFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyUInt32, tyInt64, tyUInt64,
                    tySmallInt, tyWord, tyByte, tyBoolean, tyEnum]);
end;

{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16:  [0..7] = type tag (0=int, 1=string); [8..15] = value.
  We allocate the array on the stack via subq, fill it, then call the RTL. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  Stack layout at the callq:
    [%rbp - old_frame ... fmt_ptr ... arr[0]...arr[N-1]] → then call
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value.
  Stack discipline: evaluate fmt first and push it (so later push/pop from
  nested expr evaluation cannot overwrite the array we build below it). }
procedure TX86_64Backend.EmitFormatCall(AArgs: TObjectList);
var
  I:         Integer;
  FmtCount:  Integer;
  Arg:       TASTExpr;
  IsIntArg:  Boolean;
  TotalSize: Integer;
  ArrLit:    TArrayLiteralExpr;
  UseArray:  Boolean;
begin
  UseArray := (AArgs.Count = 2) and (AArgs.Items[1] is TArrayLiteralExpr);
  if UseArray then
  begin
    ArrLit := TArrayLiteralExpr(AArgs.Items[1]);
    FmtCount := ArrLit.Elements.Count;
  end
  else
  begin
    ArrLit := nil;
    FmtCount := AArgs.Count - 1;
  end;
  Self.EmitExprToEax(TASTExpr(AArgs.Items[0]));
  Self.Emit(#9'pushq %rax');
  if FmtCount > 0 then
  begin
    TotalSize := ((FmtCount * 16) + 15) and (-16);
    Self.Emit(#9'pushq %rbx');
    Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSize]));
    Self.Emit(#9'movq %rsp, %rbx');
    for I := 0 to FmtCount - 1 do
    begin
      if UseArray then
        Arg := TASTExpr(ArrLit.Elements.Items[I])
      else
        Arg := TASTExpr(AArgs.Items[I + 1]);
      if (Arg.ResolvedType <> nil) and
         (Arg.ResolvedType.Kind in [tyDouble, tySingle]) then
      begin
        { Float arg: tag 2, value = raw IEEE-754 binary64 bits.  Evaluate to
          %xmm0, widen a Single to Double, then bit-copy the 64-bit pattern
          via movq into the value slot (matching the QBE backend's 'cast'). }
        Self.Emit(Format(#9'movq $2, %d(%%rbx)', [I * 16]));
        Self.EmitExprToXmm0(Arg);
        Self.EmitXmm0WidthAdjust(Arg.ResolvedType, False);
        Self.Emit(#9'movq %xmm0, %rax');
        Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [I * 16 + 8]));
        Continue;
      end;
      IsIntArg := (Arg.ResolvedType = nil) or
        (Arg.ResolvedType.Kind in [tyInteger, tyBoolean, tyByte, tyUInt32,
                                    tyInt64, tyUInt64, tySmallInt, tyWord, tyEnum]);
      if IsIntArg then
        Self.Emit(Format(#9'movq $0, %d(%%rbx)', [I * 16]))
      else
        Self.Emit(Format(#9'movq $1, %d(%%rbx)', [I * 16]));
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%rbx)', [I * 16 + 8]));
    end;
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [TotalSize + 8]));
    Self.Emit(#9'movq %rbx, %rsi');
    Self.Emit(Format(#9'movl $%d, %%edx', [FmtCount]));
    Self.Emit(#9'callq _StringFormatN');
    Self.Emit(Format(#9'addq $%d, %%rsp', [TotalSize]));
    Self.Emit(#9'popq %rbx');
    Self.Emit(#9'addq $8, %rsp');
  end
  else
  begin
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(#9'xorl %edx, %edx');
    Self.Emit(#9'callq _StringFormatN');
  end;
end;

{ Emit a standalone procedure/function definition.  Frame layout mirrors the
  reference (FPC -O- and the QBE backend): params, Result and locals each get
  an 8-byte-aligned %rbp-relative slot sized by their type; the prologue
  spills the incoming argument registers into the param slots at their width;
  the body runs through the slots; a function returns its Result slot
  (64-bit-extended) in %rax/%eax.  M5 supports integer-family value
  parameters and integer-family/void return. }
procedure TX86_64Backend.EmitFunctionDef(ADecl: TMethodDecl; AExported: Boolean);
var
  I, J:        Integer;
  P:           TMethodParam;
  Sym:         string;
  IntIdx:      Integer;
  XmmIdx:      Integer;
  NestedDecl:  TMethodDecl;
  SavedOuterDecl: TMethodDecl;
  AddrTaken:   TStringList;
  SlotOff:     Integer;
begin
  { Emit any nested procedures declared inside this function's body before
    emitting this function itself.  Each nested proc gets a mangled name
    OuterName_InnerName to avoid global symbol collisions.  FDbgOuterDecl
    carries the enclosing decl so DbgMarkParams can type captured vars;
    saved/restored to keep doubly-nested emission consistent. }
  if ADecl.Body <> nil then
  begin
    SavedOuterDecl := FDbgOuterDecl;
    for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
    begin
      NestedDecl := TMethodDecl(ADecl.Body.ProcDecls.Items[I]);
      if NestedDecl.Body = nil then Continue;
      NestedDecl.ResolvedQbeName := ADecl.Name + '_' + NestedDecl.Name;
      FDbgOuterDecl := ADecl;
      Self.EmitFunctionDef(NestedDecl, False);
    end;
    FDbgOuterDecl := SavedOuterDecl;
  end;

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then Continue;  { open array: (ptr, high) pair — always ok }
    if P.IsVarParam then Continue;  { var/out: always a pointer — ok }
    if not IsIntFamily(P.ResolvedType) and not IsFloatFamily(P.ResolvedType) and
       ((P.ResolvedType = nil) or
        not (P.ResolvedType.Kind in [tyString, tyPChar, tyPointer,
                                     tyClass, tyMetaClass, tyInterface,
                                     tyOpenArray, tyDynArray,
                                     tyRecord, tyStaticArray,
                                     tyProcedural, tySet])) then
      raise ENativeCodeGenError.Create(
        'native backend: unsupported parameter type (param ' + P.ParamName + ')');
  end;
  if (ADecl.ResolvedReturnType <> nil) and
     not IsIntFamily(ADecl.ResolvedReturnType) and
     not IsFloatFamily(ADecl.ResolvedReturnType) and
     not (ADecl.ResolvedReturnType.Kind in [tyRecord, tyStaticArray, tyString,
                                          tyPChar, tyPointer, tyClass, tyMetaClass,
                                          tyDynArray, tyInterface, tyProcedural,
                                          tySet]) then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported return type (function ' + ADecl.Name + ')');

  { Set FCapturedVars for the duration of this function's emission so that
    variable-access paths redirect through the capture pointers. }
  FCapturedVars := ADecl.CapturedVars;

  { Rebuild the borrowed-argument blocklist for this function: address-taken
    locals (explicit @, var/out args) plus anything captured by a nested
    procedure.  Consulted by ConstStrShape. }
  FConstArgUnsafe.Clear();
  if ADecl.Body <> nil then
  begin
    AddrTaken := CollectAddressTaken(ADecl.Body);
    for I := 0 to AddrTaken.Count - 1 do
      FConstArgUnsafe.Add(AddrTaken.Strings[I]);
    AddrTaken.Free();
    for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
      if TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars <> nil then
        for J := 0 to TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars.Count - 1 do
          FConstArgUnsafe.Add(
            TMethodDecl(ADecl.Body.ProcDecls.Items[I]).CapturedVars.Strings[J]);
  end;

  Sym := FuncSymbolFromDecl(ADecl);
  Self.DbgBeginFunc(Sym);
  Self.BuildFrame(ADecl);
  Self.DbgMarkParams(ADecl);

  Self.Emit('.text');
  if AExported then
    Self.Emit('.globl ' + Sym);
  Self.Emit(Sym + ':');
  { nostackframe: the body is an inline-asm block that owns the entire frame
    (prologue, args-from-registers, ret).  Emit no compiler prologue/epilogue,
    no param spill, no ARC — just the verbatim block.  This is the null-object
    frame strategy (see docs/inline-asm-design.adoc). }
  if ADecl.NoStackFrame then
  begin
    if (ADecl.Body <> nil) then
      Self.EmitStmtList(ADecl.Body.Stmts);
    Self.DbgEndFunc();
    Self.Emit('.type ' + Sym + ', @function');
    FExitLabel    := '';
    FCapturedVars := nil;
    Exit;
  end;
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  if FFrameSize > 0 then
    Self.Emit(Format(#9'subq $%d, %%rsp', [FFrameSize]));
  { Spill incoming argument registers into param slots.  SysV AMD64 passes
    integer args in %rdi/%rsi/... and float args in %xmm0/%xmm1/... independently.
    Track separate counters: IntIdx for integer params, XmmIdx for float params.
    For sret functions the hidden first integer arg (%rdi) is the destination
    buffer pointer; spill it into the Result slot first, then continue with
    the normal params starting at IntIdx=1. }
  IntIdx := 0;
  XmmIdx := 0;
  { Spill captured-var pointer params into their _cap_ slots. }
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      Self.Emit(Format(#9'movq %s, %s',
        [SysVArg64(IntIdx),
         Self.VarOperand('_cap_' + ADecl.CapturedVars.Strings[I])]));
      Inc(IntIdx);
    end;
  if FSretFunc then
  begin
    { Save the sret buffer pointer from %rdi into the Result slot. }
    Self.Emit(Format(#9'movq %%rdi, %s', [Self.VarOperand('Result')]));
    IntIdx := 1;
  end;
  if (ADecl.OwnerTypeName <> '') and not ADecl.IsStatic then
  begin
    { Class method: spill Self from the first int arg register into its slot.
      A `static` method has NO implicit Self — its first user parameter is the
      first integer arg (%rdi), so no Self spill and IntIdx stays put. }
    Self.Emit(Format(#9'movq %s, %s',
      [SysVArg64(IntIdx), Self.VarOperand('Self')]));
    Inc(IntIdx);
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then
    begin
      { Open array: two consecutive integer registers — data ptr then high index. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName + '_high')]));
        Inc(IntIdx);
      end;
    end
    else if IsFloatFamily(P.ResolvedType) and not P.IsVarParam then
    begin
      { SSE arg registers xmm0..7; a float beyond the 8th arrives on the stack
        (its frame slot is already the +StackOff location, so no spill). }
      if XmmIdx < 8 then
      begin
        if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]))
        else
          Self.Emit(Format(#9'movsd %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]));
        Inc(XmmIdx);
      end;
    end
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) and
            not P.IsVarParam then
    begin
      { Interface param: spill obj register into the 16-byte slot base,
        itab register into base+8.  IntfItabOperand computes Off+8 from the
        frame entry, which lands correctly because AddSlot reserved 16 bytes.
        A var/out interface param arrives as ONE pointer (the caller's fat
        pointer address) and is spilled by the IsVarParam branch below. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.IntfItabOperand(P.ParamName, False)]));
        Inc(IntIdx);
      end;
    end
    else if P.IsVarParam then
    begin
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
    end
    else if (P.ResolvedType <> nil) and
            ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
             IsJumboSet(P.ResolvedType)) then
    begin
      { Phase 1: spill only the incoming pointer.  The local copy is made
        AFTER every register is spilled — memcpy clobbers the caller-saved
        argument registers, so copying here would corrupt any parameter
        that follows this one. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArg64(IntIdx), Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
    end
    else
    begin
      if IntIdx < 6 then
      begin
        Self.EmitSpillArg(IntIdx, Self.VarOperand(P.ParamName), P.ResolvedType);
        Inc(IntIdx);
      end;
    end;
  end;
  { Phase 2: copy record / static-array value params into their local _data
    blocks (Pascal value semantics) now that all registers are spilled, then
    repoint the param slot at the copy. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray or P.IsVarParam then Continue;
    if (P.ResolvedType = nil) or
       not ((P.ResolvedType.Kind in [tyRecord, tyStaticArray]) or
            IsJumboSet(P.ResolvedType)) then Continue;
    Self.Emit(Format(#9'movq %s, %%rsi', [Self.VarOperand(P.ParamName)]));
    Self.Emit(Format(#9'leaq %s, %%rdi',
      [Self.VarOperand(P.ParamName + '_data')]));
    Self.Emit(Format(#9'movq $%d, %%rdx', [P.ResolvedType.RawSize()]));
    Self.Emit(#9'callq memcpy');
    Self.Emit(Format(#9'leaq %s, %%rax',
      [Self.VarOperand(P.ParamName + '_data')]));
    Self.Emit(Format(#9'movq %%rax, %s',
      [Self.VarOperand(P.ParamName)]));
  end;
  { Initialise Result to 0 (defined default), like the QBE backend.
    For sret functions Result IS the caller's buffer (already zeroed by caller). }
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if IsFloatFamily(ADecl.ResolvedReturnType) then
    begin
      { Zero %xmm0 by xorpd/xorps. }
      if ADecl.ResolvedReturnType.Kind = tySingle then
        Self.Emit(#9'xorps %xmm0, %xmm0')
      else
        Self.Emit(#9'xorpd %xmm0, %xmm0');
      Self.EmitStoreFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end
    else
    begin
      Self.Emit(#9'xorl %eax, %eax');
      Self.EmitStoreVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end;
  end;
  { Zero-initialise ALL local variable slots — Blaise guarantees zero
    initialisation of every variable as a language semantic.  The case
    branches mirror EmitVarAllocs in the QBE backend so both backends
    behave identically.  The else clause deliberately raises an error so
    that any new TTypeKind added in the future is caught here immediately. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType = nil then Continue;
      case TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind of

        tyInteger, tyUInt32, tySmallInt, tyWord, tyBoolean, tyByte, tyEnum:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            Self.Emit(Format(#9'movl $0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyInt64, tyUInt64,
        tyString,
        tyClass,
        tyPointer, tyPChar, tyMetaClass,
        tyDynArray:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            Self.Emit(Format(#9'movq $0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyInterface:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'movq $0, %s',
              [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
            Self.Emit(Format(#9'movq $0, %s',
              [Self.IntfItabOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
          end;

        tyDouble:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(#9'xorpd %xmm0, %xmm0');
            Self.Emit(Format(#9'movsd %%xmm0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          end;

        tySingle:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(#9'xorps %xmm0, %xmm0');
            Self.Emit(Format(#9'movss %%xmm0, %s',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          end;

        tySet:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            if IsJumboSet(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType) then
            begin
              { Jumbo set: zero the whole inline bitmap via memset. }
              Self.Emit(Format(#9'leaq %s, %%rdi',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
              Self.Emit(#9'xorl %esi, %esi');
              Self.Emit(Format(#9'movl $%d, %%edx',
                [TSetTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).RawSize()]));
              Self.Emit(#9'callq memset');
            end
            else if TSetTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).BitCount <= 32 then
              Self.Emit(Format(#9'movl $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]))
            else
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyProcedural:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
            if TProceduralTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).IsMethodPtr then
            begin
              { Method pointer: two consecutive 8-byte slots (Code + Data).
                VarOperand gives Code at the base; Data is 8 bytes above it. }
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
              FFrame.TryGetValue(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], SlotOff);
              Self.Emit(Format(#9'movq $0, %d(%%rbp)', [SlotOff + 8]));
            end
            else
              Self.Emit(Format(#9'movq $0, %s',
                [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));

        tyRecord:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'xorl %esi, %esi');
            Self.Emit(Format(#9'movq $%d, %%rdx',
              [TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.RawSize()]));
            Self.Emit(#9'callq memset');
          end;

        tyStaticArray:
          for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'xorl %esi, %esi');
            Self.Emit(Format(#9'movq $%d, %%rdx',
              [TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.RawSize()]));
            Self.Emit(#9'callq memset');
          end;

        { Open-array locals are never declared — they are caller-owned
          pointer+high pairs passed as parameters only. }
        tyOpenArray: ;

        { tyVoid and tyNil cannot appear as the type of a declared variable;
          any hit here indicates a semantic-pass bug. }
      else
        raise ENativeCodeGenError.Create(Format(
          'native zero-init: unhandled type kind %d for local ''%s''',
          [Ord(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind),
           TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[0]]));
      end;
    end;
  { ARC: retain string/class/interface value params on entry — balances the
    release pass at the epilogue.  Skip var, out, open-array and const
    params.  Const params (including const strings) are protected
    CALLER-side by shape — see EmitArgHoist and the QBE backend's
    ConstArgMode; both backends share this convention, which also keeps
    calls into the QBE-compiled RTL consistent. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam or P.IsOpenArray or P.IsConstParam then Continue;
    if P.ResolvedType = nil then Continue;
    if P.ResolvedType.Kind = tyString then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _StringAddRef');
    end
    else if P.ResolvedType.Kind = tyClass then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _ClassAddRef');
    end
    else if P.ResolvedType.Kind = tyInterface then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.IntfObjOperand(P.ParamName, False)]));
      Self.Emit(#9'callq _ClassAddRef');
    end
    else if P.ResolvedType.Kind = tyRecord then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(P.ParamName)]));
      Self.EmitRecordFieldRetains(TRecordTypeDesc(P.ResolvedType), '%rbx');
      Self.Emit(#9'popq %rbx');
    end;
  end;
  { Body.  FExitLabel directs Exit statements to the epilogue. }
  FExitLabel := Self.NewLabel('exit');
  if ADecl.Body <> nil then
    Self.EmitStmtList(ADecl.Body.Stmts);
  { Epilogue: Exit lands here.  The Result is loaded into %rax/%xmm0 only AFTER
    the ARC release passes below — those call _ClassRelease/_StringRelease, which
    clobber %rax (and may touch the XMM regs), so loading Result first would
    return garbage from a value-returning function that also releases ARC
    params/locals.  For sret functions the caller's buffer already holds the
    result, so no load is needed. }
  Self.Emit(FExitLabel + ':');
  { Release ARC-managed locals (not params, not Result).
    Result is returned to the caller who owns it. }
  if ADecl.Body <> nil then
  begin
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType = nil then Continue;
      { String locals: release the string. }
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyString then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          Self.Emit(#9'callq _StringRelease');
        end
      { Class locals: release the object reference. }
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyClass then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          if TVarDecl(ADecl.Body.Decls.Items[I]).IsWeak then
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'callq _WeakClear');
          end
          else
          begin
            Self.Emit(Format(#9'movq %s, %%rdi',
              [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
            Self.Emit(#9'callq _ClassRelease');
          end;
        end
      { Interface locals: release the obj half of the fat pointer; the itab is
        static rodata and is not refcounted. }
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyInterface then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          if TVarDecl(ADecl.Body.Decls.Items[I]).IsWeak then
          begin
            Self.Emit(Format(#9'leaq %s, %%rdi',
              [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
            Self.Emit(#9'callq _WeakClear');
          end
          else
          begin
            Self.Emit(Format(#9'movq %s, %%rdi',
              [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
            Self.Emit(#9'callq _ClassRelease');
          end;
        end
      { Dyn-array locals: release the data buffer; balances the first-assignment
        retain (a dyn-array var assignment retains the new buffer). }
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyDynArray then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          Self.Emit(#9'callq _DynArrayRelease');
        end
      { Record locals with managed fields: release each ARC-managed field at
        scope exit.  The record block lives in the frame; its address goes into
        %rbx (callee-saved) so it survives the per-field release calls. }
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyRecord then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(#9'pushq %rbx');
          Self.Emit(Format(#9'leaq %s, %%rbx',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          Self.EmitRecordFieldReleases(
            TRecordTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType), '%rbx');
          Self.Emit(#9'popq %rbx');
        end
      { Static-array-of-INTERFACE locals (array[0..N] of IFoo): release each
        fat-pointer element's obj slot at scope exit.  The inline storage base
        goes into %rbx (callee-saved).

        Scope: ONLY interface elements.  The interface element store routes
        through EmitInterfaceToFieldSlotsAt, whose retain/release is balanced by
        this scope-exit release.  Static-array-of-CLASS/STRING/record locals are
        deliberately excluded: the existing element store retains unconditionally
        while `.Free`/aliasing in the owning code (e.g. the ELF writer's
        `RelaBuf: array[0..5] of TByteBuf`) already manages those lifetimes, so a
        blanket scope-exit release double-frees and corrupts the heap.  Closing
        that gap requires reconciling the element store's ARC with the manual
        management first; it is tracked separately. }
      else if (TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyStaticArray)
        and (TStaticArrayTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).ElementType <> nil)
        and (TStaticArrayTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType).ElementType.Kind = tyInterface) then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(#9'pushq %rbx');
          Self.Emit(Format(#9'leaq %s, %%rbx',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          Self.EmitStaticArrayReleaseElems(
            TStaticArrayTypeDesc(TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType),
            '%rbx', False);
          Self.Emit(#9'popq %rbx');
        end;
    end;
  end;
  { ARC: release string/class/interface value params on exit — matches the
    entry retain pass.  Skip var, out, open-array and const params (const
    params are caller-protected; see the entry pass comment). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam or P.IsOpenArray or P.IsConstParam then Continue;
    if P.ResolvedType = nil then Continue;
    if P.ResolvedType.Kind = tyString then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _StringRelease');
    end
    else if P.ResolvedType.Kind = tyClass then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(P.ParamName)]));
      Self.Emit(#9'callq _ClassRelease');
    end
    else if P.ResolvedType.Kind = tyInterface then
    begin
      Self.Emit(Format(#9'movq %s, %%rdi',
        [Self.IntfObjOperand(P.ParamName, False)]));
      Self.Emit(#9'callq _ClassRelease');
    end
    else if P.ResolvedType.Kind = tyRecord then
    begin
      Self.Emit(#9'pushq %rbx');
      Self.Emit(Format(#9'movq %s, %%rbx', [Self.VarOperand(P.ParamName)]));
      Self.EmitRecordFieldReleases(TRecordTypeDesc(P.ResolvedType), '%rbx');
      Self.Emit(#9'popq %rbx');
    end;
  end;
  { Now that every ARC release call is done (none can clobber the result), load
    Result into %rax (int) or %xmm0 (float).  sret functions return via the
    caller's buffer and need no load.  Reg-return records load into
    rax/rdx/xmm0/xmm1 per the SysV classification. }
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if (ADecl.ResolvedReturnType.Kind = tyRecord) and (FRecRetClass <> rcSret) then
      Self.EmitRecordReturnEpilogue(
        TRecordTypeDesc(ADecl.ResolvedReturnType), FRecRetClass)
    else if IsFloatFamily(ADecl.ResolvedReturnType) then
      Self.EmitLoadFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType)
    else
      Self.EmitLoadVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
  end;
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.DbgEndFunc();
  Self.Emit('.type ' + Sym + ', @function');

  FExitLabel    := '';
  FCapturedVars := nil;
  Self.ClearFrame();
end;

{ Emit the program entry function.

  The Blaise runtime expects an exported `main(argc, argv)` returning int.  It
  must call $_SetArgs(argc, argv) before any program code, then run the body,
  then return 0.  This mirrors the QBE backend's $main shape (see the QBE IR
  for an empty program).

  The body statements are lowered between the _SetArgs call and the return-0
  epilogue.  After `pushq %rbp` the stack is 16-byte aligned, and expression
  evaluation balances its push/pop pairs, so %rsp stays aligned at every call
  site. }
procedure TX86_64Backend.EmitProgram(AProg: TProgram);
var
  I, J:  Integer;
  VD:    TVarDecl;
  Decl:  TMethodDecl;
begin
  FCurrentUnitName := AProg.Name;
  FDbgSrcFile := '';
  FProgramName := AProg.Name;
  { Register declared program-level variables as global slots. }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        if VD.IsWeak then
          Self.MarkWeakGlobal(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(VD.Names.Strings[J], VD.InitConst);
      end;
  end;

  { Class method bodies before standalone procedures. }
  Self.EmitClassMethods(AProg.Block.TypeDecls, AProg.GenericInstances,
                        AProg.GenericRecordInstances, AProg.GenericMethodInstances);

  { Array-typed constants — emit data sections so const arrays are defined
    as assembly labels before being referenced in code.  Covers block-level
    consts and local consts inside procedure bodies. }
  Self.EmitArrayConstData(AProg.Block, '');

  { Standalone procedures/functions, then $main. }
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;     { class methods: above }
    if Decl.TypeParams <> nil then Continue;       { generic templates: skip }
    if Decl.Body = nil then Continue;              { forward decls }
    if Decl.IsExternal then Continue;              { external: later }
    Self.EmitFunctionDef(Decl, True);
  end;

  { Concrete generic function instances. }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    Self.EmitFunctionDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Items[I]).MethodDecl, True);

  { Pre-count try stmts in the program body so VarOperand resolves
    _exc_frame_N as globals (FFrame is nil in main, so the global path is
    taken).  The actual .bss labels are emitted in EmitDataSection. }
  FProgExcFrameCount := 0;
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    FProgExcFrameCount := FProgExcFrameCount +
      Self.CountTryStmts(TASTStmt(AProg.Block.Stmts.Items[I]));
  { Jumbo-set scratch in main: main has no stack frame, so set literal / set-op
    result buffers live in static .bss.  A jumbo set value can appear in any
    expression in the program body (e.g. 'X in [members]' over a >64 enum), so
    always reserve the two scratch buffers. }
  FProgHasJumboSet := True;
  { Reset per-function state before emitting the program body. }
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FForEndNext   := 0;
  FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
  { Program-level vars are globals (always pinned as const args), so the
    blocklist only needs to be free of stale entries from the last function. }
  FConstArgUnsafe.Clear();

  Self.Emit('.text');
  Self.Emit('.globl main');
  Self.DbgBeginFunc('main');
  Self.Emit('main:');
  { Prologue: establish a frame.  argc is in %edi, argv in %rsi per SysV. }
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  { _SetArgs(argc, argv): args already in %edi/%rsi — pass through.  Must
    precede _BlaiseInit, which clobbers the SysV arg registers. }
  Self.Emit(#9'callq _SetArgs');
  { RTL one-time setup the per-unit init dispatch below misses for archive
    units (e.g. blaise_weak's WeakMutex — see _BlaiseInit). }
  Self.Emit(#9'callq _BlaiseInit');
  { Call initialization sections of imported units in order. }
  for I := 0 to FUnitInitNames.Count - 1 do
    Self.Emit(#9'callq ' + FUnitInitNames.Strings[I] + '_init');
  if FDebugMode then
    Self.Emit(#9'callq _LeakTrackerEnable');
  { Program body. }
  FExitLabel := Self.NewLabel('main_exit');
  Self.EmitStmtList(AProg.Block.Stmts);
  { Epilogue: Exit lands here; release ARC-managed globals, then return 0.
    Mirrors the QBE backend, which releases each managed global at @main_exit so
    a global object's _FieldCleanup (and hence its destructor) runs at program
    end. }
  Self.Emit(FExitLabel + ':');
  FExitLabel := '';
  Self.EmitGlobalReleases();
  Self.Emit(#9'movl $0, %eax');
  Self.Emit(#9'leave');
  Self.Emit(#9'ret');
  Self.DbgEndFunc();
  Self.Emit('.type main, @function');
  { Mark the stack non-executable (matches QBE output). }
  Self.Emit('.section .note.GNU-stack,"",@progbits');

  { Data section: all registered global integer/float/record slots. }
  Self.EmitDataSection();
  { Class data section: typeinfo, vtables, field-cleanup functions. }
  Self.EmitClassSection(AProg.Block.TypeDecls, AProg.GenericInstances,
                        AProg.SymbolTable);
  { Interface data: typeinfo tokens, itabs, impllists.  Emitted after the class
    section so the class-name strings and method symbols it references exist. }
  Self.Emit('.data');
  Self.EmitInterfaceDefs(AProg.Block.TypeDecls, AProg.GenericInstances,
                         AProg.GenericIntfInstances, AProg.SymbolTable);
end;

{ ------------------------------------------------------------------ }
{ Whole-program multi-unit: emit one dependency unit                   }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitUnit(AUnit: TUnit);
var
  I, J:      Integer;
  ImplDecl:  TMethodDecl;
  VD:        TVarDecl;
  UnitSym:   TSymbolTable;
  IntfNames: TStringList;
  EmptyGen:  TObjectList;   { empty generic-instance list for the ImplBlock
                             second-pass calls (generics are per-unit and were
                             emitted once with the IntfBlock pass — never
                             duplicate them). }
  SavedDOU:  string;        { prior FSymTable.DefineOwningUnit, restored at end }
begin
  FCurrentUnitName := AUnit.Name;
  FDbgSrcFile := AUnit.SourceFile;
  { Establish THIS unit as the symbol-table viewing context so that resolving
    the unit's own implementation-section (IsImplPrivate) types — for
    ClassSymName mangling and EmitClassSection's FindType — is not suppressed
    by the cross-unit-leak guard in TSymbolTable.Lookup.  Restored at end. }
  SavedDOU := '';
  if FSymTable <> nil then
  begin
    SavedDOU := FSymTable.DefineOwningUnit;
    FSymTable.DefineOwningUnit := AUnit.Name;
  end;
  { Register the unit's global variables (interface + implementation sections)
    as data slots, mirroring EmitProgram's program-global registration. }
  for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(AUnit.IntfBlock.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray, tyInterface])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(VD.Names.Strings[J], VD.InitConst);
      end;
  end;
  for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
  begin
    VD := TVarDecl(AUnit.ImplBlock.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray, tyInterface])) then
      for J := 0 to VD.Names.Count - 1 do
      begin
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
        if VD.IsThreadVar then
          Self.MarkThreadVar(VD.Names.Strings[J]);
        if VD.InitConst <> nil then
          FGlobalInits.Add(VD.Names.Strings[J], VD.InitConst);
      end;
  end;

  EmptyGen := TObjectList.Create(False);   { not owned — borrowed slots only }

  { Class / record method bodies declared in the interface block, plus any
    generic class/record instances declared in this unit.  After
    LinkClassMethodImpls the definition's TMethodDecl nodes hold the bodies. }
  Self.EmitClassMethods(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                        AUnit.GenericRecordInstances, AUnit.GenericMethodInstances);
  { Classes/records declared in the IMPLEMENTATION section: their method bodies
    are emitted too (generics already covered by the IntfBlock pass above, so
    pass empty generic lists to avoid re-emitting them). }
  Self.EmitClassMethods(AUnit.ImplBlock.TypeDecls, EmptyGen, EmptyGen, EmptyGen);

  { Array-typed constants from both interface and implementation blocks. }
  Self.EmitArrayConstData(AUnit.IntfBlock, '');
  Self.EmitArrayConstData(AUnit.ImplBlock, '');

  { Standalone procedures/functions from the implementation block.  Skip class
    method stubs (OwnerTypeName <> '': their bodies were transferred to the
    class definition and emitted above), generic templates, forward decls, and
    externals.  In monolithic mode, only interface-exported functions need
    .globl — implementation-only helpers stay local to avoid collisions with
    the same symbols in the RTL archive. }
  IntfNames := TStringList.Create();
  try
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;
      if ImplDecl.TypeParams <> nil then Continue;
      if ImplDecl.Body = nil then Continue;
      if ImplDecl.IsExternal then Continue;
      Self.EmitFunctionDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
    end;
  finally
    IntfNames.Free();
  end;

  { Concrete generic function instances declared in this unit. }
  for I := 0 to AUnit.GenericFuncInstances.Count - 1 do
    Self.EmitFunctionDef(
      TGenericFuncInstance(AUnit.GenericFuncInstances.Items[I]).MethodDecl, True);

  { Initialization section: emit as a function <Unit>_init that the program's
    $main calls before the program body.  (Finalization is not yet wired into
    the native main footer; emitted but only init is invoked.) }
  if (AUnit.InitStmts <> nil) and (AUnit.InitStmts.Count > 0) then
  begin
    { Re-assert THIS unit as the viewing context.  Earlier emit passes in this
      procedure (method-body type resolution that walks the uses chain) can
      leave DefineOwningUnit pointing at a dependency unit; if the init block
      references one of THIS unit's own implementation-section (IsImplPrivate)
      classes — e.g. a metaclass value passed to a registrar — TSymbolTable.Lookup
      would otherwise suppress it as a cross-unit leak and ClassSymName would fall
      back to a bare, unqualified, undefined typeinfo symbol (silent link-time
      garbage).  See the impl-section-class visibility guard in
      TSymbolTable.Lookup. }
    if FSymTable <> nil then
      FSymTable.DefineOwningUnit := AUnit.Name;
    FUnitInitNames.Add(NativeMangle(AUnit.Name));
    Self.ClearFrame();
    FExitLabel := '';
    FExcDepth     := 0;
    FExcFrameNext := 0;
    FForEndNext   := 0;
    FFinallyStack.Free();
  FFinallyStack := TList<TCompoundStmt>.Create();
    Self.Emit('.text');
    Self.Emit('.globl ' + NativeMangle(AUnit.Name) + '_init');
    Self.Emit(NativeMangle(AUnit.Name) + '_init:');
    Self.Emit(#9'pushq %rbp');
    Self.Emit(#9'movq %rsp, %rbp');
    Self.EmitStmtList(AUnit.InitStmts);
    Self.Emit(#9'movl $0, %eax');
    Self.Emit(#9'leave');
    Self.Emit(#9'ret');
    Self.Emit('.type ' + NativeMangle(AUnit.Name) + '_init, @function');
  end;

  { Class data section: typeinfo, vtables, field-cleanup functions for the
    unit's classes.  System defs (TObject/TCustomAttribute) emitted once. }
  { In the whole-program multi-unit model the unit is analysed as part of the
    program, so AUnit.SymbolTable is nil and its resolved types live in the
    program's (global) symbol table — supplied via SetSymbolTable before
    AppendUnit.  Prefer the unit's own table when it was analysed standalone. }
  if AUnit.SymbolTable <> nil then
    UnitSym := AUnit.SymbolTable
  else
    UnitSym := FSymTable;
  { Re-assert the viewing context (see the init-block note above): the class
    section emits unit-qualified typeinfo/vtable/_FieldCleanup names via
    ClassSymName, which must resolve THIS unit's own impl-section classes. }
  if FSymTable <> nil then
    FSymTable.DefineOwningUnit := AUnit.Name;
  Self.EmitClassSection(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                        UnitSym);
  { Impl-section classes' typeinfo / vtable / _FieldCleanup (generics already
    emitted above — empty list here). }
  Self.EmitClassSection(AUnit.ImplBlock.TypeDecls, EmptyGen, UnitSym);
  { Interface data: typeinfo tokens, itabs, impllists. }
  Self.Emit('.data');
  Self.EmitInterfaceDefs(AUnit.IntfBlock.TypeDecls, AUnit.GenericInstances,
                         AUnit.GenericIntfInstances, UnitSym);
  Self.EmitInterfaceDefs(AUnit.ImplBlock.TypeDecls, EmptyGen, EmptyGen, UnitSym);

  EmptyGen.Free();
  if FSymTable <> nil then
    FSymTable.DefineOwningUnit := SavedDOU;
end;

procedure TX86_64Backend.NoteDepInitUnit(const AUnitName: string;
  AHasInit: Boolean);
begin
  { Separate-compilation: the dep's body (and its <Unit>_init) is in its own
    object; record the mangled name so EmitProgram's $main calls it.  Mangling
    matches EmitUnit's FUnitInitNames.Add(NativeMangle(AUnit.Name)). }
  if AHasInit then
    FUnitInitNames.Add(NativeMangle(AUnitName));
  { Record the imported unit (raw name, matching TSymbol.OwningUnit) so
    EmitDataSection emits globals owned by it as references, not definitions —
    the cached object owns the definition. }
  FImportedUnits.Add(AUnitName);
end;

procedure TX86_64Backend.FinalizeEmit;
begin
  if FFinalized then Exit;
  FFinalized := True;
  Self.EmitDataSection();
end;

end.
