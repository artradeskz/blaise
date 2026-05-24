{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uParser;

// Recursive-descent parser for the Blaise grammar:
//   Program        ::= 'program' Ident ';' [Uses] Block '.'
//   Uses           ::= 'uses' Ident {',' Ident} ';'
//   Block          ::= [TypeSection] [VarSection] 'begin' StmtList 'end'
//   TypeSection    ::= 'type' TypeDecl {TypeDecl}
//   TypeDecl       ::= Ident '=' (RecordDef | ClassDef) ';'
//   RecordDef      ::= 'record' FieldList 'end'
//   ClassDef       ::= 'class' ['(' Ident ')'] FieldList MethodList 'end'
//   FieldList      ::= {FieldDecl}
//   FieldDecl      ::= IdentList ':' TypeName ';'
//   MethodList     ::= {MethodDecl}
//   MethodDecl     ::= 'procedure' Ident ['(' ParamList ')'] ';' Block ';'
//   ParamList      ::= ParamGroup {';' ParamGroup}
//   ParamGroup     ::= IdentList ':' TypeName
//   VarSection     ::= 'var' VarDecl {VarDecl}
//   VarDecl        ::= IdentList ':' TypeName ';'
//   StmtList       ::= Stmt {';' Stmt} [';']
//   Stmt           ::= FieldAssignment | MethodCall | Assignment | ProcCall | empty
//   FieldAssign    ::= Ident '.' Ident ':=' Expr
//   MethodCall     ::= Ident '.' Ident ['(' [ExprList] ')']
//   Assignment     ::= Ident ':=' Expr
//   ProcCall       ::= Ident ['(' [ExprList] ')']
//   ExprList       ::= Expr {',' Expr}
//   Expr           ::= Term (('+' | '-') Term)*
//   Term           ::= Factor (('*' | '/' | 'div') Factor)*
//   Factor         ::= IntLit | StringLit | Ident '.' Ident | Ident | '(' Expr ')'
//   TypeName       ::= Ident

interface

uses
  SysUtils, Classes, contnrs, uLexer, uAST, uStrCompat;

type
  EParseError = class(Exception);

  TParser = class
  private
    FLexer:      TLexer;
    FCurrent:    TToken;
    FLookahead:  TToken;  { one-token lookahead }
    FLookahead2: TToken;  { two-token lookahead for generic disambiguation }

    procedure Advance;
    function  PeekKind: TTokenKind;
    function  PeekKind2: TTokenKind;  { two tokens ahead }
    procedure Expect(AKind: TTokenKind);
    function  Check(AKind: TTokenKind): Boolean;
    function  CheckUnitNamePart: Boolean;
    function  ParseTypeName: string;  { reads Ident optionally followed by '<' ArgList '>' }

    function  ParseProgram: TProgram;
    procedure ParseUsesList(AList: TStringList);
    procedure ParseUses(AProg: TProgram);
    function  ParseBlock: TBlock;
    procedure ParseTypeSection(ABlock: TBlock);
    procedure ParseTypeDecl(ABlock: TBlock);
    procedure ParseConstBlock(AList: TObjectList);
    function  TryParseConstIntTypecast(out AValue: Int64): Boolean;
    function  CurrentIsConstBitOp: Boolean;
    function  ConsumeConstBitOpName: string;
    function  CollectConstBitOpExpr(const AFirstStr: string;
                                    AFirstIsIdent: Boolean): TStringList;
    function  ParseEnumDef: TEnumTypeDef;
    function  ParseSetDef: TSetTypeDef;
    function  ParseRecordDef: TRecordTypeDef;
    function  ParseProceduralTypeDef: TProceduralTypeDef;
    function  ParseGenericName: string;  { reads IDENT optionally followed by '<' TypeArgs '>' }
    function  ParseClassDef: TClassTypeDef;
    function  ParseInterfaceDef: TInterfaceTypeDef;
    procedure ParseFieldDecl(AFields: TObjectList);
    procedure ParseAttributeList(AAttrs: TStringList);
    function  ParsePropertyDecl: TPropertyDecl;
    function  ParseMethodDecl(IsFunction: Boolean; ACanHaveNestedProcs: Boolean = False): TMethodDecl;
    procedure ParseParamList(AParams: TObjectList);
    procedure ParseStandaloneDecl(ABlock: TBlock);
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseIfStmt: TIfStmt;
    function  ParseWhileStmt: TWhileStmt;
    function  ParseRepeatStmt: TRepeatStmt;
    function  ParseForStmt: TASTStmt;
    function  ParseTryStmt: TASTStmt;
    function  ParseExceptHandlerClause: TExceptHandlerClause;
    procedure ParseBodyInto(ATarget: TCompoundStmt; AStop1, AStop2: TTokenKind);
    function  ParseRaiseStmt: TRaiseStmt;
    function  ParseInheritedStmt: TInheritedCallStmt;
    function  ParseCaseStmt: TCaseStmt;
    function  ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
    function  ParseCompoundStmt: TCompoundStmt;
    function  ParseExpr: TASTExpr;
    function  ParseAddSub: TASTExpr;
    function  ParseTerm: TASTExpr;
    function  ParseFactor: TASTExpr;
    procedure ParseArgList(ACall: TProcCall);
    procedure ParseMethodCallArgList(ACall: TMethodCallStmt);
  public
    constructor Create(ALexer: TLexer);
    function Parse: TProgram;
    function ParseUnit: TUnit;
    { True iff the primed first token is `unit` — caller forks to
      ParseUnit instead of Parse.  Safe to call straight after Create. }
    function IsUnitTopLevel: Boolean;
  end;

implementation

constructor TParser.Create(ALexer: TLexer);
begin
  inherited Create;
  FLexer      := ALexer;
  FCurrent    := FLexer.Next;
  FLookahead  := FLexer.Next;
  FLookahead2 := FLexer.Next;
end;

procedure TParser.Advance;
begin
  FCurrent    := FLookahead;
  FLookahead  := FLookahead2;
  FLookahead2 := FLexer.Next;
end;

function TParser.PeekKind: TTokenKind;
begin
  Result := FLookahead.Kind;
end;

function TParser.PeekKind2: TTokenKind;
begin
  Result := FLookahead2.Kind;
end;

{ Parse a type name, including generic instantiations.
  Returns 'Integer', 'TBox<Integer>', 'TPair<string,Integer>', etc.
  Spaces around commas are stripped for a canonical representation. }
function TParser.ParseTypeName: string;
var
  LStr, HStr, ElemTypeName: string;
begin
  { Array type: static 'array[L..H] of T' or dynamic 'array of T' }
  if Check(tkArray) then
  begin
    Advance;  { consume 'array' }
    if Check(tkLBracket) then
    begin
      { Static array: array[L..H] of T }
      Advance;  { consume '[' }
      if not Check(tkIntLit) then
        raise EParseError.Create(Format('Expected integer bound at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      LStr := FCurrent.Value;
      Advance;
      Expect(tkDotDot);
      if not Check(tkIntLit) then
        raise EParseError.Create(Format('Expected integer bound at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      HStr := FCurrent.Value;
      Advance;
      Expect(tkRBracket);
      Expect(tkOf);
      ElemTypeName := Self.ParseTypeName;
      Result := Format('array[%s..%s] of %s', [LStr, HStr, ElemTypeName]);
    end
    else
    begin
      { Dynamic array: array of T }
      Expect(tkOf);
      ElemTypeName := Self.ParseTypeName;
      Result := 'array of ' + ElemTypeName;
    end;
    Exit;
  end;
  { Pointer-to type: '^TypeName' }
  if Check(tkCaret) then
  begin
    Advance;  { consume '^' }
    Result := '^' + Self.ParseTypeName;  { Self. forces recursive call, not result-var read }
    Exit;
  end;
  { Metaclass reference: 'class of TFoo' — encoded as 'class of <Name>'.
    The base class name is parsed via ParseTypeName so that 'class of
    TList<Integer>' (a metaclass of a generic instance) is also valid. }
  if Check(tkClass) then
  begin
    Advance;  { consume 'class' }
    Expect(tkOf);
    Exit('class of ' + Self.ParseTypeName);
  end;
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected type name at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Result := FCurrent.Value;
  Advance;
  if Check(tkLessThan) then
  begin
    Advance;  { consume '<' }
    Result := Result + '<';
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected type argument after ''<'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result := Result + FCurrent.Value;
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected type argument after '','' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result := Result + ',' + FCurrent.Value;
      Advance;
    end;
    Expect(tkGreaterThan);
    Result := Result + '>';
  end;
end;

procedure TParser.Expect(AKind: TTokenKind);
var
  gotName, gotDetail: string;
begin
  if FCurrent.Kind <> AKind then
  begin
    gotName := TokenKindName(FCurrent.Kind);
    if FCurrent.Value <> gotName then
      gotDetail := ' (''' + FCurrent.Value + ''')'
    else
      gotDetail := '';
    raise EParseError.Create(Format(
      'Expected ''%s'' but got ''%s''%s at line %d col %d in %s',
      [TokenKindName(AKind), gotName, gotDetail,
       FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  Advance;
end;

function TParser.Check(AKind: TTokenKind): Boolean;
begin
  Result := FCurrent.Kind = AKind;
end;

function TParser.CheckUnitNamePart: Boolean;
begin
  Result := (FCurrent.Kind = tkIdent) or
            (FCurrent.Kind in [tkInitialization, tkFinalization, tkProgram,
              tkUses, tkType, tkRecord, tkClass, tkProcedure, tkFunction,
              tkVar, tkBegin, tkEnd, tkIf, tkThen, tkElse, tkWhile, tkDo,
              tkFor, tkTo, tkDownto, tkRepeat, tkUntil, tkTry, tkFinally,
              tkExcept, tkRaise, tkNil, tkUnit, tkIntf, tkImplementation,
              tkVirtual, tkOverride, tkExternal, tkIs, tkAs, tkAnd, tkOr,
              tkNot, tkExit, tkBreak, tkContinue, tkInherited, tkCase,
              tkOf, tkArray, tkSet, tkIn, tkShl, tkShr, tkSar, tkXor, tkConst,
              tkOut, tkConstructor, tkDestructor, tkDiv, tkMod]);
end;

{ ------------------------------------------------------------------ }

function TParser.Parse: TProgram;
begin
  Result := ParseProgram;
end;

function TParser.IsUnitTopLevel: Boolean;
begin
  Result := FCurrent.Kind = tkUnit;
end;

function TParser.ParseProgram: TProgram;
begin
  Result := TProgram.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkProgram);

    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected program name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;

    Expect(tkSemicolon);

    if Check(tkUses) then
      ParseUses(Result);

    Result.Block := ParseBlock;

    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format(
        'Unexpected tokens after program end at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseUsesList(AList: TStringList);
var
  UName: string;
begin
  Expect(tkUses);
  if not CheckUnitNamePart then
    raise EParseError.Create(Format('Expected unit name after ''uses'' at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  UName := FCurrent.Value;
  Advance;
  while Check(tkDot) do
  begin
    Advance;
    if not CheckUnitNamePart then
      raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    UName := UName + '.' + FCurrent.Value;
    Advance;
  end;
  AList.Add(UName);
  while Check(tkComma) do
  begin
    Advance;
    if not CheckUnitNamePart then
      raise EParseError.Create(Format('Expected unit name after '','' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    UName := FCurrent.Value;
    Advance;
    while Check(tkDot) do
    begin
      Advance;
      if not CheckUnitNamePart then
        raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      UName := UName + '.' + FCurrent.Value;
      Advance;
    end;
    AList.Add(UName);
  end;
  Expect(tkSemicolon);
end;

procedure TParser.ParseUses(AProg: TProgram);
begin
  ParseUsesList(AProg.UsedUnits);
end;

function TParser.ParseBlock: TBlock;
begin
  Result := TBlock.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    { Accept any number of type/var/procedure/function sections in any order,
      as required when concatenating multiple Pascal units into one file. }
    while Check(tkType) or Check(tkVar) or Check(tkProcedure) or
          Check(tkFunction) or Check(tkConst) or
          Check(tkConstructor) or Check(tkDestructor) do
    begin
      if Check(tkType) then
        ParseTypeSection(Result)
      else if Check(tkVar) then
        ParseVarBlock(Result)
      else if Check(tkConst) then
        ParseConstBlock(Result.ConstDecls)
      else
        ParseStandaloneDecl(Result);
    end;

    Expect(tkBegin);
    ParseStmtList(Result);
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Type section                                                        }
{ ------------------------------------------------------------------ }

procedure TParser.ParseTypeSection(ABlock: TBlock);
begin
  Expect(tkType);
  while Check(tkIdent) or Check(tkLBracket) do
    ParseTypeDecl(ABlock);
end;

procedure TParser.ParseTypeDecl(ABlock: TBlock);
var
  TD:               TTypeDecl;
  GD:               TGenericTypeDef;
  GID:              TGenericInterfaceDef;
  AD:               TTypeAliasDef;
  ParamNames:       TStringList;
  ParamConstraints: TStringList;
  IsGeneric:        Boolean;
  Constraint:       string;
  ClassAttrs:       TStringList;
begin
  ClassAttrs := TStringList.Create;
  try
  ParseAttributeList(ClassAttrs);
  TD := TTypeDecl.Create;
  TD.Line := FCurrent.Line;
  TD.Col  := FCurrent.Col;
  try
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected type name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    TD.Name := FCurrent.Value;
    Advance;
    { Check for generic type parameters: TBox<T>, TPair<K,V>, IFoo<T> }
    IsGeneric := Check(tkLessThan);
    if IsGeneric then
    begin
      Advance;  { consume '<' }
      ParamNames       := TStringList.Create;
      ParamConstraints := TStringList.Create;
      try
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        ParamNames.Add(FCurrent.Value);
        Advance;
        { Optional constraint: T : (class | record | TypeName) }
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance;
          if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        ParamConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format(
              'Expected type parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          ParamNames.Add(FCurrent.Value);
          Advance;
          Constraint := '';
          if Check(tkColon) then
          begin
            Advance;
            if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
            else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
            else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
            else
              raise EParseError.Create(Format(
                'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          end;
          ParamConstraints.Add(Constraint);
        end;
        Expect(tkGreaterThan);
        Expect(tkEquals);
        if Check(tkIntf) then
        begin
          GID            := TGenericInterfaceDef.Create;
          GID.Line       := TD.Line;
          GID.Col        := TD.Col;
          GID.ParamNames.AddStrings(ParamNames);
          GID.ParamConstraints.AddStrings(ParamConstraints);
          GID.IntfDef := ParseInterfaceDef;
          TD.Def := GID;
        end
        else
        begin
          if not Check(tkClass) then
            raise EParseError.Create(Format(
              'Generic type must be a class or interface at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          GD            := TGenericTypeDef.Create;
          GD.Line       := TD.Line;
          GD.Col        := TD.Col;
          GD.ParamNames.AddStrings(ParamNames);
          GD.ParamConstraints.AddStrings(ParamConstraints);
          GD.ClassDef := ParseClassDef;
          GD.ClassDef.Attributes.AddStrings(ClassAttrs);
          TD.Def := GD;
        end;
      finally
        ParamConstraints.Free;
        ParamNames.Free;
      end;
    end
    else
    begin
      Expect(tkEquals);
      if Check(tkPacked) then
      begin
        { Only `packed record` is supported.  `packed class` and `packed
          array` are legal Delphi/FPC syntax but Blaise rejects them
          explicitly so users get a clear error rather than silent no-op. }
        Advance;
        if not Check(tkRecord) then
          raise EParseError.Create(Format(
            '''packed'' may only precede ''record'' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TD.Def := ParseRecordDef;
        TRecordTypeDef(TD.Def).IsPacked := True;
      end
      else if Check(tkRecord) then
        TD.Def := ParseRecordDef
      else if Check(tkClass) and (PeekKind = tkOf) then
      begin
        { Metaclass alias: type TFooClass = class of TFoo;  Use the
          generic type-name parser, which already encodes the metaclass
          form as 'class of <Name>'. }
        AD := TTypeAliasDef.Create;
        AD.TypeName := Self.ParseTypeName;
        TD.Def := AD;
      end
      else if Check(tkClass) then
      begin
        TD.Def := ParseClassDef;
        TClassTypeDef(TD.Def).Attributes.AddStrings(ClassAttrs);
      end
      else if Check(tkIntf) then
        TD.Def := ParseInterfaceDef
      else if Check(tkLParen) then
        TD.Def := ParseEnumDef
      else if Check(tkSet) then
        TD.Def := ParseSetDef
      else if Check(tkFunction) or Check(tkProcedure) then
        TD.Def := ParseProceduralTypeDef
      else if Check(tkArray) or Check(tkCaret) or Check(tkIdent) then
      begin
        { Array alias:   type TArr = array[L..H] of T;
          Pointer alias: type PFoo = ^TFoo;
          Simple alias:  type TMyInt = Integer;  (ident rhs) }
        AD := TTypeAliasDef.Create;
        AD.TypeName := Self.ParseTypeName;
        TD.Def := AD;
      end
      else
        raise EParseError.Create(Format(
          'Expected ''record'', ''class'', ''interface'', ''('', ''set'', ''function'', ''procedure'', or type name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
    Expect(tkSemicolon);
    ABlock.TypeDecls.Add(TD);
  except
    TD.Free;
    raise;
  end;
  finally
    ClassAttrs.Free;
  end;
end;

{ Recognise a TypeName(IntLit) or TypeName(-IntLit) cast in a const-init
  position and yield the truncated integer value.  Returns False (without
  consuming any tokens) when the current token is not a known integer
  type name followed by '('.

  The cast applies the type's bit-width as an unsigned truncation mask;
  signed types then sign-extend back to Int64 so e.g. Integer(-11) round-
  trips to -11 while LongWord(-11) yields $FFFFFFF5 (4294967285).  Const
  init only — full-expression casts are handled by ParseFactor. }
function TParser.TryParseConstIntTypecast(out AValue: Int64): Boolean;
var
  TypeName: string;
  Width:    Integer;  { bit-width of the target type; 64 = no truncation }
  IsSigned: Boolean;
  Negate:   Boolean;
  Raw:      Int64;
  Mask:     Int64;
  SignBit:  Int64;
begin
  Result := False;
  if not Check(tkIdent) then Exit;
  if PeekKind <> tkLParen then Exit;
  TypeName := FCurrent.Value;
  Width := 0; IsSigned := False;
  if SameText(TypeName, 'Byte') then
    begin Width := 8;  IsSigned := False; end
  else if SameText(TypeName, 'ShortInt') then
    begin Width := 8;  IsSigned := True; end
  else if SameText(TypeName, 'SmallInt') or SameText(TypeName, 'Int16') then
    begin Width := 16; IsSigned := True; end
  else if SameText(TypeName, 'Word') or SameText(TypeName, 'UInt16') then
    begin Width := 16; IsSigned := False; end
  else if SameText(TypeName, 'Integer') or SameText(TypeName, 'LongInt') then
    begin Width := 32; IsSigned := True; end
  else if SameText(TypeName, 'Cardinal') or SameText(TypeName, 'LongWord')
       or SameText(TypeName, 'UInt32') then
    begin Width := 32; IsSigned := False; end
  else if SameText(TypeName, 'Int64') then
    begin Width := 64; IsSigned := True; end
  else if SameText(TypeName, 'UInt64') or SameText(TypeName, 'QWord')
       or SameText(TypeName, 'PtrUInt') then
    begin Width := 64; IsSigned := False; end
  else
    Exit;  { unknown / non-integer type name — not our cast }
  Advance;          { consume type name }
  Expect(tkLParen);
  Negate := False;
  if Check(tkMinus) then begin Negate := True; Advance; end;
  if not Check(tkIntLit) then
    raise EParseError.Create(Format(
      'Expected integer literal inside ''%s(...)'' const cast at line %d col %d in %s',
      [TypeName, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Raw := ParseIntLiteral(FCurrent.Value);
  if Negate then Raw := -Raw;
  Advance;
  Expect(tkRParen);
  { No truncation needed for 64-bit targets — the literal already fits. }
  if Width < 64 then
  begin
    Mask    := (Int64(1) shl Width) - 1;
    SignBit := Int64(1) shl (Width - 1);
    Raw     := Raw and Mask;
    { Sign-extend by toggling the sign bit and subtracting it back. }
    if IsSigned and ((Raw and SignBit) <> 0) then
      Raw := Raw - (SignBit shl 1);
  end;
  AValue := Raw;
  Result := True;
end;

{ True when FCurrent is one of the bitwise operators legal inside a
  const initialiser: 'or', 'and', 'xor', 'shl', 'shr'.  Used to detect
  the start of a deferred bit-op expression chain after the first
  operand has been parsed. }
function TParser.CurrentIsConstBitOp: Boolean;
begin
  Result := Check(tkOr)  or Check(tkAnd) or Check(tkXor)
         or Check(tkShl) or Check(tkShr);
end;

{ Map current bit-op token to its lowercase name, then advance past it.
  Caller has already verified CurrentIsConstBitOp. }
function TParser.ConsumeConstBitOpName: string;
begin
  case FCurrent.Kind of
    tkOr:  Result := 'or';
    tkAnd: Result := 'and';
    tkXor: Result := 'xor';
    tkShl: Result := 'shl';
    tkShr: Result := 'shr';
  else
    Result := '';  { unreachable — caller gated }
  end;
  Advance;
end;

{ Build a deferred bit-op expression token list, seeded with the first
  operand which has already been parsed by the caller.  Operands and
  operators alternate; operand entries are tagged on Objects[]:

    Objects[i] = nil          → integer literal (the string is the int)
    Objects[i] = TObject(1)   → ident reference
    Objects[i] = TObject(2)   → operator name

  Each new operand may be an optionally-signed int literal, a
  TypeName(IntLit) cast, or a bare ident; trailing typecasts apply the
  same truncation rules as TryParseConstIntTypecast. }
function TParser.CollectConstBitOpExpr(const AFirstStr: string;
                                       AFirstIsIdent: Boolean): TStringList;
var
  OpName:    string;
  Sign:      Integer;
  Raw:       Int64;
  CastVal:   Int64;
begin
  Result := TStringList.Create;
  try
    if AFirstIsIdent then
      Result.AddObject(AFirstStr, TObject(1))
    else
      Result.AddObject(AFirstStr, nil);
    while CurrentIsConstBitOp do
    begin
      OpName := ConsumeConstBitOpName;
      Result.AddObject(OpName, TObject(2));
      Sign := 1;
      if Check(tkMinus) then begin Advance; Sign := -1; end;
      if Check(tkIdent) and (PeekKind = tkLParen)
         and TryParseConstIntTypecast(CastVal) then
      begin
        if Sign < 0 then CastVal := -CastVal;
        Result.AddObject(IntToStr(CastVal), nil);
      end
      else if Check(tkIntLit) then
      begin
        Raw := ParseIntLiteral(FCurrent.Value);
        if Sign < 0 then Raw := -Raw;
        Result.AddObject(IntToStr(Raw), nil);
        Advance;
      end
      else if Check(tkIdent) then
      begin
        if Sign < 0 then
          raise EParseError.Create(Format(
            'Unary minus on named constant operand is not supported '+
            'in const bit-op expression at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Result.AddObject(FCurrent.Value, TObject(1));
        Advance;
      end
      else
        raise EParseError.Create(Format(
          'Expected operand after ''%s'' in const bit-op expression '+
          'at line %d col %d in %s',
          [OpName, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseConstBlock(AList: TObjectList);
var
  CD:          TConstDecl;
  CastVal:     Int64;
  FirstOperand: string;
  FirstIsIdent: Boolean;
begin
  Expect(tkConst);
  while Check(tkIdent) do
  begin
    CD      := TConstDecl.Create;
    CD.Line := FCurrent.Line;
    CD.Col  := FCurrent.Col;
    CD.Name := FCurrent.Value;
    Advance;
    { Typed constant: const Name: TypeName = Value
      or:             const Name: array[IndexType] of ElemType = (v, ...) }
    if Check(tkColon) then
    begin
      Advance;
      if Check(tkArray) then
      begin
        { array-typed constant }
        Advance;
        Expect(tkLBracket);
        if Check(tkIntLit) then
        begin
          CD.ArrayLowBound := ParseIntLiteral(FCurrent.Value);
          Advance;
          Expect(tkDotDot);
          if not Check(tkIntLit) then
            raise EParseError.Create(Format(
              'Expected integer high bound in array const at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          CD.ArrayHighBound := ParseIntLiteral(FCurrent.Value);
          Advance;
          CD.ArrayIsRangeIndexed := True;
        end
        else if Check(tkIdent) then
        begin
          CD.ArrayIndexType := FCurrent.Value;
          Advance;
        end
        else
          raise EParseError.Create(Format(
            'Expected index type or range in array const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Expect(tkRBracket);
        Expect(tkOf);
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected element type name in array const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        CD.ArrayElemType := FCurrent.Value;
        Advance;
        CD.IsArrayConst := True;
      end
      else if Check(tkIdent) then
      begin
        CD.TypeName := FCurrent.Value;
        Advance;
      end
      else
        raise EParseError.Create(Format(
          'Expected type name after '':'' in const at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
    Expect(tkEquals);
    { Array const value list: (elem, elem, ...) }
    if CD.IsArrayConst then
    begin
      Expect(tkLParen);
      CD.ArrayElements := TStringList.Create;
      while True do
      begin
        { Each element may be a string literal, integer literal,
          optionally preceded by a minus sign, or float literal.
          Integer-typed elements may also be a bit-op chain (e.g.
          'FG_BLUE or 4'); when the chain references named consts
          it's deferred to semantic via ArrayElementParts. }
        FirstOperand := '';
        FirstIsIdent := False;
        if Check(tkMinus) then
        begin
          Advance;
          if Check(tkFloatLit) then
          begin
            CD.ArrayElements.Add('-' + FCurrent.Value);
            Advance;
          end
          else if Check(tkIntLit) then
          begin
            FirstOperand := '-' + FCurrent.Value;
            Advance;
            CD.ArrayElements.Add(FirstOperand);
          end
          else
            raise EParseError.Create(Format(
              'Expected numeric literal after minus in array const at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end
        else if Check(tkStringLit) then
        begin
          CD.ArrayElements.Add(FCurrent.Value);
          Advance;
        end
        else if Check(tkIntLit) then
        begin
          FirstOperand := FCurrent.Value;
          CD.ArrayElements.Add(FirstOperand);
          Advance;
        end
        else if Check(tkFloatLit) then
        begin
          CD.ArrayElements.Add(FCurrent.Value);
          Advance;
        end
        else if Check(tkIdent) and (PeekKind = tkLParen)
             and TryParseConstIntTypecast(CastVal) then
        begin
          { TypeName(IntLit) typecast — store the truncated value }
          FirstOperand := IntToStr(CastVal);
          CD.ArrayElements.Add(FirstOperand);
        end
        else if Check(tkIdent) then
        begin
          { named constant or boolean literal }
          FirstOperand := FCurrent.Value;
          FirstIsIdent := True;
          CD.ArrayElements.Add(FirstOperand);
          Advance;
        end
        else
          raise EParseError.Create(Format(
            'Expected constant value in array const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        { Bit-op continuation — only applies when the element started as an
          integer operand (FirstOperand was set), not strings/floats. }
        if (FirstOperand <> '') and CurrentIsConstBitOp then
        begin
          if CD.ArrayElementParts = nil then
          begin
            CD.ArrayElementParts := TObjectList.Create(True);
            { Pad with nils for prior elements that were not expressions. }
            while CD.ArrayElementParts.Count < CD.ArrayElements.Count - 1 do
              CD.ArrayElementParts.Add(nil);
          end;
          CD.ArrayElementParts.Add(
            CollectConstBitOpExpr(FirstOperand, FirstIsIdent));
        end
        else if CD.ArrayElementParts <> nil then
          CD.ArrayElementParts.Add(nil);
        if Check(tkComma) then
          Advance
        else
          Break;
      end;
      Expect(tkRParen);
      Expect(tkSemicolon);
      AList.Add(CD);
      Continue;
    end;
    if Check(tkMinus) then
    begin
      Advance;
      if Check(tkFloatLit) then
      begin
        CD.StrVal  := '-' + StripUnderscores(FCurrent.Value);
        CD.IsFloat := True;
        Advance;
      end
      else
      begin
        if not Check(tkIntLit) then
          raise EParseError.Create(Format('Expected numeric literal after minus in const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        CD.IntVal   := -ParseIntLiteral(FCurrent.Value);
        CD.IsString := False;
        Advance;
        if CurrentIsConstBitOp then
        begin
          CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CD.IntVal), False);
          CD.IntVal := 0;
        end;
      end;
    end
    else if Check(tkFloatLit) then
    begin
      CD.StrVal  := StripUnderscores(FCurrent.Value);
      CD.IsFloat := True;
      Advance;
    end
    else if Check(tkIntLit) then
    begin
      CD.IntVal   := ParseIntLiteral(FCurrent.Value);
      CD.IsString := False;
      Advance;
      if CurrentIsConstBitOp then
      begin
        CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CD.IntVal), False);
        CD.IntVal := 0;
      end;
    end
    else if Check(tkIdent) and (PeekKind = tkLParen)
         and TryParseConstIntTypecast(CastVal) then
    begin
      { TypeName(IntLit) typecast in scalar const init }
      CD.IsString := False;
      if CurrentIsConstBitOp then
      begin
        CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CastVal), False);
        CD.IntVal := 0;
      end
      else
        CD.IntVal := CastVal;
    end
    else if Check(tkIdent)
         and (PeekKind in [tkOr, tkAnd, tkXor, tkShl, tkShr]) then
    begin
      { Bit-op chain whose first operand is a named constant. }
      FirstOperand := FCurrent.Value;
      Advance;
      CD.IntExprTokens := CollectConstBitOpExpr(FirstOperand, True);
      CD.IsString := False;
    end
    else if Check(tkLBracket) then
    begin
      { Set-valued constant: const Name [: SetType] = [member, member, ...]
        or the empty set [].  Members are enum-constant identifiers; semantic
        resolves their ordinals and folds the bitmask. }
      CD.IsSet       := True;
      CD.SetElements := TStringList.Create;
      Advance;   { consume '[' }
      if not Check(tkRBracket) then
        while True do
        begin
          if not Check(tkIdent) then
            raise EParseError.Create(Format(
              'Expected set member identifier at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          CD.SetElements.Add(FCurrent.Value);
          Advance;
          if Check(tkComma) then
            Advance
          else
            Break;
        end;
      Expect(tkRBracket);
    end
    else if Check(tkStringLit) or Check(tkIdent) then
    begin
      CD.IsString := True;
      if Check(tkIdent) then
      begin
        CD.ConstParts := TStringList.Create;
        CD.ConstParts.AddObject(FCurrent.Value, TObject(1));
      end
      else
        CD.StrVal := FCurrent.Value;
      Advance;
      while Check(tkPlus) do
      begin
        Advance;
        if Check(tkStringLit) or Check(tkIdent) then
        begin
          if CD.ConstParts <> nil then
          begin
            if Check(tkIdent) then
              CD.ConstParts.AddObject(FCurrent.Value, TObject(1))
            else
              CD.ConstParts.AddObject(FCurrent.Value, nil);
          end
          else if Check(tkIdent) then
          begin
            CD.ConstParts := TStringList.Create;
            CD.ConstParts.AddObject(CD.StrVal, nil);
            CD.ConstParts.AddObject(FCurrent.Value, TObject(1));
            CD.StrVal := '';
          end
          else
            CD.StrVal := CD.StrVal + FCurrent.Value;
          Advance;
        end
        else
          raise EParseError.Create(Format(
            'Expected string literal after ''+'' in const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
    end
    else
      raise EParseError.Create(Format(
        'Expected numeric or string constant at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Expect(tkSemicolon);
    AList.Add(CD);
  end;
end;

function TParser.ParseEnumDef: TEnumTypeDef;
var
  MName: string;
  NextVal: Integer;
  Negative: Boolean;
  ExplicitVal: Integer;
begin
  Result := TEnumTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    NextVal := 0;
    Expect(tkLParen);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    MName := FCurrent.Value;
    Advance;
    if Check(tkEquals) then
    begin
      Advance;
      Negative := False;
      if Check(tkMinus) then
      begin
        Negative := True;
        Advance;
      end;
      if not Check(tkIntLit) then
        raise EParseError.Create(Format('Expected integer after ''='' in enum at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      ExplicitVal := ParseIntLiteral(FCurrent.Value);
      if Negative then ExplicitVal := -ExplicitVal;
      Advance;
      NextVal := ExplicitVal;
    end;
    Result.AddMember(MName, NextVal);
    Inc(NextVal);
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      MName := FCurrent.Value;
      Advance;
      if Check(tkEquals) then
      begin
        Advance;
        Negative := False;
        if Check(tkMinus) then
        begin
          Negative := True;
          Advance;
        end;
        if not Check(tkIntLit) then
          raise EParseError.Create(Format('Expected integer after ''='' in enum at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        ExplicitVal := ParseIntLiteral(FCurrent.Value);
        if Negative then ExplicitVal := -ExplicitVal;
        Advance;
        NextVal := ExplicitVal;
      end;
      Result.AddMember(MName, NextVal);
      Inc(NextVal);
    end;
    Expect(tkRParen);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseSetDef: TSetTypeDef;
begin
  Result := TSetTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkSet);
    Expect(tkOf);
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected base type name after ''set of'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.BaseTypeName := FCurrent.Value;
    Advance;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseProceduralTypeDef: TProceduralTypeDef;
begin
  Result := TProceduralTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if Check(tkFunction) then
    begin
      Result.IsFunction := True;
      Advance;
    end
    else if Check(tkProcedure) then
    begin
      Result.IsFunction := False;
      Advance;
    end
    else
      raise EParseError.Create(Format(
        'Expected ''function'' or ''procedure'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    if Check(tkLParen) then
    begin
      Advance;  { '(' }
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if Result.IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName;
    end;
    { Optional 'of object' modifier — turns the bare procedural type into
      a method-pointer type, with a 16-byte (Code, Data) representation. }
    if Check(tkOf) then
    begin
      Advance;  { consume 'of' }
      if not (Check(tkIdent) and SameText(FCurrent.Value, 'object')) then
        raise EParseError.Create(Format(
          'Expected ''object'' after ''of'' in procedural-type declaration at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Advance;  { consume 'object' }
      Result.IsMethodPtr := True;
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseRecordDef: TRecordTypeDef;
var
  MethDecl: TMethodDecl;
begin
  Result := TRecordTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRecord);
    repeat
      if Check(tkIdent) or Check(tkLBracket) then
        ParseFieldDecl(Result.Fields)
      else if Check(tkFunction) then
      begin
        MethDecl := ParseMethodDecl(True);
        Result.Methods.Add(MethDecl);
      end
      else if Check(tkProcedure) then
      begin
        MethDecl := ParseMethodDecl(False);
        Result.Methods.Add(MethDecl);
      end
      else
        Break;
    until False;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseGenericName: string;
var
  TypeArgs: string;
begin
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected identifier at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Result := FCurrent.Value;
  Advance;
  if Check(tkNotEquals) then
  begin
    { Diamond in type-name context: TFoo<> — lexer folds '<>' into tkNotEquals }
    Advance;
    Exit(Result + '<>');
  end;
  if Check(tkLessThan) then
  begin
    Advance;  { consume '<' }
    TypeArgs := FCurrent.Value;
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      TypeArgs := TypeArgs + ',' + FCurrent.Value;
      Advance;
    end;
    Expect(tkGreaterThan);
    Result := Result + '<' + TypeArgs + '>';
  end;
end;

function TParser.ParseClassDef: TClassTypeDef;
var
  CurrPublished: Boolean;
  MethDecl:      TMethodDecl;
begin
  Result := TClassTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkClass);
    if Check(tkLParen) then
    begin
      Advance;
      { First name may be a plain class name or a generic interface name like IFoo<T> }
      Result.ParentName := ParseGenericName;
      { Additional names after a comma are implemented interface names }
      while Check(tkComma) do
      begin
        Advance;
        Result.ImplementsNames.Add(ParseGenericName);
      end;
      Expect(tkRParen);
    end;
    { Class body: fields, properties, and methods in any order.  A field
      declaration may be preceded by an attribute list, so accept
      `[` as a legal field-start token too.  Visibility keywords
      (private/public/protected/published) update CurrPublished, which
      is then attached to each method decl so codegen can emit a
      published-method table entry. }
    CurrPublished := False;
    repeat
      if Check(tkIdent) and (SameText(FCurrent.Value, 'private') or
                              SameText(FCurrent.Value, 'public') or
                              SameText(FCurrent.Value, 'protected') or
                              SameText(FCurrent.Value, 'published')) then
      begin
        CurrPublished := SameText(FCurrent.Value, 'published');
        Advance;  { consume the visibility modifier }
      end
      else if Check(tkConst) then
        ParseConstBlock(Result.ConstDecls)
      else if Check(tkVar) then
        Advance  { optional 'var' keyword before field declarations — consume and continue }
      else if Check(tkIdent) and SameText(FCurrent.Value, 'property') then
        Result.Properties.Add(ParsePropertyDecl)
      else if Check(tkIdent) or Check(tkLBracket) then
        ParseFieldDecl(Result.Fields)
      else if Check(tkFunction) then
      begin
        MethDecl := ParseMethodDecl(True);
        MethDecl.IsPublished := CurrPublished;
        Result.Methods.Add(MethDecl);
      end
      else if Check(tkProcedure) or Check(tkConstructor) or Check(tkDestructor) then
      begin
        MethDecl := ParseMethodDecl(False);
        MethDecl.IsPublished := CurrPublished;
        Result.Methods.Add(MethDecl);
      end
      else
        Break;
    until False;
    { Empty class declaration: TFoo = class(TBase); has no body, no 'end' }
    if Check(tkEnd) then
      Advance
    else if not (Check(tkSemicolon) or Check(tkEOF)) then
      raise EParseError.Create(Format(
        'Expected ''end'' in class definition at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseInterfaceDef: TInterfaceTypeDef;
begin
  Result := TInterfaceTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIntf);
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected parent interface name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.ParentName := FCurrent.Value;
      Advance;
      Expect(tkRParen);
    end;
    while Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) do
    begin
      if Check(tkFunction) then
        Result.Methods.Add(ParseMethodDecl(True))
      else
        Result.Methods.Add(ParseMethodDecl(False));
    end;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseMethodDecl(IsFunction: Boolean; ACanHaveNestedProcs: Boolean): TMethodDecl;
var
  TempParams:       TStringList;
  TempConstraints:  TStringList;
  Constraint:       string;
begin
  TempParams      := nil;
  TempConstraints := nil;
  Result := TMethodDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if IsFunction then
      Expect(tkFunction)
    else if Check(tkProcedure) then
      Advance
    else if Check(tkConstructor) or Check(tkDestructor) then
      Advance
    else
      Expect(tkProcedure);  { will produce a clear error message }
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected method name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;
    { Type parameter list: applies to the method itself ('function Identity<T>')
      or the generic owner class ('procedure TList<T>.Add').  Parse tentatively;
      DOT after '>' decides which case it is. }
    if Check(tkLessThan) and (PeekKind = tkIdent) and
       (PeekKind2 in [tkGreaterThan, tkComma, tkColon]) then
    begin
      TempParams      := TStringList.Create;
      TempConstraints := TStringList.Create;
      try
        Advance;  { consume '<' }
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TempParams.Add(FCurrent.Value);
        Advance;
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance;
          if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        TempConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          TempParams.Add(FCurrent.Value);
          Advance;
          Constraint := '';
          if Check(tkColon) then
          begin
            Advance;
            if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
            else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
            else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
            else
              raise EParseError.Create(Format(
                'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          end;
          TempConstraints.Add(Constraint);
        end;
        Expect(tkGreaterThan);
        if Check(tkDot) then
        begin
          { Generic owner: procedure TList<T>.Add(...) — constraints are
            carried on the type decl, not repeated on method impls. }
          Result.OwnerTypeParams := TempParams;
          TempParams := nil;
          TempConstraints.Free;
          TempConstraints := nil;
        end
        else
        begin
          { Method's own type params: function Identity<T>(...) }
          Result.TypeParams           := TempParams;
          Result.TypeParamConstraints := TempConstraints;
          TempParams      := nil;
          TempConstraints := nil;
        end;
      finally
        TempParams.Free;
        TempConstraints.Free;
      end;
    end;
    { Qualified name: TypeName.MethodName or TypeName<T>.MethodName }
    if Check(tkDot) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected method name after ''.'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.OwnerTypeName := Result.Name;
      Result.Name          := FCurrent.Value;
      Advance;
    end;
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName;
    end;
    Expect(tkSemicolon);
    { Consume method directives: virtual, override, and identifier-form directives
      such as inline, stdcall, cdecl, abstract, reintroduce, static, assembler, etc. }
    while True do
    begin
      if Check(tkVirtual) then
      begin
        Result.IsVirtual := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkOverride) then
      begin
        Result.IsOverride := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkExternal) then
      begin
        Result.IsExternal := True;
        Advance;
        { optional: name 'c_symbol' }
        if Check(tkIdent) and SameText(FCurrent.Value, 'name') then
        begin
          Advance;
          Result.ExternalName := FCurrent.Value;
          Expect(tkStringLit);
        end;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'overload') then
      begin
        Result.IsOverload := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'abstract') then
      begin
        Result.IsAbstract := True;
        Result.IsVirtual  := True;  { abstract implies virtual }
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkIdent) and
              (SameText(FCurrent.Value, 'inline')      or
               SameText(FCurrent.Value, 'stdcall')     or
               SameText(FCurrent.Value, 'cdecl')       or
               SameText(FCurrent.Value, 'register')    or
               SameText(FCurrent.Value, 'pascal')      or
               SameText(FCurrent.Value, 'safecall')    or
               SameText(FCurrent.Value, 'reintroduce') or
               SameText(FCurrent.Value, 'static')      or
               SameText(FCurrent.Value, 'final')       or
               SameText(FCurrent.Value, 'assembler')   or
               SameText(FCurrent.Value, 'forward')     or
               SameText(FCurrent.Value, 'deprecated')  or
               SameText(FCurrent.Value, 'platform')    or
               SameText(FCurrent.Value, 'experimental')) then
      begin
        if SameText(FCurrent.Value, 'inline') then
          Result.IsInline := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else
        Break;
    end;
    { Body is optional — present for standalone impls and inline class methods,
      absent for class forward declarations, external declarations, etc.
      When ACanHaveNestedProcs is True (standalone proc context), a bare
      'procedure'/'function' keyword triggers body parsing so that a nested
      sub-procedure declaration is parsed as part of the enclosing routine. }
    if (not Result.IsExternal) and
       (Check(tkBegin) or Check(tkVar) or Check(tkType) or Check(tkConst) or
        (ACanHaveNestedProcs and (Check(tkProcedure) or Check(tkFunction)))) then
    begin
      Result.Body := ParseBlock;
      Expect(tkSemicolon);
    end;
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseParamList(AParams: TObjectList);
var
  Par:         TMethodParam;
  I:           Integer;
  Names:       TStringList;
  TypeN:       string;
  IsVarGrp:    Boolean;
  IsConstGrp:  Boolean;
  IsOpenArr:   Boolean;
  Default:     TASTExpr;
  DefLine:     Integer;
  DefCol:      Integer;
begin
  repeat
    IsVarGrp   := Check(tkVar) or Check(tkOut);
    IsConstGrp := Check(tkConst);
    if IsVarGrp then Advance
    else if IsConstGrp then Advance;
    Names := TStringList.Create;
    try
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Names.Add(FCurrent.Value);
      Advance;
      while Check(tkComma) do
      begin
        Advance;
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Names.Add(FCurrent.Value);
        Advance;
      end;
      Expect(tkColon);
      IsOpenArr := Check(tkArray);
      if IsOpenArr then
      begin
        Advance;        { consume 'array' }
        Expect(tkOf);
        TypeN := ParseTypeName;   { element type }
      end
      else
        TypeN := ParseTypeName;
      Default := nil;
      if Check(tkEquals) then
      begin
        if Names.Count > 1 then
          raise EParseError.Create(Format(
            'Default value not allowed in a multi-name parameter group at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        if IsVarGrp then
          raise EParseError.Create(Format(
            'Default value not allowed on var/out parameter at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        if IsOpenArr then
          raise EParseError.Create(Format(
            'Default value not allowed on open-array parameter at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        DefLine := FCurrent.Line;
        DefCol  := FCurrent.Col;
        Advance;  { consume '=' }
        Default := ParseExpr;
        if Default = nil then
          raise EParseError.Create(Format(
            'Expected default value expression at line %d col %d in %s',
            [DefLine, DefCol, FLexer.Filename]));
      end;
      for I := 0 to Names.Count - 1 do
      begin
        Par              := TMethodParam.Create;
        Par.ParamName    := Names.Strings[I];
        Par.TypeName     := TypeN;
        Par.IsVarParam   := IsVarGrp;
        Par.IsConstParam := IsConstGrp;
        Par.IsOpenArray  := IsOpenArr;
        if (I = Names.Count - 1) and (Default <> nil) then
        begin
          Par.DefaultValue := Default;
          Default := nil;  { ownership transferred to Par }
        end;
        AParams.Add(Par);
      end;
    finally
      Names.Free;
    end;
    if Check(tkSemicolon) then
      Advance
    else
      Break;
  until False;
end;

procedure TParser.ParseStandaloneDecl(ABlock: TBlock);
var
  IsFunc: Boolean;
  MD:     TMethodDecl;
begin
  IsFunc := Check(tkFunction);
  MD     := ParseMethodDecl(IsFunc, True);  { True = may have nested proc/func decls }
  ABlock.ProcDecls.Add(MD);
end;



function TParser.ParsePropertyDecl: TPropertyDecl;
begin
  Result := TPropertyDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance;  { consume 'property' identifier }
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected property name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;
    { Optional index parameter: 'property Name[ParamName: TypeName]: ...' }
    if Check(tkLBracket) then
    begin
      Advance;  { consume '[' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected index parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.IndexParamName := FCurrent.Value;
      Advance;
      Expect(tkColon);
      Result.IndexTypeName := ParseTypeName;
      Expect(tkRBracket);
    end;
    Expect(tkColon);
    Result.TypeName := ParseTypeName;
    { Optional: read Accessor }
    if Check(tkIdent) and SameText(FCurrent.Value, 'read') then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected read accessor name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.ReadName := FCurrent.Value;
      Advance;
    end;
    { Optional: write Accessor }
    if Check(tkIdent) and SameText(FCurrent.Value, 'write') then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected write accessor name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.WriteName := FCurrent.Value;
      Advance;
    end;
    Expect(tkSemicolon);
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseAttributeList(AAttrs: TStringList);
{ Parse zero or more `[Ident]` or `[Ident(...)]` attributes and append the
  bare identifier names to AAttrs.  Argument lists are consumed but
  currently discarded — only the attribute name drives compiler behaviour
  today.  Unknown attributes are accepted silently for forward
  compatibility with user-defined attributes.  Call at sites where an
  attribute list may legally appear (before var and field declarations).  }
var
  Depth: Integer;
begin
  while Check(tkLBracket) do
  begin
    Advance;  { consume [ }
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected attribute name after ''['' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    AAttrs.Add(FCurrent.Value);
    Advance;  { consume attribute name }
    { Optional argument list: (args, ...).  We simply count parens until
      balanced.  Expression-level parsing of attribute arguments is
      deferred until RTTI lands; capturing the name is enough to drive
      the compiler-recognised attribute set today. }
    if Check(tkLParen) then
    begin
      Depth := 1;
      Advance;
      while (Depth > 0) and (FCurrent.Kind <> tkEOF) do
      begin
        if      Check(tkLParen) then Inc(Depth)
        else if Check(tkRParen) then Dec(Depth);
        Advance;
      end;
    end;
    Expect(tkRBracket);
  end;
end;

procedure TParser.ParseFieldDecl(AFields: TObjectList);
var
  Fld: TFieldDecl;
begin
  Fld := TFieldDecl.Create;
  Fld.Line := FCurrent.Line;
  Fld.Col  := FCurrent.Col;
  try
    ParseAttributeList(Fld.Attributes);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected field name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Fld.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected field name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Fld.Names.Add(FCurrent.Value);
      Advance;
    end;
    Expect(tkColon);
    Fld.TypeName := ParseTypeName;
    Expect(tkSemicolon);
    AFields.Add(Fld);
  except
    Fld.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Var section                                                         }
{ ------------------------------------------------------------------ }

procedure TParser.ParseVarBlock(ABlock: TBlock);
begin
  Expect(tkVar);
  while Check(tkIdent) or Check(tkLBracket) do
    ParseVarDecl(ABlock);
end;

procedure TParser.ParseVarDecl(ABlock: TBlock);
var
  Decl: TVarDecl;
begin
  Decl := TVarDecl.Create;
  Decl.Line := FCurrent.Line;
  Decl.Col  := FCurrent.Col;
  try
    ParseAttributeList(Decl.Attributes);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected variable name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Decl.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected variable name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Decl.Names.Add(FCurrent.Value);
      Advance;
    end;
    Expect(tkColon);
    Decl.TypeName := ParseTypeName;
    Expect(tkSemicolon);
    ABlock.Decls.Add(Decl);
  except
    Decl.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Statements                                                          }
{ ------------------------------------------------------------------ }

procedure TParser.ParseStmtList(ABlock: TBlock);
var
  Stmt: TASTStmt;
begin
  while not (Check(tkEnd) or Check(tkEOF) or Check(tkElse)) do
  begin
    Stmt := ParseStmt;
    if Stmt <> nil then
      ABlock.Stmts.Add(Stmt);
    if Check(tkSemicolon) then
      Advance
    else
      Break;
  end;
end;

function TParser.ParseStmt: TASTStmt;
var
  Name:        string;
  Line, Col:   Integer;
  Call:        TProcCall;
  Assign:      TAssignment;
  FldAssign:   TFieldAssignment;
  MCall:       TMethodCallStmt;
  MCallExpr:   TMethodCallExpr;
  PtrWrite:    TPointerWriteStmt;
  PtrIdNode:   TIdentExpr;
  DerefNode:   TDerefExpr;
  SecondIdent: string;
  FldNode:     TFieldAccessExpr;
  InnerFld:    TFieldAccessExpr;
  CastRcv:     TASTExpr;
  FCallNode:   TFuncCallExpr;
  SubAssign:   TStaticSubscriptAssign;
  ExitS:       TExitStmt;
begin
  Result := nil;

  if Check(tkEnd) or Check(tkEOF) or Check(tkSemicolon) or Check(tkElse) then
    Exit;

  if Check(tkIf) then
  begin
    Exit(ParseIfStmt);
  end;

  if Check(tkWhile) then
  begin
    Exit(ParseWhileStmt);
  end;

  if Check(tkRepeat) then
  begin
    Exit(ParseRepeatStmt);
  end;

  if Check(tkFor) then
  begin
    Exit(ParseForStmt);
  end;

  if Check(tkTry) then
  begin
    Exit(ParseTryStmt);
  end;

  if Check(tkRaise) then
  begin
    Exit(ParseRaiseStmt);
  end;

  if Check(tkExit) then
  begin
    ExitS      := TExitStmt.Create;
    ExitS.Line := FCurrent.Line;
    ExitS.Col  := FCurrent.Col;
    Advance;
    { Exit(X) shorthand: assign X to Result before returning.  Semantic checks
      X is assignment-compatible with the return type and that the enclosing
      routine is a function (not a procedure). }
    if Check(tkLParen) then
    begin
      Advance;
      ExitS.Value := Self.ParseExpr;
      Expect(tkRParen);
    end;
    Exit(ExitS);
  end;

  if Check(tkBreak) then
  begin
    Result      := TBreakStmt.Create;
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance;
    Exit;
  end;

  if Check(tkContinue) then
  begin
    Result      := TContinueStmt.Create;
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance;
    Exit;
  end;

  if Check(tkInherited) then
  begin
    Exit(ParseInheritedStmt);
  end;

  if Check(tkCase) then
  begin
    Exit(ParseCaseStmt);
  end;

  if Check(tkBegin) then
  begin
    Exit(ParseCompoundStmt);
  end;

  if not Check(tkIdent) then
    raise EParseError.Create(Format(
      'Expected statement at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));

  Name := FCurrent.Value;
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Advance;

  if Check(tkLBracket) then
  begin
    { Static array subscript assignment: Name[IndexExpr] := ValueExpr }
    Advance;  { consume '[' }
    SubAssign := TStaticSubscriptAssign.Create;
    SubAssign.Line := Line;
    SubAssign.Col := Col;
    SubAssign.ArrayName := Name;
    try
      SubAssign.IndexExpr := ParseExpr;
      Expect(tkRBracket);
      Expect(tkAssign);
      SubAssign.ValueExpr := ParseExpr;
    except
      SubAssign.Free;
      raise;
    end;
    Exit(SubAssign);
  end;

  if Check(tkCaret) then
  begin
    Advance;  { consume '^' }
    if Check(tkDot) then
    begin
      { Deref-then-field assignment: Ident^.Field := Expr
        Re-use the field-assignment path with a TDerefExpr as ObjExpr. }
      Advance;  { consume '.' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected field name after ''^.'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      SecondIdent := FCurrent.Value;
      Advance;  { consume field name }
      { Build chain: handle further A^.B.C.D chaining }
      PtrIdNode        := TIdentExpr.Create;
      PtrIdNode.Line   := Line;
      PtrIdNode.Col    := Col;
      PtrIdNode.Name   := Name;
      DerefNode        := TDerefExpr.Create;
      DerefNode.Line   := Line;
      DerefNode.Col    := Col;
      DerefNode.Expr   := PtrIdNode;
      FldNode          := TFieldAccessExpr.Create;
      FldNode.Line     := Line;
      FldNode.Col      := Col;
      FldNode.Base     := DerefNode;
      FldNode.FieldName := SecondIdent;
      while Check(tkDot) and (PeekKind = tkIdent) do
      begin
        Advance;
        InnerFld           := TFieldAccessExpr.Create;
        InnerFld.Line      := FCurrent.Line;
        InnerFld.Col       := FCurrent.Col;
        InnerFld.FieldName := FCurrent.Value;
        InnerFld.Base      := FldNode;
        FldNode            := InnerFld;
        Advance;
      end;
      FldAssign         := TFieldAssignment.Create;
      FldAssign.Line    := Line;
      FldAssign.Col     := Col;
      FldAssign.ObjExpr := FldNode.Base;
      FldAssign.FieldName := FldNode.FieldName;
      FldNode.Base      := nil;
      FldNode.Free;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr;
      Result := FldAssign;
    end
    else
    begin
      { Plain pointer dereference assignment: Ident^ := Expr }
      Expect(tkAssign);
      PtrWrite         := TPointerWriteStmt.Create;
      PtrWrite.Line    := Line;
      PtrWrite.Col     := Col;
      PtrIdNode        := TIdentExpr.Create;
      PtrIdNode.Line   := Line;
      PtrIdNode.Col    := Col;
      PtrIdNode.Name   := Name;
      PtrWrite.PtrExpr := PtrIdNode;
      PtrWrite.ValExpr := ParseExpr;
      Result := PtrWrite;
    end;
  end
  else if Check(tkDot) then
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    SecondIdent := FCurrent.Value;
    Advance;

    if Check(tkLBracket) then
    begin
      { Indexed property write: Ident '.' Ident '[' Index ']' ':=' Expr }
      FldAssign := TFieldAssignment.Create;
      FldAssign.Line := Line;
      FldAssign.Col := Col;
      FldAssign.RecordName := Name;
      FldAssign.FieldName := SecondIdent;
      Advance;  { consume '[' }
      FldAssign.PropIndexExpr := ParseExpr;
      Expect(tkRBracket);
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr;
      Result := FldAssign;
    end
    else if Check(tkAssign) then
    begin
      { Field assignment: Ident '.' Ident ':=' Expr }
      FldAssign := TFieldAssignment.Create;
      FldAssign.Line := Line;
      FldAssign.Col := Col;
      FldAssign.RecordName := Name;
      FldAssign.FieldName := SecondIdent;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr;
      Result := FldAssign;
    end
    else
    begin
      { Method call: Ident '.' Ident ['(' [args] ')'] — may chain to
        Ident.Ident.Ident... with further '.' before the final method call. }
      if Check(tkDot) then
      begin
        { Chained: AProg.UsedUnits.Add(...) — build a field-access chain as
          the receiver expression. }
        MCall            := TMethodCallStmt.Create;
        MCall.Line       := Line;
        MCall.Col        := Col;
        MCall.ObjectName := '';
        { Build chain: AProg -> AProg.UsedUnits }
        PtrIdNode        := TIdentExpr.Create;
        PtrIdNode.Line   := Line;
        PtrIdNode.Col    := Col;
        PtrIdNode.Name   := Name;
        FldNode          := TFieldAccessExpr.Create;
        FldNode.Line     := Line;
        FldNode.Col      := Col;
        FldNode.Base     := PtrIdNode;
        FldNode.FieldName:= SecondIdent;
        MCall.ObjExpr    := FldNode;
        while Check(tkDot) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondIdent := FCurrent.Value;
          Advance;
          if Check(tkDot) then
          begin
            { Still more chain — extend field access path }
            FldNode          := TFieldAccessExpr.Create;
            FldNode.Line     := Line;
            FldNode.Col      := Col;
            FldNode.Base     := MCall.ObjExpr;
            FldNode.FieldName:= SecondIdent;
            MCall.ObjExpr    := FldNode;
          end
          else
          begin
            MCall.Name := SecondIdent;
            if Check(tkLParen) then
            begin
              Advance;
              if not Check(tkRParen) then
                ParseMethodCallArgList(MCall);
              Expect(tkRParen);
            end;
            Break;
          end;
        end;
        { Chained field assignment: A.B.C := value }
        if Check(tkAssign) then
        begin
          Advance;
          FldAssign           := TFieldAssignment.Create;
          FldAssign.Line      := Line;
          FldAssign.Col       := Col;
          FldAssign.FieldName := MCall.Name;
          FldAssign.ObjExpr   := MCall.ObjExpr;
          MCall.ObjExpr       := nil;  { transfer ownership — prevent double-free }
          MCall.Free;
          MCall := nil;
          FldAssign.Expr := ParseExpr;
          Exit(FldAssign);
        end;
        Result := MCall;
      end
      else
      begin
        MCall            := TMethodCallStmt.Create;
        MCall.Line       := Line;
        MCall.Col        := Col;
        MCall.ObjectName := Name;
        MCall.Name       := SecondIdent;
        if Check(tkLParen) then
        begin
          Advance;
          if not Check(tkRParen) then
            ParseMethodCallArgList(MCall);
          Expect(tkRParen);
        end;
        { Post-method chain: Name.Method(args).Field := value or .Method2(args) }
        if Check(tkDot) then
        begin
          MCallExpr            := TMethodCallExpr.Create;
          MCallExpr.Line       := Line;
          MCallExpr.Col        := Col;
          MCallExpr.ObjectName := MCall.ObjectName;
          MCallExpr.Name       := MCall.Name;
          while MCall.Args.Count > 0 do
            MCallExpr.Args.Add(MCall.Args.Extract(MCall.Args.Items[0]));
          MCall.Free;
          MCall   := nil;
          CastRcv := MCallExpr;
          while Check(tkDot) do
          begin
            Advance;
            if not Check(tkIdent) then
              raise EParseError.Create(Format(
                'Expected identifier after ''.'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            SecondIdent := FCurrent.Value;
            Advance;
            if Check(tkLParen) then
            begin
              MCall            := TMethodCallStmt.Create;
              MCall.Line       := Line;
              MCall.Col        := Col;
              MCall.ObjectName := '';
              MCall.Name       := SecondIdent;
              MCall.ObjExpr    := CastRcv;
              Advance;
              if not Check(tkRParen) then
                ParseMethodCallArgList(MCall);
              Expect(tkRParen);
              Exit(MCall);
            end;
            FldNode           := TFieldAccessExpr.Create;
            FldNode.Line      := Line;
            FldNode.Col       := Col;
            FldNode.Base      := CastRcv;
            FldNode.FieldName := SecondIdent;
            CastRcv := FldNode;
          end;
          if Check(tkAssign) and (CastRcv is TFieldAccessExpr) then
          begin
            Advance;
            FldAssign           := TFieldAssignment.Create;
            FldAssign.Line      := Line;
            FldAssign.Col       := Col;
            FldAssign.FieldName := TFieldAccessExpr(CastRcv).FieldName;
            FldAssign.ObjExpr   := TFieldAccessExpr(CastRcv).Base;
            TFieldAccessExpr(CastRcv).Base := nil;
            CastRcv.Free;
            FldAssign.Expr := ParseExpr;
            Exit(FldAssign);
          end;
          raise EParseError.Create(Format(
            'Expected method call or assignment after chain at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        Result := MCall;
      end;
    end;
  end
  else if Check(tkAssign) then
  begin
    Advance;
    Assign      := TAssignment.Create;
    Assign.Line := Line;
    Assign.Col  := Col;
    Assign.Name := Name;
    Assign.Expr := ParseExpr;
    Result := Assign;
  end
  else
  begin
    { Typecast-then-method-call statement: TCast(expr).Method(args)
      or chained Ident(arg).Field.Method(args). Detect by peeking for
      '(' followed by a '.' after the paren closure — parse directly
      into a TFuncCallExpr receiver so the inner arg lives on. }
    if Check(tkLParen) then
    begin
      FCallNode      := TFuncCallExpr.Create;
      FCallNode.Line := Line;
      FCallNode.Col  := Col;
      FCallNode.Name := Name;
      Advance;  { '(' }
      if not Check(tkRParen) then
      begin
        FCallNode.Args.Add(ParseExpr);
        while Check(tkComma) do
        begin
          Advance;
          FCallNode.Args.Add(ParseExpr);
        end;
      end;
      Expect(tkRParen);
      if Check(tkDot) then
      begin
        CastRcv := FCallNode;
        { Chain parse: each step reads '.Ident', then either '(' (call) or
          more '.'. The final method call terminates as TMethodCallStmt. }
        while Check(tkDot) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondIdent := FCurrent.Value;
          Advance;
          if Check(tkLParen) then
          begin
            MCall            := TMethodCallStmt.Create;
            MCall.Line       := Line;
            MCall.Col        := Col;
            MCall.ObjectName := '';
            MCall.Name       := SecondIdent;
            MCall.ObjExpr    := CastRcv;
            Advance;  { consume '(' }
            if not Check(tkRParen) then
              ParseMethodCallArgList(MCall);
            Expect(tkRParen);
            Exit(MCall);
          end;
          FldNode            := TFieldAccessExpr.Create;
          FldNode.Line       := Line;
          FldNode.Col        := Col;
          FldNode.Base       := CastRcv;
          FldNode.FieldName  := SecondIdent;
          CastRcv            := FldNode;
        end;
        { Field assignment through typecast/chain: TCast(expr).Field := value }
        if Check(tkAssign) and (CastRcv is TFieldAccessExpr) then
        begin
          Advance; { consume ':=' }
          FldAssign          := TFieldAssignment.Create;
          FldAssign.Line     := Line;
          FldAssign.Col      := Col;
          FldAssign.FieldName := TFieldAccessExpr(CastRcv).FieldName;
          FldAssign.ObjExpr  := TFieldAccessExpr(CastRcv).Base;
          TFieldAccessExpr(CastRcv).Base := nil; { transfer ownership }
          CastRcv.Free;
          FldAssign.Expr := ParseExpr;
          Exit(FldAssign);
        end;
        { No-arg method call: Func(...).Field treated as Func(...).Method }
        if CastRcv is TFieldAccessExpr then
        begin
          MCall            := TMethodCallStmt.Create;
          MCall.Line       := Line;
          MCall.Col        := Col;
          MCall.ObjectName := '';
          MCall.Name       := TFieldAccessExpr(CastRcv).FieldName;
          MCall.ObjExpr    := TFieldAccessExpr(CastRcv).Base;
          TFieldAccessExpr(CastRcv).Base := nil;
          CastRcv.Free;
          Exit(MCall);
        end;
        raise EParseError.Create(Format(
          'Expected method call after typecast at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
      { No '.': it was a plain procedure/function call. Move args to a
        fresh TProcCall using FPC-style Extract (removes without freeing). }
      Call      := TProcCall.Create;
      Call.Line := Line;
      Call.Col  := Col;
      Call.Name := Name;
      while FCallNode.Args.Count > 0 do
        Call.Args.Add(FCallNode.Args.Extract(FCallNode.Args.Items[0]));
      FCallNode.Free;
      Exit(Call);
    end;
    Call      := TProcCall.Create;
    Call.Line := Line;
    Call.Col  := Col;
    Call.Name := Name;
    Result := Call;
  end;
end;

function TParser.ParseWhileStmt: TWhileStmt;
begin
  Result := TWhileStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkWhile);
    Result.Condition := ParseExpr;
    Expect(tkDo);
    Result.Body := ParseStmt;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseRepeatStmt: TRepeatStmt;
var
  Stmt: TASTStmt;
begin
  Result := TRepeatStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRepeat);
    Result.Body := TCompoundStmt.Create;
    Result.Body.Line := FCurrent.Line;
    Result.Body.Col  := FCurrent.Col;
    while not (Check(tkUntil) or Check(tkEOF)) do
    begin
      Stmt := ParseStmt;
      if Stmt <> nil then
        Result.Body.Stmts.Add(Stmt);
      if Check(tkSemicolon) then
        Advance
      else
        Break;
    end;
    Expect(tkUntil);
    Result.Condition := ParseExpr;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseIfStmt: TIfStmt;
begin
  Result := TIfStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIf);
    Result.Condition := ParseExpr;
    Expect(tkThen);
    Result.ThenStmt := ParseStmt;
    // 'if cond then { comment } else' leaves ThenStmt nil when the comment is the only body.
    // Substitute an empty compound so EmitIfStmt can always call EmitStmt.
    if Result.ThenStmt = nil then
      Result.ThenStmt := TCompoundStmt.Create;
    if Check(tkElse) then
    begin
      Advance;
      Result.ElseStmt := ParseStmt;
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseForStmt: TASTStmt;
var
  SLine:    Integer;
  SCol:     Integer;
  VarName:  string;
  ForS:     TForStmt;
  ForInS:   TForInStmt;
begin
  SLine := FCurrent.Line;
  SCol  := FCurrent.Col;
  Expect(tkFor);
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected loop variable at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  VarName := FCurrent.Value;
  Advance;

  if Check(tkIn) then
  begin
    { for X in Collection do Body }
    ForInS := TForInStmt.Create;
    Result := ForInS;
    try
      ForInS.Line    := SLine;
      ForInS.Col     := SCol;
      ForInS.VarName := VarName;
      Advance;  { consume 'in' }
      ForInS.CollExpr := ParseExpr;
      Expect(tkDo);
      ForInS.Body := ParseStmt;
    except
      ForInS.Free;
      Result := nil;
      raise;
    end;
  end
  else
  begin
    { for X := Start to/downto End do Body }
    ForS := TForStmt.Create;
    Result := ForS;
    try
      ForS.Line    := SLine;
      ForS.Col     := SCol;
      ForS.VarName := VarName;
      Expect(tkAssign);
      ForS.StartExpr := ParseExpr;
      if Check(tkTo) then
      begin
        ForS.IsDownTo := False;
        Advance;
      end
      else if Check(tkDownto) then
      begin
        ForS.IsDownTo := True;
        Advance;
      end
      else
        raise EParseError.Create(Format(
          'Expected ''to'' or ''downto'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      ForS.EndExpr := ParseExpr;
      Expect(tkDo);
      ForS.Body := ParseStmt;
    except
      ForS.Free;
      Result := nil;
      raise;
    end;
  end;
end;

procedure TParser.ParseBodyInto(ATarget: TCompoundStmt;
  AStop1, AStop2: TTokenKind);
var
  S: TASTStmt;
begin
  while not (Check(AStop1) or Check(AStop2) or Check(tkEnd) or Check(tkEOF)) do
  begin
    S := ParseStmt;
    if S <> nil then
      ATarget.Stmts.Add(S);
    if Check(tkSemicolon) then
      Advance
    else
      Break;
  end;
end;

function TParser.ParseTryStmt: TASTStmt;
var
  TryBody:     TCompoundStmt;
  FinallyBody: TCompoundStmt;
  ExceptBody:  TCompoundStmt;
  TFS:         TTryFinallyStmt;
  TES:         TTryExceptStmt;
  Line, Col:   Integer;
begin
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Expect(tkTry);

  TryBody := TCompoundStmt.Create;
  TryBody.Line := Line;
  TryBody.Col  := Col;
  try
    ParseBodyInto(TryBody, tkFinally, tkExcept);

    if Check(tkFinally) then
    begin
      Advance;
      FinallyBody := TCompoundStmt.Create;
      try
        ParseBodyInto(FinallyBody, tkEnd, tkEnd);
        Expect(tkEnd);
        TFS             := TTryFinallyStmt.Create;
        TFS.Line        := Line;
        TFS.Col         := Col;
        TFS.TryBody     := TryBody;
        TFS.FinallyBody := FinallyBody;
        TryBody     := nil;
        FinallyBody := nil;
        Result := TFS;
      except
        FinallyBody.Free;
        raise;
      end;
    end
    else if Check(tkExcept) then
    begin
      Advance;
      TES      := TTryExceptStmt.Create;
      TES.Line := Line;
      TES.Col  := Col;
      TES.TryBody := TryBody;
      TryBody  := nil;
      try
        { Typed handler form: 'on [Var :] TypeName do Stmt' }
        if Check(tkIdent) and SameText(FCurrent.Value, 'on') then
        begin
          while Check(tkIdent) and SameText(FCurrent.Value, 'on') do
          begin
            TES.Handlers.Add(ParseExceptHandlerClause);
            if Check(tkSemicolon) then
              Advance;
          end;
          { Optional catch-all else clause }
          if Check(tkElse) then
          begin
            Advance;
            TES.ElseBody := TCompoundStmt.Create;
            ParseBodyInto(TES.ElseBody, tkEnd, tkEnd);
          end;
        end
        else
        begin
          { Plain catch-all body }
          ExceptBody := TCompoundStmt.Create;
          try
            ParseBodyInto(ExceptBody, tkEnd, tkEnd);
            TES.ExceptBody := ExceptBody;
            ExceptBody := nil;
          except
            ExceptBody.Free;
            raise;
          end;
        end;
        Expect(tkEnd);
        Result := TES;
        TES := nil;
      except
        TES.Free;
        raise;
      end;
    end
    else
    begin
      raise EParseError.Create(Format(
        'Expected ''finally'' or ''except'' after try body at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
  except
    TryBody.Free;
    raise;
  end;
end;

{ Parse one 'on [VarName :] TypeName do Stmt' clause.
  The leading 'on' keyword (as identifier) must be the current token. }
function TParser.ParseExceptHandlerClause: TExceptHandlerClause;
var
  Name1: string;
  H:     TExceptHandlerClause;
  Stmt:  TASTStmt;
begin
  { consume 'on' }
  Expect(tkIdent);  { value is 'on' — caller already checked }
  H := TExceptHandlerClause.Create;
  try
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected identifier after ''on'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Name1 := FCurrent.Value;
    Advance;
    if Check(tkColon) then
    begin
      { 'on VarName : TypeName do' form }
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected type name after '':'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      H.VarName  := Name1;
      H.TypeName := FCurrent.Value;
      Advance;
    end
    else
    begin
      { 'on TypeName do' form — no variable binding }
      H.VarName  := '';
      H.TypeName := Name1;
    end;
    Expect(tkDo);
    H.Body := TCompoundStmt.Create;
    { Handler body is a single statement (Delphi/FPC standard) }
    if Check(tkBegin) then
    begin
      Advance;
      ParseBodyInto(H.Body, tkEnd, tkEnd);
      Expect(tkEnd);
    end
    else
    begin
      { Single statement — nil means empty (bare semicolon); skip it }
      Stmt := ParseStmt;
      if Stmt <> nil then
        H.Body.Stmts.Add(Stmt);
    end;
    Result := H;
  except
    H.Free;
    raise;
  end;
end;

function TParser.ParseRaiseStmt: TRaiseStmt;
begin
  Result := TRaiseStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRaise);
    { Bare raise has no expression; detect by checking statement terminators }
    if not (Check(tkSemicolon) or Check(tkEnd) or Check(tkEOF) or
            Check(tkFinally) or Check(tkExcept) or Check(tkElse)) then
      Result.Expr := ParseExpr;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseInheritedStmt: TInheritedCallStmt;
begin
  Result := TInheritedCallStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkInherited);
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected method name after ''inherited'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkRParen) then
      begin
        Result.Args.Add(ParseExpr);
        while Check(tkComma) do
        begin
          Advance;
          Result.Args.Add(ParseExpr);
        end;
      end;
      Expect(tkRParen);
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseCompoundStmt: TCompoundStmt;
var
  Stmt: TASTStmt;
begin
  Result := TCompoundStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkBegin);
    while not (Check(tkEnd) or Check(tkEOF)) do
    begin
      Stmt := ParseStmt;
      if Stmt <> nil then
        Result.Stmts.Add(Stmt);
      if Check(tkSemicolon) then
        Advance
      else
        Break;
    end;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseCaseStmt: TCaseStmt;
var
  Branch:   TCaseBranch;
  Stmt:     TASTStmt;
  CmpElse:  TCompoundStmt;
begin
  Result := TCaseStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkCase);
    Result.Selector := ParseExpr;
    Expect(tkOf);
    { Parse branches: value [, value]* : stmt }
    while not (Check(tkEnd) or Check(tkElse) or Check(tkEOF)) do
    begin
      Branch := TCaseBranch.Create;
      Branch.Values.Add(ParseExpr);
      while Check(tkComma) do
      begin
        Advance;
        Branch.Values.Add(ParseExpr);
      end;
      Expect(tkColon);
      Stmt := ParseStmt;
      { consume optional trailing semicolon between branches }
      if Check(tkSemicolon) then Advance;
      if Stmt <> nil then
        Branch.Stmt := Stmt
      else
        Branch.Stmt := TCompoundStmt.Create;  { empty branch }
      Result.Branches.Add(Branch);
    end;
    if Check(tkElse) then
    begin
      Advance;  { consume 'else' }
      if Check(tkBegin) then
        Result.ElseStmt := ParseCompoundStmt
      else
      begin
        { Collect all statements until 'end' — FPC allows multi-stmt else without begin..end }
        CmpElse := TCompoundStmt.Create;
        CmpElse.Stmts.Add(ParseStmt);
        if Check(tkSemicolon) then Advance;
        while not (Check(tkEnd) or Check(tkEOF)) do
        begin
          CmpElse.Stmts.Add(ParseStmt);
          if Check(tkSemicolon) then Advance;
        end;
        if CmpElse.Stmts.Count = 1 then
        begin
          { Unwrap single-item compound for simplicity }
          Result.ElseStmt := TASTStmt(CmpElse.Stmts.Extract(CmpElse.Stmts.Items[0]));
          CmpElse.Free;
        end
        else
          Result.ElseStmt := CmpElse;
      end;
      if Check(tkSemicolon) then Advance;
    end;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseArgList(ACall: TProcCall);
begin
  ACall.Args.Add(ParseExpr);
  while Check(tkComma) do
  begin
    Advance;
    ACall.Args.Add(ParseExpr);
  end;
end;

procedure TParser.ParseMethodCallArgList(ACall: TMethodCallStmt);
begin
  ACall.Args.Add(ParseExpr);
  while Check(tkComma) do
  begin
    Advance;
    ACall.Args.Add(ParseExpr);
  end;
end;

{ ------------------------------------------------------------------ }
{ Unit parsing                                                        }
{ ------------------------------------------------------------------ }

function TParser.ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
var
  Constraint: string;
begin
  Result := TMethodDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if IsFunction then
      Expect(tkFunction)
    else if Check(tkProcedure) then
      Advance
    else if Check(tkConstructor) or Check(tkDestructor) then
      Advance
    else
      Expect(tkProcedure);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;
    { Optional generic type-parameter list: function Identity<T>(...).
      Mirrors the subset of ParseMethodDecl's logic that applies to
      forward declarations (no '.MethodName' continuation here — those
      live in the implementation section). }
    if Check(tkLessThan) and (PeekKind = tkIdent) and
       (PeekKind2 in [tkGreaterThan, tkComma, tkColon]) then
    begin
      Result.TypeParams           := TStringList.Create;
      Result.TypeParamConstraints := TStringList.Create;
      Advance;  { consume '<' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.TypeParams.Add(FCurrent.Value);
      Advance;
      Constraint := '';
      if Check(tkColon) then
      begin
        Advance;
        if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
        else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
        else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
        else
          raise EParseError.Create(Format(
            'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
      Result.TypeParamConstraints.Add(Constraint);
      while Check(tkComma) do
      begin
        Advance;
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Result.TypeParams.Add(FCurrent.Value);
        Advance;
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance;
          if      Check(tkClass)  then begin Constraint := 'class';  Advance; end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance; end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance; end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        Result.TypeParamConstraints.Add(Constraint);
      end;
      Expect(tkGreaterThan);
    end;
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName;
    end;
    Expect(tkSemicolon);
    { Directive loop — forward declarations may carry overload, external,
      and the same identifier-form directives accepted by ParseMethodDecl. }
    while True do
    begin
      if Check(tkExternal) then
      begin
        Result.IsExternal := True;
        Advance;
        if Check(tkIdent) and SameText(FCurrent.Value, 'name') then
        begin
          Advance;
          Result.ExternalName := FCurrent.Value;
          Expect(tkStringLit);
        end;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'overload') then
      begin
        Result.IsOverload := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else if Check(tkIdent) and
              (SameText(FCurrent.Value, 'inline')      or
               SameText(FCurrent.Value, 'stdcall')     or
               SameText(FCurrent.Value, 'cdecl')       or
               SameText(FCurrent.Value, 'register')    or
               SameText(FCurrent.Value, 'pascal')      or
               SameText(FCurrent.Value, 'safecall')    or
               SameText(FCurrent.Value, 'forward')     or
               SameText(FCurrent.Value, 'deprecated')  or
               SameText(FCurrent.Value, 'platform')    or
               SameText(FCurrent.Value, 'experimental')) then
      begin
        if SameText(FCurrent.Value, 'inline') then
          Result.IsInline := True;
        Advance;
        if Check(tkSemicolon) then Advance;
      end
      else
        Break;
    end;
    { Body remains nil — forward or external declaration }
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseUnit: TUnit;
var
  InitStmt: TASTStmt;
begin
  Result := TUnit.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkUnit);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected unit name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance;
    while Check(tkDot) do
    begin
      Advance;
      if not CheckUnitNamePart then
        raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.Name := Result.Name + '.' + FCurrent.Value;
      Advance;
    end;
    Expect(tkSemicolon);

    { Interface section }
    Expect(tkIntf);
    if Check(tkUses) then
      ParseUsesList(Result.UsedUnits);
    while Check(tkType) or Check(tkVar) or Check(tkConst) or
          Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) do
    begin
      if Check(tkType) then
        ParseTypeSection(Result.IntfBlock)
      else if Check(tkVar) then
        ParseVarBlock(Result.IntfBlock)
      else if Check(tkConst) then
        ParseConstBlock(Result.IntfBlock.ConstDecls)
      else if Check(tkFunction) then
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(True))
      else
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(False));
    end;

    { Implementation section }
    Expect(tkImplementation);
    if Check(tkUses) then
      ParseUsesList(Result.ImplUsedUnits);  { implementation-only deps — loaded but not re-exported }
    while Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) or
          Check(tkVar) or Check(tkConst) or Check(tkType) do
    begin
      if Check(tkFunction) then
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(True))
      else if Check(tkVar) then
        ParseVarBlock(Result.ImplBlock)
      else if Check(tkConst) then
        ParseConstBlock(Result.ImplBlock.ConstDecls)
      else if Check(tkType) then
        ParseTypeSection(Result.ImplBlock)
      else
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(False));
    end;

    { Optional initialization / finalization sections }
    if Check(tkInitialization) then
    begin
      Advance;
      Result.InitStmts := TObjectList.Create(True);
      while not (Check(tkEnd) or Check(tkFinalization) or Check(tkEOF)) do
      begin
        InitStmt := ParseStmt;
        if InitStmt <> nil then Result.InitStmts.Add(InitStmt);
        if Check(tkSemicolon) then Advance else Break;
      end;
    end;
    if Check(tkFinalization) then
    begin
      Advance;
      Result.FinalStmts := TObjectList.Create(True);
      while not (Check(tkEnd) or Check(tkEOF)) do
      begin
        InitStmt := ParseStmt;
        if InitStmt <> nil then Result.FinalStmts.Add(InitStmt);
        if Check(tkSemicolon) then Advance else Break;
      end;
    end;

    Expect(tkEnd);
    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format(
        'Unexpected tokens after unit end at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Expression parsing — standard precedence climbing                   }
{ ------------------------------------------------------------------ }

function TParser.ParseExpr: TASTExpr;
var
  Right:    TASTExpr;
  CmpOp:    TBinaryOp;
  Node:     TBinaryExpr;
  IsNode:   TIsExpr;
  AsNode:   TAsExpr;
  OpLine:   Integer;
  OpCol:    Integer;
begin
  Result := ParseAddSub;

  { Comparison — non-associative, one level only }
  if Check(tkEquals) or Check(tkNotEquals) or
     Check(tkLessThan) or Check(tkGreaterThan) or
     Check(tkLessEqual) or Check(tkGreaterEqual) then
  begin
    if      Check(tkEquals)      then CmpOp := boEQ
    else if Check(tkNotEquals)   then CmpOp := boNE
    else if Check(tkLessThan)    then CmpOp := boLT
    else if Check(tkGreaterThan) then CmpOp := boGT
    else if Check(tkLessEqual)   then CmpOp := boLE
    else                              CmpOp := boGE;
    OpLine  := FCurrent.Line;
    OpCol   := FCurrent.Col;
    Advance;
    Right       := ParseAddSub;
    Node        := TBinaryExpr.Create;
    Node.Line   := OpLine;
    Node.Col    := OpCol;
    Node.Op     := CmpOp;
    Node.Left   := Result;
    Node.Right  := Right;
    Result      := Node;
  end
  else if Check(tkIn) then
  begin
    OpLine  := FCurrent.Line;
    OpCol   := FCurrent.Col;
    Advance;
    Right       := ParseAddSub;
    Node        := TBinaryExpr.Create;
    Node.Line   := OpLine;
    Node.Col    := OpCol;
    Node.Op     := boIn;
    Node.Left   := Result;
    Node.Right  := Right;
    Result      := Node;
  end
  else if Check(tkIs) then
  begin
    IsNode          := TIsExpr.Create;
    IsNode.Line     := FCurrent.Line;
    IsNode.Col      := FCurrent.Col;
    Advance;
    IsNode.Obj      := Result;
    IsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := IsNode;
  end
  else if Check(tkAs) then
  begin
    Advance;
    AsNode          := TAsExpr.Create;
    AsNode.Obj      := Result;
    AsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := AsNode;
  end;
end;

function TParser.ParseAddSub: TASTExpr;
var
  Right:  TASTExpr;
  Op:     TBinaryOp;
  Node:   TBinaryExpr;
  OpLine: Integer;
  OpCol:  Integer;
begin
  Result := ParseTerm;
  while Check(tkPlus) or Check(tkMinus) or Check(tkOr) do
  begin
    if      Check(tkPlus)  then Op := boAdd
    else if Check(tkMinus) then Op := boSub
    else                        Op := boOr;
    OpLine := FCurrent.Line;
    OpCol  := FCurrent.Col;
    Advance;
    Right      := ParseTerm;
    Node       := TBinaryExpr.Create;
    Node.Line  := OpLine;
    Node.Col   := OpCol;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result     := Node;
  end;
end;

function TParser.ParseTerm: TASTExpr;
var
  Right:  TASTExpr;
  Op:     TBinaryOp;
  Node:   TBinaryExpr;
  OpLine: Integer;
  OpCol:  Integer;
begin
  Result := ParseFactor;
  while Check(tkStar) or Check(tkSlash) or Check(tkDiv) or Check(tkMod)
        or Check(tkAnd) or Check(tkXor) or Check(tkShl) or Check(tkShr)
        or Check(tkSar) do
  begin
    if      Check(tkStar)  then Op := boMul
    else if Check(tkSlash) then Op := boSlash
    else if Check(tkMod)   then Op := boMod
    else if Check(tkAnd)   then Op := boAnd
    else if Check(tkXor)   then Op := boXor
    else if Check(tkShl)   then Op := boShl
    else if Check(tkShr)   then Op := boShr
    else if Check(tkSar)   then Op := boSar
    else                        Op := boDiv;
    OpLine     := FCurrent.Line;
    OpCol      := FCurrent.Col;
    Advance;
    Right      := ParseFactor;
    Node       := TBinaryExpr.Create;
    Node.Line  := OpLine;
    Node.Col   := OpCol;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result     := Node;
  end;
end;

function TParser.ParseFactor: TASTExpr;
var
  IntNode:    TIntLiteral;
  FloatNode:  TFloatLiteral;
  StrNode:    TStringLiteral;
  NilNode:    TNilLiteral;
  IdNode:     TIdentExpr;
  FldNode:    TFieldAccessExpr;
  MCallNode:  TMethodCallExpr;
  FCallNode:  TFuncCallExpr;
  SuppNode:   TSupportsExpr;
  DerefNode:  TDerefExpr;
  AddrNode:   TAddrOfExpr;
  NotNode:    TNotExpr;
  Inner:      TASTExpr;
  Name:       string;
  SecondName: string;
  Line, Col:  Integer;
  ZeroNode:   TIntLiteral;
  NegNode:    TBinaryExpr;
  SubNode:       TStringSubscriptExpr;
  ArrNode:       TArrayLiteralExpr;
  IndCallNode:   TIndirectFuncCallExpr;
  ParseIntV:    Int64;
  ParseIntFlag: Boolean;
begin
  case FCurrent.Kind of
    tkAt:
      begin
        AddrNode      := TAddrOfExpr.Create;
        AddrNode.Line := FCurrent.Line;
        AddrNode.Col  := FCurrent.Col;
        Advance;  { consume '@' }
        AddrNode.Expr := Self.ParseFactor;  { Self. forces recursive call }
        Result := AddrNode;
      end;
    tkNot:
      begin
        NotNode      := TNotExpr.Create;
        NotNode.Line := FCurrent.Line;
        NotNode.Col  := FCurrent.Col;
        Advance;  { consume 'not' }
        NotNode.Expr := Self.ParseFactor;  { Self. forces recursive call }
        Result := NotNode;
      end;
    tkMinus:
      begin
        { Unary minus: synthesise as 0 - Factor }
        ZeroNode       := TIntLiteral.Create;
        ZeroNode.Line  := FCurrent.Line;
        ZeroNode.Col   := FCurrent.Col;
        ZeroNode.Value := 0;
        NegNode        := TBinaryExpr.Create;
        NegNode.Line   := FCurrent.Line;
        NegNode.Col    := FCurrent.Col;
        NegNode.Op     := boSub;
        NegNode.Left   := ZeroNode;
        Advance;  { consume '-' }
        NegNode.Right  := Self.ParseFactor;  { Self. forces recursive call, not result-var read }
        Result         := NegNode;
      end;
    tkNil:
      begin
        NilNode      := TNilLiteral.Create;
        NilNode.Line := FCurrent.Line;
        NilNode.Col  := FCurrent.Col;
        Advance;
        Result := NilNode;
      end;
    tkIntLit:
      begin
        IntNode       := TIntLiteral.Create;
        IntNode.Line  := FCurrent.Line;
        IntNode.Col   := FCurrent.Col;
        ParseIntOrUInt64Literal(FCurrent.Value, ParseIntV, ParseIntFlag);
        IntNode.Value    := ParseIntV;
        IntNode.IsUInt64 := ParseIntFlag;
        Advance;
        Result := IntNode;
      end;
    tkFloatLit:
      begin
        FloatNode       := TFloatLiteral.Create;
        FloatNode.Line  := FCurrent.Line;
        FloatNode.Col   := FCurrent.Col;
        FloatNode.Value := StripUnderscores(FCurrent.Value);
        Advance;
        Result := FloatNode;
      end;
    tkStringLit:
      begin
        StrNode       := TStringLiteral.Create;
        StrNode.Line  := FCurrent.Line;
        StrNode.Col   := FCurrent.Col;
        StrNode.Value := FCurrent.Value;
        Advance;
        Result := StrNode;
      end;
    tkIdent:
      begin
        Name := FCurrent.Value;
        Line := FCurrent.Line;
        Col  := FCurrent.Col;
        Advance;
        { Generic constructor: TypeName<Args>.Method  or diamond TypeName<>.Method
          Heuristic: '<' followed by IDENT followed by '>' or ',' is treated as
          generic type args.  '<>' (empty) is the diamond operator — type args
          inferred by the semantic pass from the LHS type.
          If the token two ahead is neither '>' nor ',', the '<' is a comparison
          operator (e.g. "if A < B then"). }
        if Check(tkNotEquals) and (PeekKind = tkDot) then
        begin
          { Diamond: TFoo<> — the lexer folds '<>' into a single tkNotEquals token }
          Advance;  { consume '<>' }
          Name := Name + '<>';
          { Must be followed by '.' (type access) }
          if not Check(tkDot) then
            raise EParseError.Create(Format(
              'Expected ''.'' after ''<>'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end
        else if Check(tkLessThan) and (PeekKind = tkIdent) and
           (PeekKind2 in [tkGreaterThan, tkComma]) then
        begin
          Advance;  { consume '<' }
          Name := Name + '<' + FCurrent.Value;
          Advance;
          while Check(tkComma) do
          begin
            Advance;
            Name := Name + ',' + FCurrent.Value;
            Advance;
          end;
          Expect(tkGreaterThan);
          Name := Name + '>';
          { Generic type args must be followed by '.' (type access) or '(' (generic func call) }
          if not (Check(tkDot) or Check(tkLParen)) then
            raise EParseError.Create(Format(
              'Expected ''.'' or ''('' after generic type arguments at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        { Supports(Obj, IFoo) or Supports(Obj, IFoo, OutVar) — compiler intrinsic }
        if SameText(Name, 'Supports') and Check(tkLParen) then
        begin
          SuppNode          := TSupportsExpr.Create;
          SuppNode.Line     := Line;
          SuppNode.Col      := Col;
          Advance;  { consume '(' }
          SuppNode.Obj      := ParseExpr;
          Expect(tkComma);
          SuppNode.IntfTypeName := FCurrent.Value;
          Expect(tkIdent);
          if Check(tkComma) then
          begin
            Advance;  { consume ',' }
            SuppNode.OutVarName := FCurrent.Value;
            Expect(tkIdent);
          end;
          Expect(tkRParen);
          Result := SuppNode;
        end
        else if Check(tkDot) then
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondName := FCurrent.Value;
          Advance;
          if Check(tkLParen) then
          begin
            { IDENT '.' IDENT '(' ... ')' — method call expression }
            MCallNode            := TMethodCallExpr.Create;
            MCallNode.Line       := Line;
            MCallNode.Col        := Col;
            MCallNode.ObjectName := Name;
            MCallNode.Name       := SecondName;
            Advance;
            if not Check(tkRParen) then
            begin
              MCallNode.Args.Add(ParseExpr);
              while Check(tkComma) do
              begin
                Advance;
                MCallNode.Args.Add(ParseExpr);
              end;
            end;
            Expect(tkRParen);
            Result := MCallNode;
          end
          else
          begin
            { IDENT '.' IDENT — field access or constructor call }
            FldNode            := TFieldAccessExpr.Create;
            FldNode.Line       := Line;
            FldNode.Col        := Col;
            FldNode.RecordName := Name;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
            { Indexed property read: Ident.Prop[idx] }
            if Check(tkLBracket) then
            begin
              Advance;
              FldNode.PropIndexExpr := ParseExpr;
              Expect(tkRBracket);
            end;
            { Chained access: A.B.C.D ... — wrap each subsequent '.IDENT' }
            while Check(tkDot) and (PeekKind = tkIdent) do
            begin
              Advance;  { consume '.' }
              SecondName := FCurrent.Value;
              Advance;  { consume field/method name }
              if Check(tkLParen) then
              begin
                { Chained method call on expression }
                MCallNode             := TMethodCallExpr.Create;
                MCallNode.Line        := FCurrent.Line;
                MCallNode.Col         := FCurrent.Col;
                MCallNode.ObjectName  := '';
                MCallNode.Name        := SecondName;
                MCallNode.ObjExpr     := Result;
                Advance;  { consume '(' }
                if not Check(tkRParen) then
                begin
                  MCallNode.Args.Add(ParseExpr);
                  while Check(tkComma) do
                  begin
                    Advance;
                    MCallNode.Args.Add(ParseExpr);
                  end;
                end;
                Expect(tkRParen);
                Result := MCallNode;
              end
              else
              begin
                FldNode            := TFieldAccessExpr.Create;
                FldNode.Line       := FCurrent.Line;
                FldNode.Col        := FCurrent.Col;
                FldNode.Base       := Result;
                FldNode.FieldName  := SecondName;
                Result := FldNode;
                { Indexed property on chained access: A.B.Prop[idx] }
                if Check(tkLBracket) then
                begin
                  Advance;
                  FldNode.PropIndexExpr := ParseExpr;
                  Expect(tkRBracket);
                end;
              end;
            end;
          end;
        end
        else if Check(tkLParen) then
        begin
          { Standalone function call expression: Ident '(' [args] ')' }
          FCallNode      := TFuncCallExpr.Create;
          FCallNode.Line := Line;
          FCallNode.Col  := Col;
          FCallNode.Name := Name;
          Advance;  { consume '(' }
          if not Check(tkRParen) then
          begin
            FCallNode.Args.Add(ParseExpr);
            while Check(tkComma) do
            begin
              Advance;
              FCallNode.Args.Add(ParseExpr);
            end;
          end;
          Expect(tkRParen);
          Result := FCallNode;
          { Postfix chained field/method access: FuncOrCast(...).Member ... }
          while Check(tkDot) and (PeekKind = tkIdent) do
          begin
            Advance;  { consume '.' }
            SecondName := FCurrent.Value;
            Advance;  { consume field/method name }
            FldNode            := TFieldAccessExpr.Create;
            FldNode.Line       := FCurrent.Line;
            FldNode.Col        := FCurrent.Col;
            FldNode.Base       := Result;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
            if Check(tkLParen) then
            begin
              { Method call with args on the chained expression — represent
                by marking the access as a method call and parsing an arg list
                into a synthesised TMethodCallExpr with Obj=Base. }
              { We convert the TFieldAccessExpr into an arg-bearing method call. }
              Advance;  { consume '(' }
              if not Check(tkRParen) then
              begin
                FldNode.ResolvedType := nil; { placeholder to note args }
              end;
              { Lift the FldNode to a method call by storing args via a
                temporary TMethodCallExpr and using Base for the receiver. }
              MCallNode             := TMethodCallExpr.Create;
              MCallNode.Line        := FldNode.Line;
              MCallNode.Col         := FldNode.Col;
              MCallNode.ObjectName  := '';  { empty — receiver is Base expr }
              MCallNode.Name        := SecondName;
              MCallNode.ObjExpr     := FldNode.Base;
              FldNode.Base          := nil;  { transfer ownership }
              FldNode.Free;
              if not Check(tkRParen) then
              begin
                MCallNode.Args.Add(ParseExpr);
                while Check(tkComma) do
                begin
                  Advance;
                  MCallNode.Args.Add(ParseExpr);
                end;
              end;
              Expect(tkRParen);
              Result := MCallNode;
            end
            else if Check(tkLBracket) then
            begin
              { Indexed property on chained access from a typecast/call:
                FuncOrCast(...).A.B.Items[idx].  Same shape as the
                A.B.Items[idx] branch above — store the index on the
                outer FieldAccess so the analyser can resolve the property
                with its index in one place. }
              Advance;
              FldNode.PropIndexExpr := ParseExpr;
              Expect(tkRBracket);
            end;
          end;
        end
        else
        begin
          IdNode      := TIdentExpr.Create;
          IdNode.Line := Line;
          IdNode.Col  := Col;
          IdNode.Name := Name;
          Result := IdNode;
        end;
        { Postfix dereference: Expr^ and optional Expr^.Field chaining }
        if Check(tkCaret) then
        begin
          Advance;
          DerefNode      := TDerefExpr.Create;
          DerefNode.Line := Line;
          DerefNode.Col  := Col;
          DerefNode.Expr := Result;
          Result         := DerefNode;
          { Deref-then-field: P^.Field or P^.Field.Sub ... }
          while Check(tkDot) and (PeekKind = tkIdent) do
          begin
            Advance;  { consume '.' }
            FldNode           := TFieldAccessExpr.Create;
            FldNode.Line      := FCurrent.Line;
            FldNode.Col       := FCurrent.Col;
            FldNode.FieldName := FCurrent.Value;
            FldNode.Base      := Result;
            Advance;  { consume field name }
            Result := FldNode;
          end;
        end;
      end;
    tkLBracket:
      begin
        ArrNode      := TArrayLiteralExpr.Create;
        ArrNode.Line := FCurrent.Line;
        ArrNode.Col  := FCurrent.Col;
        try
          Advance;  { consume '[' }
          if not Check(tkRBracket) then
          begin
            ArrNode.Elements.Add(ParseExpr);
            while Check(tkComma) do
            begin
              Advance;  { consume ',' }
              ArrNode.Elements.Add(ParseExpr);
            end;
          end;
          Expect(tkRBracket);
        except
          ArrNode.Free;
          raise;
        end;
        Result := ArrNode;
        Exit;  { array literals are not subscriptable — skip postfix check }
      end;
    tkLParen:
      begin
        Advance;
        Inner := ParseExpr;
        Expect(tkRParen);
        { Postfix dereference: (Expr)^ and optional (Expr)^.Field chaining }
        if Check(tkCaret) then
        begin
          Advance;
          DerefNode      := TDerefExpr.Create;
          DerefNode.Line := FCurrent.Line;
          DerefNode.Col  := FCurrent.Col;
          DerefNode.Expr := Inner;
          Result         := DerefNode;
          while Check(tkDot) and (PeekKind = tkIdent) do
          begin
            Advance;
            FldNode           := TFieldAccessExpr.Create;
            FldNode.Line      := FCurrent.Line;
            FldNode.Col       := FCurrent.Col;
            FldNode.FieldName := FCurrent.Value;
            FldNode.Base      := Result;
            Advance;
            Result := FldNode;
          end;
        end
        else
          Result := Inner;
      end;
  else
    raise EParseError.Create(Format(
      'Expected expression at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  { Postfix chaining loop: Expr.Field, Expr.Method(...), Expr[i], Expr^, Expr(...) }
  while Check(tkDot) or Check(tkLBracket) or Check(tkCaret) or Check(tkLParen) do
  begin
    if Check(tkLParen) then
    begin
      { Indirect call through a non-identifier expression: Expr(args).
        Build TIndirectFuncCallExpr with Result as the callee. }
      IndCallNode            := TIndirectFuncCallExpr.Create;
      IndCallNode.Line       := FCurrent.Line;
      IndCallNode.Col        := FCurrent.Col;
      IndCallNode.CalleeExpr := Result;
      Result                 := nil;
      try
        Advance;  { consume '(' }
        if not Check(tkRParen) then
        begin
          IndCallNode.Args.Add(ParseExpr);
          while Check(tkComma) do
          begin
            Advance;
            IndCallNode.Args.Add(ParseExpr);
          end;
        end;
        Expect(tkRParen);
      except
        IndCallNode.Free;
        raise;
      end;
      Result := IndCallNode;
    end
    else if Check(tkDot) then
    begin
      Advance;  { consume '.' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected field or method name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      SecondName := FCurrent.Value;
      Advance;  { consume ident }
      if Check(tkLParen) then
      begin
        MCallNode            := TMethodCallExpr.Create;
        MCallNode.Line       := FCurrent.Line;
        MCallNode.Col        := FCurrent.Col;
        MCallNode.ObjectName := '';
        MCallNode.Name       := SecondName;
        MCallNode.ObjExpr    := Result;
        Advance;  { consume '(' }
        if not Check(tkRParen) then
        begin
          MCallNode.Args.Add(ParseExpr);
          while Check(tkComma) do
          begin
            Advance;
            MCallNode.Args.Add(ParseExpr);
          end;
        end;
        Expect(tkRParen);
        Result := MCallNode;
      end
      else
      begin
        FldNode           := TFieldAccessExpr.Create;
        FldNode.Line      := FCurrent.Line;
        FldNode.Col       := FCurrent.Col;
        FldNode.Base      := Result;
        FldNode.FieldName := SecondName;
        Result := FldNode;
        if Check(tkLBracket) then
        begin
          Advance;
          FldNode.PropIndexExpr := ParseExpr;
          Expect(tkRBracket);
        end;
      end;
    end
    else if Check(tkLBracket) then
    begin
      SubNode := TStringSubscriptExpr.Create;
      SubNode.Line := FCurrent.Line;
      SubNode.Col  := FCurrent.Col;
      SubNode.StrExpr := Result;
      Result := nil;
      try
        Advance;  { consume '[' }
        SubNode.IndexExpr := ParseExpr;
        Expect(tkRBracket);
      except
        SubNode.Free;
        raise;
      end;
      Result := SubNode;
    end
    else
    begin
      Advance;  { consume '^' }
      DerefNode      := TDerefExpr.Create;
      DerefNode.Line := FCurrent.Line;
      DerefNode.Col  := FCurrent.Col;
      DerefNode.Expr := Result;
      Result         := DerefNode;
    end;
  end;
end;

end.
