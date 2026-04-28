{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause

  blaise-compiler.pas - Self-hosting source.
  Concatenated from all compiler units.
}

program BlaiseCompiler;

const
  CHR_QUOTE    = 39;    CHR_HASH     = 35;    CHR_DOLLAR   = 36;
  CHR_LF       = 10;    CHR_CR       = 13;    CHR_TAB      = 9;
  CHR_SPACE    = 32;    CHR_0        = 48;    CHR_9        = 57;
  CHR_A_UP     = 65;    CHR_F_UP     = 70;    CHR_Z_UP     = 90;
  CHR_a_LO     = 97;    CHR_f_LO     = 102;   CHR_z_LO     = 122;
  CHR_UNDER    = 95;    CHR_CARET    = 94;    CHR_DOT      = 46;
  CHR_AT       = 64;    CHR_LT       = 60;    CHR_GT       = 62;
  CHR_EQ       = 61;    CHR_PLUS     = 43;    CHR_MINUS    = 45;
  CHR_STAR     = 42;    CHR_SLASH    = 47;    CHR_LPAREN   = 40;
  CHR_RPAREN   = 41;    CHR_SEMI     = 59;    CHR_COLON    = 58;
  CHR_LBRACKET = 91;    CHR_RBRACKET = 93;    CHR_e_LO     = 101;
  CHR_E_UP     = 69;    CHR_DQUOTE   = 34;
  MaxInt       = 2147483647;

type
  Exception = class
    FMessage: string;
    procedure Create(AMessage: string);
    procedure CreateFmt(const AFmt: string; AArg: Integer);
    procedure Destroy; virtual;
    property Message: string read FMessage;
  end;
  EParseError    = class(Exception);
  ESemanticError = class(Exception);
  ECodeGenError  = class(Exception);

procedure Exception.Create(AMessage: string);
begin
  Self.FMessage := AMessage
end;

procedure Exception.CreateFmt(const AFmt: string; AArg: Integer);
begin
  Self.FMessage := Format(AFmt, AArg)
end;

procedure Exception.Destroy;
begin

end;

{ ChangeFileExt, ExtractFileName, ExtractFilePath, IncludeTrailingPathDelimiter
  are now compiler built-ins (step 11) — no hand implementations needed. }


{ === RTL: Collections === }



























const
  dupAccept = 0;
  dupIgnore = 1;
  dupError  = 2;

type
  
  
  

  TObjectList = class
    FData:        ^Pointer;
    FCount:       Integer;
    FCapacity:    Integer;
    FOwnsObjects: Boolean;
    procedure Grow;
    procedure Create(AOwnsObjects: Boolean);
    procedure   Destroy;
    function    Add(AObject: Pointer): Integer;
    function    Get(AIndex: Integer): Pointer;
    procedure   Put(AIndex: Integer; AObject: Pointer);
    function    IndexOf(AObject: Pointer): Integer;
    procedure   Delete(AIndex: Integer);
    function    Extract(AIndex: Integer): Pointer;
    procedure   Clear;
    property Count: Integer read FCount;
  end;

  
  
  

  TStringList = class
    FStrings:       ^string;
    FObjects:       ^Pointer;
    FCount:         Integer;
    FCapacity:      Integer;
    FCaseSensitive: Boolean;
    FSorted:        Boolean;
    FDuplicates:    Integer;
    procedure Grow;
    function  Compare(S1: string; S2: string): Integer;
    function  FindSorted(S: string; var Idx: Integer): Boolean;
    procedure Create;
    procedure   Destroy;
    function    Add(S: string): Integer;
    procedure   AddObject(S: string; AObject: Pointer);
    function    Find(S: string; var Index: Integer): Boolean;
    function    IndexOf(S: string): Integer;
    function    Get(AIndex: Integer): string;
    procedure   Put(AIndex: Integer; S: string);
    function    GetObject(AIndex: Integer): Pointer;
    procedure   SetObject(AIndex: Integer; AObject: Pointer);
    procedure   Delete(AIndex: Integer);
    procedure   Clear;
    procedure   Insert(AIndex: Integer; S: string);
    procedure   AddStrings(ASource: TStringList);
    function    GetText: string;
    property Count:         Integer read FCount;
    property CaseSensitive: Boolean read FCaseSensitive write FCaseSensitive;
    property Sorted:        Boolean read FSorted        write FSorted;
    property Duplicates:    Integer read FDuplicates    write FDuplicates;
  end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);






procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);
var
  I:     Integer;
  Start: Integer;
  SLo:   Integer;
  SHi:   Integer;
begin
  AList.Clear;
  Start := 1;
  I     := 1;
  while I <= Length(S) do
  begin
    if OrdAt(S, I) = ASep then
    begin
      
      SLo := Start;
      SHi := I - 1;
      while (SLo <= SHi) and (OrdAt(S, SLo) = 32) do SLo := SLo + 1;
      while (SHi >= SLo) and (OrdAt(S, SHi) = 32) do SHi := SHi - 1;
      AList.Add(Copy(S, SLo, SHi - SLo + 1));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  if Start <= Length(S) then
  begin
    SLo := Start;
    SHi := Length(S);
    while (SLo <= SHi) and (OrdAt(S, SLo) = 32) do SLo := SLo + 1;
    while (SHi >= SLo) and (OrdAt(S, SHi) = 32) do SHi := SHi - 1;
    AList.Add(Copy(S, SLo, SHi - SLo + 1));
  end;
end;


procedure TObjectList.Grow;
var
  NewCap: Integer;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
  Self.FCapacity := NewCap
end;

procedure TObjectList.Create(AOwnsObjects: Boolean);
begin
  Self.FOwnsObjects := AOwnsObjects
end;

procedure TObjectList.Destroy;
var
  I: Integer;
  Src: ^Pointer;
begin
  if Self.FOwnsObjects then
  begin
    I := 0;
    while I < Self.FCount do
    begin
      Src := Self.FData + I * SizeOf(Pointer);
      _ClassRelease(Src^);
      I := I + 1
    end
  end;
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TObjectList.Add(AObject: Pointer): Integer;
var
  Dest: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
  Dest^       := AObject;
  _ClassAddRef(AObject);
  Self.FCount := Self.FCount + 1;
  Result      := Self.FCount - 1
end;

function TObjectList.Get(AIndex: Integer): Pointer;
var
  Src: ^Pointer;
begin
  Src    := Self.FData + AIndex * SizeOf(Pointer);
  Result := Src^
end;

procedure TObjectList.Put(AIndex: Integer; AObject: Pointer);
var
  Dest: ^Pointer;
begin
  Dest  := Self.FData + AIndex * SizeOf(Pointer);
  _ClassAddRef(AObject);
  if Self.FOwnsObjects then
    _ClassRelease(Dest^);
  Dest^ := AObject
end;

function TObjectList.IndexOf(AObject: Pointer): Integer;
var
  I:   Integer;
  Src: ^Pointer;
begin
  I      := 0;
  Result := -1;
  while I < Self.FCount do
  begin
    Src := Self.FData + I * SizeOf(Pointer);
    if Src^ = AObject then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TObjectList.Delete(AIndex: Integer);
var
  I:   Integer;
  Dst: ^Pointer;
  Src: ^Pointer;
begin
  if Self.FOwnsObjects then
  begin
    Src := Self.FData + AIndex * SizeOf(Pointer);
    _ClassRelease(Src^);
  end;
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TObjectList.Clear;
var
  I: Integer;
  Src: ^Pointer;
begin
  if Self.FOwnsObjects then
  begin
    I := 0;
    while I < Self.FCount do
    begin
      Src := Self.FData + I * SizeOf(Pointer);
      _ClassRelease(Src^);
      I := I + 1
    end
  end;
  Self.FCount := 0
end;

function TObjectList.Extract(AIndex: Integer): Pointer;
var
  I:   Integer;
  Src: ^Pointer;
  Dst: ^Pointer;
begin
  Src    := Self.FData + AIndex * SizeOf(Pointer);
  Result := Src^;
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;





procedure TStringList.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FStrings  := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
  Self.FObjects  := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
  
  ZeroMem(Self.FStrings + OldCap * SizeOf(string),
          (NewCap - OldCap) * SizeOf(string));
  Self.FCapacity := NewCap
end;

function TStringList.Compare(S1: string; S2: string): Integer;
begin
  if Self.FCaseSensitive then
    Result := CompareStr(S1, S2)
  else
    Result := CompareText(S1, S2)
end;

function TStringList.FindSorted(S: string; var Idx: Integer): Boolean;
var
  Lo:   Integer;
  Hi:   Integer;
  Mid:  Integer;
  Cmp:  Integer;
  Ptr:  ^string;
  MStr: string;
begin
  Lo := 0;
  Hi := Self.FCount - 1;
  while Lo <= Hi do
  begin
    Mid  := (Lo + Hi) div 2;
    Ptr  := Self.FStrings + Mid * SizeOf(string);
    MStr := Ptr^;
    Cmp  := Self.Compare(S, MStr);
    if Cmp = 0 then
    begin
      Idx    := Mid;
      Result := True;
      Exit
    end
    else if Cmp < 0 then
      Hi := Mid - 1
    else
      Lo := Mid + 1
  end;
  Idx    := Lo;
  Result := False
end;

procedure TStringList.Create;
begin
  Self.FCaseSensitive := True;
  Self.FSorted        := False;
  Self.FDuplicates    := dupAccept
end;

procedure TStringList.Destroy;
var
  I:   Integer;
  Ptr: ^string;
begin
  
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  FreeMem(Self.FStrings);
  FreeMem(Self.FObjects);
  Self.FStrings  := nil;
  Self.FObjects  := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TStringList.Add(S: string): Integer;
var
  Idx:  Integer;
  StrP: ^string;
  ObjP: ^Pointer;
begin
  if Self.FSorted then
  begin
    Self.FindSorted(S, Idx);
    if (Self.FDuplicates = dupIgnore) and
       (Idx < Self.FCount) then
    begin
      
      StrP := Self.FStrings + Idx * SizeOf(string);
      if Self.Compare(S, StrP^) = 0 then
      begin
        Result := Idx;
        Exit
      end
    end;
    Self.Insert(Idx, S);
    Result := Idx
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow;
    StrP        := Self.FStrings + Self.FCount * SizeOf(string);
    ObjP        := Self.FObjects + Self.FCount * SizeOf(Pointer);
    StrP^       := S;
    ObjP^       := nil;
    Result      := Self.FCount;
    Self.FCount := Self.FCount + 1
  end
end;

procedure TStringList.AddObject(S: string; AObject: Pointer);
var
  Idx:  Integer;
  ObjP: ^Pointer;
begin
  Idx  := Self.Add(S);
  ObjP := Self.FObjects + Idx * SizeOf(Pointer);
  ObjP^ := AObject
end;

function TStringList.Find(S: string; var Index: Integer): Boolean;
var
  I:    Integer;
  Ptr:  ^string;
begin
  if Self.FSorted then
    Result := Self.FindSorted(S, Index)
  else
  begin
    
    I := 0;
    while I < Self.FCount do
    begin
      Ptr := Self.FStrings + I * SizeOf(string);
      if Self.Compare(S, Ptr^) = 0 then
      begin
        Index  := I;
        Result := True;
        Exit
      end;
      I := I + 1
    end;
    Index  := -1;
    Result := False
  end
end;

function TStringList.IndexOf(S: string): Integer;
var
  Idx: Integer;
begin
  if Self.Find(S, Idx) then
    Result := Idx
  else
    Result := -1
end;

function TStringList.Get(AIndex: Integer): string;
var
  Ptr: ^string;
begin
  Ptr    := Self.FStrings + AIndex * SizeOf(string);
  Result := Ptr^
end;

procedure TStringList.Put(AIndex: Integer; S: string);
var
  Ptr: ^string;
begin
  Ptr  := Self.FStrings + AIndex * SizeOf(string);
  Ptr^ := S
end;

function TStringList.GetObject(AIndex: Integer): Pointer;
var
  Ptr: ^Pointer;
begin
  Ptr    := Self.FObjects + AIndex * SizeOf(Pointer);
  Result := Ptr^
end;

procedure TStringList.SetObject(AIndex: Integer; AObject: Pointer);
var
  Ptr: ^Pointer;
begin
  Ptr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^ := AObject
end;

procedure TStringList.Delete(AIndex: Integer);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I + 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I + 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I + 1
  end;
  
  SDst  := Self.FStrings + (Self.FCount - 1) * SizeOf(string);
  SDst^ := nil;
  ODst  := Self.FObjects + (Self.FCount - 1) * SizeOf(Pointer);
  ODst^ := nil;
  Self.FCount := Self.FCount - 1
end;

procedure TStringList.Clear;
var
  I:   Integer;
  Ptr: ^string;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  Self.FCount := 0
end;

procedure TStringList.Insert(AIndex: Integer; S: string);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
  Ptr:  ^string;
  OPtr: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  
  I := Self.FCount;
  while I > AIndex do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I - 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I - 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I - 1
  end;
  
  SSrc  := Self.FStrings + AIndex * SizeOf(string);
  SSrc^ := nil;  
  
  Ptr   := Self.FStrings + AIndex * SizeOf(string);
  OPtr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^  := S;
  OPtr^ := nil;
  Self.FCount := Self.FCount + 1
end;

procedure TStringList.AddStrings(ASource: TStringList);
var
  I: Integer;
begin
  I := 0;
  while I < ASource.FCount do
  begin
    Self.Add(ASource.Get(I));
    I := I + 1
  end;
end;

function TStringList.GetText: string;
var
  I:   Integer;
  Ptr: ^string;
  Sep: string;
begin
  Result := '';
  Sep    := '';
  I := 0;
  while I < Self.FCount do
  begin
    Ptr    := Self.FStrings + I * SizeOf(string);
    Result := Result + Sep + Ptr^;
    Sep    := #10;
    I      := I + 1
  end
end;




{ === uPasTokeniser === }


var KwList: TStringList;

procedure InitKeywords;
begin
  KwList := TStringList.Create;
  KwList.Sorted := True;
  KwList.CaseSensitive := True;
  KwList.Add('ABSOLUTE');  KwList.Add('AND');       KwList.Add('ARRAY');
  KwList.Add('AS');        KwList.Add('ASM');        KwList.Add('BEGIN');
  KwList.Add('BITPACKED'); KwList.Add('CASE');       KwList.Add('CLASS');
  KwList.Add('CONST');     KwList.Add('CONSTREF');   KwList.Add('CONSTRUCTOR');
  KwList.Add('CONTAINS');  KwList.Add('DESTRUCTOR'); KwList.Add('DISPINTERFACE');
  KwList.Add('DIV');       KwList.Add('DO');         KwList.Add('DOWNTO');
  KwList.Add('ELSE');      KwList.Add('END');        KwList.Add('EXCEPT');
  KwList.Add('EXPORTS');   KwList.Add('FALSE');      KwList.Add('FILE');
  KwList.Add('FINALIZATION'); KwList.Add('FINALLY'); KwList.Add('FOR');
  KwList.Add('FUNCTION');  KwList.Add('GENERIC');    KwList.Add('GOTO');
  KwList.Add('IF');        KwList.Add('IMPLEMENTATION'); KwList.Add('IN');
  KwList.Add('INHERITED'); KwList.Add('INITIALIZATION'); KwList.Add('INLINE');
  KwList.Add('INTERFACE'); KwList.Add('IS');         KwList.Add('LABEL');
  KwList.Add('LIBRARY');   KwList.Add('MOD');        KwList.Add('NIL');
  KwList.Add('NOT');       KwList.Add('OBJCCATEGORY'); KwList.Add('OBJCCLASS');
  KwList.Add('OBJCPROTOCOL'); KwList.Add('OBJECT'); KwList.Add('OF');
  KwList.Add('OPERATOR');  KwList.Add('OR');         KwList.Add('OTHERWISE');
  KwList.Add('PACKAGE');   KwList.Add('PACKED');     KwList.Add('PROCEDURE');
  KwList.Add('PROGRAM');   KwList.Add('PROPERTY');   KwList.Add('RAISE');
  KwList.Add('RECORD');    KwList.Add('REPEAT');     KwList.Add('REQUIRES');
  KwList.Add('RESOURCESTRING'); KwList.Add('SELF'); KwList.Add('SET');
  KwList.Add('SHL');       KwList.Add('SHR');        KwList.Add('SPECIALIZE');
  KwList.Add('THEN');      KwList.Add('THREADVAR');  KwList.Add('TO');
  KwList.Add('TRUE');      KwList.Add('TRY');        KwList.Add('TYPE');
  KwList.Add('UNIT');      KwList.Add('UNTIL');      KwList.Add('USES');
  KwList.Add('VAR');       KwList.Add('WHILE');      KwList.Add('WITH');
  KwList.Add('XOR')
end;

function BinarySearchKeyword(const AText: string): Boolean;
var
  Idx: Integer;
begin
  Result := KwList.Find(AText, Idx)
end;

























type
  TFpgPasTokenKind = (
    fptkEOF,
    fptkWhitespace,
    fptkLineEnding,
    fptkIdentifier,
    fptkKeyword,
    fptkNumber,
    fptkString,
    fptkComment,
    fptkDirective,
    fptkSymbol
  );

  TFpgPasToken = record
    Kind: TFpgPasTokenKind;
    Line: Integer;       
    Column: Integer;     
    Len: Integer;        
    TextStart: Integer;  
  end;

  

  TFpgPascalTokeniser = class(TObject)

    FSource: string;
    FPos: Integer;
    FLine: Integer;
    FLineStart: Integer;  
    FToken: TFpgPasToken;
    function Peek: Integer;
    function PeekAt(AOffset: Integer): Integer;
    procedure Advance;
    procedure AdvanceLine;
    procedure ReadWhitespace;
    procedure ReadLineEnding;
    procedure ReadIdentifierOrKeyword;
    procedure ReadNumber;
    procedure ReadString;
    procedure ReadBraceCommentOrDirective;
    procedure ReadParenStarCommentOrDirective;
    procedure ReadLineComment;
    procedure ReadSymbol;

    procedure Create;
    procedure SetSource(const ASource: string);
    function NextToken: TFpgPasToken;
    function TokenText: string;
    function TokenTextUpper: string;
    property Token: TFpgPasToken read FToken;
    property Source: string read FSource;
  end;


function PasIsKeyword(const AText: string): Boolean;




function PasIsKeyword(const AText: string): Boolean;
begin
  if AText = '' then
    begin Result := False; Exit end;
  Result := BinarySearchKeyword(UpperCase(AText));
end;



procedure TFpgPascalTokeniser.Create;
begin

  FSource := '';
  FPos := 1;
  FLine := 1;
  FLineStart := 1;
end;

procedure TFpgPascalTokeniser.SetSource(const ASource: string);
begin
  FSource := ASource;
  FPos := 1;
  FLine := 1;
  FLineStart := 1;
  FToken.Kind := fptkEOF;
  FToken.Line := 1;
  FToken.Column := 1;
  FToken.Len := 0;
  FToken.TextStart := 1;
end;

function TFpgPascalTokeniser.Peek: Integer;
begin
  if FPos <= Length(FSource) then
    Result := OrdAt(FSource, FPos)
  else
    Result := 0;
end;

function TFpgPascalTokeniser.PeekAt(AOffset: Integer): Integer;
var
  p: Integer;
begin
  p := FPos + AOffset;
  if (p >= 1) and (p <= Length(FSource)) then
    Result := OrdAt(FSource, p)
  else
    Result := 0;
end;

procedure TFpgPascalTokeniser.Advance;
begin
  FPos := FPos + 1;
end;

procedure TFpgPascalTokeniser.AdvanceLine;
begin
  FLine := FLine + 1;
  FLineStart := FPos;
end;

procedure TFpgPascalTokeniser.ReadWhitespace;
begin
  FToken.Kind := fptkWhitespace;
  while (FPos <= Length(FSource)) and (((OrdAt(FSource, FPos) = 32) or (OrdAt(FSource, FPos) = 9))) do
    Advance;
  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadLineEnding;
begin
  FToken.Kind := fptkLineEnding;
  if (OrdAt(FSource, FPos) = 13) and (PeekAt(1) = 10) then
    Advance;  
  Advance;    
  FToken.Len := FPos - FToken.TextStart;
  AdvanceLine;
end;

procedure TFpgPascalTokeniser.ReadIdentifierOrKeyword;
begin
  while (FPos <= Length(FSource)) and
        ((((OrdAt(FSource, FPos) >= 65) and (OrdAt(FSource, FPos) <= 90)) or ((OrdAt(FSource, FPos) >= 97) and (OrdAt(FSource, FPos) <= 122)) or ((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)) or (OrdAt(FSource, FPos) = 95))) do
    Advance;
  FToken.Len := FPos - FToken.TextStart;
  if BinarySearchKeyword(UpperCase(TokenText)) then
    FToken.Kind := fptkKeyword
  else
    FToken.Kind := fptkIdentifier;
end;

procedure TFpgPascalTokeniser.ReadNumber;
var
  c: Integer;
begin
  FToken.Kind := fptkNumber;
  c := OrdAt(FSource, FPos);

  if c = 36 then
  begin
    
    Advance;
    while (FPos <= Length(FSource)) and
          ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)) or ((OrdAt(FSource, FPos) >= 65) and (OrdAt(FSource, FPos) <= 70)) or ((OrdAt(FSource, FPos) >= 97) and (OrdAt(FSource, FPos) <= 102)))) do
      Advance;
    FToken.Len := FPos - FToken.TextStart;
    Exit;
  end;

  if c = 37 then
  begin
    
    Advance;
    while (FPos <= Length(FSource)) and (((OrdAt(FSource, FPos) = 48) or (OrdAt(FSource, FPos) = 49))) do
      Advance;
    FToken.Len := FPos - FToken.TextStart;
    Exit;
  end;

  if c = 38 then
  begin
    
    Advance;
    while (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 55)))) do
      Advance;
    FToken.Len := FPos - FToken.TextStart;
    Exit;
  end;

  
  while (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)))) do
    Advance;

  
  if (FPos <= Length(FSource)) and (OrdAt(FSource, FPos) = 46) and
     (PeekAt(1) <> 46) then
  begin
    Advance;  
    while (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)))) do
      Advance;
  end;

  
  if (FPos <= Length(FSource)) and (((OrdAt(FSource, FPos) = 101) or (OrdAt(FSource, FPos) = 69))) then
  begin
    Advance;
    if (FPos <= Length(FSource)) and (((OrdAt(FSource, FPos) = 43) or (OrdAt(FSource, FPos) = 45))) then
      Advance;
    while (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)))) do
      Advance;
  end;

  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadString;
var
  c: Integer;
begin
  





  FToken.Kind := fptkString;

  while True do
begin
    c := Peek;
    if c = 39 then
    begin
      Advance;  
      while FPos <= Length(FSource) do
      begin
        if OrdAt(FSource, FPos) = 39 then
        begin
          Advance;
          
          if (FPos <= Length(FSource)) and (OrdAt(FSource, FPos) = 39) then
            Advance
          else
            Break;  
        end
        else if ((OrdAt(FSource, FPos) = 10) or (OrdAt(FSource, FPos) = 13)) then
          Break  
        else
          Advance;
      end;
    end
    else if c = 35 then
    begin
      Advance;  
      if (FPos <= Length(FSource)) and (OrdAt(FSource, FPos) = 36) then
      begin
        Advance;  
        while (FPos <= Length(FSource)) and
              ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)) or ((OrdAt(FSource, FPos) >= 65) and (OrdAt(FSource, FPos) <= 70)) or ((OrdAt(FSource, FPos) >= 97) and (OrdAt(FSource, FPos) <= 102)))) do
          Advance;
      end
      else
      begin
        while (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 48) and (OrdAt(FSource, FPos) <= 57)))) do
          Advance;
      end;
    end
    else if c = 94 then
    begin
      Advance;  
      if (FPos <= Length(FSource)) and ((((OrdAt(FSource, FPos) >= 65) and (OrdAt(FSource, FPos) <= 90)) or ((OrdAt(FSource, FPos) >= 97) and (OrdAt(FSource, FPos) <= 122)))) then
        Advance;
    end
    else
      Break;  
    if False then break;
end;  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadBraceCommentOrDirective;
begin
  
  if PeekAt(1) = 36 then
    FToken.Kind := fptkDirective
  else
    FToken.Kind := fptkComment;

  Advance;  
  while FPos <= Length(FSource) do
  begin
    if OrdAt(FSource, FPos) = 125 then
    begin
      Advance;
      Break;
    end
    else if OrdAt(FSource, FPos) = 13 then
    begin
      Advance;
      if (FPos <= Length(FSource)) and (OrdAt(FSource, FPos) = 10) then
        Advance;
      AdvanceLine;
    end
    else if OrdAt(FSource, FPos) = 10 then
    begin
      Advance;
      AdvanceLine;
    end
    else
      Advance;
  end;
  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadParenStarCommentOrDirective;
begin
  
  if PeekAt(2) = 36 then
    FToken.Kind := fptkDirective
  else
    FToken.Kind := fptkComment;

  Advance;  
  Advance;  
  while FPos <= Length(FSource) do
  begin
    if (OrdAt(FSource, FPos) = 42) and (PeekAt(1) = 41) then
    begin
      Advance;  
      Advance;  
      Break;
    end
    else if OrdAt(FSource, FPos) = 13 then
    begin
      Advance;
      if (FPos <= Length(FSource)) and (OrdAt(FSource, FPos) = 10) then
        Advance;
      AdvanceLine;
    end
    else if OrdAt(FSource, FPos) = 10 then
    begin
      Advance;
      AdvanceLine;
    end
    else
      Advance;
  end;
  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadLineComment;
begin
  FToken.Kind := fptkComment;
  
  while (FPos <= Length(FSource)) and
        not (((OrdAt(FSource, FPos) = 10) or (OrdAt(FSource, FPos) = 13))) do
    Advance;
  FToken.Len := FPos - FToken.TextStart;
end;

procedure TFpgPascalTokeniser.ReadSymbol;
var
  c, c2: Integer;
begin
  FToken.Kind := fptkSymbol;
  c := OrdAt(FSource, FPos);
  c2 := PeekAt(1);
  Advance;

  case c of
    58: if c2 = 61 then Advance;           
    60: if ((c2 = 62) or (c2 = 61)) then Advance;   
    62: if ((c2 = 60) or (c2 = 61)) then Advance;   
    46: if c2 = 46 then Advance;           
    42: if c2 = 42 then Advance;           
    64: if c2 = 64 then Advance;           
    43: if c2 = 61 then Advance;           
    45: if c2 = 61 then Advance;           
    47: if c2 = 61 then Advance;           
  end;

  
  if (c = 42) and (c2 <> 42) and (c2 = 61) then
    Advance;

  FToken.Len := FPos - FToken.TextStart;
end;

function TFpgPascalTokeniser.NextToken: TFpgPasToken;
var
  c, c2: Integer;
begin
  if FPos > Length(FSource) then
  begin
    FToken.Kind := fptkEOF;
    FToken.Line := FLine;
    FToken.Column := FPos - FLineStart + 1;
    FToken.Len := 0;
    FToken.TextStart := FPos;
    Result := FToken;
    Exit;
  end;

  
  FToken.TextStart := FPos;
  FToken.Line := FLine;
  FToken.Column := FPos - FLineStart + 1;

  c := OrdAt(FSource, FPos);

  
  if ((c = 32) or (c = 9)) then
  begin
    ReadWhitespace;
    Result := FToken;
    Exit;
  end;

  
  if ((c = 13) or (c = 10)) then
  begin
    ReadLineEnding;
    Result := FToken;
    Exit;
  end;

  
  if (((c >= 65) and (c <= 90)) or ((c >= 97) and (c <= 122)) or (c = 95)) then
  begin
    ReadIdentifierOrKeyword;
    Result := FToken;
    Exit;
  end;

  
  if (((c >= 48) and (c <= 57))) then
  begin
    ReadNumber;
    Result := FToken;
    Exit;
  end;
  if (c = 36) and ((((PeekAt(1) >= 48) and (PeekAt(1) <= 57)) or ((PeekAt(1) >= 65) and (PeekAt(1) <= 70)) or ((PeekAt(1) >= 97) and (PeekAt(1) <= 102)))) then
  begin
    ReadNumber;
    Result := FToken;
    Exit;
  end;
  if (c = 37) and (((PeekAt(1) = 48) or (PeekAt(1) = 49))) then
  begin
    ReadNumber;
    Result := FToken;
    Exit;
  end;
  if (c = 38) and ((((PeekAt(1) >= 48) and (PeekAt(1) <= 55)))) then
  begin
    ReadNumber;
    Result := FToken;
    Exit;
  end;

  
  if ((c = 39) or (c = 35)) then
  begin
    ReadString;
    Result := FToken;
    Exit;
  end;

  
  if c = 123 then
  begin
    ReadBraceCommentOrDirective;
    Result := FToken;
    Exit;
  end;

  c2 := PeekAt(1);

  if (c = 40) and (c2 = 42) then
  begin
    ReadParenStarCommentOrDirective;
    Result := FToken;
    Exit;
  end;

  if (c = 47) and (c2 = 47) then
  begin
    ReadLineComment;
    Result := FToken;
    Exit;
  end;

  
  ReadSymbol;
  Result := FToken;
end;

function TFpgPascalTokeniser.TokenText: string;
begin
  if (FToken.TextStart >= 1) and (FToken.Len > 0) and
     (FToken.TextStart + FToken.Len - 1 <= Length(FSource)) then
    Result := Copy(FSource, FToken.TextStart, FToken.Len)
  else
    Result := '';
end;

function TFpgPascalTokeniser.TokenTextUpper: string;
begin
  Result := UpperCase(TokenText);
end;




{ === uLexer === }
















type
  TTokenKind = (
    tkEOF,
    
    tkIntLit,
    tkStringLit,
    
    tkProgram,
    tkUses,
    tkType,
    tkRecord,
    tkClass,
    tkProcedure,
    tkFunction,
    tkVar,
    tkBegin,
    tkEnd,
    tkIf,
    tkThen,
    tkElse,
    tkWhile,
    tkDo,
    tkFor,
    tkTo,
    tkDownto,
    tkTry,
    tkFinally,
    tkExcept,
    tkRaise,
    tkNil,
    tkUnit,
    tkIntf,
    tkImplementation,
    tkVirtual,
    tkOverride,
    tkIs,
    tkAs,
    tkAnd,
    tkOr,
    tkNot,
    tkExit,
    tkBreak,
    tkContinue,
    tkInherited,
    tkCase,
    tkOf,
    tkConst,
    
    tkIdent,
    
    tkPlus,
    tkMinus,
    tkStar,
    tkSlash,    
    tkDiv,      
    
    tkAssign,        
    tkEquals,        
    tkNotEquals,     
    tkLessThan,      
    tkGreaterThan,   
    tkLessEqual,     
    tkGreaterEqual,  
    tkColon,         
    
    tkLParen,
    tkRParen,
    tkLBracket,      
    tkRBracket,      
    tkComma,
    tkSemicolon,
    tkDot,
    tkCaret          
  );

  TToken = record
    Kind:  TTokenKind;
    Value: string;   
    Line:  Integer;
    Col:   Integer;
  end;

  TLexer = class

    FTok:  TFpgPascalTokeniser;
    function MapKeyword(const AUpper: string): TTokenKind;
    function UnescapeString(const ARaw: string): string;

    procedure Create(const ASource: string);
    procedure Destroy;
    function Next: TToken;
  end;


procedure TLexer.Create(const ASource: string);
begin

  FTok := TFpgPascalTokeniser.Create;
  FTok.SetSource(ASource);
end;

procedure TLexer.Destroy;
begin
  FTok.Free;

end;

function TLexer.MapKeyword(const AUpper: string): TTokenKind;
begin
  if AUpper = 'PROGRAM' then Result := tkProgram
  else if AUpper = 'USES'    then Result := tkUses
  else if AUpper = 'VAR'     then Result := tkVar
  else if AUpper = 'BEGIN'   then Result := tkBegin
  else if AUpper = 'END'     then Result := tkEnd
  else if AUpper = 'TYPE'    then Result := tkType
  else if AUpper = 'RECORD'  then Result := tkRecord
  else if AUpper = 'CLASS'     then Result := tkClass
  else if AUpper = 'PROCEDURE' then Result := tkProcedure
  else if AUpper = 'FUNCTION'  then Result := tkFunction
  else if AUpper = 'DIV'       then Result := tkDiv
  else if AUpper = 'IF'        then Result := tkIf
  else if AUpper = 'THEN'      then Result := tkThen
  else if AUpper = 'ELSE'      then Result := tkElse
  else if AUpper = 'WHILE'     then Result := tkWhile
  else if AUpper = 'DO'        then Result := tkDo
  else if AUpper = 'FOR'       then Result := tkFor
  else if AUpper = 'TO'        then Result := tkTo
  else if AUpper = 'DOWNTO'   then Result := tkDownto
  else if AUpper = 'TRY'       then Result := tkTry
  else if AUpper = 'FINALLY'   then Result := tkFinally
  else if AUpper = 'EXCEPT'    then Result := tkExcept
  else if AUpper = 'RAISE'     then Result := tkRaise
  else if AUpper = 'NIL'            then Result := tkNil
  else if AUpper = 'UNIT'           then Result := tkUnit
  else if AUpper = 'INTERFACE'      then Result := tkIntf
  else if AUpper = 'IMPLEMENTATION' then Result := tkImplementation
  else if AUpper = 'VIRTUAL'        then Result := tkVirtual
  else if AUpper = 'OVERRIDE'       then Result := tkOverride
  else if AUpper = 'IS'             then Result := tkIs
  else if AUpper = 'AS'             then Result := tkAs
  else if AUpper = 'AND'            then Result := tkAnd
  else if AUpper = 'OR'             then Result := tkOr
  else if AUpper = 'NOT'            then Result := tkNot
  else if AUpper = 'EXIT'           then Result := tkExit
  else if AUpper = 'BREAK'          then Result := tkBreak
  else if AUpper = 'CONTINUE'       then Result := tkContinue
  else if AUpper = 'CASE'           then Result := tkCase
  else if AUpper = 'OF'             then Result := tkOf
  else if AUpper = 'CONST'          then Result := tkConst
  else if AUpper = 'INHERITED'      then Result := tkInherited
  else
    Result := tkIdent;  
end;

function TLexer.UnescapeString(const ARaw: string): string;
var
  I, Len, N, C: Integer;
begin
  Result := '';
  Len := Length(ARaw);
  I := 1;
  while I <= Len do
  begin
    C := OrdAt(ARaw, I);
    if C = 39 then
    begin
      I := I + 1;
      while I <= Len do
      begin
        C := OrdAt(ARaw, I);
        if C = 39 then
        begin
          if (I < Len) and (OrdAt(ARaw, I + 1) = 39) then
          begin
            Result := Result + '''';
            I := I + 2;
          end
          else
          begin
            I := I + 1;
            Break;
          end;
        end
        else
        begin
          Result := Result + Chr(C);
          I := I + 1;
        end;
      end;
    end
    else if C = 35 then
    begin
      I := I + 1;
      N := 0;
      while I <= Len do
      begin
        C := OrdAt(ARaw, I);
        if (C < 48) or (C > 57) then Break;
        N := N * 10 + (C - 48);
        I := I + 1;
      end;
      Result := Result + Chr(N);
    end
    else
      I := I + 1;
  end;
end;

function TLexer.Next: TToken;
var
  raw:  TFpgPasToken;
  text: string;
begin
  while True do
begin
    raw := FTok.NextToken;
    if not (((raw.Kind = fptkWhitespace) or (raw.Kind = fptkLineEnding) or (raw.Kind = fptkComment) or (raw.Kind = fptkDirective))) then break;
end;  Result.Line := raw.Line;
  Result.Col  := raw.Column;

  case raw.Kind of
    fptkEOF:
      begin
        Result.Kind  := tkEOF;
        Result.Value := '';
      end;

    fptkKeyword:
      begin
        text := FTok.TokenTextUpper;
        Result.Kind  := MapKeyword(text);
        Result.Value := FTok.TokenText;
      end;

    fptkIdentifier:
      begin
        text := FTok.TokenTextUpper;
        if      text = 'VIRTUAL'  then Result.Kind := tkVirtual
        else if text = 'OVERRIDE' then Result.Kind := tkOverride
        else if text = 'EXIT'     then Result.Kind := tkExit
        else if text = 'BREAK'    then Result.Kind := tkBreak
        else if text = 'CONTINUE' then Result.Kind := tkContinue
        else if text = 'CASE'     then Result.Kind := tkCase
        else if text = 'OF'       then Result.Kind := tkOf
        else if text = 'CONST'    then Result.Kind := tkConst
        else                           Result.Kind := tkIdent;
        Result.Value := FTok.TokenText;
      end;

    fptkNumber:
      begin
        Result.Kind  := tkIntLit;
        Result.Value := FTok.TokenText;
      end;

    fptkString:
      begin
        Result.Kind  := tkStringLit;
        Result.Value := UnescapeString(FTok.TokenText);
      end;

    fptkSymbol:
      begin
        text := FTok.TokenText;
        if      text = ':=' then Result.Kind := tkAssign
        else if text = '='  then Result.Kind := tkEquals
        else if text = '<>' then Result.Kind := tkNotEquals
        else if text = '<=' then Result.Kind := tkLessEqual
        else if text = '>=' then Result.Kind := tkGreaterEqual
        else if text = '<'  then Result.Kind := tkLessThan
        else if text = '>'  then Result.Kind := tkGreaterThan
        else if text = ':'  then Result.Kind := tkColon
        else if text = '('  then Result.Kind := tkLParen
        else if text = ')'  then Result.Kind := tkRParen
        else if text = '['  then Result.Kind := tkLBracket
        else if text = ']'  then Result.Kind := tkRBracket
        else if text = ','  then Result.Kind := tkComma
        else if text = ';'  then Result.Kind := tkSemicolon
        else if text = '.'  then Result.Kind := tkDot
        else if text = '+'  then Result.Kind := tkPlus
        else if text = '-'  then Result.Kind := tkMinus
        else if text = '*'  then Result.Kind := tkStar
        else if text = '/'  then Result.Kind := tkSlash
        else if text = '^'  then Result.Kind := tkCaret
        else
          raise Exception.Create(Format('Unexpected symbol ''%s'' at line %d col %d', text, raw.Line, raw.Column));
        Result.Value := text;
      end;

  else
    raise Exception.Create(Format('Unexpected token kind %d at line %d col %d', raw.Kind, raw.Line, raw.Column));
  end;
end;




{ === uSymbolTable === }












type
  
  
  

  TTypeKind = (
    tyInteger,    
    tyInt64,      
    tyUInt32,     
    tyByte,       
    tyBoolean,    
    tyString,     
    tyRecord,     
    tyClass,      
    tyInterface,  
    tyVoid,       
    tyNil,        
    tyPointer,    
    tyEnum        
  );

  TTypeDesc = class

    Kind: TTypeKind;
    Name: string;
    function IsNumeric: Boolean;
    function IsString: Boolean;
    function IsOrdinal: Boolean;
    function IsRecord: Boolean;

    function ByteSize: Integer;

    function AllocAlign: Integer;

    procedure Destroy; virtual;
  end;

  

  TPointerTypeDesc = class(TTypeDesc)

    BaseType: TTypeDesc;  
  end;

  


  TEnumTypeDesc = class(TTypeDesc)

    Members: TStringList;
    procedure Create(const AName: string);
    procedure Destroy; override;
    function  OrdinalOf(const AMember: string): Integer;
  end;

  
  TFieldInfo = class

    Name:     string;
    TypeDesc: TTypeDesc;  
    Offset:   Integer;    
    IsWeak:   Boolean;    


  end;

  
  TVTableEntry = class

    Slot:     Integer;  
    MethName: string;   
    ImplName: string;   
  end;

  TPropertyInfo = class

    Name:        string;
    TypeDesc:    TTypeDesc;   
    ReadField:   string;      
    ReadMethod:  string;      
    WriteField:  string;      
    WriteMethod: string;      
  end;

  
  TRecordTypeDesc = class(TTypeDesc)

    FFields:          TObjectList;  
    FKeys:            TStringList;  
    FParent:          TRecordTypeDesc;   
    FVTable:          TObjectList;  
    FImplements:      TObjectList;  
    FProperties:      TObjectList;  
    FHasDestroyMethod: Boolean;     

    procedure Create(const AName: string; AKind: TTypeKind);
    procedure Destroy; override;
    procedure AddField(const AName: string; AType: TTypeDesc);
    function  FindField(const AName: string): TFieldInfo;
    function  TotalSize: Integer;
    function  MaxAlign: Integer;

    
    function  HasVTable: Boolean;
    function  VTableCount: Integer;
    function  VTableEntryAt(ASlot: Integer): TVTableEntry;
    function  FindVTableSlot(const AMethodName: string): Integer;
    function  AddVTableSlot(const AMethodName, AImplName: string): Integer;
    procedure OverrideVTableSlot(ASlot: Integer; const AImplName: string);
    procedure CopyVTableFrom(AParent: TRecordTypeDesc);

    
    procedure AddImplements(AIntf: TInterfaceTypeDesc);
    function  ImplementsCount: Integer;
    function  ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;

    
    procedure AddProperty(AProp: TPropertyInfo);
    function  FindProperty(const AName: string): TPropertyInfo;

    property  Fields: TObjectList read FFields;
    property  Parent: TRecordTypeDesc read FParent write FParent;
    property  HasDestroyMethod: Boolean
              read FHasDestroyMethod write FHasDestroyMethod;
  end;

  
  TInterfaceTypeDesc = class(TTypeDesc)

    FMethods:     TStringList;  
    FReturnTypes: TStringList;  
    FParent:      TInterfaceTypeDesc;  

    procedure Create(const AName: string);
    procedure Destroy; override;
    procedure AddMethod(const AName: string;
                const AReturnTypeName: string);
    function  HasMethod(const AName: string): Boolean;
    function  MethodCount: Integer;
    function  MethodName(AIndex: Integer): string;
    function  MethodReturnTypeName(AIndex: Integer): string;
    function  MethodIndex(const AName: string): Integer;
    property  Parent: TInterfaceTypeDesc read FParent write FParent;
  end;

  
  
  

  TSymbolKind = (
    skVariable,
    skType,
    skProcedure,
    skFunction,
    skParameter,
    skVarParameter,
    skConstant     
  );

  TParamDesc = class

    Name:     string;
    TypeDesc: TTypeDesc;  
    IsConst:  Boolean;
    IsVar:    Boolean;
  end;

  TSymbol = class

    Name:       string;
    Kind:       TSymbolKind;
    TypeDesc:   TTypeDesc;    
    Params:     TObjectList;  
    ConstValue:  Int64;
    ConstString: string;
    IsWeak:      Boolean;


    IsGlobal:   Boolean;

    procedure Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
    procedure Destroy;
  end;

  
  
  

  TScope = class

    FParent:  TScope;
    FSymbols: TObjectList;  
    FKeys:    TStringList;  

    procedure Create(AParent: TScope);
    procedure Destroy;
    property Parent: TScope read FParent;
    
    function Define(ASymbol: TSymbol): Boolean;
    function LookupLocal(const AName: string): TSymbol;
    function Lookup(const AName: string): TSymbol;
  end;

  
  
  

  TSymbolTable = class

    FScopeStack: TObjectList;   
    FAllTypes:   TObjectList;   
    FGenerics:   TStringList;   

    FTypeInteger: TTypeDesc;
    FTypeInt64:   TTypeDesc;
    FTypeUInt32:  TTypeDesc;
    FTypeByte:    TTypeDesc;
    FTypeBoolean: TTypeDesc;
    FTypeString:  TTypeDesc;
    FTypeVoid:    TTypeDesc;
    FTypeNil:     TTypeDesc;
    FTypePointer: TPointerTypeDesc;  

    function GetCurrentScope: TScope;
    function GetScopeDepth: Integer;
    function NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
    procedure RegisterBuiltins;

    procedure Create;
    procedure Destroy;

    
    function  PushScope: TScope;
    procedure PopScope;
    property  CurrentScope: TScope read GetCurrentScope;
    property  ScopeDepth: Integer read GetScopeDepth;

    
    function Define(ASymbol: TSymbol): Boolean;
    
    function DefineGlobal(ASymbol: TSymbol): Boolean;
    function Lookup(const AName: string): TSymbol;

    
    function FindType(const AName: string): TTypeDesc;

    

    function NewRecordType(const AName: string): TRecordTypeDesc;

    
    function NewClassType(const AName: string): TRecordTypeDesc;

    
    function NewInterfaceType(const AName: string): TInterfaceTypeDesc;

    
    function NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
    function NewEnumType(const AName: string): TEnumTypeDesc;

    

    procedure RegisterGeneric(const AName: string; ATempl: TObject);
    function  FindGeneric(const AName: string): TObject;

    
    property TypeInteger: TTypeDesc read FTypeInteger;
    property TypeInt64:   TTypeDesc read FTypeInt64;
    property TypeUInt32:  TTypeDesc read FTypeUInt32;
    property TypeByte:    TTypeDesc read FTypeByte;
    property TypeBoolean: TTypeDesc read FTypeBoolean;
    property TypeString:  TTypeDesc read FTypeString;
    property TypeVoid:    TTypeDesc    read FTypeVoid;
    property TypeNil:     TTypeDesc    read FTypeNil;
    property TypePointer: TPointerTypeDesc read FTypePointer;
  end;






function TTypeDesc.IsNumeric: Boolean;
begin
  Result := ((Kind = tyInteger) or (Kind = tyInt64) or (Kind = tyUInt32) or (Kind = tyByte) or (Kind = tyEnum));
end;

function TTypeDesc.IsString: Boolean;
begin
  Result := Kind = tyString;
end;

function TTypeDesc.IsOrdinal: Boolean;
begin
  Result := ((Kind = tyInteger) or (Kind = tyInt64) or (Kind = tyUInt32) or (Kind = tyByte) or (Kind = tyBoolean) or (Kind = tyEnum));
end;

function TTypeDesc.IsRecord: Boolean;
begin
  Result := Kind = tyRecord;
end;

function TTypeDesc.ByteSize: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64:             Result := 8;
    tyByte, tyBoolean:   Result := 4;  { stored as word, same as AllocAlign }
    tyString:            Result := 8;  
    tyRecord:            Result := TRecordTypeDesc(Self).TotalSize;
    tyNil:               Result := 8;
  else
    Result := 8;
  end;
end;

function TTypeDesc.AllocAlign: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyByte, tyBoolean:   Result := 4;
    tyInt64, tyString:   Result := 8;
    tyRecord:            Result := TRecordTypeDesc(Self).MaxAlign;
  else
    Result := 8;
  end;
end;

procedure TTypeDesc.Destroy;
begin
end;




procedure TRecordTypeDesc.Create(const AName: string; AKind: TTypeKind);
begin

  Kind        := AKind;
  Name        := AName;
  FFields     := TObjectList.Create(True);
  FKeys       := TStringList.Create;
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := 1;
  FVTable     := nil;  
  FImplements := TObjectList.Create(False);  
  FProperties := TObjectList.Create(True);   
end;

procedure TRecordTypeDesc.Destroy;
begin
  FProperties.Free;
  FImplements.Free;
  FKeys.Free;
  FFields.Free;
  FVTable.Free;

end;

procedure TRecordTypeDesc.AddField(const AName: string; AType: TTypeDesc);
var
  Info:   TFieldInfo;
  Offset: Integer;
begin
  Offset := TotalSize;  
  Info          := TFieldInfo.Create;
  Info.Name     := AName;
  Info.TypeDesc := AType;
  Info.Offset   := Offset;
  FFields.Add(Info);
  FKeys.AddObject(AName, Info);
end;

function TRecordTypeDesc.FindField(const AName: string): TFieldInfo;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TFieldInfo(FKeys.GetObject(Idx))
  else
    Result := nil;
end;

function TRecordTypeDesc.TotalSize: Integer;
var
  I: Integer;
begin
  
  if HasVTable then
    Result := 8
  else
    Result := 0;
  for I := 0 to FFields.Count - 1 do
    Result := Result + TFieldInfo(FFields.Get(I)).TypeDesc.ByteSize;
end;

function TRecordTypeDesc.MaxAlign: Integer;
var
  I, A: Integer;
begin
  Result := 4;
  if HasVTable then
    Result := 8;  
  for I := 0 to FFields.Count - 1 do
  begin
    A := TFieldInfo(FFields.Get(I)).TypeDesc.AllocAlign;
    if A > Result then
      Result := A;
  end;
end;

function TRecordTypeDesc.HasVTable: Boolean;
begin
  Result := (FVTable <> nil) and (FVTable.Count > 0);
end;

function TRecordTypeDesc.VTableCount: Integer;
begin
  if FVTable = nil then
    Result := 0
  else
    Result := FVTable.Count;
end;

function TRecordTypeDesc.VTableEntryAt(ASlot: Integer): TVTableEntry;
begin
  if (FVTable = nil) or (ASlot < 0) or (ASlot >= FVTable.Count) then
    Result := nil
  else
    Result := TVTableEntry(FVTable.Get(ASlot));
end;

function TRecordTypeDesc.FindVTableSlot(const AMethodName: string): Integer;
var
  I: Integer;
  E: TVTableEntry;
begin
  Result := -1;
  if FVTable = nil then Exit;
  for I := 0 to FVTable.Count - 1 do
  begin
    E := TVTableEntry(FVTable.Get(I));
    if SameText(E.MethName, AMethodName) then
    begin
      Result := I;
      Exit;
    end;
  end;
end;

function TRecordTypeDesc.AddVTableSlot(const AMethodName, AImplName: string): Integer;
var
  E: TVTableEntry;
begin
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  E            := TVTableEntry.Create;
  E.Slot       := FVTable.Count;
  E.MethName := AMethodName;
  E.ImplName   := AImplName;
  FVTable.Add(E);
  Result := E.Slot;
end;

procedure TRecordTypeDesc.OverrideVTableSlot(ASlot: Integer; const AImplName: string);
var
  E: TVTableEntry;
begin
  if (FVTable <> nil) and (ASlot >= 0) and (ASlot < FVTable.Count) then
  begin
    E := TVTableEntry(FVTable.Get(ASlot));
    E.ImplName := AImplName;
  end;
end;

procedure TRecordTypeDesc.AddImplements(AIntf: TInterfaceTypeDesc);
begin
  FImplements.Add(AIntf);
end;

function TRecordTypeDesc.ImplementsCount: Integer;
begin
  Result := FImplements.Count;
end;

function TRecordTypeDesc.ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc(FImplements.Get(AIndex));
end;

procedure TRecordTypeDesc.CopyVTableFrom(AParent: TRecordTypeDesc);
var
  I: Integer;
  Src, Dst: TVTableEntry;
begin
  if (AParent = nil) or (AParent.VTableCount = 0) then Exit;
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  for I := 0 to AParent.VTableCount - 1 do
  begin
    Src      := AParent.VTableEntryAt(I);
    Dst      := TVTableEntry.Create;
    Dst.Slot       := Src.Slot;
    Dst.MethName := Src.MethName;
    Dst.ImplName   := Src.ImplName;
    FVTable.Add(Dst);
  end;
end;





procedure TRecordTypeDesc.AddProperty(AProp: TPropertyInfo);
begin
  FProperties.Add(AProp);
end;

function TRecordTypeDesc.FindProperty(const AName: string): TPropertyInfo;
var
  I: Integer;
begin
  for I := 0 to FProperties.Count - 1 do
    if SameText(TPropertyInfo(FProperties.Get(I)).Name, AName) then
    begin
      Result := TPropertyInfo(FProperties.Get(I));
      Exit;
    end;
  Result := nil;
end;

procedure TInterfaceTypeDesc.Create(const AName: string);
begin

  Kind         := tyInterface;
  Name         := AName;
  FMethods     := TStringList.Create;
  FMethods.CaseSensitive := False;
  FReturnTypes := TStringList.Create;
  FParent      := nil;
end;

procedure TInterfaceTypeDesc.Destroy;
begin
  FReturnTypes.Free;
  FMethods.Free;

end;

procedure TInterfaceTypeDesc.AddMethod(const AName: string;
  const AReturnTypeName: string);
begin
  FMethods.Add(AName);
  FReturnTypes.Add(AReturnTypeName);
end;

function TInterfaceTypeDesc.HasMethod(const AName: string): Boolean;
begin
  Result := FMethods.IndexOf(AName) >= 0;
end;

function TInterfaceTypeDesc.MethodCount: Integer;
begin
  Result := FMethods.Count;
end;

function TInterfaceTypeDesc.MethodName(AIndex: Integer): string;
begin
  Result := FMethods.Get(AIndex);
end;

function TInterfaceTypeDesc.MethodReturnTypeName(AIndex: Integer): string;
begin
  Result := FReturnTypes.Get(AIndex);
end;

function TInterfaceTypeDesc.MethodIndex(const AName: string): Integer;
begin
  Result := FMethods.IndexOf(AName);
end;





procedure TSymbol.Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
begin

  Name     := AName;
  Kind     := AKind;
  TypeDesc := AType;
  Params   := TObjectList.Create(True);
  IsWeak   := False;
end;

procedure TSymbol.Destroy;
begin
  Params.Free;

end;





procedure TScope.Create(AParent: TScope);
begin

  FParent  := AParent;
  FSymbols := TObjectList.Create(True);
  FKeys    := TStringList.Create;
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := 1;  
end;

procedure TScope.Destroy;
begin
  FKeys.Free;
  FSymbols.Free;

end;

function TScope.Define(ASymbol: TSymbol): Boolean;
var
  Idx: Integer;
begin
  if FKeys.Find(ASymbol.Name, Idx) then
  begin
    Result := False;
    Exit;
  end;
  FSymbols.Add(ASymbol);
  
  FKeys.AddObject(ASymbol.Name, ASymbol);
  Result := True;
end;

function TScope.LookupLocal(const AName: string): TSymbol;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TSymbol(FKeys.GetObject(Idx))
  else
    Result := nil;
end;

function TScope.Lookup(const AName: string): TSymbol;
var
  S: TScope;
begin
  S := Self;
  while S <> nil do
  begin
    Result := S.LookupLocal(AName);
    if Result <> nil then
      Exit;
    S := S.FParent;
  end;
  Result := nil;
end;





procedure TEnumTypeDesc.Create(const AName: string);
begin

  Kind    := tyEnum;
  Name    := AName;
  Members := TStringList.Create;
end;

procedure TEnumTypeDesc.Destroy;
begin
  Members.Free;

end;

function TEnumTypeDesc.OrdinalOf(const AMember: string): Integer;
var
  I: Integer;
begin
  for I := 0 to Members.Count - 1 do
    if SameText(Members.Get(I), AMember) then
    begin
      Result := I;
      Exit;
    end;
  Result := -1;
end;





procedure TSymbolTable.Create;
begin

  FScopeStack := TObjectList.Create(True);
  FAllTypes   := TObjectList.Create(True);
  FGenerics   := TStringList.Create;
  FGenerics.CaseSensitive := True;
  
  FScopeStack.Add(TScope.Create(nil));
  RegisterBuiltins;
end;

procedure TSymbolTable.Destroy;
begin
  FGenerics.Free;
  FScopeStack.Free;
  FAllTypes.Free;

end;

function TSymbolTable.NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
begin
  Result      := TTypeDesc.Create;
  Result.Kind := AKind;
  Result.Name := AName;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewRecordType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyRecord);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewClassType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyClass);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewInterfaceType(const AName: string): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
begin
  Result          := TPointerTypeDesc.Create;
  Result.Kind     := tyPointer;
  Result.Name     := AName;
  Result.BaseType := ABase;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewEnumType(const AName: string): TEnumTypeDesc;
begin
  Result := TEnumTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

procedure TSymbolTable.RegisterGeneric(const AName: string; ATempl: TObject);
begin
  FGenerics.AddObject(AName, ATempl);
end;

function TSymbolTable.FindGeneric(const AName: string): TObject;
var
  Idx: Integer;
begin
  Idx := FGenerics.IndexOf(AName);
  if Idx >= 0 then
    Result := FGenerics.GetObject(Idx)
  else
    Result := nil;
end;

procedure TSymbolTable.RegisterBuiltins;
var
  Sym: TSymbol;
begin
  
  FTypeInteger := NewType(tyInteger, 'Integer');
  FTypeInt64   := NewType(tyInt64,   'Int64');
  FTypeUInt32  := NewType(tyUInt32,  'UInt32');
  FTypeByte    := NewType(tyByte,    'Byte');
  FTypeBoolean := NewType(tyBoolean, 'Boolean');
  FTypeString  := NewType(tyString,  'string');
  FTypeVoid    := NewType(tyVoid,    'void');
  FTypeNil     := NewType(tyNil,     'nil');
  FTypePointer := NewPointerType('Pointer', nil);  

  
  Define(TSymbol.Create('Integer', skType, FTypeInteger));
  Define(TSymbol.Create('Int64',   skType, FTypeInt64));
  Define(TSymbol.Create('UInt32',  skType, FTypeUInt32));
  Define(TSymbol.Create('Byte',    skType, FTypeByte));
  Define(TSymbol.Create('Boolean', skType, FTypeBoolean));
  Define(TSymbol.Create('string',  skType, FTypeString));
  Define(TSymbol.Create('Pointer', skType, FTypePointer));

  
  Define(TSymbol.Create('TObject', skType, NewClassType('TObject')));

  
  Define(TSymbol.Create('IInterface', skType, NewInterfaceType('IInterface')));

  
  Sym := TSymbol.Create('True',  skConstant, FTypeBoolean);
  Sym.ConstValue := 1;
  Define(Sym);
  Sym := TSymbol.Create('False', skConstant, FTypeBoolean);
  Sym.ConstValue := 0;
  Define(Sym);

  
  Sym := TSymbol.Create('Write',   skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('WriteLn', skProcedure, nil);
  Define(Sym);

  
  Sym := TSymbol.Create('GetMem',     skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('ReallocMem', skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('FreeMem',    skProcedure, nil);
  Define(Sym);

  
  Sym := TSymbol.Create('Format',    skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Length',    skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Pos',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Copy',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('UpperCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('LowerCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Trim',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('SameText',  skFunction, FTypeBoolean);
  Define(Sym);
  Sym := TSymbol.Create('IntToStr',  skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('StrToInt',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('CompareStr',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('CompareText', skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('OrdAt',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Chr',         skFunction, FTypeString);
  Define(Sym);
  
  Sym := TSymbol.Create('ZeroMem',      skProcedure, nil); Define(Sym);
  Sym := TSymbol.Create('_ClassAddRef', skProcedure, nil); Define(Sym);
  Sym := TSymbol.Create('_ClassRelease',skProcedure, nil); Define(Sym);
  
  Sym := TSymbol.Create('ParamCount', skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('ParamStr',   skFunction,  FTypeString);  Define(Sym);
  
  Sym := TSymbol.Create('ReadFile',   skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('WriteFile',  skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('AppendFile', skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('FileExists',             skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('DeleteFile',             skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('CurrentExceptionMessage', skFunction,  FTypeString);  Define(Sym);
  
  Sym := TSymbol.Create('GetEnvVar',  skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('Exec',       skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Halt',       skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('ChangeFileExt',                skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFileName',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFilePath',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('IncludeTrailingPathDelimiter', skFunction, FTypeString); Define(Sym);
end;

function TSymbolTable.DefineGlobal(ASymbol: TSymbol): Boolean;
begin
  Result := TScope(FScopeStack.Get(0)).Define(ASymbol);
end;

function TSymbolTable.GetCurrentScope: TScope;
begin
  Result := TScope(FScopeStack.Get(FScopeStack.Count - 1));
end;

function TSymbolTable.GetScopeDepth: Integer;
begin
  Result := FScopeStack.Count;
end;

function TSymbolTable.PushScope: TScope;
begin
  Result := TScope.Create(CurrentScope);
  FScopeStack.Add(Result);
end;

procedure TSymbolTable.PopScope;
begin
  if FScopeStack.Count > 1 then
    FScopeStack.Delete(FScopeStack.Count - 1);
end;

function TSymbolTable.Define(ASymbol: TSymbol): Boolean;
begin
  Result := CurrentScope.Define(ASymbol);
end;

function TSymbolTable.Lookup(const AName: string): TSymbol;
begin
  Result := CurrentScope.Lookup(AName);
end;

function TSymbolTable.FindType(const AName: string): TTypeDesc;
var
  Sym: TSymbol;
begin
  Sym := CurrentScope.Lookup(AName);
  if (Sym <> nil) and (Sym.Kind = skType) then
    Result := Sym.TypeDesc
  else
    Result := nil;
end;




{ === uAST === }












type
  
  TASTNode = class

    Line: Integer;
    Col:  Integer;
    procedure Destroy; virtual;
  end;

  
  
  

  
  TASTExpr = class(TASTNode)

    ResolvedType: TTypeDesc;  
  end;

  TIntLiteral = class(TASTExpr)

    Value: Int64;
  end;

  TStringLiteral = class(TASTExpr)

    Value: string;
  end;

  TNilLiteral = class(TASTExpr);  

  TIdentExpr = class(TASTExpr)

    Name:              string;
    IsVarParam:        Boolean;
    IsConstant:        Boolean;
    ConstValue:        Int64;
    ConstString:       string;
    IsNoArgFuncCall:   Boolean;
    NoArgFuncDecl:     TObject;
    IsGlobal:          Boolean;
    IsImplicitSelf:    Boolean;
    ImplicitFieldInfo: TObject;
    IsImplicitSelfMethod: Boolean;
    ImplicitMethodDecl:   TObject;
  end;

  TFieldAccessExpr = class(TASTExpr)

    RecordName:        string;         
    FieldName:         string;
    Base:              TASTExpr;       
    FieldInfo:         TFieldInfo;    
    IsConstructorCall: Boolean;       
    IsClassAccess:     Boolean;       
    PropRead:          TPropertyInfo; 
    PropOwnerType:     string;        
    IsImplicitSelf:    Boolean;       
    ImplicitBaseInfo:  TFieldInfo;    
    IsMethodCall:      Boolean;       
    ResolvedMethod:    TObject;       
    IsGlobal:          Boolean;       
    procedure Destroy; override;
  end;

  TIsExpr = class(TASTExpr)

    Obj:                TASTExpr;   
    TypeName:           string;     
    ResolvedTargetType: TTypeDesc;  
    procedure Destroy; override;
  end;

  TAsExpr = class(TASTExpr)

    Obj:      TASTExpr;  
    TypeName: string;    
    procedure Destroy; override;
  end;

  TBinaryOp = (boAdd, boSub, boMul, boDiv, boEQ, boNE, boLT, boGT, boLE, boGE,
               boAnd, boOr);

  TBinaryExpr = class(TASTExpr)

    Op:    TBinaryOp;
    Left:  TASTExpr;  
    Right: TASTExpr;  
    procedure Destroy; override;
  end;

  TNotExpr = class(TASTExpr)

    Expr: TASTExpr;  
    procedure Destroy; override;
  end;

  
  
  

  TASTStmt = class(TASTNode);

  TAssignment = class(TASTStmt)

    Name:            string;
    Expr:            TASTExpr;   
    IsVarParam:      Boolean;    
    IsGlobal:        Boolean;    
    ResolvedLhsType: TTypeDesc;  
    IsWeakLhs:       Boolean;    



    ImplicitSelfField: TObject;  
    procedure Destroy; override;
  end;

  TIfStmt = class(TASTStmt)

    Condition: TASTExpr;   
    ThenStmt:  TASTStmt;   
    ElseStmt:  TASTStmt;   
    procedure Destroy; override;
  end;

  TCompoundStmt = class(TASTStmt)

    Stmts: TObjectList;  
    procedure Create;
    procedure Destroy; override;
  end;

  TWhileStmt = class(TASTStmt)

    Condition: TASTExpr;  
    Body:      TASTStmt;  
    procedure Destroy; override;
  end;

  TForStmt = class(TASTStmt)

    VarName:   string;
    StartExpr: TASTExpr;  
    EndExpr:   TASTExpr;  
    IsDownTo:  Boolean;
    Body:      TASTStmt;  
    procedure Destroy; override;
  end;

  TTryFinallyStmt = class(TASTStmt)

    TryBody:     TCompoundStmt;  
    FinallyBody: TCompoundStmt;  
    procedure Destroy; override;
  end;

  TTryExceptStmt = class(TASTStmt)

    TryBody:    TCompoundStmt;  
    ExceptBody: TCompoundStmt;  
    procedure Destroy; override;
  end;

  TRaiseStmt = class(TASTStmt)

    Expr: TASTExpr;  
    procedure Destroy; override;
  end;

  
  TExitStmt = class(TASTStmt);

  
  TBreakStmt = class(TASTStmt);

  
  TContinueStmt = class(TASTStmt);

  
  TCaseBranch = class

    Values: TObjectList;
    Stmt:   TASTStmt;
    procedure Create;
    procedure Destroy;
  end;

  TCaseStmt = class(TASTStmt)

    Selector: TASTExpr;    
    Branches: TObjectList; 
    ElseStmt: TASTStmt;    
    procedure Create;
    procedure Destroy; override;
  end;

  TFieldAssignment = class(TASTStmt)

    RecordName:    string;
    FieldName:     string;
    Expr:          TASTExpr;   
    ObjExpr:       TASTExpr;   
    FieldInfo:     TFieldInfo; 
    IsClassAccess: Boolean;    
    IsImplicitSelf:    Boolean; 
    ImplicitBaseInfo:  TFieldInfo; 
    IsGlobal:          Boolean; 
    procedure Destroy; override;
  end;

  
  TPointerWriteStmt = class(TASTStmt)

    PtrExpr:  TASTExpr;  
    ValExpr:  TASTExpr;  
    BaseTy:   TTypeDesc; 
    procedure Destroy; override;
  end;

  TProcCall = class(TASTStmt)

    Name:         string;
    Args:         TObjectList;  
    ResolvedDecl: TObject;      
    IsImplicitSelfMethod: Boolean; 
    procedure Create;
    procedure Destroy; override;
  end;

  TFuncCallExpr = class(TASTExpr)

    Name:         string;
    Args:         TObjectList;  
    ResolvedDecl: TObject;      
    IsImplicitSelfMethod: Boolean; 
    procedure Create;
    procedure Destroy; override;
  end;

  
  TDerefExpr = class(TASTExpr)

    Expr: TASTExpr;  
    procedure Destroy; override;
  end;

  TMethodCallStmt = class(TASTStmt)

    ObjectName: string;
    Name:       string;   
    Args:       TObjectList;   
    ObjExpr:    TASTExpr;  
    
    ResolvedClassType: TTypeDesc;   
    ResolvedMethod:    TObject;     
    IsImplicitSelf:    Boolean;     
    ImplicitBaseInfo:  TFieldInfo;  
    IsGlobal:          Boolean;     
    procedure Create;
    procedure Destroy; override;
  end;

  


  TInheritedCallStmt = class(TASTStmt)

    Name:               string;        
    Args:               TObjectList;   
    
    ResolvedParentType: TObject;       
    ResolvedMethod:     TObject;       
    procedure Create;
    procedure Destroy; override;
  end;

  
  
  

  TVarDecl = class(TASTNode)

    Names:        TStringList;  
    TypeName:     string;
    ResolvedType: TTypeDesc;    
    Attributes:   TStringList;  




    IsWeak:       Boolean;      


    IsGlobal:     Boolean;      
    procedure Create;
    procedure Destroy; override;
  end;

  
  
  

  
  TASTTypeDef = class(TASTNode);

  
  TEnumTypeDef = class(TASTTypeDef)

    Members: TStringList;  
    procedure Create;
    procedure Destroy; override;
  end;

  TFieldDecl = class(TASTNode)

    Names:        TStringList;  
    TypeName:     string;
    ResolvedType: TTypeDesc;    
    Attributes:   TStringList;  
    IsWeak:       Boolean;      
    procedure Create;
    procedure Destroy; override;
  end;

  TRecordTypeDef = class(TASTTypeDef)

    Fields: TObjectList;  
    procedure Create;
    procedure Destroy; override;
  end;

  TMethodParam = class(TASTNode)

    ParamName:    string;
    TypeName:     string;
    IsVarParam:   Boolean;    
    ResolvedType: TTypeDesc;  
  end;

  TMethodDecl = class(TASTNode)

    Name:               string;      
    OwnerTypeName:      string;      
    Params:             TObjectList; 
    ReturnTypeName:     string;      
    ResolvedReturnType: TTypeDesc;   
    Body:               TBlock;      
    OwnBody:            Boolean;     
    IsVirtual:          Boolean;     
    IsOverride:         Boolean;     
    VTableSlot:         Integer;     
    TypeParams:         TStringList; 
    TypeParamConstraints: TStringList; 

    OwnerTypeParams:    TStringList; 
    procedure Create;
    procedure Destroy; override;
  end;

  TMethodCallExpr = class(TASTExpr)

    ObjectName:        string;
    Name:              string;     
    Args:              TObjectList; 
    ObjExpr:           TASTExpr;   
    ResolvedClassType: TTypeDesc;   
    ResolvedMethod:    TObject;     
    IsConstructorCall: Boolean;    
    IsGlobal:          Boolean;    
    procedure Create;
    procedure Destroy; override;
  end;

  
  TPropertyDecl = class(TASTNode)

    Name:      string;  
    TypeName:  string;  
    ReadName:  string;  
    WriteName: string;  
  end;

  TClassTypeDef = class(TASTTypeDef)

    ParentName:      string;
    ImplementsNames: TStringList;  
    Fields:          TObjectList;  
    Methods:         TObjectList;  
    Properties:      TObjectList;  
    procedure Create;
    procedure Destroy; override;
  end;

  
  TGenericTypeDef = class(TASTTypeDef)

    ParamNames:       TStringList;   
    ParamConstraints: TStringList;   
    ClassDef:         TClassTypeDef; 
    procedure Create;
    procedure Destroy; override;
  end;

  

  TGenericFuncInstance = class

    InstName:   string;       
    MethodDecl: TMethodDecl;  
    procedure Create;
    procedure Destroy;
  end;

  

  TGenericInstance = class

    TypeName: string;
    ClassDef: TClassTypeDef;
    TypeDesc: TTypeDesc;
    procedure Create;
    procedure Destroy;
  end;

  TInterfaceTypeDef = class(TASTTypeDef)

    ParentName: string;
    Methods:    TObjectList;  
    procedure Create;
    procedure Destroy; override;
  end;

  
  TGenericInterfaceDef = class(TASTTypeDef)

    ParamNames:       TStringList;      
    ParamConstraints: TStringList;      
    IntfDef:          TInterfaceTypeDef; 
    procedure Create;
    procedure Destroy; override;
  end;

  

  TGenericInterfaceInstance = class

    InstName: string;
    IntfDef:  TInterfaceTypeDef;
    TypeDesc: TTypeDesc;
    procedure Create;
    procedure Destroy;
  end;

  TTypeDecl = class(TASTNode)

    Name: string;
    Def:  TASTTypeDef;  
    procedure Destroy; override;
  end;

  
  TConstDecl = class(TASTNode)

    Name:    string;
    IntVal:  Int64;    
    StrVal:  string;   
    IsString: Boolean;
  end;

  
  
  

  TBlock = class(TASTNode)

    TypeDecls:  TObjectList;  
    ConstDecls: TObjectList;  
    Decls:      TObjectList;  
    ProcDecls:  TObjectList;  
    Stmts:      TObjectList;  
    procedure Create;
    procedure Destroy; override;
  end;

  TProgram = class(TASTNode)

    Name:                 string;
    UsedUnits:            TStringList;    
    Block:                TBlock;         
    SymbolTable:          TSymbolTable;   
    GenericInstances:     TObjectList;    
    GenericFuncInstances: TObjectList;    
    GenericIntfInstances: TObjectList;    
    procedure Create;
    procedure Destroy; override;
  end;

  TUnit = class(TASTNode)

    Name:      string;
    IntfBlock: TBlock;  
    ImplBlock: TBlock;  
    procedure Create;
    procedure Destroy; override;
  end;

function BinaryOpName(AOp: TBinaryOp): string;
function IsComparisonOp(AOp: TBinaryOp): Boolean;


function BinaryOpName(AOp: TBinaryOp): string;
begin
  case AOp of
    boAdd: Result := '+';
    boSub: Result := '-';
    boMul: Result := '*';
    boDiv: Result := 'div';
    boEQ:  Result := '=';
    boNE:  Result := '<>';
    boLT:  Result := '<';
    boGT:  Result := '>';
    boLE:  Result := '<=';
    boGE:  Result := '>=';
    boAnd: Result := 'and';
    boOr:  Result := 'or';
  else
    Result := '?';
  end;
end;

function IsComparisonOp(AOp: TBinaryOp): Boolean;
begin
  Result := ((AOp = boEQ) or (AOp = boNE) or (AOp = boLT) or (AOp = boGT) or (AOp = boLE) or (AOp = boGE));
end;



procedure TASTNode.Destroy;
begin

end;

procedure TIfStmt.Destroy;
begin
  Condition.Free;
  ThenStmt.Free;
  ElseStmt.Free;

end;



procedure TCompoundStmt.Create;
begin

  Stmts := TObjectList.Create(True);
end;

procedure TCompoundStmt.Destroy;
begin
  Stmts.Free;

end;



procedure TWhileStmt.Destroy;
begin
  Condition.Free;
  Body.Free;

end;



procedure TForStmt.Destroy;
begin
  StartExpr.Free;
  EndExpr.Free;
  Body.Free;

end;



procedure TTryFinallyStmt.Destroy;
begin
  TryBody.Free;
  FinallyBody.Free;

end;



procedure TTryExceptStmt.Destroy;
begin
  TryBody.Free;
  ExceptBody.Free;

end;



procedure TRaiseStmt.Destroy;
begin
  Expr.Free;

end;



procedure TFieldAccessExpr.Destroy;
begin
  Base.Free;

end;



procedure TIsExpr.Destroy;
begin
  Obj.Free;

end;



procedure TAsExpr.Destroy;
begin
  Obj.Free;

end;



procedure TBinaryExpr.Destroy;
begin
  Left.Free;
  Right.Free;

end;



procedure TNotExpr.Destroy;
begin
  Expr.Free;

end;



procedure TAssignment.Destroy;
begin
  Expr.Free;

end;



procedure TFieldAssignment.Destroy;
begin
  Expr.Free;
  ObjExpr.Free;

end;



procedure TPointerWriteStmt.Destroy;
begin
  PtrExpr.Free;
  ValExpr.Free;

end;



procedure TDerefExpr.Destroy;
begin
  Expr.Free;

end;



procedure TProcCall.Create;
begin

  Args := TObjectList.Create(True);
end;

procedure TProcCall.Destroy;
begin
  Args.Free;

end;



procedure TFuncCallExpr.Create;
begin

  Args := TObjectList.Create(True);
end;

procedure TFuncCallExpr.Destroy;
begin
  Args.Free;

end;



procedure TMethodCallStmt.Create;
begin

  Args := TObjectList.Create(True);
end;

procedure TMethodCallStmt.Destroy;
begin
  Args.Free;
  ObjExpr.Free;

end;



procedure TInheritedCallStmt.Create;
begin

  Args := TObjectList.Create(True);
end;

procedure TInheritedCallStmt.Destroy;
begin
  Args.Free;

end;



procedure TVarDecl.Create;
begin

  Names      := TStringList.Create;
  Attributes := TStringList.Create;
  IsWeak     := False;
end;

procedure TVarDecl.Destroy;
begin
  Attributes.Free;
  Names.Free;

end;



procedure TFieldDecl.Create;
begin

  Names      := TStringList.Create;
  Attributes := TStringList.Create;
  IsWeak     := False;
end;

procedure TFieldDecl.Destroy;
begin
  Attributes.Free;
  Names.Free;

end;



procedure TRecordTypeDef.Create;
begin

  Fields := TObjectList.Create(True);
end;

procedure TRecordTypeDef.Destroy;
begin
  Fields.Free;

end;



procedure TMethodDecl.Create;
begin

  Params     := TObjectList.Create(True);
  VTableSlot := -1;
  OwnBody    := True;
end;

procedure TMethodDecl.Destroy;
begin
  Params.Free;
  TypeParams.Free;
  TypeParamConstraints.Free;
  OwnerTypeParams.Free;
  if OwnBody then Body.Free;

end;



procedure TMethodCallExpr.Create;
begin

  Args := TObjectList.Create(True);
end;

procedure TMethodCallExpr.Destroy;
begin
  Args.Free;
  ObjExpr.Free;

end;



procedure TClassTypeDef.Create;
begin

  ImplementsNames := TStringList.Create;
  Fields          := TObjectList.Create(True);
  Methods         := TObjectList.Create(True);
  Properties      := TObjectList.Create(True);
end;

procedure TClassTypeDef.Destroy;
begin
  Properties.Free;
  Methods.Free;
  Fields.Free;
  ImplementsNames.Free;

end;



procedure TInterfaceTypeDef.Create;
begin

  Methods := TObjectList.Create(True);
end;

procedure TInterfaceTypeDef.Destroy;
begin
  Methods.Free;

end;



procedure TGenericTypeDef.Create;
begin

  ParamNames       := TStringList.Create;
  ParamConstraints := TStringList.Create;
  ClassDef         := TClassTypeDef.Create;
end;

procedure TGenericTypeDef.Destroy;
begin
  ClassDef.Free;
  ParamConstraints.Free;
  ParamNames.Free;

end;





procedure TGenericFuncInstance.Create;
begin

end;

procedure TGenericFuncInstance.Destroy;
begin
  MethodDecl.Free;

end;



procedure TGenericInterfaceDef.Create;
begin

  ParamNames       := TStringList.Create;
  ParamConstraints := TStringList.Create;
  IntfDef          := TInterfaceTypeDef.Create;
end;

procedure TGenericInterfaceDef.Destroy;
begin
  IntfDef.Free;
  ParamConstraints.Free;
  ParamNames.Free;

end;



procedure TGenericInterfaceInstance.Create;
begin

  IntfDef := TInterfaceTypeDef.Create;
end;

procedure TGenericInterfaceInstance.Destroy;
begin
  IntfDef.Free;

end;



procedure TGenericInstance.Create;
begin

  ClassDef := TClassTypeDef.Create;
end;

procedure TGenericInstance.Destroy;
begin
  ClassDef.Free;

end;



procedure TTypeDecl.Destroy;
begin
  Def.Free;

end;



procedure TBlock.Create;
begin

  TypeDecls  := TObjectList.Create(True);
  ConstDecls := TObjectList.Create(True);
  Decls      := TObjectList.Create(True);
  ProcDecls  := TObjectList.Create(True);
  Stmts      := TObjectList.Create(True);
end;

procedure TBlock.Destroy;
begin
  TypeDecls.Free;
  ConstDecls.Free;
  Decls.Free;
  ProcDecls.Free;
  Stmts.Free;

end;



procedure TEnumTypeDef.Create;
begin

  Members := TStringList.Create;
end;

procedure TEnumTypeDef.Destroy;
begin
  Members.Free;

end;



procedure TCaseBranch.Create;
begin

  Values := TObjectList.Create(True);
end;

procedure TCaseBranch.Destroy;
begin
  Stmt.Free;
  Values.Free;

end;



procedure TCaseStmt.Create;
begin

  Branches := TObjectList.Create(True);
end;

procedure TCaseStmt.Destroy;
begin
  ElseStmt.Free;
  Branches.Free;
  Selector.Free;

end;



procedure TProgram.Create;
begin

  UsedUnits            := TStringList.Create;
  GenericInstances     := TObjectList.Create(True);
  GenericFuncInstances := TObjectList.Create(True);
  GenericIntfInstances := TObjectList.Create(True);
end;

procedure TProgram.Destroy;
begin
  GenericIntfInstances.Free;
  GenericFuncInstances.Free;
  GenericInstances.Free;
  SymbolTable.Free;
  UsedUnits.Free;
  Block.Free;

end;



procedure TUnit.Create;
begin

  IntfBlock := TBlock.Create;
  ImplBlock := TBlock.Create;
end;

procedure TUnit.Destroy;
begin
  IntfBlock.Free;
  ImplBlock.Free;

end;




{ === uParser === }








































type

  TParser = class

    FLexer:      TLexer;
    FCurrent:    TToken;
    FLookahead:  TToken;  
    FLookahead2: TToken;  

    procedure Advance;
    function  PeekKind: TTokenKind;
    function  PeekKind2: TTokenKind;  
    procedure Expect(AKind: TTokenKind);
    function  Check(AKind: TTokenKind): Boolean;
    function  ParseTypeName: string;  

    function  ParseProgram: TProgram;
    procedure ParseUses(AProg: TProgram);
    function  ParseBlock: TBlock;
    procedure ParseTypeSection(ABlock: TBlock);
    procedure ParseTypeDecl(ABlock: TBlock);
    procedure ParseConstBlock(ABlock: TBlock);
    function  ParseEnumDef: TEnumTypeDef;
    function  ParseRecordDef: TRecordTypeDef;
    function  ParseGenericName: string;  
    function  ParseClassDef: TClassTypeDef;
    function  ParseInterfaceDef: TInterfaceTypeDef;
    procedure ParseFieldDecl(AFields: TObjectList);
    procedure ParseAttributeList(AAttrs: TStringList);
    function  ParsePropertyDecl: TPropertyDecl;
    function  ParseMethodDecl(IsFunction: Boolean): TMethodDecl;
    procedure ParseParamList(AParams: TObjectList);
    procedure ParseStandaloneDecl(ABlock: TBlock);
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseIfStmt: TIfStmt;
    function  ParseWhileStmt: TWhileStmt;
    function  ParseForStmt: TForStmt;
    function  ParseTryStmt: TASTStmt;
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

    procedure Create(ALexer: TLexer);
    function Parse: TProgram;
    function ParseUnit: TUnit;
  end;


procedure TParser.Create(ALexer: TLexer);
begin

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




function TParser.ParseTypeName: string;
begin
  
  if Check(tkCaret) then
  begin
    Advance;  
    Result := '^' + Self.ParseTypeName;  
    Exit;
  end;
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected type name at line %d col %d', FCurrent.Line, FCurrent.Col));
  Result := FCurrent.Value;
  Advance;
  if Check(tkLessThan) then
  begin
    Advance;  
    Result := Result + '<';
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected type argument after ''<'' at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result := Result + FCurrent.Value;
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected type argument after '','' at line %d col %d', FCurrent.Line, FCurrent.Col));
      Result := Result + ',' + FCurrent.Value;
      Advance;
    end;
    Expect(tkGreaterThan);
    Result := Result + '>';
  end;
end;

procedure TParser.Expect(AKind: TTokenKind);
begin
  if FCurrent.Kind <> AKind then
    raise EParseError.Create(Format('Expected token %d but got %d (''%s'') at line %d col %d', AKind, FCurrent.Kind, FCurrent.Value,
       FCurrent.Line, FCurrent.Col));
  Advance;
end;

function TParser.Check(AKind: TTokenKind): Boolean;
begin
  Result := FCurrent.Kind = AKind;
end;



function TParser.Parse: TProgram;
begin
  Result := ParseProgram;
end;

function TParser.ParseProgram: TProgram;
begin
  Result := TProgram.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkProgram);

    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected program name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Name := FCurrent.Value;
    Advance;

    Expect(tkSemicolon);

    if Check(tkUses) then
      ParseUses(Result);

    Result.Block := ParseBlock;

    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format('Unexpected tokens after program end at line %d col %d', FCurrent.Line, FCurrent.Col));
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseUses(AProg: TProgram);
var
  UName: string;
begin
  Expect(tkUses);
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected unit name after ''uses'' at line %d col %d', FCurrent.Line, FCurrent.Col));
  UName := FCurrent.Value;
  Advance;
  while Check(tkDot) do
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d', FCurrent.Line, FCurrent.Col));
    UName := UName + '.' + FCurrent.Value;
    Advance;
  end;
  AProg.UsedUnits.Add(UName);
  while Check(tkComma) do
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected unit name after '','' at line %d col %d', FCurrent.Line, FCurrent.Col));
    UName := FCurrent.Value;
    Advance;
    while Check(tkDot) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d', FCurrent.Line, FCurrent.Col));
      UName := UName + '.' + FCurrent.Value;
      Advance;
    end;
    AProg.UsedUnits.Add(UName);
  end;
  Expect(tkSemicolon);
end;

function TParser.ParseBlock: TBlock;
begin
  Result := TBlock.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    

    while Check(tkType) or Check(tkVar) or Check(tkProcedure) or
          Check(tkFunction) or Check(tkConst) do
    begin
      if Check(tkType) then
        ParseTypeSection(Result)
      else if Check(tkVar) then
        ParseVarBlock(Result)
      else if Check(tkConst) then
        ParseConstBlock(Result)
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





procedure TParser.ParseTypeSection(ABlock: TBlock);
begin
  Expect(tkType);
  
  while Check(tkIdent) do
    ParseTypeDecl(ABlock);
end;

procedure TParser.ParseTypeDecl(ABlock: TBlock);
var
  TD:               TTypeDecl;
  GD:               TGenericTypeDef;
  GID:              TGenericInterfaceDef;
  ParamNames:       TStringList;
  ParamConstraints: TStringList;
  IsGeneric:        Boolean;
  Constraint:       string;
begin
  TD := TTypeDecl.Create;
  TD.Line := FCurrent.Line;
  TD.Col  := FCurrent.Col;
  try
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected type name at line %d col %d', FCurrent.Line, FCurrent.Col));
    TD.Name := FCurrent.Value;
    Advance;
    
    IsGeneric := Check(tkLessThan);
    if IsGeneric then
    begin
      Advance;  
      ParamNames       := TStringList.Create;
      ParamConstraints := TStringList.Create;
      try
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
            raise EParseError.Create(Format('Expected ''class'', ''record'', or a type name after '':'' at line %d col %d', FCurrent.Line, FCurrent.Col));
        end;
        ParamConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected type parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
              raise EParseError.Create(Format('Expected ''class'', ''record'', or a type name after '':'' at line %d col %d', FCurrent.Line, FCurrent.Col));
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
          GID.IntfDef.Free;
          GID.IntfDef := ParseInterfaceDef;
          TD.Def := GID;
        end
        else
        begin
          if not Check(tkClass) then
            raise EParseError.Create(Format('Generic type must be a class or interface at line %d col %d', FCurrent.Line, FCurrent.Col));
          GD            := TGenericTypeDef.Create;
          GD.Line       := TD.Line;
          GD.Col        := TD.Col;
          GD.ParamNames.AddStrings(ParamNames);
          GD.ParamConstraints.AddStrings(ParamConstraints);
          GD.ClassDef.Free;
          GD.ClassDef := ParseClassDef;
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
      if Check(tkRecord) then
        TD.Def := ParseRecordDef
      else if Check(tkClass) then
        TD.Def := ParseClassDef
      else if Check(tkIntf) then
        TD.Def := ParseInterfaceDef
      else if Check(tkLParen) then
        TD.Def := ParseEnumDef
      else
        raise EParseError.Create(Format('Expected ''record'', ''class'', ''interface'', or ''('' at line %d col %d', FCurrent.Line, FCurrent.Col));
    end;
    Expect(tkSemicolon);
    ABlock.TypeDecls.Add(TD);
  except
    TD.Free;
    raise;
  end;
end;

procedure TParser.ParseConstBlock(ABlock: TBlock);
var
  CD: TConstDecl;
begin
  Expect(tkConst);
  while Check(tkIdent) do
  begin
    CD      := TConstDecl.Create;
    CD.Line := FCurrent.Line;
    CD.Col  := FCurrent.Col;
    CD.Name := FCurrent.Value;
    Advance;
    Expect(tkEquals);
    if Check(tkMinus) then
    begin
      Advance;
      if not Check(tkIntLit) then
        raise EParseError.Create(Format('Expected integer after minus in const at line %d col %d', FCurrent.Line, FCurrent.Col));
      CD.IntVal  := -StrToInt(FCurrent.Value);
      CD.IsString := False;
      Advance;
    end
    else if Check(tkIntLit) then
    begin
      CD.IntVal   := StrToInt(FCurrent.Value);
      CD.IsString := False;
      Advance;
    end
    else if Check(tkStringLit) then
    begin
      CD.StrVal   := FCurrent.Value;
      CD.IsString := True;
      Advance;
    end
    else
      raise EParseError.Create(Format('Expected integer or string constant at line %d col %d', FCurrent.Line, FCurrent.Col));
    Expect(tkSemicolon);
    ABlock.ConstDecls.Add(CD);
  end;
end;

function TParser.ParseEnumDef: TEnumTypeDef;
begin
  Result := TEnumTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkLParen);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected enum member at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Members.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected enum member at line %d col %d', FCurrent.Line, FCurrent.Col));
      Result.Members.Add(FCurrent.Value);
      Advance;
    end;
    Expect(tkRParen);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseRecordDef: TRecordTypeDef;
begin
  Result := TRecordTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRecord);
    while Check(tkIdent) or Check(tkLBracket) do
      ParseFieldDecl(Result.Fields);
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
    raise EParseError.Create(Format('Expected identifier at line %d col %d', FCurrent.Line, FCurrent.Col));
  Result := FCurrent.Value;
  Advance;
  if Check(tkLessThan) then
  begin
    Advance;  
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
begin
  Result := TClassTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkClass);
    if Check(tkLParen) then
    begin
      Advance;
      
      Result.ParentName := ParseGenericName;
      
      while Check(tkComma) do
      begin
        Advance;
        Result.ImplementsNames.Add(ParseGenericName);
      end;
      Expect(tkRParen);
    end;
    


    while True do
begin
      if Check(tkIdent) and SameText(FCurrent.Value, 'property') then
        Result.Properties.Add(ParsePropertyDecl)
      else if Check(tkIdent) or Check(tkLBracket) then
        ParseFieldDecl(Result.Fields)
      else if Check(tkFunction) then
        Result.Methods.Add(ParseMethodDecl(True))
      else if Check(tkProcedure) then
        Result.Methods.Add(ParseMethodDecl(False))
      else
        Break;
      if False then break;
end;    if Check(tkEnd) then
      Advance
    else if not (Check(tkSemicolon) or Check(tkEOF)) then
      raise EParseError.Create(Format('Expected ''end'' in class definition at line %d col %d', FCurrent.Line, FCurrent.Col));
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
        raise EParseError.Create(Format('Expected parent interface name at line %d col %d', FCurrent.Line, FCurrent.Col));
      Result.ParentName := FCurrent.Value;
      Advance;
      Expect(tkRParen);
    end;
    while Check(tkProcedure) or Check(tkFunction) do
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

function TParser.ParseMethodDecl(IsFunction: Boolean): TMethodDecl;
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
    else
      Expect(tkProcedure);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected method name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Name := FCurrent.Value;
    Advance;
    


    if Check(tkLessThan) and (PeekKind = tkIdent) and
       (((PeekKind2 = tkGreaterThan) or (PeekKind2 = tkComma) or (PeekKind2 = tkColon))) then
    begin
      TempParams      := TStringList.Create;
      TempConstraints := TStringList.Create;
      try
        Advance;  
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
            raise EParseError.Create(Format('Expected ''class'', ''record'', or a type name after '':'' at line %d col %d', FCurrent.Line, FCurrent.Col));
        end;
        TempConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected type parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
              raise EParseError.Create(Format('Expected ''class'', ''record'', or a type name after '':'' at line %d col %d', FCurrent.Line, FCurrent.Col));
          end;
          TempConstraints.Add(Constraint);
        end;
        Expect(tkGreaterThan);
        if Check(tkDot) then
        begin
          

          Result.OwnerTypeParams := TempParams;
          TempParams := nil;
          TempConstraints := nil;
        end
        else
        begin
          
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
    
    if Check(tkDot) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected method name after ''.'' at line %d col %d', FCurrent.Line, FCurrent.Col));
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
    if Check(tkVirtual) then
    begin
      Result.IsVirtual := True;
      Advance;
      Expect(tkSemicolon);
    end
    else if Check(tkOverride) then
    begin
      Result.IsOverride := True;
      Advance;
      Expect(tkSemicolon);
    end;
    

    if Check(tkBegin) or Check(tkVar) or Check(tkType) then
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
  Par:      TMethodParam;
  I:        Integer;
  Names:    TStringList;
  TypeN:    string;
  IsVarGrp: Boolean;
begin
  while True do
begin
    IsVarGrp := Check(tkVar);
    if IsVarGrp then Advance
    else if Check(tkConst) then Advance;  
    Names := TStringList.Create;
    try
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
      Names.Add(FCurrent.Value);
      Advance;
      while Check(tkComma) do
      begin
        Advance;
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected parameter name at line %d col %d', FCurrent.Line, FCurrent.Col));
        Names.Add(FCurrent.Value);
        Advance;
      end;
      Expect(tkColon);
      TypeN := ParseTypeName;
      for I := 0 to Names.Count - 1 do
      begin
        Par            := TMethodParam.Create;
        Par.ParamName  := Names.Get(I);
        Par.TypeName   := TypeN;
        Par.IsVarParam := IsVarGrp;
        AParams.Add(Par);
      end;
    finally
      Names.Free;
    end;
    if Check(tkSemicolon) then
      Advance
    else
      Break;
    if False then break;
end;end;

procedure TParser.ParseStandaloneDecl(ABlock: TBlock);
var
  IsFunc: Boolean;
  MD:     TMethodDecl;
begin
  IsFunc := Check(tkFunction);
  MD     := ParseMethodDecl(IsFunc);
  ABlock.ProcDecls.Add(MD);
end;

function TParser.ParsePropertyDecl: TPropertyDecl;
begin
  Result := TPropertyDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance;  
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected property name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Name := FCurrent.Value;
    Advance;
    Expect(tkColon);
    Result.TypeName := ParseTypeName;
    
    if Check(tkIdent) and SameText(FCurrent.Value, 'read') then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected read accessor name at line %d col %d', FCurrent.Line, FCurrent.Col));
      Result.ReadName := FCurrent.Value;
      Advance;
    end;
    
    if Check(tkIdent) and SameText(FCurrent.Value, 'write') then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected write accessor name at line %d col %d', FCurrent.Line, FCurrent.Col));
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






var
  Depth: Integer;
begin
  while Check(tkLBracket) do
  begin
    Advance;  
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected attribute name after ''['' at line %d col %d', FCurrent.Line, FCurrent.Col));
    AAttrs.Add(FCurrent.Value);
    Advance;  
    



    if Check(tkLParen) then
    begin
      Depth := 1;
      Advance;
      while (Depth > 0) and (FCurrent.Kind <> tkEOF) do
      begin
        if      Check(tkLParen) then Depth := Depth + 1
        else if Check(tkRParen) then Depth := Depth - 1;
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
      raise EParseError.Create(Format('Expected field name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Fld.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected field name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
      raise EParseError.Create(Format('Expected variable name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Decl.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected variable name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
  SecondIdent: string;
  FldNode:     TFieldAccessExpr;
  CastRcv:     TASTExpr;
  FCallNode:   TFuncCallExpr;
begin
  Result := nil;

  if Check(tkEnd) or Check(tkEOF) or Check(tkSemicolon) or Check(tkElse) then
    Exit;

  if Check(tkIf) then
  begin
    Result := ParseIfStmt;
    Exit;
  end;

  if Check(tkWhile) then
  begin
    Result := ParseWhileStmt;
    Exit;
  end;

  if Check(tkFor) then
  begin
    Result := ParseForStmt;
    Exit;
  end;

  if Check(tkTry) then
  begin
    Result := ParseTryStmt;
    Exit;
  end;

  if Check(tkRaise) then
  begin
    Result := ParseRaiseStmt;
    Exit;
  end;

  if Check(tkExit) then
  begin
    Result      := TExitStmt.Create;
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance;
    Exit;
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
    Result := ParseInheritedStmt;
    Exit;
  end;

  if Check(tkCase) then
  begin
    Result := ParseCaseStmt;
    Exit;
  end;

  if Check(tkBegin) then
  begin
    Result := ParseCompoundStmt;
    Exit;
  end;

  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected statement at line %d col %d', FCurrent.Line, FCurrent.Col));

  Name := FCurrent.Value;
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Advance;

  if Check(tkCaret) then
  begin
    
    Advance;  
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
  end
  else if Check(tkDot) then
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected field or method name at line %d col %d', FCurrent.Line, FCurrent.Col));
    SecondIdent := FCurrent.Value;
    Advance;

    if Check(tkAssign) then
    begin
      
      FldAssign            := TFieldAssignment.Create;
      FldAssign.Line       := Line;
      FldAssign.Col        := Col;
      FldAssign.RecordName := Name;
      FldAssign.FieldName  := SecondIdent;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr;
      Result := FldAssign;
    end
    else
    begin
      

      if Check(tkDot) then
      begin
        

        MCall            := TMethodCallStmt.Create;
        MCall.Line       := Line;
        MCall.Col        := Col;
        MCall.ObjectName := '';
        
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
            raise EParseError.Create(Format('Expected field or method name at line %d col %d', FCurrent.Line, FCurrent.Col));
          SecondIdent := FCurrent.Value;
          Advance;
          if Check(tkDot) then
          begin
            
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
        
        if Check(tkDot) then
        begin
          MCallExpr            := TMethodCallExpr.Create;
          MCallExpr.Line       := Line;
          MCallExpr.Col        := Col;
          MCallExpr.ObjectName := MCall.ObjectName;
          MCallExpr.Name       := MCall.Name;
          while MCall.Args.Count > 0 do
            MCallExpr.Args.Add(MCall.Args.Extract(0));
          MCall.Free;
          MCall   := nil;
          CastRcv := MCallExpr;
          while Check(tkDot) do
          begin
            Advance;
            if not Check(tkIdent) then
              raise EParseError.Create(Format('Expected identifier after ''.'' at line %d col %d', FCurrent.Line, FCurrent.Col));
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
              Result := MCall;
              Exit;
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
            Result := FldAssign;
            Exit;
          end;
          raise EParseError.Create(Format('Expected method call or assignment after chain at line %d col %d', FCurrent.Line, FCurrent.Col));
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
    



    if Check(tkLParen) then
    begin
      FCallNode      := TFuncCallExpr.Create;
      FCallNode.Line := Line;
      FCallNode.Col  := Col;
      FCallNode.Name := Name;
      Advance;  
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
        

        while Check(tkDot) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d', FCurrent.Line, FCurrent.Col));
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
            Result := MCall;
            Exit;
          end;
          FldNode            := TFieldAccessExpr.Create;
          FldNode.Line       := Line;
          FldNode.Col        := Col;
          FldNode.Base       := CastRcv;
          FldNode.FieldName  := SecondIdent;
          CastRcv            := FldNode;
        end;
        
        if Check(tkAssign) and (CastRcv is TFieldAccessExpr) then
        begin
          Advance; 
          FldAssign          := TFieldAssignment.Create;
          FldAssign.Line     := Line;
          FldAssign.Col      := Col;
          FldAssign.FieldName := TFieldAccessExpr(CastRcv).FieldName;
          FldAssign.ObjExpr  := TFieldAccessExpr(CastRcv).Base;
          TFieldAccessExpr(CastRcv).Base := nil; 
          CastRcv.Free;
          FldAssign.Expr := ParseExpr;
          Result := FldAssign;
          Exit;
        end;
        raise EParseError.Create(Format('Expected method call after typecast at line %d col %d', FCurrent.Line, FCurrent.Col));
      end;
      

      Call      := TProcCall.Create;
      Call.Line := Line;
      Call.Col  := Col;
      Call.Name := Name;
      while FCallNode.Args.Count > 0 do
        Call.Args.Add(FCallNode.Args.Extract(0));
      FCallNode.Free;
      Result := Call;
      Exit;
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

function TParser.ParseForStmt: TForStmt;
begin
  Result := TForStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkFor);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected loop variable at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.VarName := FCurrent.Value;
    Advance;
    Expect(tkAssign);
    Result.StartExpr := ParseExpr;
    if Check(tkTo) then
    begin
      Result.IsDownTo := False;
      Advance;
    end
    else if Check(tkDownto) then
    begin
      Result.IsDownTo := True;
      Advance;
    end
    else
      raise EParseError.Create(Format('Expected ''to'' or ''downto'' at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.EndExpr := ParseExpr;
    Expect(tkDo);
    Result.Body := ParseStmt;
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseBodyInto(ATarget: TCompoundStmt;
  AStop1, AStop2: TTokenKind);
var
  S: TASTStmt;
begin
  while not (Check(AStop1) or Check(AStop2) or
             Check(tkEnd) or Check(tkEOF)) do
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
  Stmt:        TASTStmt;
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
      ExceptBody := TCompoundStmt.Create;
      try
        ParseBodyInto(ExceptBody, tkEnd, tkEnd);
        Expect(tkEnd);
        TES            := TTryExceptStmt.Create;
        TES.Line       := Line;
        TES.Col        := Col;
        TES.TryBody    := TryBody;
        TES.ExceptBody := ExceptBody;
        TryBody    := nil;
        ExceptBody := nil;
        Result := TES;
      except
        ExceptBody.Free;
        raise;
      end;
    end
    else
    begin
      raise EParseError.Create(Format('Expected ''finally'' or ''except'' after try body at line %d col %d', FCurrent.Line, FCurrent.Col));
    end;
  except
    TryBody.Free;
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
      raise EParseError.Create(Format('Expected method name after ''inherited'' at line %d col %d', FCurrent.Line, FCurrent.Col));
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
      
      if Check(tkSemicolon) then Advance;
      if Stmt <> nil then
        Branch.Stmt := Stmt
      else
        Branch.Stmt := TCompoundStmt.Create;  
      Result.Branches.Add(Branch);
    end;
    if Check(tkElse) then
    begin
      Advance;  
      if Check(tkBegin) then
        Result.ElseStmt := ParseCompoundStmt
      else
      begin
        
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
          
          Result.ElseStmt := TASTStmt(CmpElse.Stmts.Extract(0));
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





function TParser.ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
begin
  Result := TMethodDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if IsFunction then
      Expect(tkFunction)
    else
      Expect(tkProcedure);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Name := FCurrent.Value;
    Advance;
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
    
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseUnit: TUnit;
begin
  Result := TUnit.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkUnit);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected unit name at line %d col %d', FCurrent.Line, FCurrent.Col));
    Result.Name := FCurrent.Value;
    Advance;
    Expect(tkSemicolon);

    
    Expect(tkIntf);
    if Check(tkType) then
      ParseTypeSection(Result.IntfBlock);
    while Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkFunction) then
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(True))
      else
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(False));
    end;

    
    Expect(tkImplementation);
    while Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkFunction) then
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(True))
      else
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(False));
    end;

    Expect(tkEnd);
    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format('Unexpected tokens after unit end at line %d col %d', FCurrent.Line, FCurrent.Col));
  except
    Result.Free;
    raise;
  end;
end;





function TParser.ParseExpr: TASTExpr;
var
  Right:  TASTExpr;
  CmpOp:  TBinaryOp;
  Node:   TBinaryExpr;
  IsNode: TIsExpr;
  AsNode: TAsExpr;
begin
  Result := ParseAddSub;

  
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
    Advance;
    Right       := ParseAddSub;
    Node        := TBinaryExpr.Create;
    Node.Op     := CmpOp;
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
  Right: TASTExpr;
  Op:    TBinaryOp;
  Node:  TBinaryExpr;
begin
  Result := ParseTerm;
  while Check(tkPlus) or Check(tkMinus) or Check(tkOr) do
  begin
    if      Check(tkPlus)  then Op := boAdd
    else if Check(tkMinus) then Op := boSub
    else                        Op := boOr;
    Advance;
    Right := ParseTerm;
    Node := TBinaryExpr.Create;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result := Node;
  end;
end;

function TParser.ParseTerm: TASTExpr;
var
  Right: TASTExpr;
  Op:    TBinaryOp;
  Node:  TBinaryExpr;
begin
  Result := ParseFactor;
  while Check(tkStar) or Check(tkSlash) or Check(tkDiv) or Check(tkAnd) do
  begin
    if      Check(tkStar) then Op := boMul
    else if Check(tkAnd)  then Op := boAnd
    else                       Op := boDiv;
    Advance;
    Right := ParseFactor;
    Node := TBinaryExpr.Create;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result := Node;
  end;
end;

function TParser.ParseFactor: TASTExpr;
var
  IntNode:    TIntLiteral;
  StrNode:    TStringLiteral;
  NilNode:    TNilLiteral;
  IdNode:     TIdentExpr;
  FldNode:    TFieldAccessExpr;
  MCallNode:  TMethodCallExpr;
  FCallNode:  TFuncCallExpr;
  DerefNode:  TDerefExpr;
  NotNode:    TNotExpr;
  Inner:      TASTExpr;
  Name:       string;
  SecondName: string;
  Line, Col:  Integer;
  ZeroNode:   TIntLiteral;
  NegNode:    TBinaryExpr;
begin
  case FCurrent.Kind of
    tkNot:
      begin
        NotNode      := TNotExpr.Create;
        NotNode.Line := FCurrent.Line;
        NotNode.Col  := FCurrent.Col;
        Advance;  
        NotNode.Expr := Self.ParseFactor;  
        Result := NotNode;
      end;
    tkMinus:
      begin
        
        ZeroNode       := TIntLiteral.Create;
        ZeroNode.Line  := FCurrent.Line;
        ZeroNode.Col   := FCurrent.Col;
        ZeroNode.Value := 0;
        NegNode        := TBinaryExpr.Create;
        NegNode.Line   := FCurrent.Line;
        NegNode.Col    := FCurrent.Col;
        NegNode.Op     := boSub;
        NegNode.Left   := ZeroNode;
        Advance;  
        NegNode.Right  := Self.ParseFactor;  
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
        IntNode.Value := StrToInt(FCurrent.Value);
        Advance;
        Result := IntNode;
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
        



        if Check(tkLessThan) and (PeekKind = tkIdent) and
           (((PeekKind2 = tkGreaterThan) or (PeekKind2 = tkComma))) then
        begin
          Advance;  
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
          
          if not (Check(tkDot) or Check(tkLParen)) then
            raise EParseError.Create(Format('Expected ''.'' or ''('' after generic type arguments at line %d col %d', FCurrent.Line, FCurrent.Col));
        end;
        if Check(tkDot) then
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d', FCurrent.Line, FCurrent.Col));
          SecondName := FCurrent.Value;
          Advance;
          if Check(tkLParen) then
          begin
            
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
            
            FldNode            := TFieldAccessExpr.Create;
            FldNode.Line       := Line;
            FldNode.Col        := Col;
            FldNode.RecordName := Name;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
            
            while Check(tkDot) and (PeekKind = tkIdent) do
            begin
              Advance;  
              SecondName := FCurrent.Value;
              Advance;  
              if Check(tkLParen) then
              begin
                
                MCallNode             := TMethodCallExpr.Create;
                MCallNode.Line        := FCurrent.Line;
                MCallNode.Col         := FCurrent.Col;
                MCallNode.ObjectName  := '';
                MCallNode.Name        := SecondName;
                MCallNode.ObjExpr     := Result;
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
                FldNode            := TFieldAccessExpr.Create;
                FldNode.Line       := FCurrent.Line;
                FldNode.Col        := FCurrent.Col;
                FldNode.Base       := Result;
                FldNode.FieldName  := SecondName;
                Result := FldNode;
              end;
            end;
          end;
        end
        else if Check(tkLParen) then
        begin
          
          FCallNode      := TFuncCallExpr.Create;
          FCallNode.Line := Line;
          FCallNode.Col  := Col;
          FCallNode.Name := Name;
          Advance;  
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
          
          while Check(tkDot) and (PeekKind = tkIdent) do
          begin
            Advance;  
            SecondName := FCurrent.Value;
            Advance;  
            FldNode            := TFieldAccessExpr.Create;
            FldNode.Line       := FCurrent.Line;
            FldNode.Col        := FCurrent.Col;
            FldNode.Base       := Result;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
            if Check(tkLParen) then
            begin
              


              
              Advance;  
              if not Check(tkRParen) then
              begin
                FldNode.ResolvedType := nil; 
              end;
              

              MCallNode             := TMethodCallExpr.Create;
              MCallNode.Line        := FldNode.Line;
              MCallNode.Col         := FldNode.Col;
              MCallNode.ObjectName  := '';  
              MCallNode.Name        := SecondName;
              MCallNode.ObjExpr     := FldNode.Base;
              FldNode.Base          := nil;  
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
        
        if Check(tkCaret) then
        begin
          Advance;
          DerefNode      := TDerefExpr.Create;
          DerefNode.Line := Line;
          DerefNode.Col  := Col;
          DerefNode.Expr := Result;
          Result         := DerefNode;
        end;
      end;
    tkLParen:
      begin
        Advance;
        Inner := ParseExpr;
        Expect(tkRParen);
        
        if Check(tkCaret) then
        begin
          Advance;
          DerefNode      := TDerefExpr.Create;
          DerefNode.Line := FCurrent.Line;
          DerefNode.Col  := FCurrent.Col;
          DerefNode.Expr := Inner;
          Result         := DerefNode;
        end
        else
          Result := Inner;
      end;
  else
    raise EParseError.Create(Format('Expected expression at line %d col %d', FCurrent.Line, FCurrent.Col));
  end;
end;




{ === uSemantic === }






















type

  TSemanticAnalyser = class

    FTable:                TSymbolTable;
    FProg:                 TProgram;      
    FMethodIndex:          TStringList;  
    FProcIndex:            TStringList;  
    FGenericFuncTemplates: TStringList;  
    FLoopDepth:            Integer;      
    FScopeDepth:           Integer;      
    FCurrentClass:         TRecordTypeDesc;  

    
    function  FindTypeOrInstantiate(const AName: string): TTypeDesc;
    function  InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
    function  InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
    function  SubstTypeParam(const ATypeName: string;
                AParamNames, AArgs: TStringList): string;

    
    function  InstantiateGenericFunc(const AInstName: string): TMethodDecl;

    procedure AnalyseBlock(ABlock: TBlock);
    procedure AnalyseConstDecls(ABlock: TBlock);
    procedure AnalyseTypeDecls(ABlock: TBlock);
    procedure LinkClassMethodImpls(ABlock: TBlock);
    procedure LinkGenericClassMethodImpls(ABlock: TBlock);
    procedure AnalyseMethodBodies(ABlock: TBlock);
    procedure AnalyseMethodDecl(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure AnalyseStandaloneDecls(ABlock: TBlock);
    procedure AnalyseStandaloneBodies(ABlock: TBlock);
    procedure AnalyseStandaloneDecl(ADecl: TMethodDecl);
    procedure AnalyseVarDecls(ABlock: TBlock);
    procedure AnalyseStmts(ABlock: TBlock);
    procedure AnalyseStmt(AStmt: TASTStmt);
    procedure AnalyseAssignment(AAssign: TAssignment);
    procedure AnalyseFieldAssignment(AAssign: TFieldAssignment);
    procedure AnalyseProcCall(ACall: TProcCall);
    procedure AnalyseMethodCall(ACall: TMethodCallStmt);
    procedure AnalyseInheritedCall(ACall: TInheritedCallStmt);
    procedure AnalyseCaseStmt(AStmt: TCaseStmt);
    function  AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
    function  AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
    function  AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
    function  AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
    function  AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
    function  AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
    procedure AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);

    procedure AnalyseCompoundBody(ABody: TCompoundStmt);
    function  FindMethodDecl(const ATypeName, AMethodName: string): TMethodDecl;
    



    function  AttrMatches(const AAttrName, ACanonical: string): Boolean;
    function  HasWeakAttribute(AAttrs: TStringList): Boolean;

    procedure SemanticError(const AMsg: string; ALine, ACol: Integer);
    procedure CheckTypesMatch(AExpected, AActual: TTypeDesc;
      const AContext: string; ALine, ACol: Integer);
    
    function  IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
    


    procedure CheckTypeParamConstraint(const AParamName, AArgName, AConstraint,
      AContext: string);

    procedure Create;
    procedure Destroy;
    procedure Analyse(AProg: TProgram);
    procedure AnalyseUnit(AUnit: TUnit);
  end;


procedure TSemanticAnalyser.Create;
begin

  FTable                := TSymbolTable.Create;
  FMethodIndex          := TStringList.Create;
  FMethodIndex.CaseSensitive := False;
  FProcIndex            := TStringList.Create;
  FProcIndex.CaseSensitive := False;
  FGenericFuncTemplates := TStringList.Create;
  FGenericFuncTemplates.CaseSensitive := False;
  FLoopDepth            := 0;
end;

procedure TSemanticAnalyser.Destroy;
begin
  FGenericFuncTemplates.Free;
  FProcIndex.Free;
  FMethodIndex.Free;
  FTable.Free;

end;

procedure TSemanticAnalyser.SemanticError(const AMsg: string; ALine, ACol: Integer);
begin
  raise ESemanticError.Create(Format('%s at line %d col %d', AMsg, ALine, ACol));
end;

function TSemanticAnalyser.AttrMatches(const AAttrName, ACanonical: string): Boolean;




var
  Suffix: string;
begin
  if SameText(AAttrName, ACanonical) then
    begin Result := True;  Exit end;
  Suffix := ACanonical + 'Attribute';
  Result := SameText(AAttrName, Suffix);
end;

function TSemanticAnalyser.HasWeakAttribute(AAttrs: TStringList): Boolean;
var
  I: Integer;
begin
  if AAttrs = nil then begin Result := False; Exit end;
  for I := 0 to AAttrs.Count - 1 do
    if AttrMatches(AAttrs.Get(I), 'Weak') then
      begin Result := True;  Exit end;
  Result := False;
end;

procedure TSemanticAnalyser.CheckTypeParamConstraint(
  const AParamName, AArgName, AConstraint, AContext: string);
var
  ArgType:     TTypeDesc;
  ConstrType:  TTypeDesc;
  RT:          TRecordTypeDesc;
  I:           Integer;
  Implements:  Boolean;
begin
  if AConstraint = '' then Exit;

  ArgType := FTable.FindType(AArgName);
  if ArgType = nil then
    raise ESemanticError.Create(Format('Unknown type ''%s'' for type parameter ''%s'' in %s', AArgName, AParamName, AContext));

  if SameText(AConstraint, 'class') then
  begin
    if ArgType.Kind <> tyClass then
      raise ESemanticError.Create(Format('Type ''%s'' does not satisfy constraint ''%s: class'' in %s', AArgName, AParamName, AContext));
    Exit;
  end;

  if SameText(AConstraint, 'record') then
  begin
    if not (((ArgType.Kind = tyRecord) or (ArgType.Kind = tyInteger) or (ArgType.Kind = tyInt64) or (ArgType.Kind = tyUInt32) or (ArgType.Kind = tyByte) or (ArgType.Kind = tyBoolean) or (ArgType.Kind = tyString) or (ArgType.Kind = tyPointer))) then
      raise ESemanticError.Create(Format('Type ''%s'' does not satisfy constraint ''%s: record'' in %s', AArgName, AParamName, AContext));
    Exit;
  end;

  

  ConstrType := FTable.FindType(AConstraint);
  if ConstrType = nil then
    raise ESemanticError.Create(Format('Unknown constraint type ''%s'' for type parameter ''%s'' in %s', AConstraint, AParamName, AContext));

  if ArgType = ConstrType then Exit;

  if (ConstrType.Kind = tyClass) and (ArgType.Kind = tyClass) then
  begin
    if IsSubtypeOf(ArgType, ConstrType) then Exit;
    raise ESemanticError.Create(Format('Type ''%s'' does not inherit from ''%s'' (constraint ''%s: %s'') in %s', AArgName, AConstraint, AParamName, AConstraint, AContext));
  end;

  if (ConstrType.Kind = tyInterface) and (ArgType.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(ArgType);
    Implements := False;
    for I := 0 to RT.ImplementsCount - 1 do
      if RT.ImplementsIntfAt(I) = ConstrType then
      begin
        Implements := True;
        Break;
      end;
    if not Implements then
      raise ESemanticError.Create(Format('Type ''%s'' does not implement ''%s'' (constraint ''%s: %s'') in %s', AArgName, AConstraint, AParamName, AConstraint, AContext));
    Exit;
  end;

  raise ESemanticError.Create(Format('Type ''%s'' does not satisfy constraint ''%s: %s'' in %s', AArgName, AParamName, AConstraint, AContext));
end;

function TSemanticAnalyser.IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
var
  Walk: TRecordTypeDesc;
begin
  Result := AActual = AExpected;
  if Result then Exit;
  if (AActual = nil) or (AExpected = nil) then Exit;
  if (AActual.Kind <> tyClass) or (AExpected.Kind <> tyClass) then Exit;
  Walk := TRecordTypeDesc(AActual).Parent;
  while Walk <> nil do
  begin
    if Walk = AExpected then
    begin
      Result := True;
      Exit;
    end;
    Walk := Walk.Parent;
  end;
end;

procedure TSemanticAnalyser.CheckTypesMatch(AExpected, AActual: TTypeDesc;
  const AContext: string; ALine, ACol: Integer);
var
  RT: TRecordTypeDesc;
  I:  Integer;
begin
  if AExpected = AActual then
    Exit;
  
  if (AActual.Kind = tyNil) and (((AExpected.Kind = tyClass) or (AExpected.Kind = tyInterface) or (AExpected.Kind = tyPointer) or (AExpected.Kind = tyString))) then
    Exit;
  


  if (AExpected.Kind = tyPointer) and (AActual.Kind = tyPointer) then
  begin
    if (TPointerTypeDesc(AExpected).BaseType = nil) or
       (TPointerTypeDesc(AActual).BaseType = nil) or
       (TPointerTypeDesc(AExpected).BaseType = TPointerTypeDesc(AActual).BaseType) then
      Exit;
  end;
  

  if (AExpected.Kind = tyEnum) and AActual.IsNumeric then Exit;
  if (AActual.Kind  = tyEnum) and AExpected.IsNumeric then Exit;
  
  if AExpected.IsNumeric and AActual.IsNumeric then Exit;
  
  if IsSubtypeOf(AActual, AExpected) then
    Exit;
  
  if (AExpected.Kind = tyClass) and (AExpected.Name = 'TObject') and
     (AActual.Kind = tyClass) then
    Exit;
  
  if (AExpected.Kind = tyInterface) and (AActual.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(AActual);
    for I := 0 to RT.ImplementsCount - 1 do
      if RT.ImplementsIntfAt(I) = AExpected then
        Exit;
  end;
  
  if (AExpected.Kind = tyPointer) and
     (TPointerTypeDesc(AExpected).BaseType = nil) and
     (((AActual.Kind = tyClass) or (AActual.Kind = tyInterface) or (AActual.Kind = tyString) or (AActual.Kind = tyPointer))) then
    Exit;
  if (AActual.Kind = tyPointer) and
     (TPointerTypeDesc(AActual).BaseType = nil) and
     (((AExpected.Kind = tyClass) or (AExpected.Kind = tyInterface) or (AExpected.Kind = tyString) or (AExpected.Kind = tyPointer))) then
    Exit;
  SemanticError(
    Format('Type mismatch in %s: expected ''%s'' but got ''%s''', AContext, AExpected.Name, AActual.Name),
    ALine, ACol);
end;

procedure TSemanticAnalyser.Analyse(AProg: TProgram);
begin
  FProg := AProg;
  AnalyseBlock(AProg.Block);
  


  AProg.SymbolTable := FTable;
  FTable := nil;
end;

procedure TSemanticAnalyser.AnalyseUnit(AUnit: TUnit);
var
  I, J:     Integer;
  MDecl:    TMethodDecl;
  ImplDecl: TMethodDecl;
  ImplIdx:  Integer;
  Par:      TMethodParam;
  ParType:  TTypeDesc;
  Sym:      TSymbol;
begin
  FTable.PushScope;
  try
    
    AnalyseTypeDecls(AUnit.IntfBlock);

    
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Get(I));

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(MDecl.Params.Get(J));
        ParType := FTable.FindType(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for parameter ''%s''', Par.TypeName, Par.ParamName),
            MDecl.Line, MDecl.Col);
        Par.ResolvedType := ParType;
      end;

      if MDecl.ReturnTypeName <> '' then
      begin
        ParType := FTable.FindType(MDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''', MDecl.ReturnTypeName, MDecl.Name),
            MDecl.Line, MDecl.Col);
        MDecl.ResolvedReturnType := ParType;
      end;

      FProcIndex.AddObject(MDecl.Name, MDecl);

      if MDecl.ReturnTypeName <> '' then
        Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
      else
        Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate identifier ''%s''', MDecl.Name),
          MDecl.Line, MDecl.Col);
      end;
    end;

    

    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Get(I));
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(ImplDecl.Params.Get(J));
        ParType := FTable.FindType(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for parameter ''%s''', Par.TypeName, Par.ParamName),
            ImplDecl.Line, ImplDecl.Col);
        Par.ResolvedType := ParType;
      end;

      if ImplDecl.ReturnTypeName <> '' then
      begin
        ParType := FTable.FindType(ImplDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''', ImplDecl.ReturnTypeName, ImplDecl.Name),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedReturnType := ParType;
      end;

      ImplIdx := FProcIndex.IndexOf(ImplDecl.Name);
      if ImplIdx >= 0 then
      begin
        
        MDecl := TMethodDecl(FProcIndex.GetObject(ImplIdx));
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d', ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count),
            ImplDecl.Line, ImplDecl.Col);
        
        FProcIndex.SetObject(ImplIdx, ImplDecl);
      end
      else
      begin
        
        FProcIndex.AddObject(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''', ImplDecl.Name),
            ImplDecl.Line, ImplDecl.Col);
        end;
      end;
    end;

    
    LinkGenericClassMethodImpls(AUnit.ImplBlock);

    
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls.Get(I));
      ImplIdx := FProcIndex.IndexOf(MDecl.Name);
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.GetObject(ImplIdx)).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', MDecl.Name),
          MDecl.Line, MDecl.Col);
    end;

    
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Get(I));
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;
      AnalyseStandaloneDecl(ImplDecl);
    end;
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.LinkClassMethodImpls(ABlock: TBlock);
var
  I:    Integer;
  Decl: TMethodDecl;
  Key:  string;
  Idx:  Integer;
  CD:   TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Get(I));
    if Decl.OwnerTypeName = '' then Continue;
    if Decl.OwnerTypeParams <> nil then Continue;  
    Key := Decl.OwnerTypeName + '.' + Decl.Name;
    Idx := FMethodIndex.IndexOf(Key);
    if Idx < 0 then
      SemanticError(
        Format('Method ''%s'' is not declared in class ''%s''', Decl.Name, Decl.OwnerTypeName),
        Decl.Line, Decl.Col);
    CD := TMethodDecl(FMethodIndex.GetObject(Idx));
    if CD.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has an inline body', Decl.OwnerTypeName, Decl.Name),
        Decl.Line, Decl.Col);
    
    CD.Body   := Decl.Body;
    Decl.Body := nil;
  end;
end;

procedure TSemanticAnalyser.LinkGenericClassMethodImpls(ABlock: TBlock);
var
  I, J: Integer;
  Decl: TMethodDecl;
  Templ: TGenericTypeDef;
  MDecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Get(I));
    if (Decl.OwnerTypeName = '') or (Decl.OwnerTypeParams = nil) then
      Continue;
    
    if not (FTable.FindGeneric(Decl.OwnerTypeName) is TGenericTypeDef) then
      SemanticError(
        Format('Generic type ''%s'' not found for method ''%s''', Decl.OwnerTypeName, Decl.Name),
        Decl.Line, Decl.Col);
    Templ := TGenericTypeDef(FTable.FindGeneric(Decl.OwnerTypeName));
    
    MDecl := nil;
    for J := 0 to Templ.ClassDef.Methods.Count - 1 do
      if SameText(TMethodDecl(Templ.ClassDef.Methods.Get(J)).Name, Decl.Name) then
      begin
        MDecl := TMethodDecl(Templ.ClassDef.Methods.Get(J));
        Break;
      end;
    if MDecl = nil then
      SemanticError(
        Format('Method ''%s'' is not declared in generic class ''%s''', Decl.Name, Decl.OwnerTypeName),
        Decl.Line, Decl.Col);
    if MDecl.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has a body', Decl.OwnerTypeName, Decl.Name),
        Decl.Line, Decl.Col);
    MDecl.Body := Decl.Body;
    Decl.Body  := nil;
  end;
end;

function TSemanticAnalyser.FindTypeOrInstantiate(const AName: string): TTypeDesc;
var
  BaseName: string;
  BaseType: TTypeDesc;
  PT:       TPointerTypeDesc;
  Sym:      TSymbol;
begin
  Result := FTable.FindType(AName);
  if Result <> nil then Exit;
  
  if (Length(AName) > 1) and (OrdAt(AName, 1) = 94) then
  begin
    BaseName := Copy(AName, 2, MaxInt);
    BaseType := FindTypeOrInstantiate(BaseName);
    if BaseType <> nil then
    begin
      PT := FTable.NewPointerType(AName, BaseType);
      Sym := TSymbol.Create(AName, skType, PT);
      FTable.DefineGlobal(Sym);
      Result := PT;
    end;
    Exit;
  end;
  if Pos('<', AName) > 0 then
  begin
    Result := InstantiateGeneric(AName);
    if Result = nil then
      Result := InstantiateGenericInterface(AName);
  end;
end;

function TSemanticAnalyser.SubstTypeParam(const ATypeName: string;
  AParamNames, AArgs: TStringList): string;
var
  I: Integer;
begin
  Result := ATypeName;
  
  for I := 0 to AParamNames.Count - 1 do
    if SameText(Result, AParamNames.Get(I)) then
    begin
      Result := AArgs.Get(I);
      Exit;
    end;
  
  if (Length(Result) > 0) and (OrdAt(Result, 1) = 94) then
    Result := '^' + Self.SubstTypeParam(Copy(Result, 2, MaxInt), AParamNames, AArgs);
end;

function TSemanticAnalyser.InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
var
  BracPos:  Integer;
  BaseName: string;
  ArgsStr:  string;
  Args:     TStringList;
  Templ:    TGenericTypeDef;
  ClonedCD: TClassTypeDef;
  I, J, K:  Integer;
  FDecl:    TFieldDecl;
  NewFDecl: TFieldDecl;
  MDecl:    TMethodDecl;
  NewMDecl: TMethodDecl;
  Par:      TMethodParam;
  NewPar:   TMethodParam;
  Sym:      TSymbol;
  Key:      string;
  FldType:  TTypeDesc;
  FldName:  string;
  ParType:  TTypeDesc;
  RT:       TRecordTypeDesc;
  GI:        TGenericInstance;
  Subst:     string;
  ConcrType: TTypeDesc;
begin
  Result := nil;

  
  BracPos := Pos('<', ATypeName);
  if BracPos = 0 then Exit;
  BaseName := Copy(ATypeName, 1, BracPos - 1);
  ArgsStr  := Copy(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 1);

  Args := TStringList.Create;
  try
    while ArgsStr <> '' do
    begin
      BracPos := Pos(',', ArgsStr);
      if BracPos > 0 then
      begin
        Args.Add(Trim(Copy(ArgsStr, 1, BracPos - 1)));
        ArgsStr := Trim(Copy(ArgsStr, BracPos + 1, MaxInt));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    
    if not (FTable.FindGeneric(BaseName) is TGenericTypeDef) then Exit;
    Templ := TGenericTypeDef(FTable.FindGeneric(BaseName));
    if Templ = nil then Exit;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    
    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Get(I), Args.Get(I),
          Templ.ParamConstraints.Get(I),
          Format('instantiation ''%s''', ATypeName));

    

    RT  := FTable.NewClassType(ATypeName);
    Sym := TSymbol.Create(ATypeName, skType, RT);
    FTable.DefineGlobal(Sym);

    
    ClonedCD             := TClassTypeDef.Create;
    ClonedCD.ParentName  := Templ.ClassDef.ParentName;
    for I := 0 to Templ.ClassDef.ImplementsNames.Count - 1 do
      ClonedCD.ImplementsNames.Add(Templ.ClassDef.ImplementsNames.Get(I));

    
    for I := 0 to Templ.ClassDef.Fields.Count - 1 do
    begin
      FDecl    := TFieldDecl(Templ.ClassDef.Fields.Get(I));
      NewFDecl := TFieldDecl.Create;
      for J := 0 to FDecl.Names.Count - 1 do
        NewFDecl.Names.Add(FDecl.Names.Get(J));
      NewFDecl.TypeName := SubstTypeParam(FDecl.TypeName, Templ.ParamNames, Args);
      ClonedCD.Fields.Add(NewFDecl);
    end;

    
    for I := 0 to Templ.ClassDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.ClassDef.Methods.Get(I));
      NewMDecl         := TMethodDecl.Create;
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsVirtual     := MDecl.IsVirtual;
      NewMDecl.IsOverride    := MDecl.IsOverride;
      NewMDecl.Body          := MDecl.Body;
      NewMDecl.OwnBody       := False;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par    := TMethodParam(MDecl.Params.Get(J));
        NewPar := TMethodParam.Create;
        NewPar.ParamName  := Par.ParamName;
        NewPar.IsVarParam := Par.IsVarParam;
        NewPar.TypeName   := SubstTypeParam(Par.TypeName, Templ.ParamNames, Args);
        NewMDecl.Params.Add(NewPar);
      end;

      NewMDecl.ReturnTypeName :=
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args);

      ClonedCD.Methods.Add(NewMDecl);
    end;

    
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Get(J));
      if NewMDecl.IsVirtual then
        RT.AddVTableSlot(NewMDecl.Name, '$' + ATypeName + '_' + NewMDecl.Name)
      else if NewMDecl.IsOverride then
        RT.OverrideVTableSlot(
          RT.FindVTableSlot(NewMDecl.Name),
          '$' + ATypeName + '_' + NewMDecl.Name);
    end;

    
    for J := 0 to ClonedCD.Fields.Count - 1 do
    begin
      NewFDecl := TFieldDecl(ClonedCD.Fields.Get(J));
      FldType  := FindTypeOrInstantiate(NewFDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field in ''%s''', NewFDecl.TypeName, ATypeName),
          0, 0);
      NewFDecl.ResolvedType := FldType;
      for K := 0 to NewFDecl.Names.Count - 1 do
      begin
        FldName := NewFDecl.Names.Get(K);
        RT.AddField(FldName, FldType);
      end;
    end;

    
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Get(J));
      Key      := ATypeName + '.' + NewMDecl.Name;
      FMethodIndex.AddObject(Key, NewMDecl);
      if SameText(NewMDecl.Name, 'Destroy') then
        RT.HasDestroyMethod := True;

      if NewMDecl.IsVirtual or NewMDecl.IsOverride then
        NewMDecl.VTableSlot := RT.FindVTableSlot(NewMDecl.Name);

      for K := 0 to NewMDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(NewMDecl.Params.Get(K));
        ParType := FindTypeOrInstantiate(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for param ''%s'' in ''%s''', Par.TypeName, Par.ParamName, ATypeName),
            0, 0);
        Par.ResolvedType := ParType;
      end;

      if NewMDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(NewMDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for method ''%s'' in ''%s''', NewMDecl.ReturnTypeName, NewMDecl.Name, ATypeName),
            0, 0);
        NewMDecl.ResolvedReturnType := ParType;
      end;
    end;

    


    FTable.PushScope;
    try
      for K := 0 to Templ.ParamNames.Count - 1 do
      begin
        ConcrType := FindTypeOrInstantiate(Args.Get(K));
        if ConcrType <> nil then
        begin
          Sym := TSymbol.Create(Templ.ParamNames.Get(K), skType, ConcrType);
          FTable.Define(Sym);
        end;
      end;
      for J := 0 to ClonedCD.Methods.Count - 1 do
      begin
        NewMDecl := TMethodDecl(ClonedCD.Methods.Get(J));
        if NewMDecl.Body <> nil then
          AnalyseMethodDecl(NewMDecl, RT);
      end;
    finally
      FTable.PopScope;
    end;

    
    GI          := TGenericInstance.Create;
    GI.TypeName := ATypeName;
    GI.ClassDef := ClonedCD;
    GI.TypeDesc := RT;
    FProg.GenericInstances.Add(GI);

    Result := RT;
  finally
    Args.Free;
  end;
end;

function TSemanticAnalyser.InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TGenericInterfaceDef;
  TemplObj:    TObject;
  I:           Integer;
  MDecl:       TMethodDecl;
  Sym:         TSymbol;
  GII:         TGenericInterfaceInstance;
  MangledName: string;
begin
  Result := nil;

  BracPos := Pos('<', ATypeName);
  if BracPos = 0 then Exit;
  BaseName := Copy(ATypeName, 1, BracPos - 1);
  ArgsStr  := Copy(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 1);

  Args := TStringList.Create;
  try
    while ArgsStr <> '' do
    begin
      BracPos := Pos(',', ArgsStr);
      if BracPos > 0 then
      begin
        Args.Add(Trim(Copy(ArgsStr, 1, BracPos - 1)));
        ArgsStr := Trim(Copy(ArgsStr, BracPos + 1, MaxInt));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    TemplObj := FTable.FindGeneric(BaseName);
    if (TemplObj = nil) or not (TemplObj is TGenericInterfaceDef) then Exit;
    Templ := TGenericInterfaceDef(TemplObj);
    if Args.Count <> Templ.ParamNames.Count then Exit;

    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Get(I), Args.Get(I),
          Templ.ParamConstraints.Get(I),
          Format('interface instantiation ''%s''', ATypeName));

    
    Sym := FTable.Lookup(ATypeName);
    if (Sym <> nil) and (Sym.TypeDesc is TInterfaceTypeDesc) then
    begin
      Result := TInterfaceTypeDesc(Sym.TypeDesc);
      Exit;
    end;

    
    MangledName := BaseName;
    for I := 0 to Args.Count - 1 do
      MangledName := MangledName + '_' + Args.Get(I);

    
    Result := FTable.NewInterfaceType(ATypeName);
    Sym    := TSymbol.Create(ATypeName, skType, Result);
    FTable.DefineGlobal(Sym);

    
    for I := 0 to Templ.IntfDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(Templ.IntfDef.Methods.Get(I));
      Result.AddMethod(MDecl.Name,
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args));
    end;

    
    GII          := TGenericInterfaceInstance.Create;
    GII.InstName := MangledName;
    GII.IntfDef.Free;
    GII.IntfDef  := nil;
    GII.TypeDesc := Result;
    FProg.GenericIntfInstances.Add(GII);
  finally
    Args.Free;
  end;
end;

function TSemanticAnalyser.InstantiateGenericFunc(const AInstName: string): TMethodDecl;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TMethodDecl;
  TemplIdx:    Integer;
  NewMDecl:    TMethodDecl;
  NewPar:      TMethodParam;
  OldPar:      TMethodParam;
  ParTypeName: string;
  RetTypeName: string;
  SubstType:   TTypeDesc;
  I, J:        Integer;
  Sym:         TSymbol;
  GFI:         TGenericFuncInstance;
begin
  Result := nil;

  
  BracPos := Pos('<', AInstName);
  if BracPos = 0 then Exit;

  BaseName := Copy(AInstName, 1, BracPos - 1);
  ArgsStr  := Copy(AInstName, BracPos + 1, Length(AInstName) - BracPos - 1);

  TemplIdx := FGenericFuncTemplates.IndexOf(BaseName);
  if TemplIdx < 0 then Exit;  

  Templ := TMethodDecl(FGenericFuncTemplates.GetObject(TemplIdx));

  Args := TStringList.Create;
  try
    SplitIntoList(ArgsStr, 44, Args);


    if Args.Count <> Templ.TypeParams.Count then
      SemanticError(
        Format('Generic function ''%s'' expects %d type parameter(s) but got %d', BaseName, Templ.TypeParams.Count, Args.Count),
        0, 0);

    
    for I := 0 to Args.Count - 1 do
      if (Templ.TypeParamConstraints <> nil) and
         (I < Templ.TypeParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.TypeParams.Get(I), Args.Get(I),
          Templ.TypeParamConstraints.Get(I),
          Format('generic function ''%s''', AInstName));

    NewMDecl         := TMethodDecl.Create;
    NewMDecl.Name    := AInstName;
    NewMDecl.OwnBody := False;   
    NewMDecl.Body    := Templ.Body;

    
    RetTypeName := Templ.ReturnTypeName;
    for I := 0 to Templ.TypeParams.Count - 1 do
      if SameText(RetTypeName, Templ.TypeParams.Get(I)) then
        RetTypeName := Args.Get(I);
    NewMDecl.ReturnTypeName := RetTypeName;
    if RetTypeName <> '' then
    begin
      SubstType := FindTypeOrInstantiate(RetTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' in generic function instance ''%s''', RetTypeName, AInstName), 0, 0);
      NewMDecl.ResolvedReturnType := SubstType;
    end;

    
    for I := 0 to Templ.Params.Count - 1 do
    begin
      OldPar           := TMethodParam(Templ.Params.Get(I));
      NewPar           := TMethodParam.Create;
      NewPar.ParamName  := OldPar.ParamName;
      NewPar.IsVarParam := OldPar.IsVarParam;
      ParTypeName       := OldPar.TypeName;
      for J := 0 to Templ.TypeParams.Count - 1 do
        if SameText(ParTypeName, Templ.TypeParams.Get(J)) then
          ParTypeName := Args.Get(J);
      NewPar.TypeName := ParTypeName;
      SubstType := FindTypeOrInstantiate(ParTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' for parameter ''%s'' in ''%s''', ParTypeName, NewPar.ParamName, AInstName), 0, 0);
      NewPar.ResolvedType := SubstType;
      NewMDecl.Params.Add(NewPar);
    end;

    
    AnalyseStandaloneDecl(NewMDecl);

    
    FProcIndex.AddObject(AInstName, NewMDecl);
    if NewMDecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(AInstName, skFunction, NewMDecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(AInstName, skProcedure, nil);
    FTable.DefineGlobal(Sym);

    
    GFI            := TGenericFuncInstance.Create;
    GFI.InstName   := AInstName;
    GFI.MethodDecl := NewMDecl;
    FProg.GenericFuncInstances.Add(GFI);

    Result := NewMDecl;
  finally
    Args.Free;
  end;
end;

procedure TSemanticAnalyser.AnalyseBlock(ABlock: TBlock);
begin
  


  AnalyseConstDecls(ABlock);
  AnalyseTypeDecls(ABlock);
  

  LinkClassMethodImpls(ABlock);
  LinkGenericClassMethodImpls(ABlock);
  

  AnalyseStandaloneDecls(ABlock);
  AnalyseMethodBodies(ABlock);
  FTable.PushScope;
  FScopeDepth := FScopeDepth + 1;
  try
    AnalyseVarDecls(ABlock);
    AnalyseStandaloneBodies(ABlock);
    AnalyseStmts(ABlock);
  finally
    FScopeDepth := FScopeDepth - 1;
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseConstDecls(ABlock: TBlock);
var
  I:    Integer;
  CD:   TConstDecl;
  Sym:  TSymbol;
  TD:   TTypeDesc;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Get(I));
    if CD.IsString then
      TD := FTable.TypeString
    else
      TD := FTable.TypeInteger;
    Sym             := TSymbol.Create(CD.Name, skConstant, TD);
    Sym.ConstValue  := CD.IntVal;
    Sym.ConstString := CD.StrVal;
    if not FTable.Define(Sym) then
      Sym.Free;  
  end;
end;

procedure TSemanticAnalyser.AnalyseTypeDecls(ABlock: TBlock);
var
  I, J, K:    Integer;
  L:          Integer;
  TD:         TTypeDecl;
  FieldList:  TObjectList;
  MethodList: TObjectList;
  FDecl:      TFieldDecl;
  MDecl:      TMethodDecl;
  Par:        TMethodParam;
  ParType:    TTypeDesc;
  RT:         TRecordTypeDesc;
  ParentRT:   TRecordTypeDesc;
  ParentSym:  TSymbol;
  FldType:    TTypeDesc;
  FldName:    string;
  Sym:        TSymbol;
  Key:        string;
  FldInfo:    TFieldInfo;
  IntfDesc:   TInterfaceTypeDesc;
  IntfName:   string;
  IntfSym:    TSymbol;
  ITD:        TInterfaceTypeDef;
  PropDecl:   TPropertyDecl;
  PropInfo:   TPropertyInfo;
  PropType:   TTypeDesc;
  EnumDesc:   TEnumTypeDesc;
  EnumDef:    TEnumTypeDef;
  MName:      string;
  MSym:       TSymbol;
begin
  

  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Get(I));
    if TD.Def is TRecordTypeDef then
      RT := FTable.NewRecordType(TD.Name)
    else if TD.Def is TClassTypeDef then
      RT := FTable.NewClassType(TD.Name)
    else if TD.Def is TGenericTypeDef then
    begin
      
      FTable.RegisterGeneric(TD.Name, TD.Def);
      Continue;
    end
    else if TD.Def is TGenericInterfaceDef then
    begin
      
      FTable.RegisterGeneric(TD.Name, TD.Def);
      Continue;
    end
    else if TD.Def is TInterfaceTypeDef then
    begin
      IntfDesc := FTable.NewInterfaceType(TD.Name);
      Sym      := TSymbol.Create(TD.Name, skType, IntfDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', TD.Name), TD.Line, TD.Col);
      end;
      Continue;
    end
    else if TD.Def is TEnumTypeDef then
    begin
      
      EnumDef  := TEnumTypeDef(TD.Def);
      EnumDesc := FTable.NewEnumType(TD.Name);
      for K := 0 to EnumDef.Members.Count - 1 do
      begin
        MName           := EnumDef.Members.Get(K);
        EnumDesc.Members.Add(MName);
        MSym            := TSymbol.Create(MName, skConstant, EnumDesc);
        MSym.ConstValue := K;
        if not FTable.Define(MSym) then
          MSym.Free;
      end;
      Sym := TSymbol.Create(TD.Name, skType, EnumDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', TD.Name), TD.Line, TD.Col);
      end;
      Continue;
    end
    else
    begin
      SemanticError('Only record, class, interface, or enum type definitions are supported',
        TD.Line, TD.Col);
      Continue;
    end;
    Sym := TSymbol.Create(TD.Name, skType, RT);
    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      SemanticError(Format('Duplicate type name ''%s''', TD.Name), TD.Line, TD.Col);
    end;
  end;

  
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Get(I));

    
    if TD.Def is TGenericTypeDef then Continue;
    if TD.Def is TGenericInterfaceDef then Continue;
    if TD.Def is TEnumTypeDef then Continue;

    
    if TD.Def is TInterfaceTypeDef then
    begin
      ITD      := TInterfaceTypeDef(TD.Def);
      IntfSym  := FTable.Lookup(TD.Name);
      IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
      if ITD.ParentName <> '' then
      begin
        Sym := FTable.Lookup(ITD.ParentName);
        if (Sym = nil) or not (Sym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown parent interface ''%s'' for ''%s''', ITD.ParentName, TD.Name),
            TD.Line, TD.Col);
        IntfDesc.Parent := TInterfaceTypeDesc(Sym.TypeDesc);
        
        for J := 0 to IntfDesc.Parent.MethodCount - 1 do
          IntfDesc.AddMethod(IntfDesc.Parent.MethodName(J),
            IntfDesc.Parent.MethodReturnTypeName(J));
      end;
      for J := 0 to ITD.Methods.Count - 1 do
        IntfDesc.AddMethod(TMethodDecl(ITD.Methods.Get(J)).Name,
          TMethodDecl(ITD.Methods.Get(J)).ReturnTypeName);
      Continue;
    end;

    Sym := FTable.Lookup(TD.Name);
    RT  := TRecordTypeDesc(Sym.TypeDesc);

    if TD.Def is TRecordTypeDef then
    begin
      FieldList  := TRecordTypeDef(TD.Def).Fields;
      MethodList := nil;
    end
    else
    begin
      FieldList  := TClassTypeDef(TD.Def).Fields;
      MethodList := TClassTypeDef(TD.Def).Methods;

      



      if TClassTypeDef(TD.Def).ParentName <> '' then
      begin
        ParentSym := nil;
        
        if Pos('<', TClassTypeDef(TD.Def).ParentName) > 0 then
        begin
          IntfDesc := TInterfaceTypeDesc(
            FindTypeOrInstantiate(TClassTypeDef(TD.Def).ParentName));
          if IntfDesc <> nil then
          begin
            
            TClassTypeDef(TD.Def).ImplementsNames.Insert(
              0, TClassTypeDef(TD.Def).ParentName);
            TClassTypeDef(TD.Def).ParentName := '';
          end;
        end;
        if TClassTypeDef(TD.Def).ParentName <> '' then
        begin
          ParentSym := FTable.Lookup(TClassTypeDef(TD.Def).ParentName);
          if (ParentSym = nil) or not (ParentSym.TypeDesc is TRecordTypeDesc) then
            SemanticError(
              Format('Unknown parent class ''%s'' for ''%s''', TClassTypeDef(TD.Def).ParentName, TD.Name),
              TD.Line, TD.Col);
          ParentRT     := TRecordTypeDesc(ParentSym.TypeDesc);
          RT.Parent    := ParentRT;
          RT.CopyVTableFrom(ParentRT);
          for K := 0 to ParentRT.Fields.Count - 1 do
          begin
            FldInfo := TFieldInfo(ParentRT.Fields.Get(K));
            RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
          end;
        end;
      end;

      

      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Get(J));
          if MDecl.IsVirtual then
            RT.AddVTableSlot(MDecl.Name, '$' + TD.Name + '_' + MDecl.Name)
          else if MDecl.IsOverride then
            RT.OverrideVTableSlot(
              RT.FindVTableSlot(MDecl.Name),
              '$' + TD.Name + '_' + MDecl.Name);
        end;
    end;

    
    for J := 0 to FieldList.Count - 1 do
    begin
      FDecl   := TFieldDecl(FieldList.Get(J));
      FldType := FindTypeOrInstantiate(FDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field', FDecl.TypeName),
          FDecl.Line, FDecl.Col);
      FDecl.ResolvedType := FldType;
      
      if HasWeakAttribute(FDecl.Attributes) then
      begin
        if not ((FldType.Kind = tyClass) or (FldType.Kind = tyInterface)) then
          SemanticError(
            Format('[Weak] can only be applied to class or interface ' +
                   'fields, not ''%s''', FDecl.TypeName),
            FDecl.Line, FDecl.Col);
        FDecl.IsWeak := True;
      end;
      for K := 0 to FDecl.Names.Count - 1 do
      begin
        FldName := FDecl.Names.Get(K);
        RT.AddField(FldName, FldType);
        


        if FDecl.IsWeak then
          RT.FindField(FldName).IsWeak := True;
      end;
    end;

    
    if MethodList <> nil then
      for J := 0 to MethodList.Count - 1 do
      begin
        MDecl               := TMethodDecl(MethodList.Get(J));
        MDecl.OwnerTypeName := TD.Name;
        Key                 := TD.Name + '.' + MDecl.Name;
        FMethodIndex.AddObject(Key, MDecl);
        if SameText(MDecl.Name, 'Destroy') then
          RT.HasDestroyMethod := True;

        
        if MDecl.IsVirtual or MDecl.IsOverride then
        begin
          MDecl.VTableSlot := RT.FindVTableSlot(MDecl.Name);
          if MDecl.IsOverride and (MDecl.VTableSlot < 0) then
            SemanticError(
              Format('Method ''%s'' marked override but no virtual base method found', MDecl.Name),
              MDecl.Line, MDecl.Col);
        end;

        for K := 0 to MDecl.Params.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Get(K));
          ParType := FTable.FindType(Par.TypeName);
          if ParType = nil then
            SemanticError(
              Format('Unknown type ''%s'' for parameter ''%s''', Par.TypeName, Par.ParamName),
              MDecl.Line, MDecl.Col);
          Par.ResolvedType := ParType;
        end;

        if MDecl.ReturnTypeName <> '' then
        begin
          ParType := FTable.FindType(MDecl.ReturnTypeName);
          if ParType = nil then
            SemanticError(
              Format('Unknown return type ''%s'' for method ''%s''', MDecl.ReturnTypeName, MDecl.Name),
              MDecl.Line, MDecl.Col);
          MDecl.ResolvedReturnType := ParType;
        end;
      end;

    
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).Properties.Count - 1 do
      begin
        PropDecl := TPropertyDecl(TClassTypeDef(TD.Def).Properties.Get(J));
        PropType := FTable.FindType(PropDecl.TypeName);
        if PropType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for property ''%s''', PropDecl.TypeName, PropDecl.Name),
            PropDecl.Line, PropDecl.Col);
        PropInfo          := TPropertyInfo.Create;
        PropInfo.Name     := PropDecl.Name;
        PropInfo.TypeDesc := PropType;
        if PropDecl.ReadName <> '' then
        begin
          if RT.FindField(PropDecl.ReadName) <> nil then
            PropInfo.ReadField  := PropDecl.ReadName
          else
            PropInfo.ReadMethod := PropDecl.ReadName;
        end;
        if PropDecl.WriteName <> '' then
        begin
          if RT.FindField(PropDecl.WriteName) <> nil then
            PropInfo.WriteField  := PropDecl.WriteName
          else
            PropInfo.WriteMethod := PropDecl.WriteName;
        end;
        RT.AddProperty(PropInfo);
      end;

    
    if TD.Def is TClassTypeDef then
      for L := 0 to TClassTypeDef(TD.Def).ImplementsNames.Count - 1 do
      begin
        IntfName := TClassTypeDef(TD.Def).ImplementsNames.Get(L);
        IntfSym  := FTable.Lookup(IntfName);
        if IntfSym = nil then
        begin
          
          IntfDesc := TInterfaceTypeDesc(FindTypeOrInstantiate(IntfName));
          if IntfDesc = nil then
            SemanticError(
              Format('Unknown interface ''%s'' in implements list of ''%s''', IntfName, TD.Name),
              TD.Line, TD.Col);
          IntfSym := FTable.Lookup(IntfName);
        end;
        if (IntfSym = nil) or not (IntfSym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown interface ''%s'' in implements list of ''%s''', IntfName, TD.Name),
            TD.Line, TD.Col);
        IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
        RT.AddImplements(IntfDesc);
        for J := 0 to IntfDesc.MethodCount - 1 do
        begin
          Key := IntfDesc.MethodName(J);
          if RT.FindField(Key) = nil then
          begin
            
            MDecl := nil;
            if TD.Def is TClassTypeDef then
              for K := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
                if SameText(TMethodDecl(TClassTypeDef(TD.Def).Methods.Get(K)).Name, Key) then
                begin
                  MDecl := TMethodDecl(TClassTypeDef(TD.Def).Methods.Get(K));
                  Break;
                end;
            if MDecl = nil then
              SemanticError(
                Format('Class ''%s'' does not implement method ''%s'' from interface ''%s''', TD.Name, Key, IntfName),
                TD.Line, TD.Col);
          end;
        end;
      end;
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodBodies(ABlock: TBlock);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  RT:    TRecordTypeDesc;
  Sym:   TSymbol;
begin
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD  := TClassTypeDef(TD.Def);
    Sym := FTable.Lookup(TD.Name);
    if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
      Continue;
    RT := TRecordTypeDesc(Sym.TypeDesc);
    for J := 0 to CD.Methods.Count - 1 do
      AnalyseMethodDecl(TMethodDecl(CD.Methods.Get(J)), RT);
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodDecl(
  AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
var
  I:          Integer;
  Par:        TMethodParam;
  Sym:        TSymbol;
  SavedClass: TRecordTypeDesc;
begin
  SavedClass    := FCurrentClass;
  FCurrentClass := AClassType;
  FTable.PushScope;
  FScopeDepth := FScopeDepth + 1;
  try
    
    Sym := TSymbol.Create('Self', skVariable, AClassType);
    FTable.Define(Sym);

    
    if AMethod.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, AMethod.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    
    for I := 0 to AMethod.Params.Count - 1 do
    begin
      Par := TMethodParam(AMethod.Params.Get(I));
      if Par.ResolvedType = nil then
        SemanticError(
          Format('Parameter ''%s'' has unresolved type', Par.ParamName),
          AMethod.Line, AMethod.Col);
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate parameter name ''%s''', Par.ParamName),
          AMethod.Line, AMethod.Col);
      end;
    end;

    
    if AMethod.Body <> nil then
      AnalyseBlock(AMethod.Body);
  finally
    FScopeDepth := FScopeDepth - 1;
    FTable.PopScope;
    FCurrentClass := SavedClass;
  end;
end;

function TSemanticAnalyser.FindMethodDecl(
  const ATypeName, AMethodName: string): TMethodDecl;
var
  CurrName: string;
  Idx:      Integer;
  Key:      string;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
begin
  CurrName := ATypeName;
  while CurrName <> '' do
  begin
    Key := CurrName + '.' + AMethodName;
    Idx := FMethodIndex.IndexOf(Key);
    if Idx >= 0 then
    begin
      Result := TMethodDecl(FMethodIndex.GetObject(Idx));
      Exit;
    end;
    
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then
        CurrName := RT.Parent.Name
      else
        Break;
    end
    else
      Break;
  end;
  Result := nil;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecls(ABlock: TBlock);
var
  I, J:    Integer;
  ADecl:   TMethodDecl;
  Par:     TMethodParam;
  ParType: TTypeDesc;
  RetType: TTypeDesc;
  Sym:     TSymbol;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Get(I));
    
    if ADecl.OwnerTypeName <> '' then Continue;
    
    if ADecl.TypeParams <> nil then
    begin
      FGenericFuncTemplates.AddObject(ADecl.Name, ADecl);
      Continue;
    end;

    
    for J := 0 to ADecl.Params.Count - 1 do
    begin
      Par     := TMethodParam(ADecl.Params.Get(J));
      ParType := FTable.FindType(Par.TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for parameter ''%s'' of ''%s''', Par.TypeName, Par.ParamName, ADecl.Name),
          ADecl.Line, ADecl.Col);
      Par.ResolvedType := ParType;
    end;

    
    if ADecl.ReturnTypeName <> '' then
    begin
      RetType := FTable.FindType(ADecl.ReturnTypeName);
      if RetType = nil then
        SemanticError(
          Format('Unknown return type ''%s'' for function ''%s''', ADecl.ReturnTypeName, ADecl.Name),
          ADecl.Line, ADecl.Col);
      ADecl.ResolvedReturnType := RetType;
    end;

    

    J := FProcIndex.IndexOf(ADecl.Name);
    if (J >= 0) and (TMethodDecl(FProcIndex.GetObject(J)).Body = nil) then
    begin
      FProcIndex.SetObject(J, ADecl);
      Continue;
    end;

    
    FProcIndex.AddObject(ADecl.Name, ADecl);

    
    if ADecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(ADecl.Name, skFunction, ADecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(ADecl.Name, skProcedure, nil);

    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      SemanticError(
        Format('Duplicate identifier ''%s''', ADecl.Name),
        ADecl.Line, ADecl.Col);
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecl(ADecl: TMethodDecl);
var
  I:   Integer;
  Par: TMethodParam;
  Sym: TSymbol;
begin
  FTable.PushScope;
  FScopeDepth := FScopeDepth + 1;
  try
    
    if ADecl.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, ADecl.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      Par := TMethodParam(ADecl.Params.Get(I));
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate parameter name ''%s''', Par.ParamName),
          ADecl.Line, ADecl.Col);
      end;
    end;

    AnalyseBlock(ADecl.Body);
  finally
    FScopeDepth := FScopeDepth - 1;
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneBodies(ABlock: TBlock);
var
  I:     Integer;
  ADecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Get(I));
    
    if ADecl.OwnerTypeName <> '' then Continue;
    
    if ADecl.TypeParams <> nil then Continue;
    
    if ADecl.Body = nil then Continue;
    AnalyseStandaloneDecl(ADecl);
  end;
end;

procedure TSemanticAnalyser.AnalyseVarDecls(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  Typ:     TTypeDesc;
  VarName: string;
  Sym:     TSymbol;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Get(I));

    Typ := FindTypeOrInstantiate(Decl.TypeName);
    if Typ = nil then
      SemanticError(
        Format('Unknown type ''%s''', Decl.TypeName),
        Decl.Line, Decl.Col);

    Decl.ResolvedType := Typ;

    



    if HasWeakAttribute(Decl.Attributes) then
    begin
      if not ((Typ.Kind = tyClass) or (Typ.Kind = tyInterface)) then
        SemanticError(
          Format('[Weak] can only be applied to class or interface types, ' +
                 'not ''%s''', Decl.TypeName),
          Decl.Line, Decl.Col);
      Decl.IsWeak := True;
    end;

    
    Decl.IsGlobal := (FScopeDepth = 1);  
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Get(J);
      Sym := TSymbol.Create(VarName, skVariable, Typ);
      Sym.IsWeak   := Decl.IsWeak;
      Sym.IsGlobal := Decl.IsGlobal;
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate identifier ''%s''', VarName),
          Decl.Line, Decl.Col);
      end;
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseCompoundBody(ABody: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to ABody.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABody.Stmts.Get(I)));
end;

procedure TSemanticAnalyser.AnalyseStmts(ABlock: TBlock);
var
  I: Integer;
begin
  for I := 0 to ABlock.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABlock.Stmts.Get(I)));
end;

procedure TSemanticAnalyser.AnalyseStmt(AStmt: TASTStmt);
var
  IfS:       TIfStmt;
  CmpS:      TCompoundStmt;
  ForS:      TForStmt;
  I:         Integer;
  CondType:  TTypeDesc;
  VarSym:    TSymbol;
  StartType: TTypeDesc;
  EndType:   TTypeDesc;
begin
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    VarSym := FTable.Lookup(ForS.VarName);
    if VarSym = nil then
      SemanticError(
        Format('Undeclared loop variable ''%s''', ForS.VarName),
        ForS.Line, ForS.Col);
    if VarSym.Kind <> skVariable then
      SemanticError(
        Format('''%s'' is not a variable', ForS.VarName),
        ForS.Line, ForS.Col);
    if not VarSym.TypeDesc.IsOrdinal then
      SemanticError(
        Format('Loop variable ''%s'' must be an ordinal type, got ''%s''', ForS.VarName, VarSym.TypeDesc.Name),
        ForS.Line, ForS.Col);
    StartType := AnalyseExpr(ForS.StartExpr);
    CheckTypesMatch(VarSym.TypeDesc, StartType,
      'for-loop start expression', ForS.Line, ForS.Col);
    EndType := AnalyseExpr(ForS.EndExpr);
    CheckTypesMatch(VarSym.TypeDesc, EndType,
      'for-loop end expression', ForS.Line, ForS.Col);
    FLoopDepth := FLoopDepth + 1;
    try
      AnalyseStmt(ForS.Body);
    finally
      FLoopDepth := FLoopDepth - 1;
    end;
  end
  else if AStmt is TWhileStmt then
  begin
    begin
      CondType := AnalyseExpr(TWhileStmt(AStmt).Condition);
      if CondType.Kind <> tyBoolean then
        SemanticError(
          Format('while condition must be Boolean, got ''%s''', CondType.Name),
          AStmt.Line, AStmt.Col);
      FLoopDepth := FLoopDepth + 1;
      try
        AnalyseStmt(TWhileStmt(AStmt).Body);
      finally
        FLoopDepth := FLoopDepth - 1;
      end;
    end;
  end
  else if AStmt is TExitStmt then
  begin
    

  end
  else if AStmt is TBreakStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''break'' is not inside a loop', AStmt.Line, AStmt.Col);
  end
  else if AStmt is TContinueStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''continue'' is not inside a loop', AStmt.Line, AStmt.Col);
  end
  else if AStmt is TIfStmt then
  begin
    IfS      := TIfStmt(AStmt);
    CondType := AnalyseExpr(IfS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('if condition must be Boolean, got ''%s''', CondType.Name),
        IfS.Line, IfS.Col);
    AnalyseStmt(IfS.ThenStmt);
    if IfS.ElseStmt <> nil then
      AnalyseStmt(IfS.ElseStmt);
  end
  else if AStmt is TCompoundStmt then
  begin
    CmpS := TCompoundStmt(AStmt);
    for I := 0 to CmpS.Stmts.Count - 1 do
      AnalyseStmt(TASTStmt(CmpS.Stmts.Get(I)));
  end
  else if AStmt is TTryFinallyStmt then
  begin
    begin
      AnalyseCompoundBody(TTryFinallyStmt(AStmt).TryBody);
      AnalyseCompoundBody(TTryFinallyStmt(AStmt).FinallyBody);
    end;
  end
  else if AStmt is TTryExceptStmt then
  begin
    begin
      AnalyseCompoundBody(TTryExceptStmt(AStmt).TryBody);
      AnalyseCompoundBody(TTryExceptStmt(AStmt).ExceptBody);
    end;
  end
  else if AStmt is TRaiseStmt then
  begin
    begin
      if TRaiseStmt(AStmt).Expr <> nil then
      begin
        CondType := AnalyseExpr(TRaiseStmt(AStmt).Expr);
        if CondType.Kind <> tyClass then
          SemanticError(
            Format('raise expression must be a class instance, got ''%s''', CondType.Name),
            AStmt.Line, AStmt.Col);
      end;
    end;
  end
  else if AStmt is TFieldAssignment then
    AnalyseFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TAssignment then
    AnalyseAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    AnalyseMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TInheritedCallStmt then
    AnalyseInheritedCall(TInheritedCallStmt(AStmt))
  else if AStmt is TPointerWriteStmt then
    AnalysePointerWriteStmt(TPointerWriteStmt(AStmt))
  else if AStmt is TProcCall then
    AnalyseProcCall(TProcCall(AStmt))
  else if AStmt is TCaseStmt then
    AnalyseCaseStmt(TCaseStmt(AStmt));
end;

procedure TSemanticAnalyser.AnalyseMethodCall(ACall: TMethodCallStmt);
var
  ObjSym:  TSymbol;
  RT:      TRecordTypeDesc;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  I:       Integer;
  ObjType: TTypeDesc;
begin
  
  if ACall.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(ACall.ObjExpr);
    if not (((ObjType.Kind = tyClass) or (ObjType.Kind = tyInterface))) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class or interface', ACall.Name),
        ACall.Line, ACall.Col);
    RT := TRecordTypeDesc(ObjType);
    MDecl := FindMethodDecl(RT.Name, ACall.Name);
    if (MDecl = nil) and SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;
      Exit;
    end;
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', RT.Name, ACall.Name),
        ACall.Line, ACall.Col);
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
      Par     := TMethodParam(MDecl.Params.Get(I));
      CheckTypesMatch(Par.ResolvedType, ArgType,
        Format('argument %d of ''%s''', I + 1, ACall.Name),
        ACall.Line, ACall.Col);
    end;
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := MDecl;
    Exit;
  end;

  ObjSym := FTable.Lookup(ACall.ObjectName);
  if ObjSym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      ACall.ImplicitBaseInfo :=
        FCurrentClass.FindField(ACall.ObjectName);
      if (ACall.ImplicitBaseInfo <> nil) and
         (((ACall.ImplicitBaseInfo.TypeDesc.Kind = tyClass) or (ACall.ImplicitBaseInfo.TypeDesc.Kind = tyInterface))) then
      begin
        ACall.IsImplicitSelf := True;
        RT := TRecordTypeDesc(ACall.ImplicitBaseInfo.TypeDesc);
        MDecl := FindMethodDecl(RT.Name, ACall.Name);
        if (MDecl = nil) and SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
        begin
          ACall.ResolvedClassType := RT;
          ACall.ResolvedMethod    := nil;
          Exit;
        end;
        if MDecl = nil then
          SemanticError(
            Format('Class ''%s'' has no method ''%s''', RT.Name, ACall.Name),
            ACall.Line, ACall.Col);
        if ACall.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count),
            ACall.Line, ACall.Col);
        for I := 0 to ACall.Args.Count - 1 do
        begin
          ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
          Par     := TMethodParam(MDecl.Params.Get(I));
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', I + 1, ACall.Name),
            ACall.Line, ACall.Col);
        end;
        ACall.ResolvedClassType := RT;
        ACall.ResolvedMethod    := MDecl;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', ACall.ObjectName),
      ACall.Line, ACall.Col);
  end;
  if not (((ObjSym.Kind = skVariable) or (ObjSym.Kind = skParameter) or (ObjSym.Kind = skVarParameter))) then
    SemanticError(
      Format('''%s'' is not a variable', ACall.ObjectName),
      ACall.Line, ACall.Col);
  if not (((ObjSym.TypeDesc.Kind = tyClass) or (ObjSym.TypeDesc.Kind = tyInterface))) then
    SemanticError(
      Format('''%s'' is not a class or interface variable', ACall.ObjectName),
      ACall.Line, ACall.Col);

  
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    if not TInterfaceTypeDesc(ObjSym.TypeDesc).HasMethod(ACall.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''', ObjSym.TypeDesc.Name, ACall.Name),
        ACall.Line, ACall.Col);
    
    ACall.ResolvedClassType := ObjSym.TypeDesc;
    ACall.ResolvedMethod    := nil;  
    ACall.IsGlobal          := ObjSym.IsGlobal;
    Exit;
  end;

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  MDecl := FindMethodDecl(RT.Name, ACall.Name);
  if MDecl = nil then
  begin
    
    if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;
      ACall.IsGlobal          := ObjSym.IsGlobal;
      Exit;
    end;
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', RT.Name, ACall.Name),
      ACall.Line, ACall.Col);
  end;

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
    Par     := TMethodParam(MDecl.Params.Get(I));
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', I + 1, ACall.Name),
      ACall.Line, ACall.Col);
  end;

  ACall.ResolvedClassType := RT;
  ACall.ResolvedMethod    := MDecl;
  ACall.IsGlobal          := ObjSym.IsGlobal;
end;

procedure TSemanticAnalyser.AnalyseAssignment(AAssign: TAssignment);
var
  VarSym:  TSymbol;
  FldInfo: TFieldInfo;
  ExprType: TTypeDesc;
begin
  VarSym := FTable.Lookup(AAssign.Name);
  if VarSym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      FldInfo := FCurrentClass.FindField(AAssign.Name);
      if FldInfo <> nil then
      begin
        AAssign.ImplicitSelfField := FldInfo;
        AAssign.ResolvedLhsType   := FldInfo.TypeDesc;
        ExprType := AnalyseExpr(AAssign.Expr);
        CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', AAssign.Name),
      AAssign.Line, AAssign.Col);
  end;
  if not (((VarSym.Kind = skVariable) or (VarSym.Kind = skVarParameter))) then
    SemanticError(
      Format('''%s'' is not a variable', AAssign.Name),
      AAssign.Line, AAssign.Col);

  AAssign.IsVarParam      := (VarSym.Kind = skVarParameter);
  AAssign.ResolvedLhsType := VarSym.TypeDesc;
  AAssign.IsWeakLhs       := VarSym.IsWeak;
  AAssign.IsGlobal        := VarSym.IsGlobal;

  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(VarSym.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseInheritedCall(ACall: TInheritedCallStmt);
var
  ParentType: TRecordTypeDesc;
  MDecl:      TMethodDecl;
  ArgType:    TTypeDesc;
  Par:        TMethodParam;
  I:          Integer;
begin
  if FCurrentClass = nil then
    SemanticError('''inherited'' used outside a method body',
      ACall.Line, ACall.Col);

  if FCurrentClass.Parent = nil then
    SemanticError(
      Format('Class ''%s'' has no parent; ''inherited'' is not valid', FCurrentClass.Name),
      ACall.Line, ACall.Col);

  ParentType := FCurrentClass.Parent;
  MDecl := FindMethodDecl(ParentType.Name, ACall.Name);
  if MDecl = nil then
    SemanticError(
      Format('Parent class ''%s'' has no method ''%s''', ParentType.Name, ACall.Name),
      ACall.Line, ACall.Col);

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d', ParentType.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
    Par     := TMethodParam(MDecl.Params.Get(I));
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of inherited ''%s''', I + 1, ACall.Name),
      ACall.Line, ACall.Col);
  end;

  ACall.ResolvedParentType := ParentType;
  ACall.ResolvedMethod     := MDecl;
end;

procedure TSemanticAnalyser.AnalyseFieldAssignment(AAssign: TFieldAssignment);
var
  RecSym:   TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  BaseInfo: TFieldInfo;
  BaseType: TTypeDesc;
  PropInfo: TPropertyInfo;
  ExprType: TTypeDesc;
  ObjType:  TTypeDesc;
begin
  
  if AAssign.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(AAssign.ObjExpr);
    if not (((ObjType.Kind = tyRecord) or (ObjType.Kind = tyClass))) then
      SemanticError(
        Format('Field assignment: expression is not a record or class (got %s)', ObjType.Name),
        AAssign.Line, AAssign.Col);
    RT      := TRecordTypeDesc(ObjType);
    FldInfo := RT.FindField(AAssign.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAssign.FieldName);
      if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
      begin
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else
        SemanticError(
          Format('Type ''%s'' has no field ''%s''', ObjType.Name, AAssign.FieldName),
          AAssign.Line, AAssign.Col);
    end;
    AAssign.IsClassAccess := ObjType.Kind = tyClass;
    AAssign.FieldInfo     := FldInfo;
    ExprType := AnalyseExpr(AAssign.Expr);
    CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
      AAssign.Line, AAssign.Col);
    Exit;
  end;
  RecSym := FTable.Lookup(AAssign.RecordName);
  if RecSym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      BaseInfo := FCurrentClass.FindField(AAssign.RecordName);
      if (BaseInfo <> nil) and
         (((BaseInfo.TypeDesc.Kind = tyRecord) or (BaseInfo.TypeDesc.Kind = tyClass))) then
      begin
        AAssign.IsImplicitSelf   := True;
        AAssign.ImplicitBaseInfo := BaseInfo;
        AAssign.IsClassAccess    := BaseInfo.TypeDesc.Kind = tyClass;
        BaseType := BaseInfo.TypeDesc;
        RT       := TRecordTypeDesc(BaseType);
        FldInfo  := RT.FindField(AAssign.FieldName);
        if FldInfo = nil then
        begin
          PropInfo := RT.FindProperty(AAssign.FieldName);
          if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
          begin
            AAssign.FieldName := PropInfo.WriteField;
            FldInfo           := RT.FindField(PropInfo.WriteField);
          end
          else
            SemanticError(
              Format('Type ''%s'' has no field ''%s''', AAssign.RecordName, AAssign.FieldName),
              AAssign.Line, AAssign.Col);
        end;
        AAssign.FieldInfo := FldInfo;
        ExprType := AnalyseExpr(AAssign.Expr);
        CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
          AAssign.Line, AAssign.Col);
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', AAssign.RecordName),
      AAssign.Line, AAssign.Col);
  end;
  if not ((RecSym.Kind = skVariable) or (RecSym.Kind = skParameter)) then
    SemanticError(
      Format('''%s'' is not a variable', AAssign.RecordName),
      AAssign.Line, AAssign.Col);
  if not (((RecSym.TypeDesc.Kind = tyRecord) or (RecSym.TypeDesc.Kind = tyClass))) then
    SemanticError(
      Format('''%s'' is not a record or class variable', AAssign.RecordName),
      AAssign.Line, AAssign.Col);

  AAssign.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAssign.IsGlobal      := RecSym.IsGlobal;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAssign.FieldName);
  if FldInfo = nil then
  begin
    
    PropInfo := RT.FindProperty(AAssign.FieldName);
    if PropInfo <> nil then
    begin
      if PropInfo.WriteField <> '' then
      begin
        
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else if PropInfo.WriteMethod <> '' then
        SemanticError(
          Format('Method-backed property write not yet supported for ''%s''', AAssign.FieldName),
          AAssign.Line, AAssign.Col)
      else
        SemanticError(
          Format('Property ''%s'' is read-only', AAssign.FieldName),
          AAssign.Line, AAssign.Col);
    end
    else
      SemanticError(
        Format('Type ''%s'' has no field ''%s''', AAssign.RecordName, AAssign.FieldName),
        AAssign.Line, AAssign.Col);
  end;

  AAssign.FieldInfo := FldInfo;
  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
    AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseProcCall(ACall: TProcCall);
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
begin
  Sym := FTable.Lookup(ACall.Name);
  if Sym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      MDecl := FindMethodDecl(FCurrentClass.Name, ACall.Name);
      if MDecl <> nil then
      begin
        if ACall.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d', FCurrentClass.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count),
            ACall.Line, ACall.Col);
        for I := 0 to ACall.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Get(I));
          ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', I + 1, ACall.Name),
            ACall.Line, ACall.Col);
        end;
        ACall.ResolvedDecl         := MDecl;
        ACall.IsImplicitSelfMethod := True;
        Exit;
      end;
    end;
    
    if Pos('<', ACall.Name) > 0 then
      InstantiateGenericFunc(ACall.Name);
    Sym := FTable.Lookup(ACall.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared procedure ''%s''', ACall.Name),
        ACall.Line, ACall.Col);
  end;
  if not (((Sym.Kind = skProcedure) or (Sym.Kind = skFunction))) then
    SemanticError(
      Format('''%s'' is not a procedure or function', ACall.Name),
      ACall.Line, ACall.Col);

  
  Idx := FProcIndex.IndexOf(ACall.Name);
  if Idx >= 0 then
  begin
    MDecl := TMethodDecl(FProcIndex.GetObject(Idx));
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Procedure ''%s'' expects %d argument(s) but got %d', ACall.Name, MDecl.Params.Count, ACall.Args.Count),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if Par.IsVarParam then
      begin
        
        if not (TASTExpr(ACall.Args.Get(I)) is TIdentExpr) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable', I + 1, ACall.Name),
            ACall.Line, ACall.Col);
        ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', I + 1, ACall.Name),
          ACall.Line, ACall.Col);
      end
      else
      begin
        ArgType := AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('argument %d of ''%s''', I + 1, ACall.Name),
          ACall.Line, ACall.Col);
      end;
    end;
    ACall.ResolvedDecl := MDecl;
  end
  else
  begin
    
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args.Get(I)));
  end;
end;

function TSemanticAnalyser.AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
begin
  
  if SameText(AExpr.Name, 'SizeOf') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SizeOf requires exactly one argument', AExpr.Line, AExpr.Col);
    if AExpr.Args.Get(0) is TIdentExpr then
    begin
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Get(0)).Name);
      if (Sym <> nil) and (Sym.Kind = skType) then
        TIdentExpr(AExpr.Args.Get(0)).ResolvedType := Sym.TypeDesc;
    end;
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  Sym := FTable.Lookup(AExpr.Name);
  if Sym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      MDecl := FindMethodDecl(FCurrentClass.Name, AExpr.Name);
      if MDecl <> nil then
      begin
        if AExpr.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d', FCurrentClass.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Get(I));
          ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', I + 1, AExpr.Name),
            AExpr.Line, AExpr.Col);
        end;
        AExpr.ResolvedDecl         := MDecl;
        AExpr.IsImplicitSelfMethod := True;
        Result := MDecl.ResolvedReturnType;
        AExpr.ResolvedType := Result;
        Exit;
      end;
    end;
    
    if Pos('<', AExpr.Name) > 0 then
      InstantiateGenericFunc(AExpr.Name);
    Sym := FTable.Lookup(AExpr.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared function ''%s''', AExpr.Name),
        AExpr.Line, AExpr.Col);
  end;
  
  if Sym.Kind = skType then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(
        Format('Type cast ''%s'' expects exactly one argument', AExpr.Name),
        AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := Sym.TypeDesc;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if Sym.Kind <> skFunction then
    SemanticError(
      Format('''%s'' is not a function', AExpr.Name),
      AExpr.Line, AExpr.Col);

  
  if SameText(AExpr.Name, 'GetMem') or SameText(AExpr.Name, 'ReallocMem') then
  begin
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  

  if SameText(AExpr.Name, 'Length') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Length requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    if ArgType.Kind <> tyString then
      SemanticError('Length argument must be a string', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Pos') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('Pos requires exactly two arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Copy') then
  begin
    if AExpr.Args.Count <> 3 then
      SemanticError('Copy requires exactly three arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(2)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UpperCase') or SameText(AExpr.Name, 'LowerCase')
     or SameText(AExpr.Name, 'Trim') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'SameText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('SameText requires exactly two arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'IntToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('IntToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToInt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToInt requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Format') then
  begin
    if AExpr.Args.Count < 1 then
      SemanticError('Format requires at least one argument', AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'OrdAt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('OrdAt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Chr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Chr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'CompareStr') or SameText(AExpr.Name, 'CompareText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError(AExpr.Name + ' requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  
  if SameText(AExpr.Name, 'ParamCount') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('ParamCount takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ParamStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ParamStr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  
  if SameText(AExpr.Name, 'ReadFile') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ReadFile requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'FileExists') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('FileExists requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  
  if SameText(AExpr.Name, 'GetEnvVar') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('GetEnvVar requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Exec') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Exec requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ChangeFileExt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('ChangeFileExt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    AnalyseExpr(TASTExpr(AExpr.Args.Get(1)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ExtractFileName') or
     SameText(AExpr.Name, 'ExtractFilePath') or
     SameText(AExpr.Name, 'IncludeTrailingPathDelimiter') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', AExpr.Name),
                    AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Get(0)));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  Idx := FProcIndex.IndexOf(AExpr.Name);
  if Idx < 0 then
    SemanticError(
      Format('Cannot find declaration for function ''%s''', AExpr.Name),
      AExpr.Line, AExpr.Col);

  MDecl := TMethodDecl(FProcIndex.GetObject(Idx));

  if AExpr.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Function ''%s'' expects %d argument(s) but got %d', AExpr.Name, MDecl.Params.Count, AExpr.Args.Count),
      AExpr.Line, AExpr.Col);

  for I := 0 to AExpr.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    Par     := TMethodParam(MDecl.Params.Get(I));
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', I + 1, AExpr.Name),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedDecl := MDecl;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
var
  ObjSym:   TSymbol;
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  Par:      TMethodParam;
  ArgType:  TTypeDesc;
  I:        Integer;
  IntfDesc: TInterfaceTypeDesc;
  ObjType:  TTypeDesc;
begin
  
  if AExpr.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(AExpr.ObjExpr);
    if not (((ObjType.Kind = tyClass) or (ObjType.Kind = tyInterface))) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class or interface', AExpr.Name),
        AExpr.Line, AExpr.Col);
    if ObjType.Kind = tyInterface then
    begin
      IntfDesc := TInterfaceTypeDesc(ObjType);
      if not IntfDesc.HasMethod(AExpr.Name) then
        SemanticError(
          Format('Interface ''%s'' has no method ''%s''', ObjType.Name, AExpr.Name),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
        AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
      AExpr.ResolvedClassType := ObjType;
      AExpr.ResolvedMethod    := nil;
      Result := FindTypeOrInstantiate(
        IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
      if Result = nil then Result := FTable.TypeInteger;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    RT    := TRecordTypeDesc(ObjType);
    MDecl := FindMethodDecl(RT.Name, AExpr.Name);
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', RT.Name, AExpr.Name),
        AExpr.Line, AExpr.Col);
    if AExpr.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
      Par     := TMethodParam(MDecl.Params.Get(I));
      CheckTypesMatch(Par.ResolvedType, ArgType,
        Format('argument %d of ''%s''', I + 1, AExpr.Name),
        AExpr.Line, AExpr.Col);
    end;
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := MDecl;
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  ObjSym := FTable.Lookup(AExpr.ObjectName);
  if ObjSym = nil then
  begin
    

    if FCurrentClass <> nil then
    begin
      ObjType := nil;
      ObjSym  := nil;
      begin
        
        AExpr.ObjExpr := TIdentExpr.Create;
        TIdentExpr(AExpr.ObjExpr).Name := AExpr.ObjectName;
        TIdentExpr(AExpr.ObjExpr).Line := AExpr.Line;
        TIdentExpr(AExpr.ObjExpr).Col  := AExpr.Col;
        try
          ObjType := AnalyseExpr(AExpr.ObjExpr);
        except
          AExpr.ObjExpr.Free;
          AExpr.ObjExpr := nil;
          SemanticError(
            Format('Undeclared identifier ''%s''', AExpr.ObjectName),
            AExpr.Line, AExpr.Col);
        end;
      end;
      if (ObjType = nil) or not (((ObjType.Kind = tyClass) or (ObjType.Kind = tyInterface))) then
      begin
        AExpr.ObjExpr.Free;
        AExpr.ObjExpr := nil;
        SemanticError(
          Format('Undeclared identifier ''%s''', AExpr.ObjectName),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.ObjectName := '';
      if ObjType.Kind = tyInterface then
      begin
        IntfDesc := TInterfaceTypeDesc(ObjType);
        if not IntfDesc.HasMethod(AExpr.Name) then
          SemanticError(
            Format('Interface ''%s'' has no method ''%s''', ObjType.Name, AExpr.Name),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
          AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
        AExpr.ResolvedClassType := ObjType;
        AExpr.ResolvedMethod    := nil;
        Result := FindTypeOrInstantiate(
          IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
        if Result = nil then Result := FTable.TypeInteger;
        AExpr.ResolvedType := Result;
        Exit;
      end;
      RT    := TRecordTypeDesc(ObjType);
      MDecl := FindMethodDecl(RT.Name, AExpr.Name);
      if MDecl = nil then
        SemanticError(
          Format('Class ''%s'' has no method ''%s''', RT.Name, AExpr.Name),
          AExpr.Line, AExpr.Col);
      if AExpr.Args.Count <> MDecl.Params.Count then
        SemanticError(
          Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
        Par     := TMethodParam(MDecl.Params.Get(I));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('argument %d of ''%s''', I + 1, AExpr.Name),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := MDecl;
      Result := MDecl.ResolvedReturnType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', AExpr.ObjectName),
      AExpr.Line, AExpr.Col);
  end;

  

  if (ObjSym.Kind = skType) and
     (SameText(AExpr.Name, 'Create') or
      (Pos('Create', AExpr.Name) = 1)) then
  begin
    if ObjSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot construct non-class type ''%s''', AExpr.ObjectName),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    
    MDecl := FindMethodDecl(AExpr.ObjectName, AExpr.Name);
    AExpr.ResolvedMethod    := MDecl;
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.IsConstructorCall := True;
    Result := ObjSym.TypeDesc;
    Exit;
  end;

  if not (((ObjSym.Kind = skVariable) or (ObjSym.Kind = skParameter) or (ObjSym.Kind = skVarParameter))) then
    SemanticError(
      Format('''%s'' is not a variable', AExpr.ObjectName),
      AExpr.Line, AExpr.Col);
  if not (((ObjSym.TypeDesc.Kind = tyClass) or (ObjSym.TypeDesc.Kind = tyInterface))) then
    SemanticError(
      Format('''%s'' is not a class or interface variable', AExpr.ObjectName),
      AExpr.Line, AExpr.Col);

  
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(ObjSym.TypeDesc);
    if not IntfDesc.HasMethod(AExpr.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''', ObjSym.TypeDesc.Name, AExpr.Name),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.ResolvedMethod    := nil;  
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    
    Result := FindTypeOrInstantiate(
      IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
    if Result = nil then
      Result := FTable.TypeInteger;  
    Exit;
  end;

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  MDecl := FindMethodDecl(RT.Name, AExpr.Name);
  if MDecl = nil then
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', RT.Name, AExpr.Name),
      AExpr.Line, AExpr.Col);
  if MDecl.ResolvedReturnType = nil then
    SemanticError(
      Format('Method ''%s.%s'' is a procedure (no return value)', RT.Name, AExpr.Name),
      AExpr.Line, AExpr.Col);

  if AExpr.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d', RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count),
      AExpr.Line, AExpr.Col);

  for I := 0 to AExpr.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Get(I)));
    Par     := TMethodParam(MDecl.Params.Get(I));
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', I + 1, AExpr.Name),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedClassType := RT;
  AExpr.ResolvedMethod    := MDecl;
  AExpr.IsGlobal          := ObjSym.IsGlobal;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
var
  Sym:       TSymbol;
  FldInfo:   TFieldInfo;
  PropInfo:  TPropertyInfo;
  NoArgIdx:  Integer;
begin
  if AExpr is TNilLiteral then
    Result := FTable.TypeNil
  else if AExpr is TIntLiteral then
    Result := FTable.TypeInteger
  else if AExpr is TStringLiteral then
    Result := FTable.TypeString
  else if AExpr is TIdentExpr then
  begin
    Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if Sym = nil then
    begin
      
      if FCurrentClass <> nil then
      begin
        FldInfo := FCurrentClass.FindField(TIdentExpr(AExpr).Name);
        if FldInfo <> nil then
        begin
          TIdentExpr(AExpr).IsImplicitSelf   := True;
          TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
          Result := FldInfo.TypeDesc;
          AExpr.ResolvedType := Result;
          Exit;
        end;
        
        TIdentExpr(AExpr).ImplicitMethodDecl :=
          FindMethodDecl(FCurrentClass.Name, TIdentExpr(AExpr).Name);
        if TIdentExpr(AExpr).ImplicitMethodDecl <> nil then
        begin
          TIdentExpr(AExpr).IsImplicitSelfMethod := True;
          Result :=
            TMethodDecl(TIdentExpr(AExpr).ImplicitMethodDecl).ResolvedReturnType;
          AExpr.ResolvedType := Result;
          Exit;
        end;
        
        FldInfo := nil;  
        begin
          PropInfo := FCurrentClass.FindProperty(TIdentExpr(AExpr).Name);
          if PropInfo <> nil then
          begin
            if PropInfo.ReadMethod <> '' then
            begin
              TIdentExpr(AExpr).ImplicitMethodDecl :=
                FindMethodDecl(FCurrentClass.Name, PropInfo.ReadMethod);
              if TIdentExpr(AExpr).ImplicitMethodDecl <> nil then
              begin
                TIdentExpr(AExpr).IsImplicitSelfMethod := True;
                TIdentExpr(AExpr).Name := PropInfo.ReadMethod;
                Result := PropInfo.TypeDesc;
                AExpr.ResolvedType := Result;
                Exit;
              end;
            end
            else if PropInfo.ReadField <> '' then
            begin
              FldInfo := FCurrentClass.FindField(PropInfo.ReadField);
              if FldInfo <> nil then
              begin
                TIdentExpr(AExpr).IsImplicitSelf := True;
                TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
                Result := FldInfo.TypeDesc;
                AExpr.ResolvedType := Result;
                Exit;
              end;
            end;
          end;
        end;
      end;
      SemanticError(
        Format('Undeclared identifier ''%s''', TIdentExpr(AExpr).Name),
        AExpr.Line, AExpr.Col);
    end;
    TIdentExpr(AExpr).IsVarParam := (Sym.Kind = skVarParameter);
    TIdentExpr(AExpr).IsGlobal  := Sym.IsGlobal;
    if Sym.Kind = skConstant then
    begin
      TIdentExpr(AExpr).IsConstant  := True;
      TIdentExpr(AExpr).ConstValue  := Sym.ConstValue;
      TIdentExpr(AExpr).ConstString := Sym.ConstString;
    end;
    
    if (Sym.Kind = skFunction) and (Sym.TypeDesc <> nil) then
    begin
      TIdentExpr(AExpr).IsNoArgFuncCall := True;
      NoArgIdx := FProcIndex.IndexOf(TIdentExpr(AExpr).Name);
      if NoArgIdx >= 0 then
        TIdentExpr(AExpr).NoArgFuncDecl := FProcIndex.GetObject(NoArgIdx);
    end;
    Result := Sym.TypeDesc;
  end
  else if AExpr is TFuncCallExpr then
    Result := AnalyseFuncCallExpr(TFuncCallExpr(AExpr))
  else if AExpr is TMethodCallExpr then
    Result := AnalyseMethodCallExpr(TMethodCallExpr(AExpr))
  else if AExpr is TFieldAccessExpr then
    Result := AnalyseFieldAccess(TFieldAccessExpr(AExpr))
  else if AExpr is TBinaryExpr then
    Result := AnalyseBinaryExpr(TBinaryExpr(AExpr))
  else if AExpr is TIsExpr then
    Result := AnalyseIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := AnalyseAsExpr(TAsExpr(AExpr))
  else if AExpr is TDerefExpr then
    Result := AnalyseDerefExpr(TDerefExpr(AExpr))
  else if AExpr is TNotExpr then
  begin
    Result := AnalyseExpr(TNotExpr(AExpr).Expr);
    if Result.Kind <> tyBoolean then
      SemanticError(
        Format('''not'' requires a Boolean operand, got ''%s''', Result.Name),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
  end
  else
    SemanticError('Unknown expression node', AExpr.Line, AExpr.Col);

  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
var
  RecSym:   TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  PropInfo: TPropertyInfo;
  BaseType: TTypeDesc;
begin
  


  if AAccess.Base <> nil then
  begin
    BaseType := AnalyseExpr(AAccess.Base);
    if not (((BaseType.Kind = tyRecord) or (BaseType.Kind = tyClass))) then
      SemanticError(
        Format('Field access ''.%s'' requires a record or class base, got ''%s''', AAccess.FieldName, BaseType.Name),
        AAccess.Line, AAccess.Col);
    AAccess.IsClassAccess := BaseType.Kind = tyClass;
    RT      := TRecordTypeDesc(BaseType);
    FldInfo := RT.FindField(AAccess.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAccess.FieldName);
      if (PropInfo <> nil) and (PropInfo.ReadField <> '') then
      begin
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        Result := PropInfo.TypeDesc;
        Exit;
      end;
      
      AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
      if AAccess.ResolvedMethod <> nil then
      begin
        AAccess.IsMethodCall := True;
        Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
        Exit;
      end;
      SemanticError(
        Format('Type ''%s'' has no field ''%s''', BaseType.Name, AAccess.FieldName),
        AAccess.Line, AAccess.Col);
    end;
    AAccess.FieldInfo := FldInfo;
    Result := FldInfo.TypeDesc;
    Exit;
  end;

  RecSym := FTable.Lookup(AAccess.RecordName);
  if RecSym = nil then
  begin
    
    if FCurrentClass <> nil then
    begin
      FldInfo := FCurrentClass.FindField(AAccess.RecordName);
      if (FldInfo <> nil) and
         (((FldInfo.TypeDesc.Kind = tyRecord) or (FldInfo.TypeDesc.Kind = tyClass))) then
      begin
        AAccess.IsImplicitSelf   := True;
        AAccess.ImplicitBaseInfo := FldInfo;
        AAccess.IsClassAccess    := FldInfo.TypeDesc.Kind = tyClass;
        RT := TRecordTypeDesc(FldInfo.TypeDesc);
        AAccess.FieldInfo := RT.FindField(AAccess.FieldName);
        if AAccess.FieldInfo = nil then
        begin
          
          PropInfo := RT.FindProperty(AAccess.FieldName);
          if (PropInfo <> nil) and (PropInfo.ReadField <> '') then
          begin
            AAccess.FieldName := PropInfo.ReadField;
            AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
            Result := PropInfo.TypeDesc;
            AAccess.ResolvedType := Result;
            Exit;
          end;
          
          AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
          if AAccess.ResolvedMethod <> nil then
          begin
            AAccess.IsMethodCall := True;
            Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
            AAccess.ResolvedType := Result;
            Exit;
          end;
          SemanticError(
            Format('Type ''%s'' has no field ''%s''', AAccess.RecordName, AAccess.FieldName),
            AAccess.Line, AAccess.Col);
        end;
        Result := AAccess.FieldInfo.TypeDesc;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', AAccess.RecordName),
      AAccess.Line, AAccess.Col);
  end;

  
  if RecSym.Kind = skType then
  begin
    if RecSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot call procedure on non-class type ''%s''', AAccess.RecordName),
        AAccess.Line, AAccess.Col);
    if not SameText(AAccess.FieldName, 'Create') then
      SemanticError(
        Format('Unknown class method ''%s'' on type ''%s''', AAccess.FieldName, AAccess.RecordName),
        AAccess.Line, AAccess.Col);
    AAccess.IsConstructorCall := True;
    AAccess.ResolvedMethod    := FindMethodDecl(TRecordTypeDesc(RecSym.TypeDesc).Name, 'Create');
    Result := RecSym.TypeDesc;
    Exit;
  end;


  if not (((RecSym.Kind = skVariable) or (RecSym.Kind = skParameter) or (RecSym.Kind = skVarParameter))) then
    SemanticError(
      Format('''%s'' is not a variable or type', AAccess.RecordName),
      AAccess.Line, AAccess.Col);

  if not (((RecSym.TypeDesc.Kind = tyRecord) or (RecSym.TypeDesc.Kind = tyClass))) then
    SemanticError(
      Format('''%s'' is not a record or class', AAccess.RecordName),
      AAccess.Line, AAccess.Col);

  AAccess.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAccess.IsGlobal      := RecSym.IsGlobal;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAccess.FieldName);
  if FldInfo = nil then
  begin
    
    AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
    if AAccess.ResolvedMethod <> nil then
    begin
      AAccess.IsMethodCall := True;
      Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
      AAccess.ResolvedType := Result;
      Exit;
    end;
    
    PropInfo := RT.FindProperty(AAccess.FieldName);
    if PropInfo <> nil then
    begin
      if PropInfo.ReadField <> '' then
      begin
        
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end
      else if PropInfo.ReadMethod <> '' then
      begin
        
        AAccess.PropRead      := PropInfo;
        AAccess.PropOwnerType := RT.Name;
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end;
    end;
    SemanticError(
      Format('Type ''%s'' has no field ''%s''', AAccess.RecordName, AAccess.FieldName),
      AAccess.Line, AAccess.Col);
  end;

  AAccess.FieldInfo := FldInfo;
  Result := FldInfo.TypeDesc;
end;

function TSemanticAnalyser.AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
var
  LType, RType: TTypeDesc;
begin
  LType := AnalyseExpr(ABin.Left);
  RType := AnalyseExpr(ABin.Right);

  
  if ((ABin.Op = boAnd) or (ABin.Op = boOr)) then
  begin
    if LType.Kind <> tyBoolean then
      SemanticError(
        Format('Left operand of ''%s'' must be Boolean, got ''%s''', BinaryOpName(ABin.Op), LType.Name),
        ABin.Line, ABin.Col);
    if RType.Kind <> tyBoolean then
      SemanticError(
        Format('Right operand of ''%s'' must be Boolean, got ''%s''', BinaryOpName(ABin.Op), RType.Name),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
    Exit;
  end;

  if IsComparisonOp(ABin.Op) then
  begin
    
    if not (
      (LType = RType) or
      ((LType.Kind = tyNil) and (((RType.Kind = tyClass) or (RType.Kind = tyInterface) or (RType.Kind = tyPointer)))) or
      ((RType.Kind = tyNil) and (((LType.Kind = tyClass) or (LType.Kind = tyInterface) or (LType.Kind = tyPointer)))) or
      ((LType.Kind = tyPointer) and (RType.Kind = tyPointer)) or
      
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       (IsSubtypeOf(LType, RType) or IsSubtypeOf(RType, LType))) or
      
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       ((LType.Name = 'TObject') or (RType.Name = 'TObject')))
    ) then
      CheckTypesMatch(LType, RType,
        Format('comparison ''%s''', BinaryOpName(ABin.Op)),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
  end
  else
  begin
    
    if (ABin.Op = boAdd) and LType.IsString and RType.IsString then
    begin
      Result := FTable.TypeString;
      Exit;
    end;

    
    if (((ABin.Op = boAdd) or (ABin.Op = boSub))) and (LType.Kind = tyPointer) and RType.IsNumeric then
    begin
      Result := LType;
      Exit;
    end;
    if (ABin.Op = boAdd) and LType.IsNumeric and (RType.Kind = tyPointer) then
    begin
      Result := RType;
      Exit;
    end;

    if not LType.IsNumeric then
      SemanticError(
        Format('Left operand of ''%s'' must be numeric, got ''%s''', BinaryOpName(ABin.Op), LType.Name),
        ABin.Line, ABin.Col);
    if not RType.IsNumeric then
      SemanticError(
        Format('Right operand of ''%s'' must be numeric, got ''%s''', BinaryOpName(ABin.Op), RType.Name),
        ABin.Line, ABin.Col);
    CheckTypesMatch(LType, RType, 'binary expression', ABin.Line, ABin.Col);
    Result := LType;
  end;
end;

function TSemanticAnalyser.AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := AnalyseExpr(AExpr.Obj);
  
  if not ((ObjType.Kind = tyClass) or (ObjType.Kind = tyPointer) or
          (ObjType.Kind = tyInterface)) then
    SemanticError(
      Format('''is'' requires a class instance on the left, got ''%s''', ObjType.Name),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''is'' requires a class or interface type name on the right, got ''%s''', AExpr.TypeName),
      AExpr.Line, AExpr.Col);

  AExpr.ResolvedTargetType := TargetType;
  Result := FTable.TypeBoolean;
end;

function TSemanticAnalyser.AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := AnalyseExpr(AExpr.Obj);
  if ObjType.Kind <> tyClass then
    SemanticError(
      Format('''as'' requires a class instance on the left, got ''%s''', ObjType.Name),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''as'' requires a class or interface type name on the right, got ''%s''', AExpr.TypeName),
      AExpr.Line, AExpr.Col);

  Result := TargetType;
end;

function TSemanticAnalyser.AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
var
  PtrType: TTypeDesc;
begin
  PtrType := AnalyseExpr(AExpr.Expr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Dereference operator ''%s^'' requires a pointer type', PtrType.Name),
      AExpr.Line, AExpr.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot dereference untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AExpr.Line, AExpr.Col);
  Result := TPointerTypeDesc(PtrType).BaseType;
end;

procedure TSemanticAnalyser.AnalyseCaseStmt(AStmt: TCaseStmt);
var
  SelType:  TTypeDesc;
  Branch:   TCaseBranch;
  ValType:  TTypeDesc;
  I, J:     Integer;
begin
  SelType := AnalyseExpr(AStmt.Selector);
  if not SelType.IsOrdinal then
    SemanticError(
      Format('case selector must be ordinal type, got ''%s''', SelType.Name),
      AStmt.Line, AStmt.Col);
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch := TCaseBranch(AStmt.Branches.Get(I));
    for J := 0 to Branch.Values.Count - 1 do
    begin
      ValType := AnalyseExpr(TASTExpr(Branch.Values.Get(J)));
      CheckTypesMatch(SelType, ValType, 'case value', AStmt.Line, AStmt.Col);
    end;
    AnalyseStmt(Branch.Stmt);
  end;
  if AStmt.ElseStmt <> nil then
    AnalyseStmt(AStmt.ElseStmt);
end;

procedure TSemanticAnalyser.AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);
var
  PtrType: TTypeDesc;
  ValType: TTypeDesc;
begin
  PtrType := AnalyseExpr(AStmt.PtrExpr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Pointer write requires a pointer type, got ''%s''', PtrType.Name),
      AStmt.Line, AStmt.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot write through untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AStmt.Line, AStmt.Col);
  AStmt.BaseTy := TPointerTypeDesc(PtrType).BaseType;
  ValType := AnalyseExpr(AStmt.ValExpr);
  CheckTypesMatch(AStmt.BaseTy, ValType, 'pointer write', AStmt.Line, AStmt.Col);
end;




{ === uCodeGenQBE === }

















type

  TCodeGenQBE = class

    FOutput:       TStringList;
    FStrLits:      TStringList;  
    FTempCount:    Integer;
    FLabelCount:   Integer;
    FCurrentBlock: TBlock;       
    FBreakLabels:    TStringList;  
    FContinueLabels: TStringList;  
    FExitLabel:    string;       

    function  AllocTemp: string;
    function  AllocLabel(const APrefix: string): string;
    function  EmitStrLit(const AValue: string): string;
    procedure EmitLine(const ALine: string);
    procedure EmitDataSection;
    procedure EmitMainHeader;
    procedure EmitMainFooter;
    procedure EmitTypeInfoDefs(AProg: TProgram);
    procedure EmitVTableDefs(AProg: TProgram);
    procedure EmitMethodDefs(AProg: TProgram);
    procedure EmitInterfaceDefs(AProg: TProgram);
    procedure EmitFieldCleanupDefs(AProg: TProgram);
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ARec: TRecordTypeDesc);
    procedure EmitMethodDef(const ATypeName: string; AMethod: TMethodDecl);
    procedure EmitStandaloneDefs(AProg: TProgram);
    procedure EmitStandaloneDef(ADecl: TMethodDecl);
    procedure EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
    function  IsRecordCall(AExpr: TASTExpr): Boolean;
    procedure EmitRecordCopy(ARec: TRecordTypeDesc; const ADestAddr, ASrcAddr: string);
    procedure EmitRecordCallSret(AExpr: TASTExpr; const ASretAddr: string);
    procedure EmitRecordReleaseFields(ARec: TRecordTypeDesc; const AAddr: string);
    procedure EmitBlock(ABlock: TBlock);
    procedure EmitVarAllocs(ABlock: TBlock);
    procedure EmitGlobalVarData(ABlock: TBlock);
    procedure EmitParamAllocs(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure EmitArcCleanup(ABlock: TBlock);
    procedure EmitExcPathArcCleanup(ABlock: TBlock);
    procedure EmitStmt(AStmt: TASTStmt);
    procedure EmitIfStmt(AStmt: TIfStmt);
    procedure EmitWhileStmt(AStmt: TWhileStmt);
    procedure EmitForStmt(AStmt: TForStmt);
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    procedure EmitCompoundStmt(AStmt: TCompoundStmt);
    procedure EmitAssignment(AAssign: TAssignment);
    procedure EmitFieldAssignment(AAssign: TFieldAssignment);
    procedure EmitMethodCall(ACall: TMethodCallStmt);
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    procedure EmitCaseStmt(AStmt: TCaseStmt);
    procedure EmitProcCall(ACall: TProcCall);
    procedure EmitPointerWrite(AStmt: TPointerWriteStmt);
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    function  EmitExpr(AExpr: TASTExpr): string;
    function  EmitIsExpr(AExpr: TIsExpr): string;
    function  EmitAsExpr(AExpr: TAsExpr): string;
    


    function  EmitInstancePtr(AExpr: TASTExpr): string;
    function  FieldPtr(const ARecordVar: string; AOffset: Integer): string;
    

    function  VarRef(const AName: string; AIsGlobal: Boolean): string;
    function  EmitVarArgAddr(AIdent: TIdentExpr): string;
    function  QbeTypeOf(AType: TTypeDesc): string;
    function  QbeEscapeString(const AStr: string): string;
    
    function  QBEMangle(const AName: string): string;

    procedure Create;
    procedure Destroy;
    procedure Generate(AProg: TProgram);
    procedure GenerateUnit(AUnit: TUnit);
    function  GetOutput: string;
  end;


procedure TCodeGenQBE.Create;
begin

  FOutput       := TStringList.Create;
  FStrLits      := TStringList.Create;
  FBreakLabels    := TStringList.Create;
  FContinueLabels := TStringList.Create;
  FTempCount      := 0;
end;

procedure TCodeGenQBE.Destroy;
begin
  FBreakLabels.Free;
  FContinueLabels.Free;
  FOutput.Free;
  FStrLits.Free;

end;

function TCodeGenQBE.AllocTemp: string;
begin
  Result := Format('%%_t%d', FTempCount);
  FTempCount := FTempCount + 1;
end;

function TCodeGenQBE.AllocLabel(const APrefix: string): string;
begin
  Result := Format('%s_%d', APrefix, FLabelCount);
  FLabelCount := FLabelCount + 1;
end;

function TCodeGenQBE.EmitStrLit(const AValue: string): string;
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Result := Format('$__s%d', Idx);
end;

procedure TCodeGenQBE.EmitLine(const ALine: string);
begin
  FOutput.Add(ALine);
end;

procedure TCodeGenQBE.EmitDataSection;
var
  I:       Integer;
  StrLen:  Integer;
begin
  

  if FStrLits.Count > 0 then
  begin
    EmitLine('# String literals');
    for I := 0 to FStrLits.Count - 1 do
    begin
      StrLen := Length(FStrLits.Get(I));
      EmitLine(Format('data $__s%d = { w -1, w %d, w %d, b "%s", b 0 }', I, StrLen, StrLen, QbeEscapeString(FStrLits.Get(I))));
    end;
  end;
  




  EmitLine('data $__fmt_s_nl = { b "%s\n", b 0 }');
  EmitLine('data $__fmt_s    = { b "%s", b 0 }');
  EmitLine('data $__fmt_d_nl = { b "%d\n", b 0 }');
  EmitLine('data $__fmt_d    = { b "%d", b 0 }');
  EmitLine('data $__fmt_nl   = { b "\n", b 0 }');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitMainHeader;
begin
  EmitLine('export function w $main(w %argc, l %argv) {');
  EmitLine('@start');
  EmitLine('  call $_SetArgs(w %argc, l %argv)');
end;

procedure TCodeGenQBE.EmitMainFooter;
begin
  EmitLine('  ret 0');
  EmitLine('}');
end;

function TCodeGenQBE.QbeTypeOf(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum: Result := 'w';
    tyInt64, tyString:                      Result := 'l';
    tyRecord:                               Result := 'l';  
    tyClass:                                Result := 'l';  
    tyPointer:                              Result := 'l';  
  else
    Result := 'w';
  end;
end;

procedure TCodeGenQBE.EmitVarAllocs(ABlock: TBlock);
var
  I, J:     Integer;
  Decl:     TVarDecl;
  VarName:  string;
  RT:       TRecordTypeDesc;
  RecSize:  Integer;
  RecAlign: Integer;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Get(I));
    if Decl.ResolvedType = nil then
      raise ECodeGenError.Create(Format('Variable ''%s'' has no resolved type — semantic pass required', Decl.Names.Get(0)));
    if Decl.IsGlobal then
      Continue;  

    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Get(J);
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', VarName));
            EmitLine(Format('  storew 0, %%_var_%s', VarName));
          end;

        tyInt64:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s', VarName));
          end;

        tyString:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s', VarName));
          end;

        tyRecord:
          begin
            RT       := TRecordTypeDesc(Decl.ResolvedType);
            RecSize  := RT.TotalSize;
            RecAlign := RT.MaxAlign;
            if RecAlign >= 8 then
              EmitLine(Format('  %%_var_%s =l alloc8 %d', VarName, RecSize))
            else
              EmitLine(Format('  %%_var_%s =l alloc4 %d', VarName, RecSize));
            


            if RecSize > 0 then
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)', VarName, RecSize));
          end;

        tyClass:
          begin
            
            EmitLine(Format('  %%_var_%s =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s', VarName));
          end;

        tyPointer:
          begin
            
            EmitLine(Format('  %%_var_%s =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s', VarName));
          end;

        tyInterface:
          begin
            
            EmitLine(Format('  %%_var_%s_obj  =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s_obj', VarName));
            EmitLine(Format('  %%_var_%s_itab =l alloc8 1', VarName));
            EmitLine(Format('  storel 0, %%_var_%s_itab', VarName));
          end;

      else
        raise ECodeGenError.Create(Format('Unsupported type kind %d for variable ''%s''', Decl.ResolvedType.Kind, VarName));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitGlobalVarData(ABlock: TBlock);




var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  RT:      TRecordTypeDesc;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Get(I));
    if not Decl.IsGlobal then Continue;
    if Decl.ResolvedType = nil then Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Get(J);
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          EmitLine(Format('data $%s = { w 0 }', VarName));
        tyInt64:
          EmitLine(Format('data $%s = { l 0 }', VarName));
        tyString, tyClass, tyPointer:
          EmitLine(Format('data $%s = { l 0 }', VarName));
        tyInterface:
          begin
            EmitLine(Format('data $%s_obj  = { l 0 }', VarName));
            EmitLine(Format('data $%s_itab = { l 0 }', VarName));
          end;
        tyRecord:
          begin
            RT := TRecordTypeDesc(Decl.ResolvedType);
            if RT.TotalSize > 0 then
              EmitLine(Format('data $%s = { z %d }', VarName, RT.TotalSize))
            else
              EmitLine(Format('data $%s = { l 0 }', VarName));
          end;
      else
        EmitLine(Format('data $%s = { l 0 }', VarName));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitArcCleanup(ABlock: TBlock);






var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
  IsIntf:  Boolean;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Get(I));
    if Decl.ResolvedType = nil then Continue;
    IsIntf := Decl.ResolvedType.Kind = tyInterface;
    if Decl.IsWeak then
    begin
      


      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Get(J);
        if IsIntf then
          EmitLine(Format('  call $_WeakClear(l %s_obj)', VarRef(VarName, Decl.IsGlobal)))
        else
          EmitLine(Format('  call $_WeakClear(l %s)', VarRef(VarName, Decl.IsGlobal)));
      end;
      Continue;
    end;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'  
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Get(J);
      ValTemp := AllocTemp;
      if IsIntf then
        EmitLine(Format('  %s =l loadl %s_obj', ValTemp, VarRef(VarName, Decl.IsGlobal)))
      else
        EmitLine(Format('  %s =l loadl %s', ValTemp, VarRef(VarName, Decl.IsGlobal)));
      EmitLine(Format('  call %s(l %s)', RelFn, ValTemp));
    end;
  end;
end;

procedure TCodeGenQBE.EmitBlock(ABlock: TBlock);
var
  I: Integer;
begin
  FCurrentBlock := ABlock;
  EmitVarAllocs(ABlock);
  for I := 0 to ABlock.Stmts.Count - 1 do
    EmitStmt(TASTStmt(ABlock.Stmts.Get(I)));
  
  if FExitLabel <> '' then
  begin
    EmitLine(Format('  jmp @%s', FExitLabel));
    EmitLine('@' + FExitLabel);
  end;
  EmitArcCleanup(ABlock);
end;

procedure TCodeGenQBE.EmitExcPathArcCleanup(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
  IsIntf:  Boolean;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Get(I));
    if Decl.ResolvedType = nil then Continue;
    IsIntf := Decl.ResolvedType.Kind = tyInterface;
    if Decl.IsWeak then
    begin
      

      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Get(J);
        if IsIntf then
          EmitLine(Format('  call $_WeakClear(l %s_obj)', VarRef(VarName, Decl.IsGlobal)))
        else
          EmitLine(Format('  call $_WeakClear(l %s)', VarRef(VarName, Decl.IsGlobal)));
      end;
      Continue;
    end;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Get(J);
      ValTemp := AllocTemp;
      if IsIntf then
      begin
        EmitLine(Format('  %s =l loadl %s_obj', ValTemp, VarRef(VarName, Decl.IsGlobal)));
        EmitLine(Format('  call %s(l %s)', RelFn, ValTemp));
        EmitLine(Format('  storel 0, %s_obj', VarRef(VarName, Decl.IsGlobal)));
      end
      else
      begin
        EmitLine(Format('  %s =l loadl %s', ValTemp, VarRef(VarName, Decl.IsGlobal)));
        EmitLine(Format('  call %s(l %s)', RelFn, ValTemp));
        EmitLine(Format('  storel 0, %s', VarRef(VarName, Decl.IsGlobal)));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitStmt(AStmt: TASTStmt);
var
  DeadLbl: string;
begin
  if AStmt = nil then
    raise ECodeGenError.Create('EmitStmt called with nil statement');
  if AStmt is TTryFinallyStmt then
    EmitTryFinallyStmt(TTryFinallyStmt(AStmt))
  else if AStmt is TTryExceptStmt then
    EmitTryExceptStmt(TTryExceptStmt(AStmt))
  else if AStmt is TRaiseStmt then
    EmitRaiseStmt(TRaiseStmt(AStmt))
  else if AStmt is TForStmt then
    EmitForStmt(TForStmt(AStmt))
  else if AStmt is TWhileStmt then
    EmitWhileStmt(TWhileStmt(AStmt))
  else if AStmt is TIfStmt then
    EmitIfStmt(TIfStmt(AStmt))
  else if AStmt is TCompoundStmt then
    EmitCompoundStmt(TCompoundStmt(AStmt))
  else if AStmt is TFieldAssignment then
    EmitFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TPointerWriteStmt then
    EmitPointerWrite(TPointerWriteStmt(AStmt))
  else if AStmt is TAssignment then
    EmitAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    EmitMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TInheritedCallStmt then
    EmitInheritedCall(TInheritedCallStmt(AStmt))
  else if AStmt is TCaseStmt then
    EmitCaseStmt(TCaseStmt(AStmt))
  else if AStmt is TProcCall then
    EmitProcCall(TProcCall(AStmt))
  else if AStmt is TExitStmt then
  begin
    if FExitLabel <> '' then
      EmitLine(Format('  jmp @%s', FExitLabel))
    else
      EmitLine('  ret 0');
    
    DeadLbl := AllocLabel('after_exit');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ECodeGenError.Create('break outside loop');
    EmitLine(Format('  jmp @%s', FBreakLabels.Get(FBreakLabels.Count - 1)));
    DeadLbl := AllocLabel('after_break');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ECodeGenError.Create('continue outside loop');
    EmitLine(Format('  jmp @%s', FContinueLabels.Get(FContinueLabels.Count - 1)));
    DeadLbl := AllocLabel('after_continue');
    EmitLine('@' + DeadLbl);
  end
  else
    raise ECodeGenError.Create(Format('Unknown statement node type at line %d', AStmt.Line));
end;

procedure TCodeGenQBE.EmitIfStmt(AStmt: TIfStmt);
var
  CondTemp:  string;
  LblThen:   string;
  LblElse:   string;
  LblEnd:    string;
begin
  LblThen := AllocLabel('if_then');
  LblEnd  := AllocLabel('if_end');

  CondTemp := EmitExpr(AStmt.Condition);

  if AStmt.ElseStmt <> nil then
  begin
    LblElse := AllocLabel('if_else');
    EmitLine(Format('  jnz %s, @%s, @%s', CondTemp, LblThen, LblElse));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', LblEnd));
    EmitLine('@' + LblElse);
    EmitStmt(AStmt.ElseStmt);
    EmitLine(Format('  jmp @%s', LblEnd));
  end
  else
  begin
    EmitLine(Format('  jnz %s, @%s, @%s', CondTemp, LblThen, LblEnd));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', LblEnd));
  end;

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  ExcTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblFinExc := AllocLabel('fin_exc');
  LblEnd    := AllocLabel('fin_end');

  


  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', FrameTemp));
  EmitLine(Format('  call $_PushExcFrame(l %s)', FrameTemp));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', SjrTemp, FrameTemp));
  EmitLine(Format('  jnz %s, @%s, @%s', SjrTemp, LblFinExc, LblTry));

  
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Get(I)));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Get(I)));
  EmitLine(Format('  jmp @%s', LblEnd));

  

  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp;
  EmitLine(Format('  %s =l call $_CurrentException()', ExcTemp));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Get(I)));
  EmitExcPathArcCleanup(FCurrentBlock);
  EmitLine(Format('  call $_Reraise(l %s)', ExcTemp));
  EmitLine(Format('  jmp @%s', LblEnd));  

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblExcept := AllocLabel('except_handler');
  LblEnd    := AllocLabel('except_end');

  


  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', FrameTemp));
  EmitLine(Format('  call $_PushExcFrame(l %s)', FrameTemp));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', SjrTemp, FrameTemp));
  EmitLine(Format('  jnz %s, @%s, @%s', SjrTemp, LblExcept, LblTry));

  
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Get(I)));
  EmitLine('  call $_PopExcFrame()');
  EmitLine(Format('  jmp @%s', LblEnd));

  
  EmitLine('@' + LblExcept);
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts.Get(I)));
  EmitLine(Format('  jmp @%s', LblEnd));

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitRaiseStmt(AStmt: TRaiseStmt);
var
  ObjTemp: string;
begin
  if AStmt.Expr <> nil then
  begin
    ObjTemp := EmitExpr(AStmt.Expr);
    EmitLine(Format('  call $_Raise(l %s)', ObjTemp));
  end
  else
    
    EmitLine('  call $_Raise(l 0)');
end;

procedure TCodeGenQBE.EmitForStmt(AStmt: TForStmt);
var
  LblCond:  string;
  LblBody:  string;
  LblNext:  string;  
  LblEnd:   string;
  StartT:   string;
  EndT:     string;
  CurT:     string;
  CmpT:     string;
  StepT:    string;
  CmpOp:    string;
  StepOp:   string;
begin
  LblCond := AllocLabel('for_cond');
  LblBody := AllocLabel('for_body');
  LblNext := AllocLabel('for_next');
  LblEnd  := AllocLabel('for_end');

  
  StartT := EmitExpr(AStmt.StartExpr);
  EmitLine(Format('  storew %s, %%_var_%s', StartT, AStmt.VarName));

  
  EndT := EmitExpr(AStmt.EndExpr);

  
  EmitLine(Format('  jmp @%s', LblCond));

  
  EmitLine('@' + LblCond);
  CurT := AllocTemp;
  EmitLine(Format('  %s =w loadw %%_var_%s', CurT, AStmt.VarName));
  CmpT := AllocTemp;
  if AStmt.IsDownTo then
    CmpOp := 'csgew'   
  else
    CmpOp := 'cslew';  
  EmitLine(Format('  %s =w %s %s, %s', CmpT, CmpOp, CurT, EndT));
  EmitLine(Format('  jnz %s, @%s, @%s', CmpT, LblBody, LblEnd));

  
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  FContinueLabels.Add(LblNext);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', LblNext));

  
  EmitLine('@' + LblNext);
  CurT  := AllocTemp;
  StepT := AllocTemp;
  EmitLine(Format('  %s =w loadw %%_var_%s', CurT, AStmt.VarName));
  if AStmt.IsDownTo then
    StepOp := 'sub'
  else
    StepOp := 'add';
  EmitLine(Format('  %s =w %s %s, 1', StepT, StepOp, CurT));
  EmitLine(Format('  storew %s, %%_var_%s', StepT, AStmt.VarName));
  EmitLine(Format('  jmp @%s', LblCond));

  
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitWhileStmt(AStmt: TWhileStmt);
var
  LblCond: string;
  LblBody: string;
  LblEnd:  string;
  CondTemp: string;
begin
  LblCond := AllocLabel('while_cond');
  LblBody := AllocLabel('while_body');
  LblEnd  := AllocLabel('while_end');

  
  EmitLine(Format('  jmp @%s', LblCond));

  
  EmitLine('@' + LblCond);
  CondTemp := EmitExpr(AStmt.Condition);
  EmitLine(Format('  jnz %s, @%s, @%s', CondTemp, LblBody, LblEnd));

  
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  FContinueLabels.Add(LblCond);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', LblCond));

  
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitCompoundStmt(AStmt: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to AStmt.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.Stmts.Get(I)));
end;

procedure TCodeGenQBE.EmitAssignment(AAssign: TAssignment);
var
  ValTemp, OldTemp, QType, StoreInstr, PtrTemp: string;
  IntfDesc:  TInterfaceTypeDesc;
  ClassRT:   TRecordTypeDesc;
  ItabName:  string;
  AE:        TAsExpr;
  ObjTemp:   string;
  ItabTemp:  string;
  CheckTemp: string;
  LblOk:     string;
  LblFail:   string;
  LblEnd:    string;
  ISFld:     TFieldInfo;
  ISAddrT:   string;
  ExtTemp:   string;
begin
  if AAssign.Expr.ResolvedType = nil then
    raise ECodeGenError.Create(Format('Expression in assignment to ''%s'' has no resolved type', AAssign.Name));

  
  if AAssign.ImplicitSelfField <> nil then
  begin
    ISFld   := TFieldInfo(AAssign.ImplicitSelfField);
    ObjTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_Self', ObjTemp));
    if ISFld.Offset > 0 then
    begin
      ISAddrT := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', ISAddrT, ObjTemp, ISFld.Offset));
      ObjTemp := ISAddrT;
    end;
    if ISFld.TypeDesc.Kind = tyRecord then
    begin
      ClassRT := TRecordTypeDesc(ISFld.TypeDesc);
      if IsRecordCall(AAssign.Expr) then
      begin
        EmitRecordReleaseFields(ClassRT, ObjTemp);
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', ObjTemp, ClassRT.TotalSize));
        EmitRecordCallSret(AAssign.Expr, ObjTemp);
      end
      else
      begin
        ValTemp := EmitExpr(AAssign.Expr);
        EmitRecordCopy(ClassRT, ObjTemp, ValTemp);
      end;
      Exit;
    end;
    ValTemp := EmitExpr(AAssign.Expr);
    QType := QbeTypeOf(ISFld.TypeDesc);
    if QType = 'w' then
      EmitLine(Format('  storew %s, %s', ValTemp, ObjTemp))
    else
    begin
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', ExtTemp, ValTemp));
        ValTemp := ExtTemp;
      end;
      if ISFld.TypeDesc.IsString then
      begin
        OldTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', OldTemp, ObjTemp));
        EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
        EmitLine(Format('  call $_StringRelease(l %s)', OldTemp));
      end
      else if ISFld.TypeDesc.Kind = tyClass then
      begin
        OldTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', OldTemp, ObjTemp));
        EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
        EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
      end;
      EmitLine(Format('  storel %s, %s', ValTemp, ObjTemp));
    end;
    Exit;
  end;

  




  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr is TAsExpr) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE        := TAsExpr(AAssign.Expr);
    IntfDesc  := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ObjTemp   := EmitExpr(AE.Obj);
    ItabTemp  := AllocTemp;
    EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)', ItabTemp, ObjTemp, AE.TypeName));
    CheckTemp := AllocTemp;
    LblOk   := AllocLabel('as_ok');
    LblFail := AllocLabel('as_fail');
    LblEnd  := AllocLabel('as_end');
    EmitLine(Format('  %s =w cnel %s, 0', CheckTemp, ItabTemp));
    EmitLine(Format('  jnz %s, @%s, @%s', CheckTemp, LblOk, LblFail));
    EmitLine('@' + LblFail);
    EmitLine('  call $_Raise_InvalidCast()');
    EmitLine(Format('  jmp @%s', LblEnd));
    EmitLine('@' + LblOk);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)', VarRef(AAssign.Name, AAssign.IsGlobal), ObjTemp))
    else
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj', OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
      EmitLine(Format('  call $_ClassAddRef(l %s)', ObjTemp));
      EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
      EmitLine(Format('  storel %s, %s_obj', ObjTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    end;
    EmitLine(Format('  storel %s, %s_itab', ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    EmitLine('@' + LblEnd);
    Exit;
  end;

  



  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyClass) then
  begin
    IntfDesc := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ClassRT  := TRecordTypeDesc(AAssign.Expr.ResolvedType);
    ItabName := '$itab_' + ClassRT.Name + '_' + IntfDesc.Name;
    ValTemp  := EmitExpr(AAssign.Expr);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)', VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp))
    else
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj', OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
      EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
      EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
      EmitLine(Format('  storel %s, %s_obj', ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    end;
    EmitLine(Format('  storel %s, %s_itab', ItabName, VarRef(AAssign.Name, AAssign.IsGlobal)));
    Exit;
  end;

  



  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) and
     (AAssign.Expr is TIdentExpr) then
  begin
    ObjTemp  := AllocTemp;
    ItabTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj', ObjTemp, VarRef(TIdentExpr(AAssign.Expr).Name, TIdentExpr(AAssign.Expr).IsGlobal)));
    EmitLine(Format('  %s =l loadl %s_itab', ItabTemp, VarRef(TIdentExpr(AAssign.Expr).Name, TIdentExpr(AAssign.Expr).IsGlobal)));
    if AAssign.IsWeakLhs then
    begin
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)', VarRef(AAssign.Name, AAssign.IsGlobal), ObjTemp));
      EmitLine(Format('  storel %s, %s_itab', ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
      Exit;
    end;
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj', OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    EmitLine(Format('  call $_ClassAddRef(l %s)', ObjTemp));
    EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
    EmitLine(Format('  storel %s, %s_obj', ObjTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    EmitLine(Format('  storel %s, %s_itab', ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    Exit;
  end;

  if AAssign.IsVarParam then
  begin
    QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
    ValTemp := EmitExpr(AAssign.Expr);
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', PtrTemp, AAssign.Name));
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %s', StoreInstr, ValTemp, PtrTemp));
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyRecord) then
  begin
    ClassRT := TRecordTypeDesc(AAssign.ResolvedLhsType);
    if IsRecordCall(AAssign.Expr) then
    begin
      EmitRecordReleaseFields(ClassRT, VarRef(AAssign.Name, AAssign.IsGlobal));
      EmitLine(Format('  call $memset(l %s, w 0, l %d)', VarRef(AAssign.Name, AAssign.IsGlobal), ClassRT.TotalSize));
      EmitRecordCallSret(AAssign.Expr, VarRef(AAssign.Name, AAssign.IsGlobal));
    end
    else
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      EmitRecordCopy(ClassRT, VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp);
    end;
  end
  else if AAssign.Expr.ResolvedType.IsString then
  begin
    
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
    EmitLine(Format('  call $_StringRelease(l %s)', OldTemp));
    EmitLine(Format('  storel %s, %s', ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
  end
  else if AAssign.IsWeakLhs and (AAssign.Expr.ResolvedType.Kind = tyClass) then
  begin
    



    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_WeakAssign(l %s, l %s)', VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp));
  end
  else if AAssign.Expr.ResolvedType.Kind = tyClass then
  begin
    

    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
    EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
    EmitLine(Format('  storel %s, %s', ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
  end
  else
  begin
    

    if (AAssign.ResolvedLhsType <> nil) and
       (QbeTypeOf(AAssign.ResolvedLhsType) = 'l') then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', ExtTemp, ValTemp));
        ValTemp := ExtTemp;
      end;
      EmitLine(Format('  storel %s, %s', ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    end
    else
    begin
      QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
      ValTemp := EmitExpr(AAssign.Expr);
      if QType = 'w' then StoreInstr := 'storew'
                     else StoreInstr := 'storel';
      EmitLine(Format('  %s %s, %s', StoreInstr, ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)));
    end;
  end;
end;

function TCodeGenQBE.EmitInstancePtr(AExpr: TASTExpr): string;
var
  Id:     TIdentExpr;
  Fld:    TFieldAccessExpr;
  Base:   string;
  Ptr:    string;
  Loaded: string;
  SelfT:  string;
  ImplFld: TFieldInfo;
begin
  if AExpr is TIdentExpr then
  begin
    Id := TIdentExpr(AExpr);
    
    if Id.IsImplicitSelf then
    begin
      ImplFld := TFieldInfo(Id.ImplicitFieldInfo);
      SelfT   := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', SelfT));
      if ImplFld.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, SelfT, ImplFld.Offset));
        SelfT := Ptr;
      end;
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', Loaded, SelfT));
      Result := Loaded;
      Exit;
    end;
    if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', Loaded, VarRef(Id.Name, Id.IsGlobal)));
      Result := Loaded;
    end
    else
      Result := VarRef(Id.Name, Id.IsGlobal);  
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Fld := TFieldAccessExpr(AExpr);
    if Fld.Base <> nil then
      Base := EmitInstancePtr(Fld.Base)
    else
    begin
      
      if (Fld.ResolvedType = nil) then
        raise ECodeGenError.Create('Chained base has no resolved type');
      if Fld.IsClassAccess then
      begin
        Loaded := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', Loaded, VarRef(Fld.RecordName, Fld.IsGlobal)));
        Base := Loaded;
      end
      else
        Base := VarRef(Fld.RecordName, Fld.IsGlobal);
    end;
    if Fld.FieldInfo = nil then
      raise ECodeGenError.Create(
        'Chained field access ''' + Fld.FieldName + ''' has no resolved field info');
    if Fld.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', Ptr, Base, Fld.FieldInfo.Offset));
    end
    else
      Ptr := Base;
    

    if Fld.FieldInfo.TypeDesc.Kind = tyClass then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', Loaded, Ptr));
      Result := Loaded;
    end
    else
      Result := Ptr;
    Exit;
  end;

  

  if (AExpr.ResolvedType <> nil) and
     (((AExpr.ResolvedType.Kind = tyClass) or (AExpr.ResolvedType.Kind = tyInterface) or (AExpr.ResolvedType.Kind = tyPointer) or (AExpr.ResolvedType.Kind = tyRecord))) then
  begin
    Result := EmitExpr(AExpr);
    Exit;
  end;
  raise ECodeGenError.Create('EmitInstancePtr: unsupported base expression');
end;

function TCodeGenQBE.FieldPtr(const ARecordVar: string; AOffset: Integer): string;
var
  PtrTemp: string;
begin
  if AOffset = 0 then
  begin
    Result := Format('%%_var_%s', ARecordVar);
  end
  else
  begin
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l add %%_var_%s, %d', PtrTemp, ARecordVar, AOffset));
    Result := PtrTemp;
  end;
end;

function TCodeGenQBE.VarRef(const AName: string; AIsGlobal: Boolean): string;
begin
  if AIsGlobal then
    Result := '$' + AName
  else
    Result := '%_var_' + AName;
end;

function TCodeGenQBE.EmitVarArgAddr(AIdent: TIdentExpr): string;
var
  T: string;
begin
  if AIdent.IsVarParam then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', T, AIdent.Name));
    Result := T;
  end
  else
    Result := VarRef(AIdent.Name, AIdent.IsGlobal);
end;

procedure TCodeGenQBE.EmitFieldAssignment(AAssign: TFieldAssignment);
var
  Ptr, PtrTemp, ValTemp, OldTemp, QType, StoreInstr, ExtTemp: string;
  IsArc: Boolean;
  IsStr: Boolean;
begin
  if AAssign.FieldInfo = nil then
    raise ECodeGenError.Create(Format('Field assignment ''%s.%s'' has no resolved field info', AAssign.RecordName, AAssign.FieldName));

  ValTemp := EmitExpr(AAssign.Expr);

  if AAssign.ObjExpr <> nil then
  begin
    PtrTemp := EmitExpr(AAssign.ObjExpr);
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', Ptr, PtrTemp, AAssign.FieldInfo.Offset));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsImplicitSelf then
  begin
    
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_Self', PtrTemp));
    if AAssign.ImplicitBaseInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', Ptr, PtrTemp, AAssign.ImplicitBaseInfo.Offset));
      PtrTemp := Ptr;
    end;
    if AAssign.IsClassAccess then
    begin
      
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', Ptr, PtrTemp));
      PtrTemp := Ptr;
    end;
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', Ptr, PtrTemp, AAssign.FieldInfo.Offset));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsClassAccess then
  begin
    
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', Ptr, PtrTemp, AAssign.FieldInfo.Offset));
    end
    else
      Ptr := PtrTemp;
  end
  else
    Ptr := FieldPtr(AAssign.RecordName, AAssign.FieldInfo.Offset);

  IsStr := AAssign.FieldInfo.TypeDesc.IsString;
  IsArc := IsStr or (AAssign.FieldInfo.TypeDesc.Kind = tyClass);
  if AAssign.FieldInfo.IsWeak then
  begin
    

    EmitLine(Format('  call $_WeakAssign(l %s, l %s)', Ptr, ValTemp));
  end
  else if IsArc then
  begin
    

    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', OldTemp, Ptr));
    if IsStr then
    begin
      EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
      EmitLine(Format('  call $_StringRelease(l %s)', OldTemp));
    end
    else
    begin
      EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
      EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
    end;
    EmitLine(Format('  storel %s, %s', ValTemp, Ptr));
  end
  else
  begin
    QType := QbeTypeOf(AAssign.FieldInfo.TypeDesc);
    if QType = 'w' then StoreInstr := 'storew'
                   else
                   begin
                     StoreInstr := 'storel';
                     
                     if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
                     begin
                       ExtTemp := AllocTemp;
                       EmitLine(Format('  %s =l extsw %s', ExtTemp, ValTemp));
                       ValTemp := ExtTemp;
                     end;
                   end;
    EmitLine(Format('  %s %s, %s', StoreInstr, ValTemp, Ptr));
  end;
end;

procedure TCodeGenQBE.EmitMethodCall(ACall: TMethodCallStmt);
var
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  SelfTemp: string;
  Par:      TMethodParam;
  ArgTemp:  string;
  ArgLine:  string;
  I:        Integer;
  QType:    string;
  FuncName: string;
  VTblTemp: string;
  FPtrTemp: string;
  SlotOff:  Integer;
  IntfDesc: TInterfaceTypeDesc;
begin
  
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    IntfDesc := TInterfaceTypeDesc(ACall.ResolvedClassType);
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj', SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)));
    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_itab', VTblTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)));
    SlotOff  := IntfDesc.MethodIndex(ACall.Name) * 8;
    FPtrTemp := AllocTemp;
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', FPtrTemp, VTblTemp))
    else
    begin
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', ArgTemp, VTblTemp, SlotOff));
      EmitLine(Format('  %s =l loadl %s', FPtrTemp, ArgTemp));
    end;
    EmitLine(Format('  call %s(l %s)', FPtrTemp, SelfTemp));
    Exit;
  end;

  
  if ACall.ObjExpr <> nil then
  begin
    SelfTemp := EmitExpr(ACall.ObjExpr);
    RT    := TRecordTypeDesc(ACall.ResolvedClassType);
    MDecl := TMethodDecl(ACall.ResolvedMethod);
    if (MDecl = nil) and SameText(ACall.Name, 'Free') then
    begin
      EmitLine(Format('  call $_ClassRelease(l %s)', SelfTemp));
      Exit;
    end;
    ArgLine := Format('l %s', SelfTemp);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Get(I)))))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(I)));
        QType   := QbeTypeOf(Par.ResolvedType);
        ArgLine := ArgLine + Format(', %s %s', QType, ArgTemp);
      end;
    end;
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
    else
      FuncName := '$' + RT.Name + '_' + ACall.Name;
    EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
    Exit;
  end;

  




  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    SelfTemp := AllocTemp;
    if ACall.IsImplicitSelf then
    begin
      

      EmitLine(Format('  %s =l loadl %%_var_Self', SelfTemp));
      if ACall.ImplicitBaseInfo.Offset > 0 then
      begin
        FPtrTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset));
      end
      else
        FPtrTemp := SelfTemp;
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', ArgTemp, FPtrTemp));
      EmitLine(Format('  call $_ClassRelease(l %s)', ArgTemp));
      EmitLine(Format('  storel 0, %s', FPtrTemp));
      Exit;
    end;
    EmitLine(Format('  %s =l loadl %s', SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)));
    EmitLine(Format('  call $_ClassRelease(l %s)', SelfTemp));
    EmitLine(Format('  storel 0, %s', VarRef(ACall.ObjectName, ACall.IsGlobal)));
    Exit;
  end;

  RT    := TRecordTypeDesc(ACall.ResolvedClassType);
  MDecl := TMethodDecl(ACall.ResolvedMethod);

  
  SelfTemp := AllocTemp;
  if ACall.IsImplicitSelf then
  begin
    
    EmitLine(Format('  %s =l loadl %%_var_Self', SelfTemp));
    if ACall.ImplicitBaseInfo.Offset > 0 then
    begin
      FPtrTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset));
      SelfTemp := FPtrTemp;
    end;
    FPtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', FPtrTemp, SelfTemp));
    SelfTemp := FPtrTemp;
  end
  else
    EmitLine(Format('  %s =l loadl %s', SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)));

  
  ArgLine := Format('l %s', SelfTemp);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Get(I));
    if Par.IsVarParam then
      ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Get(I)))))
    else
    begin
      ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(I)));
      QType   := QbeTypeOf(Par.ResolvedType);
      ArgLine := ArgLine + Format(', %s %s', QType, ArgTemp);
    end;
  end;

  if MDecl.VTableSlot >= 0 then
  begin
    

    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', VTblTemp, SelfTemp));
    FPtrTemp := AllocTemp;
    SlotOff  := (MDecl.VTableSlot + 1) * 8;
    ArgTemp  := AllocTemp;
    EmitLine(Format('  %s =l add %s, %d', ArgTemp, VTblTemp, SlotOff));
    EmitLine(Format('  %s =l loadl %s', FPtrTemp, ArgTemp));
    EmitLine(Format('  call %s(%s)', FPtrTemp, ArgLine));
  end
  else
  begin
    
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
    else
      FuncName := '$' + RT.Name + '_' + ACall.Name;
    EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
  end;
end;

procedure TCodeGenQBE.EmitCaseStmt(AStmt: TCaseStmt);
var
  SelTemp:     string;
  ValTemp:     string;
  CmpTemp:     string;
  NextLbl:     string;
  BranchLbl:   string;
  ElseLbl:     string;
  EndLbl:      string;
  Branch:      TCaseBranch;
  I, J:        Integer;
  BranchLabels: TStringList;
begin
  SelTemp  := EmitExpr(AStmt.Selector);
  EndLbl   := AllocLabel('case_end');
  ElseLbl  := AllocLabel('case_else');

  BranchLabels := TStringList.Create;
  try
    for I := 0 to AStmt.Branches.Count - 1 do
      BranchLabels.Add(AllocLabel('case_br'));

    

    for I := 0 to AStmt.Branches.Count - 1 do
    begin
      Branch    := TCaseBranch(AStmt.Branches.Get(I));
      BranchLbl := BranchLabels.Get(I);
      for J := 0 to Branch.Values.Count - 1 do
      begin
        ValTemp := EmitExpr(TASTExpr(Branch.Values.Get(J)));
        CmpTemp := AllocTemp;
        NextLbl := AllocLabel('case_next');
        EmitLine(Format('  %s =w ceqw %s, %s', CmpTemp, SelTemp, ValTemp));
        EmitLine(Format('  jnz %s, @%s, @%s', CmpTemp, BranchLbl, NextLbl));
        EmitLine('@' + NextLbl);
      end;
    end;
    EmitLine(Format('  jmp @%s', ElseLbl));

    
    for I := 0 to AStmt.Branches.Count - 1 do
    begin
      Branch    := TCaseBranch(AStmt.Branches.Get(I));
      BranchLbl := BranchLabels.Get(I);
      EmitLine('@' + BranchLbl);
      EmitStmt(Branch.Stmt);
      EmitLine(Format('  jmp @%s', EndLbl));
    end;

    EmitLine('@' + ElseLbl);
    if AStmt.ElseStmt <> nil then
      EmitStmt(AStmt.ElseStmt);
    EmitLine(Format('  jmp @%s', EndLbl));

    EmitLine('@' + EndLbl);
  finally
    BranchLabels.Free;
  end;
end;

procedure TCodeGenQBE.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  MDecl:    TMethodDecl;
  SelfTemp: string;
  ArgLine:  string;
  ArgTemp:  string;
  Par:      TMethodParam;
  QType:    string;
  I:        Integer;
begin
  MDecl := TMethodDecl(ACall.ResolvedMethod);

  
  SelfTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %%_var_Self', SelfTemp));

  
  ArgLine := Format('l %s', SelfTemp);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par     := TMethodParam(MDecl.Params.Get(I));
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(I)));
    QType   := QbeTypeOf(Par.ResolvedType);
    ArgLine := ArgLine + Format(', %s %s', QType, ArgTemp);
  end;

  
  EmitLine(Format('  call $%s_%s(%s)', MDecl.OwnerTypeName, ACall.Name, ArgLine));
end;

procedure TCodeGenQBE.EmitParamAllocs(AMethod: TMethodDecl;
  AClassType: TRecordTypeDesc);
var
  I:   Integer;
  Par: TMethodParam;
begin
  
  EmitLine('  %_var_Self =l alloc8 1');
  EmitLine('  storel %_par_Self, %_var_Self');

  
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Get(I));
    if Par.IsVarParam then
    begin
      
      EmitLine(Format('  %%_var_%s =l alloc8 1', Par.ParamName));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
    end
    else
    case Par.ResolvedType.Kind of
      tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', Par.ParamName));
          EmitLine(Format('  storew %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
        end;
      tyInt64, tyString, tyClass:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', Par.ParamName));
          EmitLine(Format('  storel %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
        end;
    else
      EmitLine(Format('  %%_var_%s =l alloc8 1', Par.ParamName));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
    end;
  end;
end;

procedure TCodeGenQBE.EmitMethodDef(const ATypeName: string;
  AMethod: TMethodDecl);
var
  Sig:           string;
  I:             Integer;
  Par:           TMethodParam;
  FuncName:      string;
  IsFunc:        Boolean;
  RetQType:      string;
  RetTemp:       string;
  SavedExitLbl:  string;
  ValTemp:       string;
begin
  FuncName := '$' + ATypeName + '_' + AMethod.Name;
  IsFunc   := AMethod.ResolvedReturnType <> nil;

  
  Sig := 'l %_par_Self';
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Get(I));
    if Par.IsVarParam then
      Sig := Sig + Format(', l %%_par_%s', Par.ParamName)
    else
      Sig := Sig + Format(', %s %%_par_%s', QbeTypeOf(Par.ResolvedType), Par.ParamName);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(AMethod.ResolvedReturnType);
    if AMethod.ResolvedReturnType.Kind = tyRecord then
    begin
      Sig := 'l %_par__sret, ' + Sig;
      EmitLine(Format('function %s(%s) {', FuncName, Sig));
    end
    else
      EmitLine(Format('function %s %s(%s) {', RetQType, FuncName, Sig));
  end
  else
    EmitLine(Format('function %s(%s) {', FuncName, Sig));

  EmitLine('@start');
  EmitParamAllocs(AMethod, nil);

  



  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Get(I));
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
    end;
  end;

  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  %_var_Result =l copy %_par__sret')
    else if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('method_exit');
  try
    EmitBlock(AMethod.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Get(I));
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_ClassRelease(l %s)', ValTemp));
    end;
  end;

  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')
    else
    begin
      RetTemp := AllocTemp;
      if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', RetTemp))
      else
        EmitLine(Format('  %s =l loadl %%_var_Result', RetTemp));
      EmitLine(Format('  ret %s', RetTemp));
    end;
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitTypeInfoDefs(AProg: TProgram);










var
  I:         Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  GI:        TGenericInstance;
  ParentStr: string;
  ImplStr:   string;
  MName:     string;
begin
  EmitLine('data $typeinfo_TObject = { l 0, l 0 }');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + RT.Parent.Name
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := '$impllist_' + TD.Name
    else
      ImplStr := '0';
    EmitLine('data $typeinfo_' + TD.Name +
             ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances.Get(I));
    RT    := TRecordTypeDesc(GI.TypeDesc);
    MName := QBEMangle(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
    else
      ParentStr := '0';
    ImplStr := '0';
    EmitLine('data $typeinfo_' + MName + ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitVTableDefs(AProg: TProgram);


var
  I, S:  Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
  E:     TVTableEntry;
  Line:  string;
  MName: string;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable then Continue;
    
    Line := 'data $vtable_' + TD.Name + ' = { l $typeinfo_' + TD.Name;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + E.ImplName;
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances.Get(I));
    RT    := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable then Continue;
    MName := QBEMangle(GI.TypeName);
    Line  := 'data $vtable_' + MName + ' = { l $typeinfo_' + MName;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + QBEMangle(E.ImplName);
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitInterfaceDefs(AProg: TProgram);





var
  I, J, K:     Integer;
  TD:          TTypeDecl;
  TDesc:       TTypeDesc;
  IntfDesc:    TInterfaceTypeDesc;
  ClassRT:     TRecordTypeDesc;
  ItabLine:    string;
  ImplLine:    string;
  MethName:    string;
  IntfMangle:  string;
  GII:         TGenericInterfaceInstance;
begin
  
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    EmitLine('data $typeinfo_' + TD.Name + ' = { l 0 }');
  end;

  
  for I := 0 to AProg.GenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AProg.GenericIntfInstances.Get(I));
    EmitLine('data $typeinfo_' + GII.InstName + ' = { l 0 }');
  end;

  
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    if ClassRT.ImplementsCount = 0 then Continue;

    
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + TD.Name + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if K = 0 then
          ItabLine := ItabLine + ' l $' + TD.Name + '_' + MethName
        else
          ItabLine := ItabLine + ', l $' + TD.Name + '_' + MethName;
      end;
      ItabLine := ItabLine + ' }';
      EmitLine(ItabLine);
    end;

    
    ImplLine := 'data $impllist_' + TD.Name + ' = {';
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle;
    end;
    ImplLine := ImplLine + ', l 0 }';
    EmitLine(ImplLine);
  end;
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupFn(const AMangledName: string;
                                         ARec: TRecordTypeDesc);














var
  I:      Integer;
  F:      TFieldInfo;
  Temp:   string;
  PtrT:   string;
begin
  EmitLine(Format('function $_FieldCleanup_%s(l %%self) {', AMangledName));
  EmitLine('@start');
  

  if ARec.HasDestroyMethod then
    EmitLine(Format('  call $%s_Destroy(l %%self)', AMangledName));
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Get(I));
    if F.TypeDesc = nil then Continue;
    if not (F.TypeDesc.IsString or (F.TypeDesc.Kind = tyClass)) then
      Continue;
    if F.Offset > 0 then
    begin
      PtrT := AllocTemp;
      EmitLine(Format('  %s =l add %%self, %d', PtrT, F.Offset));
    end
    else
      PtrT := '%self';
    if F.IsWeak then
    begin
      

      EmitLine(Format('  call $_WeakClear(l %s)', PtrT));
      Continue;
    end;
    Temp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', Temp, PtrT));
    if F.TypeDesc.IsString then
      EmitLine(Format('  call $_StringRelease(l %s)', Temp))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', Temp));
  end;
  EmitLine('  ret');
  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupDefs(AProg: TProgram);



var
  I:     Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    EmitFieldCleanupFn(TD.Name, RT);
  end;
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Get(I));
    RT := TRecordTypeDesc(GI.TypeDesc);
    EmitFieldCleanupFn(QBEMangle(GI.TypeName), RT);
  end;
end;

procedure TCodeGenQBE.EmitMethodDefs(AProg: TProgram);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  GI:    TGenericInstance;
  MDecl: TMethodDecl;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Get(I));
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD := TClassTypeDef(TD.Def);
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Get(J)).Body <> nil then
        EmitMethodDef(TD.Name, TMethodDecl(CD.Methods.Get(J)));
  end;

  
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Get(I));
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(GI.ClassDef.Methods.Get(J));
      if MDecl.Body <> nil then
        EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
    end;
  end;
end;

function TCodeGenQBE.IsRecordCall(AExpr: TASTExpr): Boolean;
var
  MDecl: TMethodDecl;
  FldA:  TFieldAccessExpr;
begin
  Result := False;
  if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).ResolvedDecl = nil then Exit;
    MDecl  := TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end
  else if AExpr is TMethodCallExpr then
  begin
    if TMethodCallExpr(AExpr).ResolvedMethod = nil then Exit;
    MDecl  := TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldA := TFieldAccessExpr(AExpr);
    if not FldA.IsMethodCall then Exit;
    if FldA.ResolvedMethod = nil then Exit;
    MDecl  := TMethodDecl(FldA.ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end;
end;

procedure TCodeGenQBE.EmitRecordReleaseFields(ARec: TRecordTypeDesc;
  const AAddr: string);
var
  I:       Integer;
  F:       TFieldInfo;
  FldAddr: string;
  ValT:    string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Get(I));
    if F.TypeDesc = nil then Continue;
    if not (F.TypeDesc.IsString or (F.TypeDesc.Kind = tyClass)) then Continue;
    if F.Offset > 0 then
    begin
      FldAddr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', FldAddr, AAddr, F.Offset));
    end
    else
      FldAddr := AAddr;
    ValT := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', ValT, FldAddr));
    if F.TypeDesc.IsString then
      EmitLine(Format('  call $_StringRelease(l %s)', ValT))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', ValT));
  end;
end;

procedure TCodeGenQBE.EmitRecordCopy(ARec: TRecordTypeDesc;
  const ADestAddr, ASrcAddr: string);
var
  I:        Integer;
  F:        TFieldInfo;
  SrcField: string;
  DstField: string;
  ValTemp:  string;
  OldTemp:  string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Get(I));
    if F.TypeDesc = nil then Continue;
    if F.Offset > 0 then
    begin
      SrcField := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', SrcField, ASrcAddr, F.Offset));
      DstField := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', DstField, ADestAddr, F.Offset));
    end
    else
    begin
      SrcField := ASrcAddr;
      DstField := ADestAddr;
    end;
    if F.TypeDesc.IsString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', ValTemp, SrcField));
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', OldTemp, DstField));
      EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
      EmitLine(Format('  call $_StringRelease(l %s)', OldTemp));
      EmitLine(Format('  storel %s, %s', ValTemp, DstField));
    end
    else if F.TypeDesc.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', ValTemp, SrcField));
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', OldTemp, DstField));
      EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
      EmitLine(Format('  call $_ClassRelease(l %s)', OldTemp));
      EmitLine(Format('  storel %s, %s', ValTemp, DstField));
    end
    else if QbeTypeOf(F.TypeDesc) = 'w' then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =w loadw %s', ValTemp, SrcField));
      EmitLine(Format('  storew %s, %s', ValTemp, DstField));
    end
    else
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', ValTemp, SrcField));
      EmitLine(Format('  storel %s, %s', ValTemp, DstField));
    end;
  end;
end;

procedure TCodeGenQBE.EmitRecordCallSret(AExpr: TASTExpr;
  const ASretAddr: string);
var
  FCallExpr: TFuncCallExpr;
  MCallExpr: TMethodCallExpr;
  FldAccess: TFieldAccessExpr;
  MDecl:     TMethodDecl;
  ArgLine:   string;
  ArgTemp:   string;
  SelfTemp:  string;
  Par:       TMethodParam;
  I:         Integer;
  FuncName:  string;
  Ptr:       string;
begin
  if AExpr is TFuncCallExpr then
  begin
    FCallExpr := TFuncCallExpr(AExpr);
    MDecl := TMethodDecl(FCallExpr.ResolvedDecl);
    if FCallExpr.IsImplicitSelfMethod then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', SelfTemp));
      FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + FCallExpr.Name);
      ArgLine  := Format('l %s, l %s', ASretAddr, SelfTemp);
    end
    else
    begin
      FuncName := '$' + QBEMangle(FCallExpr.Name);
      ArgLine  := Format('l %s', ASretAddr);
    end;
    for I := 0 to FCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(FCallExpr.Args.Get(I)))))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(FCallExpr.Args.Get(I)));
        ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
      end;
    end;
    EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
  end
  else if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);
    MDecl     := TMethodDecl(MCallExpr.ResolvedMethod);
    SelfTemp  := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)));
    FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + MCallExpr.Name);
    ArgLine  := Format('l %s, l %s', ASretAddr, SelfTemp);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(MCallExpr.Args.Get(I)))))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Get(I)));
        ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
      end;
    end;
    EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    MDecl     := TMethodDecl(FldAccess.ResolvedMethod);
    if FldAccess.IsImplicitSelf then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', SelfTemp));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, SelfTemp, FldAccess.ImplicitBaseInfo.Offset));
        SelfTemp := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', Ptr, SelfTemp));
        SelfTemp := Ptr;
      end;
    end
    else
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)));
    end;
    FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + FldAccess.FieldName);
    ArgLine  := Format('l %s, l %s', ASretAddr, SelfTemp);
    EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
  end;
end;

procedure TCodeGenQBE.EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
var
  Sig:          string;
  I:            Integer;
  Par:          TMethodParam;
  FuncName:     string;
  IsFunc:       Boolean;
  RetQType:     string;
  RetTemp:      string;
  ValTemp:      string;
  Prefix:       string;
  SavedExitLbl: string;
begin
  FuncName := '$' + QBEMangle(ADecl.Name);
  IsFunc   := ADecl.ResolvedReturnType <> nil;
  if AExported then Prefix := 'export ' else Prefix := '';

  Sig := '';
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Get(I));
    if Sig <> '' then Sig := Sig + ', ';
    if Par.IsVarParam then
      Sig := Sig + Format('l %%_par_%s', Par.ParamName)
    else
      Sig := Sig + Format('%s %%_par_%s', QbeTypeOf(Par.ResolvedType), Par.ParamName);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(ADecl.ResolvedReturnType);
    if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      if Sig <> '' then Sig := 'l %_par__sret, ' + Sig
      else Sig := 'l %_par__sret';
      EmitLine(Format('%sfunction %s(%s) {', Prefix, FuncName, Sig));
    end
    else
      EmitLine(Format('%sfunction %s %s(%s) {', Prefix, RetQType, FuncName, Sig));
  end
  else
    EmitLine(Format('%sfunction %s(%s) {', Prefix, FuncName, Sig));

  EmitLine('@start');

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Get(I));
    if Par.IsVarParam then
    begin
      
      EmitLine(Format('  %%_var_%s =l alloc8 1', Par.ParamName));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
    end
    else
    begin
      case Par.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', Par.ParamName));
            EmitLine(Format('  storew %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
          end;
      else
        EmitLine(Format('  %%_var_%s =l alloc8 1', Par.ParamName));
        EmitLine(Format('  storel %%_par_%s, %%_var_%s', Par.ParamName, Par.ParamName));
      end;
    end;
  end;

  

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Get(I));
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_ClassAddRef(l %s)', ValTemp));
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  %_var_Result =l copy %_par__sret')
    else if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('func_exit');
  try
    EmitBlock(ADecl.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Get(I));
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_StringRelease(l %s)', ValTemp));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', ValTemp, Par.ParamName));
      EmitLine(Format('  call $_ClassRelease(l %s)', ValTemp));
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')
    else
    begin
      RetTemp := AllocTemp;
      if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', RetTemp))
      else
        EmitLine(Format('  %s =l loadl %%_var_Result', RetTemp));
      EmitLine(Format('  ret %s', RetTemp));
    end;
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitStandaloneDef(ADecl: TMethodDecl);
begin
  EmitFuncDef(ADecl, False);
end;

procedure TCodeGenQBE.EmitStandaloneDefs(AProg: TProgram);
var
  I:    Integer;
  Decl: TMethodDecl;
begin
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Get(I));
    
    if Decl.OwnerTypeName <> '' then Continue;
    
    if Decl.TypeParams <> nil then Continue;
    
    if Decl.Body = nil then Continue;
    EmitStandaloneDef(Decl);
  end;
  
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    EmitStandaloneDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Get(I)).MethodDecl);
end;

procedure TCodeGenQBE.EmitProcCall(ACall: TProcCall);
var
  UCaseName: string;
  MDecl:     TMethodDecl;
  Par:       TMethodParam;
  ArgTemp:   string;
  ArgTemp2:  string;
  SizeTemp:  string;
  ArgLine:   string;
  I:         Integer;
begin
  
  if ACall.ResolvedDecl <> nil then
  begin
    MDecl := TMethodDecl(ACall.ResolvedDecl);
    if ACall.IsImplicitSelfMethod then
    begin
      
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', ArgTemp));
      ArgLine := Format('l %s', ArgTemp);
      for I := 0 to ACall.Args.Count - 1 do
      begin
        Par     := TMethodParam(MDecl.Params.Get(I));
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(I)));
        ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
      end;
      EmitLine(Format('  call $%s_%s(%s)', MDecl.OwnerTypeName, ACall.Name, ArgLine));
      Exit;
    end;
    ArgLine := '';
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      if Par.IsVarParam then
        ArgLine := ArgLine + Format('l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Get(I)))))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(I)));
        ArgLine := ArgLine + Format('%s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
      end;
    end;
    EmitLine(Format('  call $%s(%s)', QBEMangle(ACall.Name), ArgLine));
    Exit;
  end;

  
  UCaseName := UpperCase(ACall.Name);
  if UCaseName = 'WRITELN' then
    EmitWrite(ACall, True)
  else if UCaseName = 'WRITE' then
    EmitWrite(ACall, False)
  else if UCaseName = 'FREEMEM' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    EmitLine(Format('  call $free(l %s)', ArgTemp));
  end
  else if UCaseName = 'ZEROMEM' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Get(1)));
    SizeTemp := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', SizeTemp, ArgTemp2));
    EmitLine(Format('  call $memset(l %s, w 0, l %s)', ArgTemp, SizeTemp));
  end
  else if UCaseName = '_CLASSADDREF' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    EmitLine(Format('  call $_ClassAddRef(l %s)', ArgTemp));
  end
  else if UCaseName = '_CLASSRELEASE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    EmitLine(Format('  call $_ClassRelease(l %s)', ArgTemp));
  end
  else if UCaseName = 'WRITEFILE' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Get(1)));
    EmitLine(Format('  call $_WriteFile(l %s, l %s)', ArgTemp, ArgTemp2));
  end
  else if UCaseName = 'APPENDFILE' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Get(1)));
    EmitLine(Format('  call $_AppendFile(l %s, l %s)', ArgTemp, ArgTemp2));
  end
  else if UCaseName = 'HALT' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    EmitLine(Format('  call $exit(w %s)', ArgTemp));
  end
  else if UCaseName = 'DELETEFILE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Get(0)));
    EmitLine(Format('  call $_DeleteFile(l %s)', ArgTemp));
  end
  else
    raise ECodeGenError.Create(Format('Unknown procedure ''%s'' at line %d', ACall.Name, ACall.Line));
end;

procedure TCodeGenQBE.EmitPointerWrite(AStmt: TPointerWriteStmt);
var
  PtrTemp:    string;
  ValTemp:    string;
  OldTemp:    string;
  QType:      string;
  StoreInstr: string;
begin
  PtrTemp := EmitExpr(AStmt.PtrExpr);
  
  if (AStmt.BaseTy <> nil) and AStmt.BaseTy.IsString then
  begin
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', OldTemp, PtrTemp));
    ValTemp := EmitExpr(AStmt.ValExpr);
    EmitLine(Format('  call $_StringAddRef(l %s)', ValTemp));
    EmitLine(Format('  call $_StringRelease(l %s)', OldTemp));
    EmitLine(Format('  storel %s, %s', ValTemp, PtrTemp));
    Exit;
  end;
  ValTemp := EmitExpr(AStmt.ValExpr);
  QType   := QbeTypeOf(AStmt.BaseTy);
  if QType = 'w' then StoreInstr := 'storew'
                 else StoreInstr := 'storel';
  EmitLine(Format('  %s %s, %s', StoreInstr, ValTemp, PtrTemp));
end;

procedure TCodeGenQBE.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  ArgExpr:  TASTExpr;
  ArgTemp:  string;
  CharPtr:  string;
  IsString: Boolean;
  I:        Integer;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
      EmitLine('  call $printf(l $__fmt_nl)');
    Exit;
  end;

  


  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgExpr  := TASTExpr(ACall.Args.Get(I));
    IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString;
    ArgTemp  := EmitExpr(ArgExpr);
    if IsString then
    begin
      
      CharPtr := AllocTemp;
      EmitLine(Format('  %s =l add %s, 12', CharPtr, ArgTemp));
      EmitLine(Format('  call $printf(l $__fmt_s, ..., l %s)', CharPtr));
    end
    else
      EmitLine(Format('  call $printf(l $__fmt_d, ..., w %s)', ArgTemp));
  end;

  if ANewline then
    EmitLine('  call $printf(l $__fmt_nl)');
end;

function TCodeGenQBE.EmitExpr(AExpr: TASTExpr): string;
var
  T, L, R:    string;
  Op:         string;
  BinExpr:    TBinaryExpr;
  FldAccess:  TFieldAccessExpr;
  MCallExpr:  TMethodCallExpr;
  Ptr:        string;
  QType:      string;
  LoadInstr:  string;
  SelfTemp:   string;
  ArgLine:    string;
  ArgTemp:    string;
  Par:        TMethodParam;
  MDecl:      TMethodDecl;
  RT:         TRecordTypeDesc;
  FuncName:   string;
  I:          Integer;
  IntfDesc:     TInterfaceTypeDesc;
  VTblTemp:     string;
  FPtrTemp:     string;
  SlotOff:      Integer;
  NoArgCall:    TFuncCallExpr;
  ImplFld:      TFieldInfo;
  SelfT:        string;
  PtrT:         string;
  SretBuf:      string;
begin
  if AExpr is TFuncCallExpr then
  begin
    
    begin
      
      if SameText(TFuncCallExpr(AExpr).Name, 'SizeOf') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w copy %d', T, TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)).ResolvedType.ByteSize));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'GetMem') then
      begin
        ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        
        L := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', L, ArgTemp));
        EmitLine(Format('  %s =l call $malloc(l %s)', T, L));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'ReallocMem') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', ArgTemp, R));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $realloc(l %s, l %s)', T, L, ArgTemp));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'Length') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringLength(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'Pos') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringPos(l %s, l %s)', T, L, R));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'Copy') then
      begin
        L       := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R       := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(2)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringCopy(l %s, w %s, w %s)', T, L, R, ArgTemp));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'UpperCase') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringUpperCase(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'LowerCase') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringLowerCase(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'Trim') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringTrim(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'SameText') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringSameText(l %s, l %s)', T, L, R));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'IntToStr') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_IntToStr(w %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'StrToInt') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StrToInt(l %s)', T, L));
        Result := T;
        Exit;
      end;

      


      if SameText(TFuncCallExpr(AExpr).Name, 'Format') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        
        ArgLine := Format('l %s, ...', L);
        for I := 1 to TFuncCallExpr(AExpr).Args.Count - 1 do
        begin
          ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)));
          if ((TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyInteger) or (TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyBoolean) or (TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyByte) or (TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyUInt32) or (TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyInt64) or (TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)).ResolvedType.Kind = tyEnum)) then
            ArgLine := ArgLine + Format(', w 0, w %s', ArgTemp)
          else
            ArgLine := ArgLine + Format(', w 1, l %s', ArgTemp);
        end;
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringFormat(%s)', T, ArgLine));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'OrdAt') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_OrdAt(l %s, w %s)', T, L, R));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'Chr') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_Chr(w %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'CompareStr') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringCompare(l %s, l %s)', T, L, R));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'CompareText') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        R := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringCompareText(l %s, l %s)', T, L, R));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'ParamCount') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_ParamCount()', T));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'ParamStr') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ParamStr(w %s)', T, L));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'ReadFile') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ReadFile(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'FileExists') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_FileExists(l %s)', T, L));
        Result := T;
        Exit;
      end;

      
      if SameText(TFuncCallExpr(AExpr).Name, 'GetEnvVar') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_GetEnvVar(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'CurrentExceptionMessage') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_CurrentExceptionMessage()', T));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'Exec') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_Exec(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'ChangeFileExt') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ChangeFileExt(l %s, l %s)',
          T, L, EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(1)))));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFileName') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFileName(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'ExtractFilePath') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFilePath(l %s)', T, L));
        Result := T;
        Exit;
      end;

      if SameText(TFuncCallExpr(AExpr).Name, 'IncludeTrailingPathDelimiter') then
      begin
        L := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_IncludeTrailingPathDelimiter(l %s)', T, L));
        Result := T;
        Exit;
      end;

      
      if TFuncCallExpr(AExpr).ResolvedDecl = nil then
      begin
        ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(0)));
        T       := AllocTemp;
        QType   := QbeTypeOf(TFuncCallExpr(AExpr).ResolvedType);
        if QType = 'w' then
          EmitLine(Format('  %s =w copy %s', T, ArgTemp))
        else
          EmitLine(Format('  %s =l copy %s', T, ArgTemp));
        Result := T;
        Exit;
      end;

      MDecl    := TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl);
      QType    := QbeTypeOf(MDecl.ResolvedReturnType);
      if MDecl.ResolvedReturnType.Kind = tyRecord then
      begin
        RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
        SretBuf := AllocTemp;
        if RT.MaxAlign >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', SretBuf, RT.TotalSize))
        else
          EmitLine(Format('  %s =l alloc4 %d', SretBuf, RT.TotalSize));
        if RT.TotalSize > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', SretBuf, RT.TotalSize));
        EmitRecordCallSret(AExpr, SretBuf);
        Result := SretBuf;
        Exit;
      end;
      if TFuncCallExpr(AExpr).IsImplicitSelfMethod then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_Self', ArgTemp));
        ArgLine  := Format('l %s', ArgTemp);
        FuncName := '$' + MDecl.OwnerTypeName + '_' + TFuncCallExpr(AExpr).Name;
        for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Get(I));
          if Par.IsVarParam then
            ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)))))
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)));
            ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
          end;
        end;
        T := AllocTemp;
        EmitLine(Format('  %s =%s call %s(%s)', T, QType, FuncName, ArgLine));
        Result := T;
        Exit;
      end;
      FuncName := '$' + QBEMangle(TFuncCallExpr(AExpr).Name);
      ArgLine  := '';
      for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Get(I));
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        if Par.IsVarParam then
          ArgLine := ArgLine + Format('l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)))))
        else
        begin
          ArgTemp := EmitExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Get(I)));
          ArgLine := ArgLine + Format('%s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
        end;
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =%s call %s(%s)', T, QType, FuncName, ArgLine));
      Result := T;
    end;
    Exit;
  end;

  if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);

    
    if (MCallExpr.ResolvedClassType <> nil) and
       (MCallExpr.ResolvedClassType.Kind = tyInterface) then
    begin
      IntfDesc := TInterfaceTypeDesc(MCallExpr.ResolvedClassType);
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj', SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)));
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_itab', VTblTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)));
      SlotOff := IntfDesc.MethodIndex(MCallExpr.Name) * 8;
      FPtrTemp := AllocTemp;
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', FPtrTemp, VTblTemp))
      else
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', ArgTemp, VTblTemp, SlotOff));
        EmitLine(Format('  %s =l loadl %s', FPtrTemp, ArgTemp));
      end;
      
      ArgLine := Format('l %s', SelfTemp);
      for I := 0 to MCallExpr.Args.Count - 1 do
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Get(I)));
        ArgLine := ArgLine + Format(', w %s', ArgTemp);
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =w call %s(%s)', T, FPtrTemp, ArgLine));
      Result := T;
      Exit;
    end;

    RT := TRecordTypeDesc(MCallExpr.ResolvedClassType);

    
    if MCallExpr.IsConstructorCall then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)', SelfTemp, RT.TotalSize, RT.Name));
      if RT.HasVTable then
        EmitLine(Format('  storel $vtable_%s, %s', QBEMangle(RT.Name), SelfTemp));
      EmitLine(Format('  call $_ClassAddRef(l %s)', SelfTemp));
      
      if MCallExpr.ResolvedMethod <> nil then
      begin
        MDecl   := TMethodDecl(MCallExpr.ResolvedMethod);
        ArgLine := Format('l %s', SelfTemp);
        for I := 0 to MCallExpr.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Get(I));
          ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Get(I)));
          ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
        end;
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MDecl.OwnerTypeName + '_' + MCallExpr.Name
        else
          FuncName := '$' + RT.Name + '_' + MCallExpr.Name;
        EmitLine(Format('  call %s(%s)', FuncName, ArgLine));
      end;
      Result := SelfTemp;
      Exit;
    end;

    MDecl     := TMethodDecl(MCallExpr.ResolvedMethod);
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + MCallExpr.Name
    else
      FuncName := '$' + RT.Name + '_' + MCallExpr.Name;
    QType     := QbeTypeOf(MDecl.ResolvedReturnType);
    if MDecl.ResolvedReturnType.Kind = tyRecord then
    begin
      RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
      SretBuf := AllocTemp;
      if RT.MaxAlign >= 8 then
        EmitLine(Format('  %s =l alloc8 %d', SretBuf, RT.TotalSize))
      else
        EmitLine(Format('  %s =l alloc4 %d', SretBuf, RT.TotalSize));
      if RT.TotalSize > 0 then
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', SretBuf, RT.TotalSize));
      EmitRecordCallSret(AExpr, SretBuf);
      Result := SretBuf;
      Exit;
    end;

    if MCallExpr.ObjExpr <> nil then
      SelfTemp := EmitExpr(MCallExpr.ObjExpr)
    else
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)));
    end;

    
    ArgLine := Format('l %s', SelfTemp);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Get(I));
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s', EmitVarArgAddr(TIdentExpr(TASTExpr(MCallExpr.Args.Get(I)))))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Get(I)));
        ArgLine := ArgLine + Format(', %s %s', QbeTypeOf(Par.ResolvedType), ArgTemp);
      end;
    end;

    T := AllocTemp;
    if MDecl.VTableSlot >= 0 then
    begin
      
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', VTblTemp, SelfTemp));
      FPtrTemp := AllocTemp;
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', ArgTemp, VTblTemp, SlotOff));
      EmitLine(Format('  %s =l loadl %s', FPtrTemp, ArgTemp));
      EmitLine(Format('  %s =%s call %s(%s)', T, QType, FPtrTemp, ArgLine));
    end
    else
      EmitLine(Format('  %s =%s call %s(%s)', T, QType, FuncName, ArgLine));
    Result := T;
    Exit;
  end;

  if AExpr is TNilLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =l copy 0', T));
    Result := T;
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =w copy %d', T, TIntLiteral(AExpr).Value));
    Result := T;
  end
  else if AExpr is TStringLiteral then
  begin
    Result := EmitStrLit(TStringLiteral(AExpr).Value);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    

    if FldAccess.Base <> nil then
    begin
      if FldAccess.IsMethodCall then
      begin
        L     := EmitInstancePtr(FldAccess.Base);
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.ResolvedReturnType.Kind = tyRecord then
        begin
          RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
          SretBuf := AllocTemp;
          if RT.MaxAlign >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', SretBuf, RT.TotalSize))
          else
            EmitLine(Format('  %s =l alloc4 %d', SretBuf, RT.TotalSize));
          if RT.TotalSize > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', SretBuf, RT.TotalSize));
          EmitLine(Format('  call $%s_%s(l %s, l %s)', MDecl.OwnerTypeName, FldAccess.FieldName, SretBuf, L));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s_%s(l %s)', T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L));
          Result := T;
        end;
        Exit;
      end;
      L := EmitInstancePtr(FldAccess.Base);
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.Create(Format('Chained field ''%s'' has no resolved field info', FldAccess.FieldName));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, L, FldAccess.FieldInfo.Offset));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', T, QType, LoadInstr, Ptr));
      Result := T;
      Exit;
    end;
    if FldAccess.IsImplicitSelf then
    begin
      
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', L));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, L, FldAccess.ImplicitBaseInfo.Offset));
        L := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', Ptr, L));
        L := Ptr;
      end;
      if FldAccess.IsMethodCall then
      begin
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.ResolvedReturnType.Kind = tyRecord then
        begin
          RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
          SretBuf := AllocTemp;
          if RT.MaxAlign >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', SretBuf, RT.TotalSize))
          else
            EmitLine(Format('  %s =l alloc4 %d', SretBuf, RT.TotalSize));
          if RT.TotalSize > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', SretBuf, RT.TotalSize));
          EmitLine(Format('  call $%s_%s(l %s, l %s)', MDecl.OwnerTypeName, FldAccess.FieldName, SretBuf, L));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s_%s(l %s)', T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L));
          Result := T;
        end;
        Exit;
      end;
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, L, FldAccess.FieldInfo.Offset));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', T, QType, LoadInstr, Ptr));
      Result := T;
    end
    else if FldAccess.IsMethodCall then
    begin
      MDecl := TMethodDecl(FldAccess.ResolvedMethod);
      if MDecl.ResolvedReturnType.Kind = tyRecord then
      begin
        RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
        SretBuf := AllocTemp;
        if RT.MaxAlign >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', SretBuf, RT.TotalSize))
        else
          EmitLine(Format('  %s =l alloc4 %d', SretBuf, RT.TotalSize));
        if RT.TotalSize > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', SretBuf, RT.TotalSize));
        EmitRecordCallSret(AExpr, SretBuf);
        Result := SretBuf;
      end
      else
      begin
        L := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)));
        QType := QbeTypeOf(MDecl.ResolvedReturnType);
        T := AllocTemp;
        EmitLine(Format('  %s =%s call $%s_%s(l %s)', T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L));
        Result := T;
      end;
    end
    else if FldAccess.IsConstructorCall then
    begin
      T := AllocTemp;
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)', T, TRecordTypeDesc(FldAccess.ResolvedType).TotalSize,
         QBEMangle(FldAccess.ResolvedType.Name)));
      if TRecordTypeDesc(FldAccess.ResolvedType).HasVTable then
        EmitLine(Format('  storel $vtable_%s, %s', QBEMangle(FldAccess.ResolvedType.Name), T));
      if FldAccess.ResolvedMethod <> nil then
      begin
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MDecl.OwnerTypeName + '_' + FldAccess.FieldName
        else
          FuncName := '$' + QBEMangle(FldAccess.ResolvedType.Name) + '_' + FldAccess.FieldName;
        EmitLine(Format('  call %s(l %s)', FuncName, T));
      end;
      Result := T;
    end
    else if FldAccess.PropRead <> nil then
    begin
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)));
      T     := AllocTemp;
      QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
      EmitLine(Format('  %s =%s call $%s_%s(l %s)', T, QType, QBEMangle(FldAccess.PropOwnerType),
         FldAccess.PropRead.ReadMethod, L));
      Result := T;
    end
    else if FldAccess.IsClassAccess then
    begin
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', Ptr, L, FldAccess.FieldInfo.Offset));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', T, QType, LoadInstr, Ptr));
      Result := T;
    end
    else
    begin
      
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.Create(Format('Field access ''%s.%s'' has no resolved field info', FldAccess.RecordName, FldAccess.FieldName));
      Ptr   := FieldPtr(FldAccess.RecordName, FldAccess.FieldInfo.Offset);
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', T, QType, LoadInstr, Ptr));
      Result := T;
    end;
  end
  else if AExpr is TIdentExpr then
  begin
    T := AllocTemp;
    if TIdentExpr(AExpr).IsImplicitSelf then
    begin
      ImplFld := TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo);
      SelfT   := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', SelfT));
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyRecord) then
      begin
        if ImplFld.Offset > 0 then
        begin
          PtrT := AllocTemp;
          EmitLine(Format('  %s =l add %s, %d', PtrT, SelfT, ImplFld.Offset));
          Result := PtrT;
        end
        else
          Result := SelfT;
        Exit;
      end;
      T := AllocTemp;
      QType := QbeTypeOf(AExpr.ResolvedType);
      if ImplFld.Offset > 0 then
      begin
        PtrT := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', PtrT, SelfT, ImplFld.Offset));
        if QType = 'w' then
          EmitLine(Format('  %s =w loadw %s', T, PtrT))
        else
          EmitLine(Format('  %s =l loadl %s', T, PtrT));
      end
      else
      begin
        if QType = 'w' then
          EmitLine(Format('  %s =w loadw %s', T, SelfT))
        else
          EmitLine(Format('  %s =l loadl %s', T, SelfT));
      end;
      Result := T;
      Exit;
    end;

    if TIdentExpr(AExpr).IsImplicitSelfMethod then
    begin
      
      NoArgCall := TFuncCallExpr.Create;
      try
        NoArgCall.Name                 := TIdentExpr(AExpr).Name;
        NoArgCall.ResolvedType         := AExpr.ResolvedType;
        NoArgCall.ResolvedDecl         := TIdentExpr(AExpr).ImplicitMethodDecl;
        NoArgCall.IsImplicitSelfMethod := True;
        Result := EmitExpr(NoArgCall);
      finally
        NoArgCall.Free;
      end;
      Exit;
    end
    else if TIdentExpr(AExpr).IsNoArgFuncCall then
    begin
      NoArgCall := TFuncCallExpr.Create;
      try
        NoArgCall.Name         := TIdentExpr(AExpr).Name;
        NoArgCall.ResolvedType := AExpr.ResolvedType;
        NoArgCall.ResolvedDecl := TIdentExpr(AExpr).NoArgFuncDecl;
        Result := EmitExpr(NoArgCall);
      finally
        NoArgCall.Free;
      end;
      Exit;
    end
    else if TIdentExpr(AExpr).IsConstant then
    begin
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyString) then
        EmitLine(Format('  %s =l copy %s', T, EmitStrLit(TIdentExpr(AExpr).ConstString)))
      else
        EmitLine(Format('  %s =w copy %d', T, TIdentExpr(AExpr).ConstValue));
    end
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', Ptr, TIdentExpr(AExpr).Name));
      QType := QbeTypeOf(AExpr.ResolvedType);
      if QType = 'l' then
        EmitLine(Format('  %s =l loadl %s', T, Ptr))
      else
        EmitLine(Format('  %s =w loadw %s', T, Ptr));
    end
    else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyRecord) then
    begin
      Result := VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal);
      Exit;
    end
    else if TIdentExpr(AExpr).IsGlobal then
    begin
      if (AExpr.ResolvedType <> nil) and (QbeTypeOf(AExpr.ResolvedType) = 'w') then
        EmitLine(Format('  %s =w loadw $%s', T, TIdentExpr(AExpr).Name))
      else
        EmitLine(Format('  %s =l loadl $%s', T, TIdentExpr(AExpr).Name));
    end
    else if (AExpr.ResolvedType <> nil) and (QbeTypeOf(AExpr.ResolvedType) = 'l') then
    begin
      EmitLine(Format('  %s =l loadl %%_var_%s', T, TIdentExpr(AExpr).Name));
    end
    else
    begin
      EmitLine(Format('  %s =w loadw %%_var_%s', T, TIdentExpr(AExpr).Name));
    end;
    Result := T;
  end
  else if AExpr is TBinaryExpr then
  begin
    BinExpr := TBinaryExpr(AExpr);
    if (BinExpr.Op = boAnd) or (BinExpr.Op = boOr) then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l alloc4 1', SelfTemp));
      L := EmitExpr(BinExpr.Left);
      EmitLine(Format('  storew %s, %s', L, SelfTemp));
      FuncName := AllocLabel('sc_rhs');
      ArgLine  := AllocLabel('sc_end');
      if BinExpr.Op = boAnd then
        EmitLine(Format('  jnz %s, @%s, @%s', L, FuncName, ArgLine))
      else
        EmitLine(Format('  jnz %s, @%s, @%s', L, ArgLine, FuncName));
      EmitLine('@' + FuncName);
      R := EmitExpr(BinExpr.Right);
      EmitLine(Format('  storew %s, %s', R, SelfTemp));
      EmitLine(Format('  jmp @%s', ArgLine));
      EmitLine('@' + ArgLine);
      T := AllocTemp;
      EmitLine(Format('  %s =w loadw %s', T, SelfTemp));
      Result := T;
      Exit;
    end;
    L := EmitExpr(BinExpr.Left);
    R := EmitExpr(BinExpr.Right);
    T := AllocTemp;
    
    if (BinExpr.Op = boAdd) and
       (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString then
    begin
      if BinExpr.Left is TBinaryExpr then
        EmitLine(Format('  call $_StringAddRef(l %s)', L));
      if (BinExpr.Right is TBinaryExpr) or
         (BinExpr.Right is TFuncCallExpr) or
         (BinExpr.Right is TMethodCallExpr) then
        EmitLine(Format('  call $_StringAddRef(l %s)', R));
      EmitLine(Format('  %s =l call $_StringConcat(l %s, l %s)', T, L, R));
      if BinExpr.Left is TBinaryExpr then
        EmitLine(Format('  call $_StringRelease(l %s)', L));
      if (BinExpr.Right is TBinaryExpr) or
         (BinExpr.Right is TFuncCallExpr) or
         (BinExpr.Right is TMethodCallExpr) then
        EmitLine(Format('  call $_StringRelease(l %s)', R));
      Result := T;
      Exit;
    end;
    
    if (((BinExpr.Op = boAdd) or (BinExpr.Op = boSub))) and
       (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind = tyPointer) then
    begin
      
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', ArgTemp, R));
      if BinExpr.Op = boAdd then
        EmitLine(Format('  %s =l add %s, %s', T, L, ArgTemp))
      else
        EmitLine(Format('  %s =l sub %s, %s', T, L, ArgTemp));
      Result := T;
      Exit;
    end;
    
    if (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString and
       (((BinExpr.Op = boEQ) or (BinExpr.Op = boNE))) then
    begin
      EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)', T, L, R));
      if BinExpr.Op = boNE then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =w ceqw %s, 0', ArgTemp, T));
        T := ArgTemp;
      end;
      Result := T;
      Exit;
    end;
    
    if (BinExpr.Left.ResolvedType <> nil) and
       (((BinExpr.Left.ResolvedType.Kind = tyClass) or (BinExpr.Left.ResolvedType.Kind = tyNil))) then
    begin
      case BinExpr.Op of
        boEQ: Op := 'ceql';
        boNE: Op := 'cnel';
      else
        Op := 'ceql';
      end;
      EmitLine(Format('  %s =w %s %s, %s', T, Op, L, R));
    end
    else
    begin
      case BinExpr.Op of
        boAdd: Op := 'add';
        boSub: Op := 'sub';
        boMul: Op := 'mul';
        boDiv: Op := 'div';
        boEQ:  Op := 'ceqw';
        boNE:  Op := 'cnew';
        boLT:  Op := 'csltw';
        boGT:  Op := 'csgtw';
        boLE:  Op := 'cslew';
        boGE:  Op := 'csgew';
        boAnd: Op := 'and';
        boOr:  Op := 'or';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =w %s %s, %s', T, Op, L, R));
    end;
    Result := T;
  end
  else if AExpr is TNotExpr then
  begin
    
    L := EmitExpr(TNotExpr(AExpr).Expr);
    T := AllocTemp;
    EmitLine(Format('  %s =w xor %s, 1', T, L));
    Result := T;
  end
  else if AExpr is TDerefExpr then
  begin
    
    T     := EmitExpr(TDerefExpr(AExpr).Expr);
    QType := QbeTypeOf(AExpr.ResolvedType);
    L     := AllocTemp;
    if QType = 'w' then
      EmitLine(Format('  %s =w loadw %s', L, T))
    else
      EmitLine(Format('  %s =l loadl %s', L, T));
    Result := L;
  end
  else if AExpr is TIsExpr then
    Result := EmitIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := EmitAsExpr(TAsExpr(AExpr))
  else
    raise ECodeGenError.Create('Unknown expression node type');
end;

function TCodeGenQBE.EmitIsExpr(AExpr: TIsExpr): string;
var
  ObjTemp: string;
  ResTemp: string;
begin
  ObjTemp := EmitExpr(AExpr.Obj);
  ResTemp := AllocTemp;
  if (AExpr.ResolvedTargetType <> nil) and
     (AExpr.ResolvedTargetType.Kind = tyInterface) then
    EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)', ResTemp, ObjTemp, AExpr.TypeName))
  else
    EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)', ResTemp, ObjTemp, AExpr.TypeName));
  Result := ResTemp;
end;

function TCodeGenQBE.EmitAsExpr(AExpr: TAsExpr): string;
var
  ObjTemp:  string;
  OkTemp:   string;
  SlotTemp: string;
  ResTemp:  string;
  LblOk:    string;
  LblFail:  string;
  LblEnd:   string;
begin
  ObjTemp  := EmitExpr(AExpr.Obj);
  SlotTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc8 1', SlotTemp));

  OkTemp  := AllocTemp;
  LblOk   := AllocLabel('as_ok');
  LblFail := AllocLabel('as_fail');
  LblEnd  := AllocLabel('as_end');

  EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)', OkTemp, ObjTemp, AExpr.TypeName));
  EmitLine(Format('  jnz %s, @%s, @%s', OkTemp, LblOk, LblFail));

  EmitLine('@' + LblFail);
  EmitLine('  call $_Raise_InvalidCast()');
  EmitLine(Format('  storel 0, %s', SlotTemp));  
  EmitLine(Format('  jmp @%s', LblEnd));

  EmitLine('@' + LblOk);
  EmitLine(Format('  storel %s, %s', ObjTemp, SlotTemp));
  EmitLine(Format('  jmp @%s', LblEnd));

  EmitLine('@' + LblEnd);
  ResTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', ResTemp, SlotTemp));
  Result := ResTemp;
end;

function TCodeGenQBE.QBEMangle(const AName: string): string;
var
  I: Integer;
  C: Integer;
begin
  Result := '';
  for I := 1 to Length(AName) do
  begin
    C := OrdAt(AName, I);
    if C = 60 then
      Result := Result + '_'
    else if C = 62 then
      begin end
    else if C = 44 then
      Result := Result + '_'
    else
      Result := Result + Copy(AName, I, 1);
  end;
end;

function TCodeGenQBE.QbeEscapeString(const AStr: string): string;
var
  I: Integer;
  C: Integer;
begin
  Result := '';
  for I := 1 to Length(AStr) do
  begin
    C := OrdAt(AStr, I);
    if C = 34 then
      Result := Result + '\"'
    else if C = 92 then
      Result := Result + '\\'
    else if C = 10 then
      Result := Result + '\n'
    else if C = 13 then
      Result := Result + '\r'
    else if C = 9 then
      Result := Result + '\t'
    else if (C < 32) or (C > 126) then
      Result := Result + Format('\%02x', C)
    else
      Result := Result + Copy(AStr, I, 1);
  end;
end;

procedure TCodeGenQBE.Generate(AProg: TProgram);
var
  Body:        TStringList;
  SavedOutput: TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TStringList.Create;
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader;
      EmitBlock(AProg.Block);
      EmitMainFooter;
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection;
    EmitGlobalVarData(AProg.Block);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AddStrings(Body);
  finally
    Body.Free;
  end;
end;

procedure TCodeGenQBE.GenerateUnit(AUnit: TUnit);
var
  I:         Integer;
  ImplDecl:  TMethodDecl;
  IntfNames: TStringList;
  Body:      TStringList;
  SavedOut:  TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FTempCount  := 0;
  FLabelCount := 0;

  IntfNames := TStringList.Create;
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Get(I)).Name);

    Body := TStringList.Create;
    try
      SavedOut := FOutput;
      FOutput  := Body;
      try
        for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
        begin
          ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Get(I));
          EmitFuncDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
        end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Generated by Blaise Compiler');
      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitDataSection;
      FOutput.AddStrings(Body);
    finally
      Body.Free;
    end;
  finally
    IntfNames.Free;
  end;
end;

function TCodeGenQBE.GetOutput: string;
begin
  Result := FOutput.GetText;
end;




{ === Main program === }























const
  Version = '0.3.0-dev';
  CompilerName = 'Blaise';

procedure PrintUsage;
begin
  WriteLn('Blaise Compiler v', Version);
  WriteLn('Copyright (c) 2026 Graeme Geldenhuys');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  blaise --source <file.pas> --output <binary>');
  WriteLn('  blaise --source <file.pas> --emit-ir');
  WriteLn('');
  WriteLn('Flags:');
  WriteLn('  --source <path>     Pascal source file');
  WriteLn('  --output <path>     Output binary path');
  WriteLn('  --target <id>       linux-x86_64 (default), macos-arm64');
  WriteLn('  --emit-ir           Print QBE IR to stdout and exit');
end;



procedure HandleFPCInfoQuery(const AArg: string);
var
  Query: string;
begin
  Query := Copy(AArg, 3, MaxInt);  
  if Query = 'V' then
  begin
    WriteLn('3.2.2');
    Halt(0);
  end
  else if Query = 'TP' then
  begin
    WriteLn('x86_64');
    Halt(0);
  end
  else if Query = 'TO' then
  begin
    WriteLn('linux');
    Halt(0);
  end;
  
end;




function ParseFPCArgs(
  var SourceFile: string;
  var OutputFile: string): Boolean;
var
  I:       Integer;
  Arg:     string;
  OutDir:  string;
  OutName: string;
begin
  Result     := False;
  SourceFile := '';
  OutputFile := '';
  OutDir     := '';
  OutName    := '';

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);

    if Copy(Arg, 1, 2) = '-i' then
      HandleFPCInfoQuery(Arg)
    else if Copy(Arg, 1, 3) = '-FE' then
      OutDir := Copy(Arg, 4, MaxInt)
    else if Copy(Arg, 1, 3) = '-FU' then begin end
    else if Copy(Arg, 1, 3) = '-Fu' then begin end
    else if Copy(Arg, 1, 2) = '-o' then
      OutName := Copy(Arg, 3, MaxInt)
    else if Copy(Arg, 1, 2) = '-M' then begin end
    else if Copy(Arg, 1, 2) = '-O' then begin end
    else if Copy(Arg, 1, 2) = '-d' then begin end
    else if (Arg = '-g') or (Arg = '-gl') or (Arg = '-CX') or
            (Arg = '-XX') or (Arg = '-Xs') then begin end
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else if (Length(Arg) > 0) and (OrdAt(Arg, 1) <> 45) then
    begin
      
      if SourceFile = '' then
        SourceFile := Arg;
    end;
    

    I := I + 1;
  end;

  if SourceFile = '' then
  begin
    WriteLn('Error: no source file specified');
    Exit;
  end;

  
  if OutName = '' then
    OutName := ChangeFileExt(ExtractFileName(SourceFile), '');
  if OutDir <> '' then
    OutputFile := (OutDir + '/') + OutName
  else
    OutputFile := OutName;

  Result := True;
end;



function IsFPCStyleInvocation: Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result := False;
  for I := 1 to ParamCount do
  begin
    Arg := ParamStr(I);
    if (Length(Arg) >= 2) and (OrdAt(Arg, 1) = 45) and (OrdAt(Arg, 2) <> 45) then
    begin
      Result := True;
      Exit;
    end;
  end;
end;

function ParseArgs(
  var SourceFile: string;
  var OutputFile: string;
  var EmitIR:     Boolean): Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result     := False;
  SourceFile := '';
  OutputFile := '';
  EmitIR     := False;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);
    if (Arg = '--source') and (I < ParamCount) then
    begin
      I := I + 1;
      SourceFile := ParamStr(I);
    end
    else if (Arg = '--output') and (I < ParamCount) then
    begin
      I := I + 1;
      OutputFile := ParamStr(I);
    end
    else if Arg = '--emit-ir' then
      EmitIR := True
    else if Arg = '--target' then
      I := I + 1  
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else
    begin
      WriteLn('Unknown flag: ', Arg);
      Exit;
    end;
    I := I + 1;
  end;

  if SourceFile = '' then
  begin
    WriteLn('Error: --source is required');
    Exit;
  end;
  if (not EmitIR) and (OutputFile = '') then
  begin
    WriteLn('Error: --output is required (or use --emit-ir)');
    Exit;
  end;

  Result := True;
end;

function RunProcess(const ACmd: string; var AOutput: string): Integer;
begin
  Result := Exec(ACmd);
  AOutput := ''
end;





function FindRTL: string;
var
  BinDir: string;
begin
  Result := GetEnvVar('BLAISE_RTL');
  if (Result <> '') and FileExists(Result) then
    Exit;
  BinDir := Copy(ParamStr(0), 1, Length(ParamStr(0)) - Length('blaise'));
  Result  := (BinDir + '/') + 'blaise_rtl.a';
  if FileExists(Result) then
    Exit;
  Result := '';
end;

procedure CompileToNative(const AIRFile, AOutputFile: string);
var
  AsmFile, RTLPath: string;
  Msg:              string;
  ExitCode:         Integer;
begin
  AsmFile := AIRFile + '.s';
  RTLPath := FindRTL;

  ExitCode := RunProcess('qbe' + ' ' + '-o' + ' ' + AsmFile + ' ' + AIRFile, Msg);
  if ExitCode <> 0 then
  begin
    WriteLn('qbe error (exit ', ExitCode, '):');
    Write(Msg);
    Halt(1);
  end;

  if RTLPath <> '' then
    ExitCode := RunProcess('cc' + ' ' + '-o' + ' ' + AOutputFile + ' ' + AsmFile + ' ' + RTLPath, Msg)
  else
    ExitCode := RunProcess('cc' + ' ' + '-o' + ' ' + AOutputFile + ' ' + AsmFile, Msg);

  if ExitCode <> 0 then
  begin
    WriteLn('cc error (exit ', ExitCode, '):');
    Write(Msg);
    Halt(1);
  end;

  DeleteFile(AsmFile);
end;

var
  SourceFile, OutputFile: string;
  EmitIR: Boolean;
  Source: TStringList;
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  IR:     string;
  IRFile: string;

begin
  InitKeywords;
  if IsFPCStyleInvocation then
  begin
    if not ParseFPCArgs(SourceFile, OutputFile) then
    begin
      PrintUsage;
      Halt(1);
    end;
    EmitIR := False;
  end
  else
  begin
    if not ParseArgs(SourceFile, OutputFile, EmitIR) then
    begin
      PrintUsage;
      Halt(1);
    end;
  end;

  if not FileExists(SourceFile) then
  begin
    WriteLn('Error: source file not found: ', SourceFile);
    Halt(1);
  end;

  Source := TStringList.Create;
  try
    Source.Add(ReadFile(SourceFile));
  except

    begin
      WriteLn('Error reading source: ', CurrentExceptionMessage);
      Halt(1);
    end;
  end;

  Lexer    := nil;
  Parser   := nil;
  Prog     := nil;
  Semantic := nil;
  CG       := nil;
  try
    try
      Lexer  := TLexer.Create(Source.GetText);
      Parser := TParser.Create(Lexer);
      Prog   := Parser.Parse;
    except

      begin
        WriteLn('Parse error: ', CurrentExceptionMessage);
        Halt(1);
      end;
    end;

    try
      Semantic := TSemanticAnalyser.Create;
      Semantic.Analyse(Prog);
    except

      begin
        WriteLn('Semantic error: ', CurrentExceptionMessage);
        Halt(1);
      end;
    end;

    try
      CG := TCodeGenQBE.Create;
      CG.Generate(Prog);
      IR := CG.GetOutput;
    except

      begin
        WriteLn('Code generation error: ', CurrentExceptionMessage);
        Halt(1);
      end;
    end;
  finally
    CG.Free;
    Semantic.Free;
    Prog.Free;
    Parser.Free;
    Lexer.Free;
    Source.Free;
  end;

  if EmitIR then
  begin
    Write(IR);
    Halt(0);
  end;

  IRFile := OutputFile + '.ssa';
  try
    Source := TStringList.Create;
    try
      
      WriteFile(IRFile, IR);
    finally
      Source.Free;
    end;
  except

    begin
      WriteLn('Error writing IR: ', CurrentExceptionMessage);
      Halt(1);
    end;
  end;

  CompileToNative(IRFile, OutputFile);
  DeleteFile(IRFile);

end.
