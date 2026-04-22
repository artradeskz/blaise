program Phase3Milestone;

{ Phase 3 milestone: exercises TList<Integer> and TDictionary<string,Integer>.
  Must produce correct output and zero valgrind leaks. }

type
  TIntList = class
    FData:     ^Integer;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Add(Value: Integer);
    function  Get(AIndex: Integer): Integer;
    procedure Delete(AIndex: Integer);
    procedure Free;
    property Count: Integer read FCount;
  end;

  TStrIntDict = class
    FKeys:     ^string;
    FValues:   ^Integer;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    function  FindKey(Key: string): Integer;
    procedure Add(Key: string; Value: Integer);
    function  TryGetValue(Key: string; var Value: Integer): Boolean;
    function  ContainsKey(Key: string): Boolean;
    procedure Remove(Key: string);
    procedure Free;
    property Count: Integer read FCount;
  end;

procedure TIntList.Grow;
var
  NewCap: Integer;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Integer));
  Self.FCapacity := NewCap
end;

procedure TIntList.Add(Value: Integer);
var
  Dest: ^Integer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  Dest        := Self.FData + Self.FCount * SizeOf(Integer);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TIntList.Get(AIndex: Integer): Integer;
var
  Src: ^Integer;
begin
  Src    := Self.FData + AIndex * SizeOf(Integer);
  Result := Src^
end;

procedure TIntList.Delete(AIndex: Integer);
var
  Src: ^Integer;
  Dst: ^Integer;
  I:   Integer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Integer);
    Src  := Self.FData + (I + 1) * SizeOf(Integer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TIntList.Free;
begin
  FreeMem(Self.FData);
  FreeMem(Self)
end;

procedure TStrIntDict.Grow;
var
  NewCap: Integer;
begin
  if Self.FCapacity = 0 then
    NewCap := 8
  else
    NewCap := Self.FCapacity * 2;
  Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(string));
  Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Integer));
  Self.FCapacity := NewCap
end;

function TStrIntDict.FindKey(Key: string): Integer;
var
  I:   Integer;
  Ptr: ^string;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(string);
    if Ptr^ = Key then
    begin
      Result := I;
      I      := Self.FCount
    end
    else
      I := I + 1
  end
end;

procedure TStrIntDict.Add(Key: string; Value: Integer);
var
  Idx:  Integer;
  KPtr: ^string;
  VPtr: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr  := Self.FValues + Idx * SizeOf(Integer);
    VPtr^ := Value
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow;
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(string);
    VPtr  := Self.FValues + Self.FCount * SizeOf(Integer);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1
  end
end;

function TStrIntDict.TryGetValue(Key: string; var Value: Integer): Boolean;
var
  Idx:  Integer;
  VPtr: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(Integer);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TStrIntDict.ContainsKey(Key: string): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TStrIntDict.Remove(Key: string);
var
  Idx:  Integer;
  I:    Integer;
  KDst: ^string;
  KSrc: ^string;
  VDst: ^Integer;
  VSrc: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(string);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(string);
      VDst  := Self.FValues + I * SizeOf(Integer);
      VSrc  := Self.FValues + (I + 1) * SizeOf(Integer);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    Self.FCount := Self.FCount - 1
  end
end;

procedure TStrIntDict.Free;
begin
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  FreeMem(Self)
end;

var
  List:  TIntList;
  Dict:  TStrIntDict;
  V:     Integer;
  Found: Boolean;

begin
  { --- TList<Integer> --- }
  List := TIntList.Create;
  List.Add(10);
  List.Add(20);
  List.Add(30);
  List.Add(40);
  List.Add(50);

  Write('list.count='); WriteLn(List.Count);    { 5 }
  Write('list[0]=');    WriteLn(List.Get(0));    { 10 }
  Write('list[4]=');    WriteLn(List.Get(4));    { 50 }

  List.Delete(1);
  Write('count_after_delete='); WriteLn(List.Count);  { 4 }
  Write('list[1]_after_delete='); WriteLn(List.Get(1)); { 30 }

  List.Free;

  { --- TDictionary<string,Integer> --- }
  Dict := TStrIntDict.Create;
  Dict.Add('alpha', 1);
  Dict.Add('beta',  2);
  Dict.Add('gamma', 3);
  Dict.Add('delta', 4);

  Write('dict.count='); WriteLn(Dict.Count);     { 4 }

  Found := Dict.TryGetValue('beta', V);
  Write('beta='); WriteLn(V);                    { 2 }

  Found := Dict.ContainsKey('gamma');
  Write('has_gamma='); WriteLn(Found);           { 1 }

  Dict.Add('beta', 99);
  Found := Dict.TryGetValue('beta', V);
  Write('beta_after_update='); WriteLn(V);       { 99 }

  Dict.Remove('alpha');
  Write('count_after_remove='); WriteLn(Dict.Count);  { 3 }
  Found := Dict.ContainsKey('alpha');
  Write('has_alpha_after_remove='); WriteLn(Found);   { 0 }

  Dict.Free
end.
