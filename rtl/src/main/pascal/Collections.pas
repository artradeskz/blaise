unit Collections;

// Blaise RTL — generic collections.
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.
// It uses Blaise syntax and semantics.

interface

type
  TList<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    var
      NewCap: Integer;
    begin
      if Self.FCapacity = 0 then
        NewCap := 4
      else
        NewCap := Self.FCapacity * 2;
      Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
      Self.FCapacity := NewCap
    end;
    procedure Add(Value: T);
    var
      Dest: ^T;
    begin
      if Self.FCount = Self.FCapacity then
        Self.Grow;
      Dest        := Self.FData + Self.FCount * SizeOf(T);
      Dest^       := Value;
      Self.FCount := Self.FCount + 1
    end;
    function Get(AIndex: Integer): T;
    var
      Src: ^T;
    begin
      Src    := Self.FData + AIndex * SizeOf(T);
      Result := Src^
    end;
    procedure Delete(AIndex: Integer);
    var
      Src:  ^T;
      Dst:  ^T;
      I:    Integer;
    begin
      I := AIndex;
      while I < Self.FCount - 1 do
      begin
        Dst  := Self.FData + I * SizeOf(T);
        Src  := Self.FData + (I + 1) * SizeOf(T);
        Dst^ := Src^;
        I    := I + 1
      end;
      Self.FCount := Self.FCount - 1
    end;
    procedure Clear;
    begin
      Self.FCount := 0
    end;
    procedure Free;
    begin
      FreeMem(Self.FData)
    end;
    property Count: Integer read FCount;
  end;

implementation

end.
