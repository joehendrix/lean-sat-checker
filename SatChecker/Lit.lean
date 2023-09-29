import SatChecker.Stream.Ascii

def Var := UInt64
  deriving BEq, Hashable, ToString

namespace Var

end Var
/--
 - SignedInt types encoded for quick sign tests and magnitude.
 -
 - The internal encoding sets the least significant bit if the
 - value is negative, and the value is shifted to the left by one.
 -/
structure Lit := (value : UInt64)

namespace Lit

def isNull (l:Lit) : Bool := l.value == 0

/-- Return true if literal is positive. -/
def isPos (l:Lit) : Bool := l.value &&& 1 == 0

/-- Return true if literal is negative. -/
def isNeg (l:Lit) : Bool := l.value &&& 1 == 1

/-- Return true if literal is positive and false if negative. -/
def polarity (l:Lit) : Bool := l.isPos

def var (l:Lit) : Var := l.value >>> 1

def isZero (l:Lit) : Bool := l.value == 0

protected def neg (l:Lit) : Lit := { value := l.value ^^^ 1 } 

instance : Neg Lit where
  neg := Lit.neg

instance : Inhabited Lit := ⟨{value := 0}⟩

protected def toString (s:Lit) : String :=
  if s.isNeg then s!"-{s.var}" else s!"{s.var}"

instance : ToString Lit where
  toString := Lit.toString

private def toNat (s : String) (idx : Nat) (varCount: UInt64) : Except String UInt64 := do
  let t := s.drop idx
  if !t.isNat then
    throw s!"Invalid literal {s}"
  let n := t.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  if n > varCount.toNat then
    throw s!"Invalid literal {n}"
  pure (UInt64.ofNat n)

def mkPos (v:UInt64) : Lit := ⟨v <<< 1⟩ 
def mkNeg (v:UInt64) : Lit := ⟨v <<< 1 ||| 1⟩ 

def ofString (varCount: UInt64) (s:String) : Except String Lit := do
  if s.startsWith "-" then
    Lit.mkNeg <$> toNat s 1 varCount
  else
    Lit.mkPos <$> toNat s 0 varCount

#print Bool


-- @read h vc@ read the next signed numeral from @h@ with magnitude
-- between 0 and vc and returns a literal for it.
def read (h:AsciiStream) (name:String) (varCount: UInt64) : IO Lit := do
  h.skipWS
  if ← h.matchChar '-' then
    h.skipByte
    let w ← h.getUInt64
    if w == 0 then
      throw $ IO.userError "Expected nonzero"
    if (w > varCount) then
      throw $ IO.userError s!"Negated {name} too large (idx  = {w}, limit = {varCount})"
    pure (mkNeg w)
  else if ← h.matchChar '0' then
    h.skipByte
    if !(← h.isEof) then
      let c ← h.peek
      if !(Char.isWhitespace c) then
        throw $ IO.userError s!"Expected whitespace or end-of-line (found = {c})."
    pure ⟨0⟩
  else if ← h.nextMatchesPred Char.isDigit then
    let w ← h.getUInt64
    if (w > varCount) then
      throw $ IO.userError s!"{name} too large (idx  = {w}, limit = {varCount})"
    pure (mkPos w)
  else
    throw $ IO.userError s!"Expected number."

-- @Lit.read h vc@ read the next signed numeral from @h@ with magnitude
-- between 0 and vc and returns a literal for it.
-- def read (h:AsciiStream) (varCount: UInt64) : IO Lit := SignedInt.read h "Variable" varCount



protected def beq (x y : Lit) : Bool := x.value == y.value

instance : BEq Lit where
  beq := Lit.beq


end Lit
