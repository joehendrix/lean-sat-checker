import SatChecker.ByteStream

/--
 - SignedInt types encoded for quick sign tests and magnitude.
 -
 - The internal encoding sets the least significant bit if the
 - value is negative, and the value is shifted to the left by one.
 -/
structure SignedInt := (value : UInt64)

def SignedInt.magnitude (l:SignedInt) : UInt64 := l.value >>> 1

def SignedInt.isZero (l:SignedInt) : Bool := l.value == 0

/-- Return true if literal is positive. -/
def SignedInt.isPos (l:SignedInt) : Bool := l.value &&& 1 == 0 && l.value > 0

/-- Return true if literal is negative. -/
def SignedInt.isNeg (l:SignedInt) : Bool := l.value &&& 1 == 1

namespace SignedInt

protected def toString (s:SignedInt) : String :=
  if s.isNeg then s!"-{s.magnitude}" else s!"{s.magnitude}"

instance : ToString SignedInt where
  toString := SignedInt.toString

end SignedInt

-- @Lit.read h vc@ read the next signed numeral from @h@ with magnitude
-- between 0 and vc and returns a literal for it.
def SignedInt.read (h:ByteStream) (name:String) (varCount: UInt64) : IO SignedInt := do
  h.skipWS
  let b ← h.getByte
  if b == '-'.toUInt8 then
    let w ← h.getUInt64
    if w == 0 then
      throw $ IO.userError "Expected nonzero"
    if (w > varCount) then
      throw $ IO.userError s!"Negated variable too large (idx  = {w}, limit = {varCount})"
    pure ⟨w <<< 1 ||| 1⟩
  else if b == '0'.toUInt8 then
    if !(← h.isEof) then
      let b ← h.peekByte
      if !(b == ' '.toUInt8 || b == 10 || b == 13) then
        throw $ IO.userError s!"Expected whitespace or end-of-line (found = {b})."
    pure ⟨0⟩
  else if '1'.toUInt8 ≤ b && b ≤ '9'.toUInt8 then
    let w ← h.getUInt64' (b - '0'.toUInt8).toUInt64
    if (w > varCount) then
      throw $ IO.userError s!"{name} too large (idx  = {w}, limit = {varCount})"
    pure ⟨w <<< 1⟩
  else
    throw $ IO.userError s!"Expected number."