import SatChecker.Common

/--
 - A stream of bytes we we can peek one byte ahead.
 -/
structure AsciiStream where
  eofRef : IO.Ref Bool
  next : IO.Ref UInt8
  rest : IO.FS.Handle

namespace AsciiStream

/- Create AsciiStream from path. -/
def fromPath (path:String) : IO AsciiStream := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.read

  let b ← h.read 1
  let n := if b.size > 0 then b.get! 0 else 0

  let eofRef ← IO.mkRef (b.size == 0)
  let nextRef ← IO.mkRef n
  pure { eofRef := eofRef, next := nextRef, rest := h }

def isEof (h:AsciiStream) : IO Bool := h.eofRef.get

def peekByte (h:AsciiStream) : IO UInt8 := do
  if ← h.isEof then
    throw $ IO.userError "Attempt to read past end of file."
  h.next.get

def peek (h:AsciiStream) : IO Char := UInt8.toChar <$> h.peekByte

def skipByte (h:AsciiStream) : IO Unit := do
  let b ← h.rest.read 1
  if b.size == 0 then
    if ← h.isEof then
      throw $ IO.userError "Attempt to read past end of file."
    h.eofRef.set true
    h.next.set 0
  else
    h.next.set (b.get! 0)

def matchChar (h:AsciiStream) (c:Char) : IO Bool := do
  if ← h.isEof then
    throw $ IO.userError "Attempt to read past end of file."
  if (← h.next.get) = c.toUInt8 then
    skipByte h
    pure true
  else
    pure false

def nextMatchesPred (h:AsciiStream) (p:Char → Bool) : IO Bool := do
  if !(← h.isEof) && p (← h.next.get).toChar then
    pure true
  else
    pure false

def getByte (h:AsciiStream) : IO UInt8 := do
  let n ← h.next.get
  skipByte h
  pure n

def getLine (h:AsciiStream) : IO Unit := do
  if ← h.eofRef.get then
    throw $ IO.userError "Attempt to read past end of file."
  if (← h.next.get) == 10 then
    h.skipByte
  else
    let _ ← h.rest.getLine
    h.skipByte

-- Skip whitespace
partial def skipWS (h:AsciiStream) : IO Unit := do
  if (← h.peekByte) == ' '.toUInt8 then
    h.skipByte
    h.skipWS
  else
    pure ()

partial def getWord' (h:AsciiStream) (a:String) : IO String := do
  let c ← h.peek
  if c.isWhitespace then
    pure a
  else
    h.skipByte
    h.getWord' (a ++ c.toString)

/-
Reads the next non-whitespace characters.
-/
partial def getWord (h:AsciiStream) : IO String := do
  if ← h.matchChar ' ' then
    h.getWord
  else
    h.getWord' ""

partial def getUInt64' (h:AsciiStream) (c : UInt64) : IO UInt64 := do
  let b ← h.peekByte
  if '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8 then
    h.skipByte
    let d := (b - '0'.toUInt8)
    let c' := 10 * c + d.toUInt64
    if c' < c then
      throw (IO.userError <| s! "Numeric overflow: 10 * {c} + {d} .")
    h.getUInt64' c'
  else if b == ' '.toUInt8  || b == 10 || b == 13 then
    pure c
  else
    throw (IO.userError <| s! "Expected digit {b}.")

/-
Reads an unsigned uint64.
-/
partial def getUInt64 (h:AsciiStream) : IO UInt64 := do
  h.skipWS
  let b ← h.peekByte
  if '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8 then
    h.skipByte
    h.getUInt64' (b - '0'.toUInt8).toUInt64
  else
    throw (IO.userError "Expected initial digit.")

end AsciiStream