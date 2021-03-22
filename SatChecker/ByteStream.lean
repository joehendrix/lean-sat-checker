import SatChecker.Common

/--
 - A stream of bytes we we can peek one byte ahead.
 -/
structure ByteStream where
  eofRef : IO.Ref Bool
  next : IO.Ref UInt8
  rest : IO.FS.Handle

namespace ByteStream

/- Create bytestream from path. -/
def fromPath (path:String) : IO ByteStream := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.read

  let eof ← h.isEof
  let b ← if eof then pure ByteArray.empty else h.read 1
  let n := if b.size > 0 then b.get! 0 else 0

  let eofRef ← IO.mkRef (b.size == 0)
  let nextRef ← IO.mkRef n
  pure { eofRef := eofRef, next := nextRef, rest := h }

def isEof (h:ByteStream) : IO Bool := h.eofRef.get

def peekByte (h:ByteStream) : IO UInt8 := do
  if ← h.isEof then
    throw $ IO.userError "Attempt to read past end of file."
  h.next.get

def skipByte (h:ByteStream) : IO Unit := do
  if ← h.isEof then
    throw $ IO.userError "Attempt to read past end of file."
  if ← h.rest.isEof then
    h.eofRef.set true
  else
    let b ← h.rest.read 1
    if b.size == 0 then
      h.eofRef.set true
    else
      h.next.set (b.get! 0)

def getByte (h:ByteStream) : IO UInt8 := do
  if ← h.eofRef.get then
    throw $ IO.userError "Attempt to read past end of file."
  let b ← h.next.get
  if ← h.rest.isEof then
    h.eofRef.set true
  else
    let b ← h.rest.read 1
    if b.size == 0 then
      h.eofRef.set true
    else
      h.next.set (b.get! 0)
  pure b

def getLine (h:ByteStream) : IO Unit := do
  if ← h.eofRef.get then
    throw $ IO.userError "Attempt to read past end of file."
  if (← h.next.get) == 10 then
    h.skipByte
  else
    let _ ← h.rest.getLine
    h.skipByte

-- Skip whitespace
partial def skipWS (h:ByteStream) : IO Unit := do
  if (← h.peekByte) == ' '.toUInt8 then
    h.skipByte
    h.skipWS
  else
    pure ()

partial def getWord' (h:ByteStream) (a:ByteArray) : IO ByteArray := do
  let b ← h.peekByte
  if b == ' '.toUInt8 then
    pure a
  else
    h.skipByte
    h.getWord' (a.push b)

partial def getWord (h:ByteStream) : IO ByteArray := do
  let b ← h.getByte
  if b == ' '.toUInt8 then
    h.getWord
  else
    h.getWord' (ByteArray.empty.push b)

partial def getUInt64' (h:ByteStream) (c : UInt64) : IO UInt64 := do
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

partial def getUInt64 (h:ByteStream) : IO UInt64 := do
  h.skipWS
  let b ← h.peekByte
  if '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8 then
    h.skipByte
    h.getUInt64' (b - '0'.toUInt8).toUInt64
  else
    throw (IO.userError "Expected initial digit.")

end ByteStream