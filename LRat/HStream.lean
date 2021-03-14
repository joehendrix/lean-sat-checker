import LRat.Common

structure HStream where
 next : IO.Ref UInt8
 rest : IO.FS.Handle

namespace HStream

def fromPath (path:String) : IO HStream := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.read
  let n ← h.read 1
  let r ← IO.mkRef (n.get! 0)
  pure { next := r, rest := h }

def peekByte (h:HStream) : IO UInt8 := h.next.get

def skipByte (h:HStream) : IO Unit := do
  let n ← h.rest.read 1
  h.next.set (n.get! 0)

def getByte (h:HStream) : IO UInt8 := do
  let b ← peekByte h
  h.skipByte
  pure b

def getLine (h:HStream) : IO Unit := do
  let b ← h.next.get
  if b == 10 then
    h.skipByte
  else
    let _ ← h.rest.getLine
    h.skipByte

-- Skip whitespace
partial def skipWS (h:HStream) : IO Unit := do
  let b ← h.peekByte
  if b == ' '.toUInt8 then
    h.skipByte
    h.skipWS
  else
    pure ()

partial def getWord' (h:HStream) (a:ByteArray) : IO ByteArray := do
  let b ← h.peekByte
  if b == ' '.toUInt8 then
    pure a
  else
    h.skipByte
    h.getWord' (a.push b)

partial def getWord (h:HStream) : IO ByteArray := do
  let b ← h.getByte
  if b == ' '.toUInt8 then
    h.getWord
  else
    h.getWord' (ByteArray.empty.push b)

partial def getUInt64' (h:HStream) (c : UInt64) : IO UInt64 := do
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

partial def getUInt64 (h:HStream) : IO UInt64 := do
  h.skipWS
  let b ← h.peekByte
  if '0'.toUInt8 ≤ b && b ≤ '9'.toUInt8 then
    h.skipByte
    h.getUInt64' (b - '0'.toUInt8).toUInt64
  else
    throw (IO.userError "Expected initial digit.")

end HStream