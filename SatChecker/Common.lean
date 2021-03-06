import Std.Data.HashMap

def Char.toUInt8 (c:Char) := UInt8.ofNat c.toNat

def UInt8.toChar (w:UInt8) : Char := Char.ofNat w.toNat
def UInt8.toUInt64 (w:UInt8) : UInt64 := UInt64.ofNat w.toNat

def String.toByteArray (s:String) : ByteArray := s.foldl (λa c => a.push (UInt8.ofNat c.toNat)) ByteArray.empty

partial def ByteArray.beq (x y : ByteArray) : Bool := do
  if x.size == y.size then
    let rec loop (i : Nat) :=
      if i ≥  x.size then
        true
      else if x.get! i == y.get! i then
        loop (i+1)
      else
        false
    loop 0
  else
    false

instance : BEq ByteArray where
  beq := ByteArray.beq

def max {α} [h:HasLessEq α] [DecidableRel (@HasLessEq.LessEq α h)] (x y : α) : α := if x ≥ y then x else y

namespace Std
namespace HashMap
variable {α β} [BEq α] [Hashable α]

def modify (m:HashMap α β) (a:α) (f : β → β) : HashMap α β :=
  match m.find? a with
  | none => m
  | some x => m.insert a (f x)

end HashMap
end Std
