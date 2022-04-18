import Std.Data.HashMap

def Char.toUInt8 (c:Char) := UInt8.ofNat c.toNat

def UInt8.toChar (w:UInt8) : Char := Char.ofNat w.toNat

def String.toByteArray (s:String) : ByteArray := s.foldl (λa c => a.push (UInt8.ofNat c.toNat)) ByteArray.empty

partial def ByteArray.beq (x y : ByteArray) : Bool :=
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

namespace Std
namespace HashMap
variable {α β} [BEq α] [Hashable α]

def modify (m:HashMap α β) (a:α) (f : β → β) : HashMap α β :=
  match m.find? a with
  | none => m
  | some x => m.insert a (f x)

end HashMap
end Std

class ForIn2 (m : Type u₁ → Type u₂) (ρ : Type u) (x : ρ) (α : outParam (Type v)) where
  forIn {β} [Monad m] (b : β) (f : α → β → m (ForInStep β)) : m β

partial def Fin.forIn {β} {n} [Monad m] (b : β) (f : (a : Fin n) → β → m (ForInStep β)) : m β := do
  let rec loop (i:Nat) (b:β) : m β := do
        if h : i < n then
            match ← f  ⟨i, h⟩ b with
            | ForInStep.done a => pure a
            | ForInStep.yield a => loop (i+i) b
        else
          pure b
  loop 0 b

instance (n:Nat) : ForIn2 m Type (Fin n) (Fin n) where
  forIn := Fin.forIn