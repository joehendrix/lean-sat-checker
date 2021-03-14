universes u v w

def ContT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  (α → m ρ) → m ρ

namespace ContT
section
variable {ρ : Type u} {m : Type u → Type v}
variable [Monad m] {α β : Type u}

@[inline] protected def pure (a : α) : ContT ρ m α := fun c => c a

@[inline] protected def bind (x : ContT ρ m α) (f : α → ContT ρ m β) : ContT ρ m β :=
  fun c => x (fun a => f a c)

def terminate (r : ρ) : ContT ρ m α := λc => pure r

-- @[inline] protected def map (f : α → β) (x : ContT ρ m α) : ContT ρ m β :=
-- fun c => x (fun a => pure (c ) do let (a, s) ← x s; pure (f a, s)

instance : Monad (ContT σ m) where
  pure := ContT.pure
  bind := ContT.bind
  -- map  := StateT.Maps

end
end ContT

export ContT(terminate)

abbrev Cont ρ := ContT ρ Id

def Cont.runSame {ρ} (c:Cont ρ ρ) : ρ := c id
