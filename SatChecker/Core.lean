import SatChecker.Common
import SatChecker.Lit

structure Clause :=
(lits : Array Lit)
(p : 0 < lits.size)

namespace Clause

def pivot (c:Clause) : Lit := let h := c.p; c.lits[0]

protected def forIn {β} [Monad m] (x : Clause) (b : β) (f : Lit → β → m (ForInStep β)) : m β := x.lits.forIn b f

instance : ForIn2 m Clause x Lit where
  forIn := Clause.forIn x

instance : ForIn m Clause Lit where
  forIn := Clause.forIn

protected def member (c:Clause) (l:Lit) : Bool := Id.run do
  let mut r : Bool := false
  for k in c.lits do
    if l == k then
      r := true
      break
  r

protected def size (self:Clause) : Nat := self.lits.size

/-- Return lit at given index in clause. -/
def getOp (self:Clause) (idx:Nat) : Lit :=
  if h : idx < self.lits.size then self.lits[idx] else ⟨0⟩

protected def mem (l:Lit) (c:Clause) : Prop := ∃(i:Fin c.lits.size), c.lits[i] = l

instance : Membership Lit Clause where
  mem := Clause.mem

end Clause