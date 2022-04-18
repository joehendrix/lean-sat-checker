import SatChecker.Common
import SatChecker.SignedInt

/-- A literal
 - A literal is encoded as the literal index shifted by one.
 - The least significant bit is set if the literal is negated.
 -/
def Lit := SignedInt

def Var := UInt64
  deriving BEq, Hashable

namespace Lit

def isNull (l:Lit) : Bool := l.value == 0

def var (l:Lit) : Var := l.magnitude

/-- Return true if literal is positive and false if negative. -/
def polarity (l:Lit) : Bool := l.isPos

-- @Lit.read h vc@ read the next signed numeral from @h@ with magnitude
-- between 0 and vc and returns a literal for it.
def read (h:ByteStream) (varCount: UInt64) : IO Lit := SignedInt.read h "Variable" varCount

-- Negate literal
def negate (l:Lit) : Lit := ⟨l.value ^^^ 1⟩

instance : Inhabited Lit := ⟨{value := 0}⟩

protected def beq (x y : Lit) : Bool := x.value == y.value

instance : BEq Lit where
  beq := Lit.beq

instance : ToString Lit where
  toString := SignedInt.toString

end Lit

structure Clause :=
(lits : Array Lit)

namespace Clause

def pivot (c:Clause) : Lit := c.lits[0]

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
  if idx < self.lits.size then self.lits[idx] else ⟨0⟩

protected def mem (l:Lit) (c:Clause) : Prop := ∃(i:Fin c.lits.size), c.lits[i] = l

instance : Membership Lit Clause where
  mem := Clause.mem

end Clause