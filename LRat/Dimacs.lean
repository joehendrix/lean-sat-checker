import LRat.HStream
import LRat.SignedInt

/-- A literal
 - A literal is encoded as the literal index shifted by one.
 - The least significant bit is set if the literal is negated.
 -/
def Lit := SignedInt

namespace Lit

def isNull (l:Lit) : Bool := !(l.value == 0)

def var (l:Lit) : UInt64 := l.magnitude

/-- Return true if literal is positive and false if negative. -/
def polarity (l:Lit) : Bool := l.isPos

-- @Lit.read h vc@ read the next signed numeral from @h@ with magnitude
-- between 0 and vc and returns a literal for it.
def read (h:HStream) (varCount: UInt64) : IO Lit := SignedInt.read h varCount

-- Negate literal
def negate (l:Lit) : Lit := ⟨l.value ^^^ 1⟩

instance : Inhabited Lit := ⟨{value := 0}⟩

protected def beq (x y : Lit) : Bool := x.value == y.value

instance : BEq Lit where
  beq := Lit.beq

end Lit

structure Clause :=
(lits : Array Lit)

namespace Clause

-- def empty : Clause := ⟨Array.empty⟩

def pivot (c:Clause) : Lit := c.lits[0]

protected def forIn {β} [Monad m] (x : Clause) (b : β) (f : Lit → β → m (ForInStep β)) : m β := x.lits.forIn b f

instance : ForIn m Clause Lit where
  forIn := Clause.forIn

protected def member (c:Clause) (l:Lit) : Bool := do
  let mut r : Bool := false
  for k in c.lits do
    if l == k then
      r := true
      break
  r

protected def size (self:Clause) : Nat := self.lits.size

/-- Return lit at given index in clause. -/
def getOp (self:Clause) (idx:Nat) : Lit := self.lits[idx]

--- @Clause.read' h vc a@ Read a list of ints with magnitude between 1 and vc
--- and stops when it reads a zero.
partial def read' (h:HStream) (varCount: UInt64) (a:Array Lit) : IO Clause := do
  h.skipWS
  let l ← Lit.read h varCount
  if l.isNull then
      pure ⟨a⟩
  else
    read' h varCount (a.push l)

/--- Read a line expected to contain a clause. -/
def read (h:HStream) (varCount:UInt64): IO Clause := do
  read' h varCount Array.empty

end Clause


structure Dimacs :=
(varCount : UInt64)
(clauses : Array Clause)

def Dimacs.clauseCount (d:Dimacs) : Nat := d.clauses.size

partial def Dimacs.read (h:HStream) : IO Dimacs := do
  let c ← h.getByte
  if c == 'c'.toUInt8 then
    let _ ← h.getLine
    read h
  else if c == 'p'.toUInt8 then
    let cnf ← h.getWord
    if cnf != "cnf".toByteArray then do
      throw (IO.userError ("Expected \"cnf\" -- found " ++ toString cnf))
    else
      let varCnt    ← h.getUInt64
      let clauseCnt ← h.getUInt64
      if varCnt ≥ UInt64.ofNat (UInt64.size >>> 1) then
        throw $ IO.userError "Variable count is too large."
      let _ ← h.getLine
      let rec loop (remaining:UInt64) (a:Array Clause) : IO (Array Clause) := do
                if remaining == 0 then
                  pure a
                else do
                  let c ← Clause.read h varCnt
                  let _ ← h.getLine
                  loop (remaining - 1) (a.push c)
      let a ← loop clauseCnt Array.empty
      pure { varCount := varCnt, clauses := a }
  else
    throw (IO.userError ("Unknown command: " ++ toString c))