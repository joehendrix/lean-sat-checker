import SatChecker.Common
import SatChecker.Core

import Std.Data.HashMap

-- Maps variables to their assigned value (true or false)
structure Assignment where
  values : Std.HashMap Var Bool

namespace Assignment

protected def toString (a:Assignment) : String :=
  let ppElt (p:UInt64 × Bool) : String := if p.snd then s!"{p.fst}" else s!"-{p.fst}"
  @List.toString _ ⟨ppElt⟩ a.values.toList

instance : ToString Assignment where
  toString := Assignment.toString

def empty : Assignment := { values := Std.HashMap.empty }

-- Proposition that holds if the variable is assigned either true or false.
protected
def assigned (a:Assignment) (l:Var) : Bool := a.values.contains l

def value (a:Assignment) (l:Lit) : Option Bool :=
  match a.values.find? l.var with
  | none => none
  | some b => some (b = l.polarity)

--- Set the value of the literal in the assignment
def set (a:Assignment) (l:Lit) : Assignment :=
  { values := a.values.insert l.var l.polarity }

-- Create assignment from negating literals in clause.
def negatedClause (c:Clause) : Assignment := Id.run do
  let mut a : Std.HashMap UInt64 Bool := ∅
  for l in c do
    a := a.insert l.var !l.polarity
  { values := a }

-- Return value of literal in assignment (none if unassigned).
def getOp (self:Assignment) (idx:Lit) : Option Bool :=
  let r := self.values.find? idx.var
  if idx.polarity then r else r.map not

instance : Membership Var Assignment where
  mem v a := a.assigned v

instance : CoeFun Assignment (λa => Lit → Option Bool) where
  coe := value

def isExtension (a b:Assignment) : Prop := ∀(l:Lit), l.var ∈ a → a l = b l

def satisfies (a:Assignment) (c:Clause) : Prop :=
  ∃(l : Lit), l ∈ c ∧ a l = true

end Assignment