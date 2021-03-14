import LRat.HStream
import LRat.SignedInt
import LRat.Dimacs
import Std.Data.HashMap

namespace Std
namespace HashMap
variable {α β} [BEq α] [Hashable α]

def modify (m:HashMap α β) (a:α) (f : β → β) : HashMap α β :=
  match m.find? a with
  | none => m
  | some x => m.insert a (f x)

end HashMap
end Std

-- Maps variables to their assigned value (true or false)
structure Assignment where
  values : Std.HashMap UInt64 Bool

/-
application type mismatch
  (0, c)
argument
  c
has type
  Clause : Type
but is expected to have type
  Array Lit : Type
-/

namespace Assignment

def empty : Assignment := { values := Std.HashMap.empty }

--- Set the value of the literal in the assignment
--
-- Fails if literal already assigned.
def set! (a:Assignment) (l:Lit) : Assignment :=
  { values := a.values.insert l.var l.polarity }

--- Set the value of the literal in the assignment
--
-- Fails if literal already assigned.
def setLit (a:Assignment) (l:Lit) : Option Assignment :=
  match a.values.find? l.var with
  | none => some { values := a.values.insert l.var l.polarity }
  | some b =>
     if b == l.polarity then
       some a
     else
       none

def negatedClause (c:Clause) : Assignment := do
  let mut a : Std.HashMap UInt64 Bool := ∅
  for l in c do
    a := a.insert l.var !l.polarity
  { values := a }

/-- Return value of literal in assignment (none if unassigned). -/
def getOp (self:Assignment) (idx:Lit) : Option Bool :=
  let r := self.values.find? idx.var
  if idx.polarity then r else r.map not

end Assignment


-- | A one based index of a clause
@[reducible]
def ClauseId := UInt64

-- A set of clauses for checking.
structure ClauseDB where
  -- First clause index (0 if empty)
  headClauseId :  ClauseId
  -- Last clause index (0 if empty)
  lastClauseId : ClauseId
  -- Maximum index added to clause db
  maxClauseId  : ClauseId
  -- Clauses added to database
  clauses : Std.HashMap ClauseId (ClauseId × ClauseId × Array Lit)

namespace ClauseDB

def fromDimacs (d:Dimacs) : ClauseDB := sorry

--def empty : ClauseDB := { maxIdx := 0, clauses := ∅ }

protected partial
def forIn {β} [Monad m] (db : ClauseDB) (b : β)
          (f : ClauseId × Clause → β → m (ForInStep β)) : m β := do
  let rec @[specialize] loop (i : ClauseId) (b : β) : m β := do
    if i == 0 then
      pure b
    else
      match db.clauses.find? i with
      | none => pure b
      | some (_, nextId, c) => do
        match (← f (i,⟨c⟩) b) with
        | ForInStep.done  b =>
          pure b
        | ForInStep.yield b =>
          loop nextId b
  loop 0 b

instance : ForIn m ClauseDB (ClauseId × Clause) where
  forIn := ClauseDB.forIn

def insertClause (db:ClauseDB) (clauseId:ClauseId) (c:Clause) : ClauseDB := do
  let mut cl := db.clauses
  if db.lastClauseId != 0 then
    cl := cl.modify db.lastClauseId (λ(p, _, c) => (p, clauseId, c))
  { maxClauseId := clauseId,
    headClauseId := if db.headClauseId == 0 then clauseId else db.headClauseId,
    lastClauseId := clauseId,
    clauses := cl.insert clauseId (db.lastClauseId, 0, c.lits)
  }

def deleteClause (db:ClauseDB) (clauseId:ClauseId) : ClauseDB := do
  match db.clauses.find? clauseId with
  | none => db
  | some (prevId, nextId, a) => do
    let mut cl := db.clauses.erase clauseId
    if prevId != 0 then
      cl := cl.modify prevId (λ(p,_,c) => (p, nextId, c))
    if nextId != 0 then
      cl := cl.modify nextId (λ(p,_,c) => (p, prevId, c))
    { maxClauseId := db.maxClauseId,
      headClauseId := if prevId == 0 then nextId else db.headClauseId,
      lastClauseId := if nextId == 0 then prevId else db.lastClauseId,
      clauses := cl
    }

/-- Return clause at given index. -/
def getOp (self:ClauseDB) (idx:ClauseId) : Clause :=
  match self.clauses.find? idx with
  | none => ⟨∅⟩
  | some (_, _, a) => ⟨a⟩

end ClauseDB

inductive RupResult
| conflict : RupResult
| unit (l:Lit) : RupResult
| trueLit : RupResult -- Returned if literal in clause is true
| multipleUnassigned : RupResult -- Returned if here are multiple unassigned literals.


/-- Apply unit propagation to an assignment and clause-/
def rup (a:Assignment) (cl:Clause) : RupResult := do
  -- Return conflict if we do not find an unassigned or true literal
  let mut r : RupResult := RupResult.conflict
  -- Iterate through literals.
  for i in [0:cl.size] do
    let l := cl[i]
    match a[l] with
    -- If literal is false, then keep going
    | some false =>
      pure ()
    | some true =>
      r := RupResult.trueLit
    -- Unassigned literal
    | none =>
      r := RupResult.unit l
      -- Check to make sure all remaining literals are false
      for j in [i+1:cl.size] do
        if !(a[cl[j]] == some false) then
          r := RupResult.multipleUnassigned
          break
      break
  -- Return value
  r

/--
 - Read the unit propagation and rat formula code.
 -/
partial def getRup (h:HStream) (db:ClauseDB) (a:Assignment) : IO ClauseId := do
  let n ← SignedInt.read h db.maxClauseId
  if n.isZero then
    throw $ IO.userError "Satisfiable assignment at end of list."
  if n.isNeg then
    pure n.magnitude
  else
    let clId := n.magnitude
    let nextClause := db[clId]
    match rup a nextClause with
    | RupResult.conflict => do
      let r ← SignedInt.read h db.maxClauseId
      if !r.isZero then
        throw $ IO.userError "Expected zero after conflict."
      let _ <- h.getLine
      pure 0
    | RupResult.unit l => do
      getRup h db (a.set! l)
    | RupResult.trueLit =>
      throw $ IO.userError "Found true literal in clause."
    | RupResult.multipleUnassigned =>
      throw $ IO.userError "Multiple unassigned literal in clause."

/--
 - Read the unit propagation and rat formula code.
 -/
partial def readRup (h:HStream) (db:ClauseDB) (pivot:Lit) (a:Assignment) : IO Unit := do
  let clId0 ← getRup h db a
  if clId0 != 0 then
    -- Index of next clause to search for pivot in or 0 if we no longer
    -- expect clauses.
    let mut clId : ClauseId := clId0
    for (i, cl) in db do
      if clId == 0 || i < clId then
        if cl.member pivot then
            throw $ IO.userError "Pivot belongs to class when not expected."
        continue
      if i > clId then
        throw $ IO.userError "Skipped over class."

      let mut resolved : Bool := false
      let mut a : Assignment := a
      -- Iterate through literals in clause.
      for l in cl do
        if l == pivot then
          continue
        match a[l] with
        -- Assign proof
        | none => a := a.set! l.negate
        -- If literal is already false then do nothing
        | some false => pure ()
        -- If literal is true, then we should be able to resolve.
        | some true =>
          resolved := true
          break
      -- We already resolved this so there should just be end of
      if resolved then
        let n ← SignedInt.read h db.maxClauseId
        if !n.isZero && n.isPos then
          throw $ IO.userError "Expected next clause"
        clId := n.magnitude
      else
        clId ← getRup h db a

partial def readLRat (h:HStream) (varCount:UInt64) (db:ClauseDB) : IO Unit := do
  let newClauseId ← h.getUInt64
  if h : newClauseId ≤ db.maxClauseId then
    throw $ IO.userError "Expected new clause to exceed maximum clause."
  h.skipWS;
  let c ← h.peekByte
  -- If deletion information
  if c == 'd'.toUInt8 then
    h.skipByte
    -- Read clauses to delete
    let rec loop (db:ClauseDB) := do
          let clId ← h.getUInt64
          if clId == 0 then
            h.getLine
          else
            loop (db.deleteClause clId)
    loop db
    readLRat h varCount db
  else
    let cl ← Clause.read h varCount
    readRup h db cl.pivot.negate (Assignment.negatedClause cl)
    let db := db.insertClause newClauseId cl
    readLRat h varCount db
