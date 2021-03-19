import LRat.ByteStream
import LRat.SignedInt
import LRat.Dimacs
import Std.Data.HashMap

-- Maps variables to their assigned value (true or false)
structure Assignment where
  values : Std.HashMap UInt64 Bool

namespace Assignment

protected def toString (a:Assignment) : String := do
  let ppElt (p:UInt64 × Bool) : String := if p.snd then s!"{p.fst}" else s!"!{p.fst}"
  @List.toString _ ⟨ppElt⟩ a.values.toList


instance : ToString Assignment where
  toString := Assignment.toString

def empty : Assignment := { values := Std.HashMap.empty }

--- Set the value of the literal in the assignment
def set (a:Assignment) (l:Lit) : Assignment :=
  { values := a.values.insert l.var l.polarity }

-- Create assignment from negating literals in clause.
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

def ClauseId.ofNat := UInt64.ofNat

-- A set of clauses for checking.
structure ClauseDB where
  -- First clause index (0 if empty)
  headClauseId :  ClauseId
  -- Maximum index added to clause db
  maxClauseId  : ClauseId
  -- Clauses added to database
  clauses : Std.HashMap ClauseId (ClauseId × Array Lit)

namespace ClauseDB

def fromDimacs (d:Dimacs) : ClauseDB := do
  let cl := d.clauses
  if cl.size == 0 then
    pure { headClauseId := 0, maxClauseId := 0, clauses := ∅ }
  else
    let cnt := ClauseId.ofNat cl.size
    let mut cm : Std.HashMap ClauseId (ClauseId × Array Lit) := ∅
    for i in [1:cl.size+1], c in cl do
      let i := ClauseId.ofNat i
      cm := cm.insert i (i+1, c.lits)
    pure { headClauseId := 1, maxClauseId := cnt, clauses := cm }

def modify (db : ClauseDB) (i:ClauseId) (f : ClauseId × Array Lit → ClauseId × Array Lit) : ClauseDB :=
  { db with clauses := db.clauses.modify i f }

def erase (db : ClauseDB) (i:ClauseId) : ClauseDB :=
  { db with clauses := db.clauses.erase i }


protected partial
def visitClauses {β} (db : ClauseDB) (b : β)
          (f : β → ClauseId → Clause → IO β) : IO (β × ClauseDB) := do
  let rec @[specialize] restLoop (db : ClauseDB) (upd:Bool) (prev i : ClauseId) (b : β) : IO (β × ClauseDB) := do
    match db.clauses.find? i with
    | none => pure (b, db)
    | some (nextId, c) => do
      if c.size = 0 then
        restLoop (db.erase i) true prev nextId b
      else
        let b ← f b i ⟨c⟩
        let db := if upd then db.modify prev (λ(_,c) => (i, c)) else db
        restLoop db false i nextId b
  let rec @[specialize] headLoop (db : ClauseDB) (upd:Bool) (i : ClauseId) (b : β) : IO (β × ClauseDB) := do
    match db.clauses.find? i with
    | none => pure (b, db)
    | some (nextId, c) => do
      if c.size = 0 then
        headLoop (db.erase i) true nextId b
      else
        let b ← f b i ⟨c⟩
        let db := if upd then {db with headClauseId := i }  else db
        restLoop db false i nextId b
  headLoop db false db.headClauseId b

def insertClause (db:ClauseDB) (clauseId:ClauseId) (c:Clause) : Option ClauseDB := do
  if clauseId != db.maxClauseId + 1 then
    none
  else
    some { headClauseId := if db.headClauseId == 0 then clauseId else db.headClauseId,
           maxClauseId := clauseId,
           clauses := db.clauses.insert clauseId (clauseId + 1, c.lits)
         }

def deleteClause (db:ClauseDB) (clauseId:ClauseId) : ClauseDB := do
  db.modify clauseId (λ(nextId, _) => (nextId, ∅))

/-- Return clause at given index. -/
def getOp (self:ClauseDB) (idx:ClauseId) : Clause :=
  match self.clauses.find? idx with
  | none => ⟨∅⟩
  | some (_, a) => ⟨a⟩

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
 -
 - Returns nothing and next clause if conflict found and assignment otherwise.
 -/
partial def getRup (h:ByteStream) (db:ClauseDB) (a:Assignment) : IO (Option Assignment × ClauseId) := do
  let n ← SignedInt.read h "Clause" db.maxClauseId
  if !n.isPos then
    pure (some a, n.magnitude)
  else
    let clId := n.magnitude
    let nextClause := db[clId]
    match rup a nextClause with
    | RupResult.conflict => do
      let r ← SignedInt.read h "Clause" db.maxClauseId
      if r.isPos then
        throw $ IO.userError $ s!"Expected end of hints instead of {r} after conflict."
      pure (none, r.magnitude)
    | RupResult.unit l => do
      getRup h db (a.set l)
    | RupResult.trueLit =>
      throw $ IO.userError s!"Found true literal in clause."
    | RupResult.multipleUnassigned =>
      throw $ IO.userError s!"Multiple unassigned literal in clause."

section
variable (h:ByteStream) (db:ClauseDB) (pivot:Lit) (a:Assignment)

/- This checks the clause for a pivot. -/
def checkClause (clId:ClauseId) (i:ClauseId) (cl:Clause) : IO ClauseId := do
  if clId == 0 || i < clId then
    if cl.member pivot then
      throw $ IO.userError s!"Pivot {pivot} in clause {i} when not expected until {clId}."
    pure clId
  else
    if i > clId then
      throw $ IO.userError s!"Skipped over clause."
    let mut resolved : Bool := false
    let mut a : Assignment := a
    -- Iterate through literals in clause.
    for l in cl do
      if l == pivot then
        continue
      match a[l] with
      -- Assign proof
      | none => a := a.set l.negate
      -- If literal is already false then do nothing
      | some false => pure ()
      -- If literal is true, then we should be able to resolve.
      | some true =>
        resolved := true
        break
    -- We already resolved this so there should just be end of clauses.
    if resolved then
      let n ← SignedInt.read h "Clause" db.maxClauseId
      if n.isPos then
        throw $ IO.userError s!"Expected next clause"
      pure n.magnitude
    else
      let (ma,clId) ←  getRup h db a
      match ma with
      | none => pure clId
      | some _ => throw $ IO.userError s!"Failed to find conflict in clause."

end

/--
 - Read the unit propagation and rat formula code.
 -/
partial def readRup (h:ByteStream) (db:ClauseDB) (pivot:Lit) (a:Assignment) : IO ClauseDB := do
  let (ma,clId0) ← getRup h db a
  if clId0 == 0 then
    match ma with
    | none =>
      if !(←h.isEof) then
        h.getLine
      pure db
    | some _ => throw $ IO.userError s!"Failed to find conflict in clause."
  else
    -- Index of next clause to search for pivot in or 0 if we no longer
    -- expect clauses.
    let mut clId : ClauseId := clId0
    let ⟨_,db⟩ ← db.visitClauses clId0 (checkClause h db pivot a)
    if !(←h.isEof) then
      h.getLine
    pure db

def lratError {α} (msg:String) : IO α := do
  throw $ IO.userError msg

partial def readLRat (h:ByteStream) (varCount:UInt64) (db:ClauseDB) : IO Unit := do
  let mut db := db
  h.skipWS;
  if ←h.isEof then lratError s!"End of file reached before empty clause derived."
  let newClauseId ← h.getUInt64
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
    if h : newClauseId ≤ db.maxClauseId then
      lratError s!"Expected new clause id {newClauseId} to exceed maximum clause id {db.maxClauseId}."
    let cl ← Clause.read h varCount
    if cl.size == 0 then
      let (ma,clId0) ← getRup h db (Assignment.negatedClause cl)
      if clId0 != 0 then
        lratError s!"Final conflict clause {newClauseId} only resolvable through unit propagation."
      match ma with
      | none => pure ()
      | some _ => throw $ IO.userError s!"Failed to find conflict in clause {newClauseId}."
      IO.println "UNSAT"
    else
      db ← readRup h db cl.pivot.negate (Assignment.negatedClause cl)
      match db.insertClause newClauseId cl with
        | none => IO.println s!"Unknown clause id {newClauseId}"
        | some db => readLRat h varCount db
