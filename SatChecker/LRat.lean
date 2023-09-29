import SatChecker.Assignment
import SatChecker.Dimacs

-- | A one based index of a clause
@[reducible]
def ClauseId := UInt64

def ClauseId.ofNat := UInt64.ofNat

-- A set of clauses for checking.
--
-- This is designed to support efficient lookup of clauses by ids,
-- clause deletion and traversing the list of all undeleted clauses.
structure ClauseDB where
  -- First clause index (0 if empty)
  headClauseId :  ClauseId
  -- Maximum index added to clause db
  maxClauseId  : ClauseId
  -- Maps clauses with given identifier to identifier of next
  -- clause and literals in clause or empty array if clause
  -- is deleted.
  clauses : Std.HashMap ClauseId (ClauseId × Array Lit)

namespace ClauseDB

def member (c:Clause) (db:ClauseDB) : Prop :=
  ∃(cid: ClauseId),
    match db.clauses.find? cid with
    | none => False
    | some (_, lits) => c.lits = lits

instance : Membership Clause ClauseDB where
  mem := ClauseDB.member

-- Return true if the assignment satifies all clauses in the database
def satisfies (db:ClauseDB) (a:Assignment) : Prop := ∀(c: Clause), c ∈ db → a.satisfies c

def fromDimacs (d:Dimacs) : ClauseDB :=
  let cl := d.clauses
  if cl.size == 0 then
    { headClauseId := 0, maxClauseId := 0, clauses := ∅ }
  else Id.run do
    let cnt := ClauseId.ofNat cl.size
    let mut cm : Std.HashMap ClauseId (ClauseId × Array Lit) := ∅
    for i in [1:cl.size+1], c in cl do
      let i := ClauseId.ofNat i
      cm := cm.insert i (i+1, c.lits)
    pure { headClauseId := 1, maxClauseId := cnt, clauses := cm }

def modify (db : ClauseDB) (i:ClauseId) (f : ClauseId → ClauseId × Array Lit → ClauseId × Array Lit) : ClauseDB :=
  { db with clauses := db.clauses.modify i f }

def erase (db : ClauseDB) (i:ClauseId) : ClauseDB :=
  { db with clauses := db.clauses.erase i }

protected partial
def visitClauses {β} (db : ClauseDB) (b : β)
          (f : β → ClauseId → Clause → Except String β) : Except String (β × ClauseDB) := do
  let rec @[specialize] restLoop (db : ClauseDB) (upd:Bool) (prev i : ClauseId) (b : β) : Except String (β × ClauseDB) := do
    match db.clauses.find? i with
    | none => pure (b, db)
    | some (nextId, c) => do
      if p:c.size > 0 then
        let b ← f b i ⟨c, p⟩
        let db := if upd then db.modify prev (λ_ (_,c) => (i, c)) else db
        restLoop db false i nextId b
      else
        restLoop (db.erase i) true prev nextId b
  let rec @[specialize] headLoop (db : ClauseDB) (upd:Bool) (i : ClauseId) (b : β) : Except String (β × ClauseDB) := do
    match db.clauses.find? i with
    | none => pure (b, db)
    | some (nextId, c) => do
      if p : c.size > 0 then
        let b ← f b i ⟨c,p⟩ 
        let db := if upd then {db with headClauseId := i }  else db
        restLoop db false i nextId b
      else
        headLoop (db.erase i) true nextId b
  headLoop db false db.headClauseId b

def insertClause (db:ClauseDB) (clauseId:ClauseId) (c:Clause) : Option ClauseDB :=
  if clauseId != db.maxClauseId + 1 then
    none
  else
    some { headClauseId := if db.headClauseId == 0 then clauseId else db.headClauseId,
           maxClauseId := clauseId,
           clauses := db.clauses.insert clauseId (clauseId + 1, c.lits)
         }

def deleteClause (db:ClauseDB) (clauseId:ClauseId) : ClauseDB :=
  db.modify clauseId (λ_ (nextId, _) => (nextId, ∅))

/-- Return clause at given index. -/
def getOp (self:ClauseDB) (idx:ClauseId) : Option Clause :=
  match self.clauses.find? idx with
  | none => none
  | some (_, a) => if p : a.size > 0 then some ⟨a, p⟩ else none  

end ClauseDB

inductive RupResult
| conflict : RupResult
| unit (l:Lit) : RupResult
| trueLit : RupResult -- Returned if literal in clause is true
| multipleUnassigned : RupResult -- Returned if here are multiple unassigned literals.

/-- Apply unit propagation to an assignment and clause-/
def rup (a:Assignment) (lits:Array Lit) : RupResult := Id.run do
  -- Return conflict if we do not find an unassigned or true literal
  let mut r : RupResult := RupResult.conflict
  -- Iterate through literals.
  for bnd : i in [0:lits.size] do
    have p : i < lits.size := bnd.upper
    let l := lits[i]
    match a.getOp l with
    -- If literal is false, then keep going
    | some false =>
      pure ()
    | some true =>
      r := RupResult.trueLit
    -- Unassigned literal
    | none =>
      r := RupResult.unit l
      -- Check to make sure all remaining literals are false
      for j_bnd : j in [i+1:lits.size] do
        have q : j < lits.size := j_bnd.upper
        if !(a.getOp lits[j] == some false) then
          r := RupResult.multipleUnassigned
          break
      break
  -- Return value
  r

@[reducible]
def UnitClauseArray := Array ClauseId

/--
 - applyRup applies reverse unit propagation to extend an assignment
 - containing literal implies by unit clauses.
 -
 - Returns nothing if conflict found and assignment otherwise.
 -/
def applyRup (db:ClauseDB)
             (a:Assignment) -- Assignment generated from reverse-unit propagation
             (clauses:Array ClauseId)
             : Except String (Option Assignment) := do
  let mut a : Assignment := a
  for i_bnd : i in [0:clauses.size] do
    let p : i < clauses.size := i_bnd.upper
    let clId := clauses[i]
    let nextClause ← 
          match db.getOp clId with
          | none => throw "Unknown clause"
          | some cl => pure cl
    match rup a nextClause.lits with
    | RupResult.conflict => do
      if i != clauses.size - 1 then
        throw $ "Additional propagation steps defined after conflict detected."
      return none
    | RupResult.unit l => do
      a := a.set l
    | RupResult.trueLit =>
      throw $ "Reverse unit propagation applied to clause assigned true."
    | RupResult.multipleUnassigned =>
      throw $ "Reverse unit propagation applied to non-unit clause."
  pure $ some a

--theorem applyRupIsNone (db:ClauseDB) (a:Assignment) (cl:Array ClauseId)
--   : applyRup db a cl = Except.ok none → isUnsat db a := sorry

-- set_option trace.Meta.Tactic.simp.rewrite true

/- This checks the clause for a pivot. -/
def ratCheckClause (db:ClauseDB) (pivot:Lit) (a:Assignment) (c: Array (ClauseId × UnitClauseArray)) (hintIdx:Nat) (i:ClauseId) (cl:Clause)
    : Except String Nat := do

  if p : hintIdx ≥ c.size then
    if cl.member pivot then
      throw $ s!"Pivot {pivot} in clause {i} when not expected."
    pure hintIdx
  else 
    let q : hintIdx < c.size := Nat.gt_of_not_le p
    if i < c[hintIdx].fst then
      if cl.member pivot then
        throw $ s!"Pivot {pivot} in clause {i} when not expected."
      pure hintIdx
    else
      let (clId, hints) := c[hintIdx]
      if i > clId then
        throw $ "Skipped over clause."
      let mut resolved : Bool := false
      let mut a : Assignment := a
      -- Iterate through literals in clause.
      for l in cl do
        if l == pivot then
          continue
        match a.getOp l with
        -- Assign proof
        | none => a := a.set (-l)
        -- If literal is already false then do nothing
        | some false => pure ()
        -- If literal is true, then we should be able to resolve.
        | some true =>
          resolved := true
          break
      -- We already resolved this so there should just be end of clauses.
      if !resolved then
        match ← applyRup db a hints with
        | some _ => throw $ "Failed to find conflict in clause."
        | none => pure ()
      pure (hintIdx+1)

-- A proof step in an LRat proof.
inductive LRatStep
-- A rule resolvable solely through unit propagation
| rup (clId:ClauseId) (cl:Array Lit) (p:UnitClauseArray)
-- A lrat rule.
| lrat (clId:ClauseId) (cl:Clause) (p:UnitClauseArray) (c: Array (ClauseId × UnitClauseArray))
-- A rule to delete clauses
| delete (a:Array ClauseId)

namespace LRatStep

/--
 - Read the unit propagation information and return terminating clauseId
 -/
partial def getRup (h:AsciiStream) (maxClauseId:ClauseId) : IO (UnitClauseArray × ClauseId) := do
  let rec loop (a:Array ClauseId) : IO (UnitClauseArray × ClauseId) := do
            let n ← Lit.read h "Clause" maxClauseId
            if !n.isPos then
              pure (a, n.var)
            else
              loop (a.push n.var)
  loop Array.empty

/--
 - Get next step from LRat format
 -/
partial def read (h:AsciiStream) (varCount:UInt64) (maxClauseId:ClauseId) : IO LRatStep := do
  -- Read the next clause
  let newClauseId ← h.getUInt64
  h.skipWS;
  let c ← h.peekByte
  -- If deletion information
  if c == 'd'.toUInt8 then
    h.skipByte
    -- Read clauses to delete
    let rec loopDel (a:Array ClauseId) : IO LRatStep := do
          let clId ← h.getUInt64
          if clId == 0 then
            if !(←h.isEof) then h.getLine
            pure (delete a)
          else
            loopDel (a.push clId)
    loopDel ∅
  else
    if _h : newClauseId ≤ maxClauseId then
      throw $ IO.userError s!"Expected new clause id {newClauseId} to exceed maximum clause id {maxClauseId}."
    let cl ← Dimacs.readClause' h varCount Array.empty
    let (clauses, clId0) ← getRup h maxClauseId
    if clId0 == 0 then
      if !(←h.isEof) then h.getLine
      pure (rup newClauseId cl clauses)
    else
      let rec loop (a:Array (ClauseId × UnitClauseArray)) (clId:ClauseId) : IO LRatStep := do
            let (rest, next) ← getRup h maxClauseId
            let a' := a.push (clId, rest)
            if next == 0 then
              if !(←h.isEof) then h.getLine
              if p : 0 < cl.size then
                pure (lrat newClauseId ⟨cl, p⟩ clauses a')
              else 
                throw $ IO.userError s!"{newClauseId} failed: rat rule not allowed on empty clause."
            else
              loop a' next
      loop ∅ clId0

/--
 - This verifies a clause against the clause database.
 -/
def verify (db:ClauseDB) : LRatStep → Except String (Option ClauseDB)
| rup clId c clauses =>
  let a := Assignment.negatedClause' c
  match applyRup db a clauses with
  | Except.error msg   => throw s!"{clId} failed: {msg}"
  | Except.ok (some _) => throw s!"{clId} failed: Failed to find conflict."
  | Except.ok none =>
    if p : 0 < c.size then
      match db.insertClause clId ⟨c, p⟩ with
      | none => throw s!"Unexpected clause id {clId}"
      | some db => pure (some db)
    else
      pure none
| lrat clId c clauses cases => do
  let a := Assignment.negatedClause c
  let pivot := -c.pivot
  match ← applyRup db a clauses with
  | none =>
    throw s!"{clId} unexpected: Unit propagation resolved."
  | some a =>
    let ⟨_,db⟩ ← db.visitClauses 0 (ratCheckClause db pivot a cases)
    match db.insertClause clId c with
    | none => throw s!"Unexpected clause id {clId}"
    | some db => pure (some db)
| delete clauses => do
  let mut db := db
  for clId in clauses do
    db := db.deleteClause clId
  pure (some db)

end LRatStep


/-
def ClauseDB.isSat (db:ClauseDB) : Prop := sorry

-- This states that if verifyClause returns a new clause database and the input was
-- satisfiable, then the output was as well.
theorem verifyRulePreservesSat (db:ClauseDB) (rl:Rule) (db':ClauseDB)
   : db.isSat
   → verifyRule db rl = Except.ok (some db')
   → db'.isSat := by
  admit

theorem verifyRuleShowsUnsat (db:ClauseDB) (rl:Rule)
  : verifyRule db rl = Except.ok none → ¬ db.isSat := by
  admit
-/

-- Reads lines from the proof file and updates the clause database
def readLRat (h:AsciiStream) (varCount:UInt64) (db:ClauseDB) (cnt:Nat) : IO Unit := do
  h.skipWS;
  if ←h.isEof then throw $ IO.userError s!"End of file reached before empty clause derived."
  let rl ← LRatStep.read h varCount db.maxClauseId
  match LRatStep.verify db rl with
  | Except.error msg =>
    throw $ IO.userError msg
  -- We are done with a proof that 
  | Except.ok none => do
    pure ()
  -- We
  | Except.ok (some db) =>
    match cnt with
    | Nat.succ cnt => readLRat h varCount db cnt
    | 0 => throw (IO.userError s!"Out of gas.")

def maxProofGas : Nat := (1 <<< 64) - 1 

def verifyDimacs (cnf : Dimacs) (h:AsciiStream) : IO Unit := do
  readLRat h cnf.varCount (ClauseDB.fromDimacs cnf) maxProofGas
