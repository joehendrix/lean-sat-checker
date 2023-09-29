import SatChecker.Core

structure Dimacs :=
(varCount : UInt64)
(clauses : Array Clause)

namespace Dimacs

def clauseCount (d:Dimacs) : Nat := d.clauses.size

--- @Clause.read' h vc a@ Read a list of lits with variables bounded by vc and
--  stop when it reads a zero.
partial def readClause' (h:AsciiStream) (varCount: UInt64) (a:Array Lit) : IO (Array Lit) := do
  h.skipWS
  let l ← Lit.read h "Variable" varCount
  if l.isNull then
    pure a
  else
    readClause' h varCount (a.push l)

/--- Read a line expected to contain a clause. -/
def readClause (h:AsciiStream) (varCount:UInt64) : IO Clause := do
  let a ← readClause' h varCount Array.empty
  if p : 0 < a.size then
    pure ⟨a, p⟩
  else
   throw (IO.userError ("Encountered non-empty clause."))

partial def read (h:AsciiStream) : IO Dimacs := do
  if ← h.matchChar 'c' then
    h.getLine
    read h
  else if ← h.matchChar 'p' then
    let cnf ← h.getWord
    if cnf ≠ "cnf" then
      throw <| IO.userError s!"Expected \"cnf\" -- found {cnf}"
    let varCnt    ← h.getUInt64
    let clauseCnt ← h.getUInt64
    if varCnt ≥ UInt64.ofNat (UInt64.size >>> 1) then
      throw $ IO.userError "Variable count {varCnt} is too large."
    let _ ← h.getLine
    let rec loop (remaining:UInt64) (a:Array Clause) : IO (Array Clause) := do
              if remaining == 0 then
                pure a
              else do
                let c ← readClause h varCnt
                if !(← h.isEof) then
                  h.getLine
                loop (remaining - 1) (a.push c)
    let a ← loop clauseCnt Array.empty
    pure { varCount := varCnt, clauses := a }
  else
    let c ← h.peek
    throw (IO.userError ("Unknown command: " ++ toString c))

end Dimacs