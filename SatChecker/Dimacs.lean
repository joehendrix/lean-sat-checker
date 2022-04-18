import SatChecker.ByteStream
import SatChecker.Core

structure Dimacs :=
(varCount : UInt64)
(clauses : Array Clause)

namespace Dimacs

def clauseCount (d:Dimacs) : Nat := d.clauses.size

--- @Clause.read' h vc a@ Read a list of ints with magnitude between 1 and vc
--- and stops when it reads a zero.
partial def readClause' (h:ByteStream) (varCount: UInt64) (a:Array Lit) : IO Clause := do
  h.skipWS
  let l ← Lit.read h varCount
  if l.isNull then
      pure ⟨a⟩
  else
    readClause' h varCount (a.push l)

/--- Read a line expected to contain a clause. -/
def readClause (h:ByteStream) (varCount:UInt64) : IO Clause := do
  readClause' h varCount Array.empty

partial def read (h:ByteStream) : IO Dimacs := do
  let c ← h.getByte
  if c == 'c'.toUInt8 then
    let _ ← h.getLine
    read h
  else if c == 'p'.toUInt8 then
    let cnf ← h.getWord
    if cnf != "cnf".toByteArray then
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
                  let c ← readClause h varCnt
                  if !(← h.isEof) then
                    h.getLine
                  loop (remaining - 1) (a.push c)
      let a ← loop clauseCnt Array.empty
      pure { varCount := varCnt, clauses := a }
  else
    throw (IO.userError ("Unknown command: " ++ toString c))

end Dimacs