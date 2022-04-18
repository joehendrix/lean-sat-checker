import SatChecker.LRat

def main (args:List String) : IO Unit := do
  match args with
  | [] =>
    IO.println "Provide a command (dimacs or lrat)"
  | ["dimacs", dimacsFile] => do
    let h ← ByteStream.fromPath dimacsFile
    let cnf ← Dimacs.read h
  | "dimacs" :: _ => do
    IO.println "Expected dimacsfile."
  | ["lrat", dimacsFile, lratFile] => do
    let h ← ByteStream.fromPath dimacsFile
    let cnf ← Dimacs.read h
    let h ← ByteStream.fromPath lratFile
    readLRat h cnf.varCount (ClauseDB.fromDimacs cnf)
    IO.println s!"Verified {dimacsFile} is unsat."
  | "lrat" :: _ => do
    IO.println "Expected dimacsfile and lratfile."
  | cmd :: _ =>
    IO.println "Unknown command {cmd}."