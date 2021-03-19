
import LRat.Dimacs
import LRat.LRat

def main (args:List String) : IO Unit := do
  match args with
  | [dimacsFile] => do
    let h ← ByteStream.fromPath dimacsFile
    let cnf ← Dimacs.read h
  | [dimacsFile, lratFile] => do
    let h ← ByteStream.fromPath dimacsFile
    let cnf ← Dimacs.read h
    let h ← ByteStream.fromPath lratFile
    readLRat h cnf.varCount (ClauseDB.fromDimacs cnf)
  | _ => do
    IO.println "Expected dimacsfile and lratfile."