import SatChecker.LRat

inductive SatResult
| sat : (a : Array Lit) → SatResult
| unsat : SatResult

namespace SatResult

def pp : SatResult → String
| sat a => s!"s SATISFIABLE\nv {String.intercalate " " (toString <$> a.toList)} 0\n"
| unsat => "s UNSATISFIABLE\n" 

end SatResult

namespace AigToCnf

def run : IO Unit := pure ()

end AigToCnf

namespace Kissat

inductive Output
| comment : String → Output
| result : String → Output
| model : Array Lit → Output

namespace Output


def pp : Output → String
| comment msg => s!"c {msg}"
| result msg => s!"s {msg}"
| model l => s!"v {String.intercalate " " (toString <$> l.toList)}"

end Output

/-
TODO: Investigate spawn and see if we can improve error message.
-/

partial def run (ppOutput : Output → IO Unit) (cmd : String := "kissat") (dimacsFile bdratFile : String) : IO SatResult := do
  let child ← IO.Process.spawn { 
      cmd := cmd,
      args := #[dimacsFile, bdratFile],
      stdin := IO.Process.Stdio.null
      stdout := IO.Process.Stdio.piped
      stderr := IO.Process.Stdio.piped
    }
  let stdout : IO.FS.Handle := child.stdout
  let stderr : IO.FS.Handle := child.stderr

  let rec monitorStdout (res : Option SatResult) := do
        let ln ← stdout.getLine
        if ln.isEmpty then
          pure res
        else if ln.startsWith "c" then
          ppOutput (Output.comment (ln.drop 1))
          monitorStdout res
        else if ln = "s SATISFIABLE\n" then
          if res.isSome then
            throw <| IO.userError s!"Result already defined."
          let mdlLine ← stdout.getLine
          if mdlLine.startsWith "v " then
            let words := ((mdlLine.drop 2).dropRight 1).splitOn " " |> List.toArray
            if words.size = 0 then
              throw <| IO.userError "Missing model values."
            let values ← 
                  match words.mapM (Lit.ofString (UInt64.ofNat (2^63-1))) with
                  | Except.error err => throw <| IO.userError s!"Invalid model {mdlLine}:  {err}\n  {words}"
                  | Except.ok l => pure l
            let last : Lit := values.back
            if not last.isNull then
              throw <| IO.userError "Missing zero terminating element."
            monitorStdout (some (SatResult.sat values.pop))
          else
            throw <| IO.userError s!"Expected model instead of {mdlLine}"
        else if ln = "s UNSATISFIABLE\n" then
          if res.isSome then
            throw <| IO.userError s!"Result already defined."
          monitorStdout (some SatResult.unsat)
        else
          throw <| IO.userError s!"Unexpected standard output contents \"{ln}\""
  let res ← monitorStdout none
  let exitCode ← child.wait
  if exitCode = 1 then
    let ln ← stderr.readToEnd
    throw <| IO.userError s!"Kissat failed:\n  {ln}"
  else if exitCode = 10 then
    match res with
    | some r@(SatResult.sat _) =>
      pure r
    | _ => 
      throw <| IO.userError "Expected kissat to return a sat result."
  else if exitCode = 20 then
    match res with
    | some r@SatResult.unsat =>
      pure r
    | _ => 
      throw <| IO.userError "Expected kissat to return an unsat result."
  else if exitCode = 255 then
    throw <| IO.userError s!"Could not execute {cmd}"
  else 
    throw <| IO.userError s!"Unexpected return code from kissat {exitCode}"

end Kissat



namespace DratTrim

structure RunArgs where
  /-- Command name. -/
  cmd : String := "drat-trim"
  /-- Input DIMACS file. -/
  input : String
  /-- Proof file in DRAT format. -/
  proof : String
  /-- File to print lemmas in LRAT format. -/
  lrat : Option String

partial def run (runArgs : RunArgs) : IO Unit := do
  let mut args := #[runArgs.input, runArgs.proof]
  match runArgs.lrat with
  | some path =>
    args := (args.push "-L").push path
  | none => pure ()

  let child ← IO.Process.spawn { 
      cmd := runArgs.cmd,
      args := args,
      stdin := IO.Process.Stdio.null
      stdout := IO.Process.Stdio.null
      stderr := IO.Process.Stdio.null
    }
  let exitCode ← child.wait
  if exitCode = 255 then
    throw <| IO.userError s!"Could not execute {runArgs.cmd}"
  else if exitCode ≠ 0 then 
    throw <| IO.userError s!"drat-trim returned unexpected exit code {exitCode}"

end DratTrim

def main (args:List String) : IO Unit := do
  match args with
  | [] =>
    IO.println "Provide a command (dimacs or lrat)"
  | ["dimacs", dimacsFile] => do
    let h ← AsciiStream.fromPath dimacsFile
    let _ ← Dimacs.read h
    IO.println s!"Successfully read"
  | "dimacs" :: _ => do
    IO.println "Expected dimacsfile."
  | ["lrat", dimacsFile, lratFile] => do
    let hDimacs ← AsciiStream.fromPath dimacsFile
    let cnf   ← Dimacs.read hDimacs
    let hLrat ← AsciiStream.fromPath lratFile
    verifyDimacs cnf hLrat
    IO.println s!"s VERIFIED"
  | "lrat" :: _ => do
    IO.println "c Expected dimacsfile and lratfile."
  | ["verify", dimacsFile, bdratFile, lratFile] => do
    --let bdratFile : String := "temp.bdrat"
    let r ← Kissat.run (λ_ => pure ()) "kissat" dimacsFile bdratFile
    match r with
    | SatResult.sat _a => 
      IO.println s!"{r.pp}"
    | SatResult.unsat => do
      IO.println "c drat-trim started"
      DratTrim.run { 
          input := dimacsFile
          proof := bdratFile
          lrat := some lratFile
        }
      IO.println "c drat-trim done"
      IO.println "c verification started"
      let hDimacs ← AsciiStream.fromPath dimacsFile
      let cnf   ← Dimacs.read hDimacs
      let hLrat ← AsciiStream.fromPath lratFile
      verifyDimacs cnf hLrat
      IO.println "c verification done"
      IO.println s!"{r.pp}"
  | "verify" :: _ => do
    throw <| IO.userError "Expected dimacsfile bdratFile and lratFile."
  | cmd :: _ =>
    IO.println s!"Unknown command {cmd}."