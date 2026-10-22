import Comparator.Compare
open Lean

def readExport (path : String) : IO Export.ExportedEnv := do
  let h ← IO.FS.Handle.mk path .read
  Export.parseStream (IO.FS.Stream.ofHandle h)

def diagnostic (label : String) (info : Option ConstantInfo) : IO Unit := do
  match info with
  | none => IO.eprintln s!"{label}: declaration missing"
  | some info =>
    IO.eprintln s!"{label} NAME: {info.name}; LEVELS: {info.levelParams}"
    IO.eprintln s!"{label} TYPE: {reprStr info.type}"
    if let some value := info.value? (allowOpaque := true) then
      IO.eprintln s!"{label} VALUE: {reprStr value}"
    if let .ctorInfo value := info then
      IO.eprintln s!"{label} CONSTRUCTOR: {value.induct}; {value.cidx}; {value.numParams}; {value.numFields}; {value.isUnsafe}"

def main (args : List String) : IO Unit := do
  let challengePath :: solutionPath :: targetString :: models := args
    | throw (IO.userError "Expected challenge export, solution export, target, model roots")
  let challenge ← readExport challengePath
  let solution ← readExport solutionPath
  let target := targetString.toName
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let modelRoots := models.toArray.map String.toName
  -- The theorem is a theorem target. Definitions are NOT definition holes.
  match Comparator.compareAt challenge solution #[target] #[] (modelRoots ++ allowed) with
  | .ok () => pure ()
  | .error error =>
    let parts := error.splitOn "'"
    if let some name := parts[1]? then
      diagnostic "CHALLENGE" (challenge.constMap[name.toName]?)
      diagnostic "SOLUTION" (solution.constMap[name.toName]?)
    throw (IO.userError error)
  IO.ofExcept (Comparator.checkAxioms solution #[target] #[] allowed)
  IO.println s!"Matched theorem and reachable definitions; permitted axioms only: {target}"
