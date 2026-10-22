import SolutionFC
import Mathlib

/-!
Read the raw PR's compiled interface without importing its sorried declaration.
The full-Mathlib reference and the narrower proof import closure synthesize
different, definitionally equal PartialOrder instance paths for sets. Verify
the entire model and target interface against the raw, unaligned PR variant.
-/
open Lean Elab Command Meta in
run_cmd do
  let (data, _) ← readModuleData (← findOLean `RawPRFC)
  let mut reference : NameMap ConstantInfo := {}
  for info in data.constants do
    reference := reference.insert info.name info
  let models := #[
    `Funk.FormalConjectures.IsSymmetricConvexBody,
    `Funk.FormalConjectures.IsFinitePolytope,
    `Funk.FormalConjectures.FullFlag,
    `Funk.FormalConjectures.FullFlag.mk,
    `Funk.FormalConjectures.FullFlag.faces,
    `Funk.FormalConjectures.FullFlag.nonempty,
    `Funk.FormalConjectures.FullFlag.convex,
    `Funk.FormalConjectures.FullFlag.extreme,
    `Funk.FormalConjectures.FullFlag.proper,
    `Funk.FormalConjectures.FullFlag.dimension,
    `Funk.FormalConjectures.FullFlag.chain]
  let targets := #[`Funk.FormalConjectures.kalaiFullFlags]
  for name in models ++ targets do
    let some original := reference.find? name
      | throwError "Missing raw PR declaration: {name}"
    liftTermElabM do
      let proved ← getConstInfo name
      unless proved.levelParams == original.levelParams &&
          (← isDefEq proved.type original.type) do
        throwError "Raw PR declaration type mismatch: {name}"
      if models.contains name then
        match proved.value?, original.value? with
        | some a, some b =>
          unless ← isDefEq a b do
            throwError "Raw PR geometric definition mismatch: {name}"
        | none, none => pure ()
        | _, _ => throwError "Raw PR declaration kind mismatch: {name}"
  logInfo m!"Exact raw PR model/target agreement: {models.size + targets.size} declarations"
