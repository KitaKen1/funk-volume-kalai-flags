import FinalTheorems
import Mathlib

/-! Read the compiled public interfaces of the actual FC problem statements.
Their declarations, including the proof placeholders, are never installed in
the proof environment. Compare their types and geometric definition bodies.
Mathlib supplies the constants appearing in the compiled FC expressions. -/

open Lean Elab Command Meta in
run_cmd do
  let mut reference : NameMap ConstantInfo := {}
  for modName in #[`KalaiFullFlags, `SymmetricFunkVolume] do
    let (data, _) ← readModuleData (← findOLean modName)
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
    `Funk.FormalConjectures.FullFlag.chain,
    `FunkVolume.IsSymmetricConvexBody,
    `FunkVolume.coordinatePolar,
    `FunkVolume.translate,
    `FunkVolume.funkVolume]
  let targets := #[`FunkVolume.symmetricFunkVolume,
    `Funk.FormalConjectures.kalaiFullFlags]
  for name in models ++ targets do
    let some original := reference.find? name
      | throwError "Missing FC reference declaration: {name}"
    liftTermElabM do
      let proved ← getConstInfo name
      unless proved.levelParams == original.levelParams &&
          (← isDefEq proved.type original.type) do
        throwError "FC declaration type mismatch: {name}"
      if models.contains name then
        match proved.value?, original.value? with
        | some a, some b =>
          unless ← isDefEq a b do
            throwError "FC geometric definition mismatch: {name}"
        | none, none => pure ()
        | _, _ => throwError "FC definition kind mismatch: {name}"
    if targets.contains name then
      logInfo m!"Exact FC target type match: {name}"
  logInfo m!"FC geometric declarations matched: {models.size} (types and definition bodies)"

#print axioms FunkVolume.symmetricFunkVolume
#print axioms Funk.FormalConjectures.kalaiFullFlags
