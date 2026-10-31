import PMDynamics.OscillationAlgebra
import PMDynamics.SymmetricMass
import PMDynamics.CPAsymmetry
import PMDynamics.RelativisticPhase
import Lean

/-! These general results deliberately use no theory-package imports.
Keep that boundary checked separately from the full application closure. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.allImportedModuleNames do
    if name.toString.startsWith "PM" then
      unless name == `PMDynamics.OscillationAlgebra || name == `PMDynamics.SymmetricMass ||
          name == `PMDynamics.CPAsymmetry || name == `PMDynamics.RelativisticPhase do
        throwError "Theory dependency {name} in the independent algebra modules"
  logInfo "Independent algebra audit passed: no earlier or later paper imports"
