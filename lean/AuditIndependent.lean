import PMFlavor.OscillationAlgebra
import PMFlavor.SymmetricMass
import PMFlavor.CPAsymmetry
import PMFlavor.RelativisticPhase
import PMFlavor.OscillationStability
import PMFlavor.SpectralVariance
import Lean

/-! These general results deliberately use no theory-package imports.
Keep that boundary checked separately from the full application closure. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.allImportedModuleNames do
    if name.toString.startsWith "PM" then
      unless name == `PMFlavor.OscillationAlgebra || name == `PMFlavor.SymmetricMass ||
          name == `PMFlavor.CPAsymmetry || name == `PMFlavor.RelativisticPhase ||
          name == `PMFlavor.OscillationStability || name == `PMFlavor.SpectralVariance do
        throwError "Theory dependency {name} in the independent algebra modules"
  logInfo "Independent algebra audit passed: no earlier or later paper imports"
