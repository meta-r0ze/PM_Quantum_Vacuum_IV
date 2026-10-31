import PMDynamics
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.allImportedModuleNames do
    for downstream in [`PMDecay, `PMCosmo] do
      if downstream.isPrefixOf name then
        throwError "Downstream dependency {name} in Paper IV"
  logInfo "Dependency audit passed: no Paper V–VI imports in Paper IV"
