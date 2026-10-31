import PMDynamics.OscillationAlgebra
import PMDynamics.FlavourEvolution

/-! Apply independent three-component interference algebra to the already
constructed finite flavour evolution. No new earlier-paper theorem is assumed.
Vacuum conjugation is the supplied antineutrino prescription here; matter effects,
physical energies, preparation and baseline calibration remain outside this model. -/
noncomputable section
namespace PMDynamics.OscillationObservables
open Matrix
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def coefficients (U : M) (a b : Fin 3) : Fin 3 → ℂ := fun i => U a i*star (U b i)
def conjugated (U : M) : M := fun i j => star (U i j)

def phases (E : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := fun i => -t*E i

theorem evolution_entry (U : M) (E : Fin 3 → ℝ) (t : ℝ) (a b : Fin 3) :
    FlavourEvolution.evolution U E t a b =
      ∑ i, coefficients U a b i*OscillationAlgebra.phase (phases E t i) := by
  unfold FlavourEvolution.evolution PMAction.LinkExpansion.phaseDiag
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    coefficients, phases, OscillationAlgebra.phase_exp]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem probability_bridge (U : M) (E : Fin 3 → ℝ) (t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U E t a b =
      OscillationAlgebra.probability (coefficients U a b) (phases E t) := by
  unfold FlavourEvolution.probability OscillationAlgebra.probability
  rw [evolution_entry]

/-- The actual finite evolution has the full three-state interference formula. -/
theorem expanded_probability (U : M) (E : Fin 3 → ℝ) (t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U E t a b =
      (∑ i, Complex.normSq (coefficients U a b i))+
      2*(OscillationAlgebra.interference (coefficients U a b) (phases E t) 0 1+
         OscillationAlgebra.interference (coefficients U a b) (phases E t) 0 2+
         OscillationAlgebra.interference (coefficients U a b) (phases E t) 1 2) := by
  rw [probability_bridge, OscillationAlgebra.expanded]

/-- Normalized squared-sine formula, with the Kronecker initial condition
proved from completeness instead of inserted by hand. -/
theorem unitary_squared_sine (U : M) (hU : U*Uᴴ=1) (E : Fin 3 → ℝ) (t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U E t a b = (if a=b then 1 else 0)+
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 0 1+
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 0 2+
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 1 2 := by
  rw [probability_bridge,OscillationAlgebra.squared_sine_form]
  have h := congrArg (fun A : M => A a b) hU
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] at h
  have hn : Complex.normSq (∑ i, coefficients U a b i) = if a=b then 1 else 0 := by
    unfold coefficients
    rw [h]
    split_ifs <;> norm_num
  rw [hn]

/-- Probabilities detect energy differences, not a common energy offset. -/
theorem energy_shift (U : M) (E : Fin 3 → ℝ) (c t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U (fun i => E i+c) t a b =
      FlavourEvolution.probability U E t a b := by
  simp only [probability_bridge]
  have he : phases (fun i => E i+c) t = fun i => phases E t i+(-t*c) := by
    funext i; unfold phases; ring
  rw [he, OscillationAlgebra.common_phase]

/-- Equal eigenenergies cannot give flavour conversion in a complete unitary basis. -/
theorem degenerate_no_conversion (U : M) (hU : U*Uᴴ=1) (E t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U (fun _ => E) t a b = if a=b then 1 else 0 := by
  rw [probability_bridge]
  change OscillationAlgebra.probability _ (fun _ => -t*E) = _
  rw [OscillationAlgebra.equal_phases]
  have h := congrArg (fun A : M => A a b) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  change Complex.normSq (∑ i, U a i*star (U b i)) = _
  rw [h]
  split_ifs <;> norm_num

/-- Vacuum coefficient conjugation is equivalent to reversing propagation time. -/
theorem conjugation_time (U : M) (E : Fin 3 → ℝ) (t : ℝ) (a b : Fin 3) :
    FlavourEvolution.probability (conjugated U) E t a b =
      FlavourEvolution.probability U E (-t) a b := by
  simp only [probability_bridge]
  have hc : coefficients (conjugated U) a b =
      fun i => star (coefficients U a b i) := by funext i; simp [coefficients,conjugated]
  have ht : phases E t = fun i => -phases E (-t) i := by
    funext i; unfold phases; ring
  rw [hc,ht, OscillationAlgebra.conjugate_reverse]

/-- A survival channel has real pair quartets, hence no vacuum conjugation asymmetry. -/
theorem survival_no_asymmetry (U : M) (E : Fin 3 → ℝ) (t : ℝ) (a : Fin 3) :
    FlavourEvolution.probability U E t a a =
      FlavourEvolution.probability (conjugated U) E t a a := by
  simp only [probability_bridge]
  have hc : coefficients (conjugated U) a a =
      fun i => star (coefficients U a a i) := by funext i; simp [coefficients,conjugated]
  rw [hc]
  apply OscillationAlgebra.real_quartets_no_asymmetry <;>
    simp [OscillationAlgebra.quartet, coefficients, Complex.mul_conj]

end PMDynamics.OscillationObservables
