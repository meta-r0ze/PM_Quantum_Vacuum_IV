import PMAction.OrderComparison
import PMDynamics.ReferenceSelection
import PMDynamics.FlavourResponseSelection
import PMDynamics.NativeFlavourPropagation
import PMDynamics.OscillationObservables

/-!
# A joint-sector comparison can observe relative flavour mixing

The separate uniform comparisons in `FlavourResponseSelection` see only
individual spectra. Compare the two evolution orders instead, using Paper II's
existing reversible comparison readout. The exact finite response depends on
noncommutation, so it can distinguish relative frames without choosing unequal
ensemble weights. A supplied three-mode phase-flip example keeps the reference
fixed and the individual spectra unchanged while its joint response varies.

This supplies a candidate observable, not its physical necessity, pricing or a
selected mixing angle. The complete native wall loop is treated separately on
one common embedding; a common reduced three-mode sector for two different wall
links is not assumed to follow from their separate preparations.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.FlavourOrderComparison
open Matrix PMAction
open scoped Kronecker
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def meanFlag (A B : M) : ℝ := OrderComparison.total A B / 3

theorem mean_formula (A B : M) :
    meanFlag A B = (∑ i, ∑ j, Complex.normSq ((A*B-B*A) i j))/12 := by
  rw [meanFlag, OrderComparison.total_formula]
  ring

theorem mean_zero_iff (A B : M) : meanFlag A B = 0 ↔ A*B=B*A := by
  simp only [meanFlag, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,
    OrderComparison.total_zero_iff]

/-- This loop uses the supplied exact flavour evolutions at finite times. -/
theorem evolution_loop_unitary (U V : M) (hu : U*Uᴴ=1) (hv : V*Vᴴ=1)
    (eu ev : Fin 3 → ℝ) (s t : ℝ) :
    OrderComparison.compareLoop (FlavourEvolution.evolution U eu s)
      (FlavourEvolution.evolution V ev t) ∈ unitary _ :=
  OrderComparison.loop_unitary _ _ (FlavourEvolution.evolution_unitary U eu hu s)
    (FlavourEvolution.evolution_unitary V ev hv t)

/-- In the up eigenbasis, response resolves phase gaps and down-sector amplitudes. -/
theorem diagonal_response (phase : Fin 3 → ℂ) (B : M) :
    meanFlag (diagonal phase) B =
      (∑ i, ∑ j, Complex.normSq (phase i-phase j) * Complex.normSq (B i j))/12 := by
  rw [mean_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (diagonal phase*B-B*diagonal phase) i j = (phase i-phase j)*B i j := by
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [he, Complex.normSq_mul]

def flip : M := diagonal ![1,1,-1]
def rotated (c s : ℝ) : M := ReferenceSelection.turn c s * flip * (ReferenceSelection.turn c s)ᴴ

theorem flip_unitary : flip ∈ unitary M := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [flip, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]

theorem rotated_unitary (c s : ℝ) (h : c^2+s^2=1) : rotated c s ∈ unitary M := by
  have ht : ReferenceSelection.turn c s ∈ unitary M :=
    ⟨mul_eq_one_comm.mp (ReferenceSelection.turn_unitary c s h), ReferenceSelection.turn_unitary c s h⟩
  exact (unitary M).mul_mem ((unitary M).mul_mem ht flip_unitary) (Unitary.star_mem ht)

theorem reference_fixed (c s : ℝ) :
    rotated c s *ᵥ (Pi.single 1 1) = (Pi.single 1 1 : Fin 3 → ℂ) := by
  ext i
  fin_cases i <;>
    simp [rotated, flip, ReferenceSelection.turn, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply]

theorem commutator_entries (c s : ℝ) :
    flip * rotated c s - rotated c s * flip =
      !![0,0,-((4*c*s:ℝ):ℂ); 0,0,0; ((4*c*s:ℝ):ℂ),0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotated, flip, ReferenceSelection.turn, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, conjTranspose_apply] <;> ring

theorem rotation_response (c s : ℝ) : meanFlag flip (rotated c s) = (8/3:ℝ)*c^2*s^2 := by
  rw [mean_formula, commutator_entries]
  simp [Fin.sum_univ_three, Complex.normSq_apply]
  ring

/-- A concrete positive joint signal, with no measured angle or mass as input. -/
theorem rational_signal : meanFlag flip (rotated (3/5) (4/5)) = (384/625:ℝ) := by
  rw [rotation_response]
  norm_num

theorem aligned_signal : meanFlag flip (rotated 1 0) = 0 := by
  rw [rotation_response]
  norm_num

/-- Each isolated uniformly averaged readout is unchanged by the rotation. -/
theorem isolated_rotation_response (c s : ℝ) (h : c^2+s^2=1) :
    (∑ a, CommonResponse.stateFlag (rotated c s) (Pi.single a 1))/3 = (1/3:ℝ) := by
  simp_rw [CommonResponse.basis_case _ (rotated_unitary c s h),
    InterferenceReadout.flag_formula _ (rotated_unitary c s h)]
  simp [rotated, flip, ReferenceSelection.turn, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_three, conjTranspose_apply, Complex.mul_re]
  ring

theorem response_zero_iff (c s : ℝ) : meanFlag flip (rotated c s) = 0 ↔ c=0 ∨ s=0 := by
  rw [rotation_response]
  simp [mul_eq_zero]

/-- This squared comparison is CP-even: it cannot select a conjugation branch. -/
theorem conjugation_tie (A B : M) :
    meanFlag (OscillationObservables.conjugated A) (OscillationObservables.conjugated B) =
      meanFlag A B := by
  have he : OscillationObservables.conjugated A * OscillationObservables.conjugated B -
      OscillationObservables.conjugated B * OscillationObservables.conjugated A =
      OscillationObservables.conjugated (A*B-B*A) := by
    ext i j
    simp [OscillationObservables.conjugated, Matrix.mul_apply, star_sub, star_sum, star_mul, mul_comm]
  rw [mean_formula, mean_formula, he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Complex.normSq_conj _

section Native
variable (a : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

def wallStep (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (t : ℝ) :
    Matrix (NativeFlavourWall.Modes (f := f) × r) (NativeFlavourWall.Modes (f := f) × r) ℂ :=
  NormedSpace.exp ((((-t:ℝ):ℂ)*Complex.I) •
    (WallExchange.H (NativeFlavourWall.momentum k) δ Y ⊗ₖ (1:Matrix r r ℂ)))

theorem native_step_observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (t : ℝ) :
    NativeObservation.Obs (NativeFlavourWall.embedding (r := r) a)
      (NativeFlavourPropagation.evolve (r := r) a p k δ Y t) (wallStep (r := r) k δ Y t) :=
  NativeObservation.exp (NativeFlavourWall.observed a p hp hp1 k δ Y) (((-t:ℝ):ℂ)*Complex.I)

/-- Both full wall evolutions use one embedding; no separate three-mode identification
is silently used to compose the native sectors. -/
theorem native_wall_loop (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y Z : Matrix f f ℂ) (s t : ℝ) :
    NativeObservation.Obs (NativeFlavourWall.embedding (r := r) a)
      (OrderComparison.compareLoop
        (NativeFlavourPropagation.evolve (r := r) a p k δ Y s)
        (NativeFlavourPropagation.evolve (r := r) a p k δ Z t))
      (OrderComparison.compareLoop (wallStep (r := r) k δ Y s) (wallStep (r := r) k δ Z t)) := by
  exact OrderComparison.observed_loop _ _ _ _ _
    (native_step_observed a p hp hp1 k δ Y s) (native_step_observed a p hp hp1 k δ Z t)

theorem native_wall_flag (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y Z : Matrix f f ℂ) (s t : ℝ)
    (ψ : NativeFlavourWall.Modes (f := f) × r → ℂ) :
    OrderComparison.flag (NativeFlavourPropagation.evolve (r := r) a p k δ Y s)
      (NativeFlavourPropagation.evolve (r := r) a p k δ Z t)
      (NativeFlavourWall.embedding a *ᵥ ψ) =
    OrderComparison.flag (wallStep (r := r) k δ Y s) (wallStep (r := r) k δ Z t) ψ :=
  OrderComparison.encoded_flag _ (NativeFlavourWall.isometry a) _ _ _ _
    (native_step_observed a p hp hp1 k δ Y s) (native_step_observed a p hp hp1 k δ Z t) ψ

end Native
end PMDynamics.FlavourOrderComparison
