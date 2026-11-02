import PMDynamics.ReferenceSpectrum
import PMDynamics.SpectralVariance
import PMDynamics.MassMixing

/-!
# Quantitative stationarity test for the actual flavour Hamiltonian

The energy-basis residual is derived from `MassMixing.mass`, not assigned as a
new physical cost. Its exact minimum is energy variance. A nonzero mixing pair
and an energy gap force a strictly positive residual at every trial frequency.
This tests proposed stationary references; it selects neither dynamics nor masses.
-/

noncomputable section
namespace PMDynamics.FlavourStationarity
open Matrix Complex

abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def weights (U : M) (a : Fin 3) : Fin 3 → ℝ := fun i => normSq (U a i)

theorem weights_sum (U : M) (hU : U * Uᴴ = 1) (a : Fin 3) :
    ∑ i, weights U a i = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun hU a) a)
  simpa [weights, mul_apply, conjTranspose_apply, Complex.mul_conj] using h

/-- Coordinates of `(H - f) e_a` in the energy basis, for the existing Hamiltonian. -/
theorem residual_coordinates (U : M) (hU : U * Uᴴ = 1)
    (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    Uᴴ *ᵥ (MassMixing.mass U energy *ᵥ Pi.single a 1 -
      (f : ℂ) • Pi.single a 1) =
      fun i => ((energy i - f : ℝ) : ℂ) * star (U a i) := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hd : Uᴴ * MassMixing.mass U energy = MassMixing.eigenMass energy * Uᴴ := by
    simp [MassMixing.mass, ← Matrix.mul_assoc, hU']
  rw [mulVec_sub, mulVec_smul, mulVec_mulVec, hd, ← mulVec_mulVec]
  ext i
  simp [MassMixing.eigenMass, mulVec_diagonal, mulVec_single, conjTranspose_apply]
  ring

/-- Squared residual, expressed in the orthonormal energy coordinates. -/
def residual (U : M) (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) : ℝ :=
  ∑ i, normSq ((Uᴴ *ᵥ (MassMixing.mass U energy *ᵥ Pi.single a 1 -
    (f : ℂ) • Pi.single a 1)) i)

/-- The energy-coordinate residual equals the squared residual in the original
flavour coordinates; changing the basis does not change its size. -/
theorem physical_residual (U : M) (hU : U * Uᴴ = 1)
    (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    residual U energy a f = ∑ i, normSq ((MassMixing.mass U energy *ᵥ Pi.single a 1 -
      (f : ℂ) • (Pi.single a 1 : Fin 3 → ℂ)) i) := by
  have hu : Uᴴ ∈ unitary M := by
    exact ⟨by simpa only [star_eq_conjTranspose, conjTranspose_conjTranspose] using hU,
      by simpa only [star_eq_conjTranspose, conjTranspose_conjTranspose] using
        (mul_eq_one_comm.mp hU)⟩
  have h := congrArg Complex.re (PMAction.CommonResponse.unitary_nsq Uᴴ hu
    (MassMixing.mass U energy *ᵥ Pi.single a 1 - (f : ℂ) • Pi.single a 1))
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.re_sum, Complex.ofReal_re] at h
  exact h

theorem residual_eq (U : M) (hU : U * Uᴴ = 1)
    (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    residual U energy a f = SpectralVariance.residual (weights U a) energy f := by
  unfold residual
  rw [residual_coordinates U hU]
  apply Finset.sum_congr rfl
  intro i _
  simp [weights, normSq_apply, Complex.mul_re,
    Complex.mul_im, pow_two]
  ring

/-- Exact minimum and its unique trial frequency, for any supplied unitary mixing. -/
theorem minimum_residual (U : M) (hU : U * Uᴴ = 1)
    (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    residual U energy a f = SpectralVariance.variance (weights U a) energy +
      (SpectralVariance.mean (weights U a) energy - f) ^ 2 := by
  rw [residual_eq U hU]
  exact SpectralVariance.residual_decomposition _ _ (weights_sum U hU a) f

/-- Mixing between two split energies imposes a nonzero lower bound on stationarity error. -/
theorem gap_lower_bound (U : M) (hU : U * Uᴴ = 1)
    (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    normSq (U a 0) * normSq (U a 1) * (energy 0 - energy 1) ^ 2 ≤
      residual U energy a f := by
  rw [residual_eq U hU]
  exact SpectralVariance.gap_lower_bound _ _ (weights_sum U hU a)
    (fun i => normSq_nonneg _) f

/-- For the supplied PMNS matrix, a split of energies 0 and 1 excludes zero residual
for every charged flavour and every real trial frequency. No measured mass is used. -/
theorem pmns_residual_positive (energy : Fin 3 → ℝ) (hgap : energy 0 ≠ energy 1)
    (a : Fin 3) (f : ℝ) : 0 < residual PMNS.matrix energy a f := by
  have h0 := normSq_pos.mpr (GenerationBreaking.pmns_all_nonzero a 0)
  have h1 := normSq_pos.mpr (GenerationBreaking.pmns_all_nonzero a 1)
  have hp : 0 < normSq (PMNS.matrix a 0) * normSq (PMNS.matrix a 1) *
      (energy 0 - energy 1) ^ 2 :=
    mul_pos (mul_pos h0 h1) (sq_pos_of_ne_zero (sub_ne_zero.mpr hgap))
  exact hp.trans_le (gap_lower_bound _ PMNS.rows energy a f)

/-- Complete zero-residual characterization, including all possible degeneracies. -/
theorem pmns_zero_iff_constant (energy : Fin 3 → ℝ) (a : Fin 3) (f : ℝ) :
    residual PMNS.matrix energy a f = 0 ↔ ∀ i, energy i = f := by
  rw [residual_eq _ PMNS.rows]
  exact SpectralVariance.zero_iff_constant _ _
    (fun i => normSq_pos.mpr (GenerationBreaking.pmns_all_nonzero a i)) f

end PMDynamics.FlavourStationarity
