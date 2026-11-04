import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# The minimum stationarity residual of three spectral components

For nonnegative normalized weights, energy variance is exactly the minimum
squared residual from any single real frequency. This is algebra, independent
of the substrate, measured parameters, or a proposed flavour-selection cost.
-/

namespace PMFlavor.SpectralVariance

def mean (w energy : Fin 3 → ℝ) : ℝ := ∑ i, w i * energy i

def residual (w energy : Fin 3 → ℝ) (frequency : ℝ) : ℝ :=
  ∑ i, w i * (energy i - frequency) ^ 2

def variance (w energy : Fin 3 → ℝ) : ℝ := residual w energy (mean w energy)

/-- Exact completion of the square; no positivity assumption is needed for this identity. -/
theorem residual_decomposition (w energy : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (f : ℝ) :
    residual w energy f = variance w energy + (mean w energy - f) ^ 2 := by
  simp only [Fin.sum_univ_three] at hw
  simp only [residual, variance, mean, Fin.sum_univ_three]
  linear_combination (f ^ 2 - (w 0 * energy 0 + w 1 * energy 1 + w 2 * energy 2) ^ 2) * hw

theorem minimum (w energy : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (f : ℝ) :
    variance w energy ≤ residual w energy f := by
  rw [residual_decomposition w energy hw f]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem unique_minimizer (w energy : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (f : ℝ) :
    residual w energy f = variance w energy ↔ f = mean w energy := by
  rw [residual_decomposition w energy hw f]
  constructor
  · intro h
    nlinarith [sq_nonneg (mean w energy - f)]
  · rintro rfl; simp

/-- Variance is a sum over pairs: mixing weights multiply squared energy gaps. -/
theorem pairwise (w energy : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    variance w energy =
      w 0 * w 1 * (energy 0 - energy 1) ^ 2 +
      w 0 * w 2 * (energy 0 - energy 2) ^ 2 +
      w 1 * w 2 * (energy 1 - energy 2) ^ 2 := by
  have h := residual_decomposition w energy hw 0
  simp only [residual, variance, mean, Fin.sum_univ_three] at h ⊢
  simp only [Fin.sum_univ_three] at hw
  linear_combination -h - (w 0 * energy 0 ^ 2 + w 1 * energy 1 ^ 2 + w 2 * energy 2 ^ 2) * hw

/-- A quantitative lower bound using any two occupied slots, here slots 0 and 1. -/
theorem gap_lower_bound (w energy : Fin 3 → ℝ) (hw : ∑ i, w i = 1)
    (hn : ∀ i, 0 ≤ w i) (f : ℝ) :
    w 0 * w 1 * (energy 0 - energy 1) ^ 2 ≤ residual w energy f := by
  calc
    _ ≤ variance w energy := by
      rw [pairwise w energy hw]
      have h02 := mul_nonneg (mul_nonneg (hn 0) (hn 2)) (sq_nonneg (energy 0 - energy 2))
      have h12 := mul_nonneg (mul_nonneg (hn 1) (hn 2)) (sq_nonneg (energy 1 - energy 2))
      linarith
    _ ≤ _ := minimum w energy hw f

/-- With every slot occupied, zero residual is possible only for a constant
spectrum equal to the trial frequency. No normalization is needed for this test. -/
theorem zero_iff_constant (w energy : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (f : ℝ) :
    residual w energy f = 0 ↔ ∀ i, energy i = f := by
  constructor
  · intro h i
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        mul_nonneg (hw j).le (sq_nonneg (energy j - f)))).mp h i (Finset.mem_univ i)
    have hs := (mul_eq_zero.mp ht).resolve_left (ne_of_gt (hw i))
    nlinarith [sq_nonneg (energy i - f)]
  · intro h
    simp [residual, h]

end PMFlavor.SpectralVariance
