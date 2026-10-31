import PMDynamics.OscillationAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Stability of the squared-amplitude readout under phase errors. This layer
uses Mathlib and interference algebra only; no spectrum or mixing is selected. -/
noncomputable section
namespace PMDynamics.OscillationStability
open OscillationAlgebra

lemma norm_phase_eq_one (x : ℝ) : ‖phase x‖ = 1 := by
  have h := phase_norm x
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (phase x)]

/-- Unit complex phases are 1-Lipschitz in their real arguments. -/
theorem phase_error (x y : ℝ) : ‖phase x - phase y‖ ≤ |x-y| := by
  have hf : phase x-phase y=(phase (x-y)-1)*phase y := by
    rw [sub_mul,one_mul,← phase_add]
    congr 2
    ring
  rw [hf,norm_mul,norm_phase_eq_one,mul_one,phase_exp]
  simpa only [mul_comm,Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

lemma amplitude_bound (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) :
    ‖∑ i, z i*phase (θ i)‖ ≤ ∑ i, ‖z i‖ := by
  calc
    _ ≤ ∑ i, ‖z i*phase (θ i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_phase_eq_one,mul_one]

/-- A weighted sum of the phase errors bounds the amplitude error. -/
theorem amplitude_error (z : Fin 3 → ℂ) (θ φ : Fin 3 → ℝ) :
    ‖(∑ i, z i*phase (θ i))-(∑ i, z i*phase (φ i))‖ ≤
      ∑ i, ‖z i‖ * |θ i-φ i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i, z i*(phase (θ i)-phase (φ i))‖ := by simp only [mul_sub]
    _ ≤ ∑ i, ‖z i*(phase (θ i)-phase (φ i))‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (phase_error _ _) (norm_nonneg _)

/-- Normalized amplitude coefficients turn phase errors into an explicit
probability error. No small-error approximation is used in this inequality. -/
theorem probability_error (z : Fin 3 → ℂ) (hz : ∑ i, ‖z i‖ ≤ 1)
    (θ φ : Fin 3 → ℝ) :
    |probability z θ-probability z φ| ≤ 2*∑ i, ‖z i‖ * |θ i-φ i| := by
  have ha := (amplitude_bound z θ).trans hz
  have hb := (amplitude_bound z φ).trans hz
  have hd := abs_norm_sub_norm_le (∑ i, z i*phase (θ i)) (∑ i, z i*phase (φ i))
  have he := amplitude_error z θ φ
  have hs : ‖∑ i, z i*phase (θ i)‖+‖∑ i, z i*phase (φ i)‖ ≤ 2 := by linarith
  have hn : 0 ≤ ‖∑ i, z i*phase (θ i)‖+‖∑ i, z i*phase (φ i)‖ := by positivity
  unfold probability
  simp only [Complex.normSq_eq_norm_sq]
  rw [show ‖∑ i, z i*phase (θ i)‖^2-‖∑ i, z i*phase (φ i)‖^2 =
    (‖∑ i, z i*phase (θ i)‖-‖∑ i, z i*phase (φ i)‖)*
    (‖∑ i, z i*phase (θ i)‖+‖∑ i, z i*phase (φ i)‖) by ring,
    abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ ‖(∑ i, z i*phase (θ i))-(∑ i, z i*phase (φ i))‖*2 :=
      mul_le_mul hd hs hn (norm_nonneg _)
    _ ≤ _ := by nlinarith [he]

/-- A uniform phase tolerance gives a uniform probability tolerance. -/
theorem probability_error_uniform (z : Fin 3 → ℂ) (hz : ∑ i, ‖z i‖ ≤ 1)
    (θ φ : Fin 3 → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ i, |θ i-φ i| ≤ ε) :
    |probability z θ-probability z φ| ≤ 2*ε := by
  have he : (∑ i, ‖z i‖ * |θ i-φ i|) ≤ ε := by
    calc
      _ ≤ ∑ i, ‖z i‖ * ε := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
      _ = (∑ i, ‖z i‖)*ε := (Finset.sum_mul ..).symm
      _ ≤ ε := by nlinarith
  exact (probability_error z hz θ φ).trans (by linarith)

end PMDynamics.OscillationStability
