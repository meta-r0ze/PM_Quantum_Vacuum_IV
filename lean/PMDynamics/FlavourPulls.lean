import PMNested.TableConsequences
import PMArch.Impedance
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Paper IV's mixing formulas against PDG 2024 and NuFIT 6.0, and the shared weak mixing

`α⁻¹` is Paper I's derived `geometricIndex`; `φ = (1 + √5)/2`.

**CKM** (PDG 2024):
* `vus_pull`: `|V_us| = s₁₂c₁₃`, `s₁₂ = π/(ν − χ)`, `s₁₃ = 1/(χα⁻¹ + π)`, within `0.2σ` of `0.22431(85)`.
* `vcb_pull`: `|V_cb| = (π + χ)/(α⁻¹ − Dπ)` within `0.2σ` of `0.0411(12)`.
* `vub_pull`: `|V_ub| = s₁₃` is `1.0–1.1σ` below `0.00382(20)`.

**PMNS** (NuFIT 6.0, as the calculator cites):
* `solar_pull`: `sin²θ₁₂ = 1/(2φ)` within `0.5σ` of `0.304(12)`.
* `atmos_pull`: `sin²θ₂₃ = (1 + π/(ν+σ))/χ` within `0.1σ` of `0.574(16)`.
* `reactor_pull`: `sin²θ₁₃ = (σ − χ)/α⁻¹` within `0.7σ` of `0.02225(56)`.

**The weak mixing is Paper III's.** Paper IV's impedance-matching form
`sin²θ_W = Δ/(DΔ + 3πη/(2 sin θ_C) + (1 − η)σ)` with `sin θ_C = s₁₂ = π/(ν − χ)` is exactly
Paper III's `Δ/N_sys = 1849/8295` (`weak_mixing_shared`), since `3πη/(2·π/14) + (1−η)σ = 16η + 5`.
-/

noncomputable section
namespace PMDynamics.FlavourPulls
open PMArch

def αinv : ℝ := geometricIndex
def s12 : ℝ := Real.pi / 14
def s13 : ℝ := 1 / (2 * αinv + Real.pi)
def vus : ℝ := s12 * Real.sqrt (1 - s13 ^ 2)
def vcb : ℝ := (Real.pi + 2) / (αinv - 4 * Real.pi)
def φ : ℝ := (1 + Real.sqrt 5) / 2

lemma pi_b : (3.14159265358979 : ℝ) < Real.pi ∧ Real.pi < 3.1415926535898 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩
lemma g_b : (137.035999212 : ℝ) < αinv ∧ αinv < 137.035999213 := by
  have h := geometricIndex_bounds; constructor <;> unfold αinv <;> linarith [h.1, h.2]

lemma s13_b : (0.0036072 : ℝ) < s13 ∧ s13 < 0.0036074 := by
  have hp := pi_b; have hg := g_b
  have hd : 0 < 2 * αinv + Real.pi := by linarith
  unfold s13; constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

theorem vus_pull : |(vus - 0.22431) / 0.00085| < 0.2 := by
  have hp := pi_b; have h13 := s13_b
  have hc : (0.99999349 : ℝ) < Real.sqrt (1 - s13 ^ 2) ∧ Real.sqrt (1 - s13 ^ 2) ≤ 1 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith
    · rw [Real.sqrt_le_one]; nlinarith
  have hs : (0.22439947 : ℝ) < s12 ∧ s12 < 0.22439948 := by
    unfold s12; constructor <;> linarith
  unfold vus
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

theorem vcb_pull : |(vcb - 0.0411) / 0.0012| < 0.2 := by
  have hp := pi_b; have hg := g_b
  have hd : 0 < αinv - 4 * Real.pi := by linarith
  unfold vcb
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num), lt_sub_iff_add_lt, lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ (by norm_num), sub_lt_iff_lt_add, div_lt_iff₀ hd]; nlinarith

theorem vub_pull : -1.1 < (s13 - 0.00382) / 0.0002 ∧ (s13 - 0.00382) / 0.0002 < -1.0 := by
  have h := s13_b
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

lemma sqrt5_b : (2.2360679 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2360680 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg 5
  constructor <;> nlinarith

theorem solar_pull : |(1 / (2 * φ) - 0.304) / 0.012| < 0.5 := by
  have h := sqrt5_b
  have hd : 0 < 2 * φ := by unfold φ; positivity
  have q1 : 1 / (2 * φ) < 0.30902 := by rw [div_lt_iff₀ hd]; unfold φ; nlinarith
  have q2 : 0.30901 < 1 / (2 * φ) := by rw [lt_div_iff₀ hd]; unfold φ; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem atmos_pull : |((1 + Real.pi / (16 + 5)) / 2 - 0.574) / 0.016| < 0.1 := by
  have hp := pi_b
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

theorem reactor_pull : |((5 - 2) / αinv - 0.02225) / 0.00056| < 0.7 := by
  have hg := g_b
  have hd : 0 < αinv := by linarith
  have q1 : (5 - 2 : ℝ) / αinv < 0.0218921 := by rw [div_lt_iff₀ hd]; nlinarith
  have q2 : 0.0218920 < (5 - 2 : ℝ) / αinv := by rw [lt_div_iff₀ hd]; nlinarith
  rw [abs_lt]; constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **Paper IV's weak mixing is Paper III's.** -/
theorem weak_mixing_shared :
    (43 : ℝ) / (4 * 43 + 3 * Real.pi * PMNested.overhead / (2 * s12) + (1 - PMNested.overhead) * 5) =
      PMNested.clockRatio ∧ PMNested.clockRatio = 1849 / 8295 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, by norm_num [PMNested.clockRatio, PMNested.footprint, PMNested.overhead]⟩
  unfold PMNested.clockRatio PMNested.footprint s12
  congr 1
  field_simp
  ring

end PMDynamics.FlavourPulls
