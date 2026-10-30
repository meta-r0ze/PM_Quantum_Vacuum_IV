import PMDynamics.CKM

/-!
# The two CP phases, certified

`CKM` bounds `sin δ` for `δ = arctan(σ/χ) = arctan(5/2)` but not the angle itself. This module
certifies both CP phases as angles and compares them with current data.

* `arctan_lower`, `arctan_upper`: for `x ≥ 0`, the alternating series brackets `arctan x`
  (`x − x³/3 + x⁵/5 − x⁷/7 ≤ arctan x ≤ … + x⁹/9`), proved from the derivatives
  `x⁸/(1+x²) ≥ 0` and `x¹⁰/(1+x²) ≥ 0`.
* `δ_bounds`: `δ = π/2 − arctan(2/5)` lies in `(1.190284, 1.190317)` rad.
* `δ_degrees`: `68.198° < δ < 68.201°`.
* `δ_vs_gamma`: against LHCb's 2024 combination `γ = (64.6 ± 2.8)°` (in the standard
  parametrization `δ ≈ γ`), the pull is `+1.28` to `+1.29σ`. Against the `(68 ± 5)°` the paper
  cites it is below `0.05σ`.
* `nu_phase`: the leptonic phase `360°/φ = 180°(√5 − 1)` lies in `(222.492°, 222.493°)`, pull
  `+0.94σ` against NuFIT 6.0's `(197 ± 27)°`.
-/

noncomputable section
namespace PMDynamics.CPPhases
open Real

theorem arctan_lower (x : ℝ) (hx : 0 ≤ x) : x - x^3/3 + x^5/5 - x^7/7 ≤ arctan x := by
  let φ : ℝ → ℝ := fun y => arctan y - (y - y^3/3 + y^5/5 - y^7/7)
  have hd : ∀ y, HasDerivAt φ (y^8 / (1 + y^2)) y := by
    intro y
    have h1 := hasDerivAt_arctan y
    have h2 : HasDerivAt (fun y : ℝ => y - y^3/3 + y^5/5 - y^7/7) (1 - y^2 + y^4 - y^6) y := by
      have := ((((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
        ((hasDerivAt_pow 5 y).div_const 5)).sub ((hasDerivAt_pow 7 y).div_const 7))
      convert this using 1; norm_num
    convert h1.sub h2 using 1
    have : (1 + y^2) ≠ 0 := by positivity
    field_simp; ring
  have hmono : Monotone φ := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    (fun y => by rw [(hd y).deriv]; positivity)
  have := hmono hx
  simp only [φ, arctan_zero] at this
  linarith

theorem arctan_upper (x : ℝ) (hx : 0 ≤ x) :
    arctan x ≤ x - x^3/3 + x^5/5 - x^7/7 + x^9/9 := by
  let φ : ℝ → ℝ := fun y => (y - y^3/3 + y^5/5 - y^7/7 + y^9/9) - arctan y
  have hd : ∀ y, HasDerivAt φ (y^10 / (1 + y^2)) y := by
    intro y
    have h1 := hasDerivAt_arctan y
    have h2 : HasDerivAt (fun y : ℝ => y - y^3/3 + y^5/5 - y^7/7 + y^9/9)
        (1 - y^2 + y^4 - y^6 + y^8) y := by
      have := (((((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
        ((hasDerivAt_pow 5 y).div_const 5)).sub ((hasDerivAt_pow 7 y).div_const 7)).add
        ((hasDerivAt_pow 9 y).div_const 9))
      convert this using 1; norm_num
    convert h2.sub h1 using 1
    have : (1 + y^2) ≠ 0 := by positivity
    field_simp; ring
  have hmono : Monotone φ := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    (fun y => by rw [(hd y).deriv]; positivity)
  have := hmono hx
  simp only [φ, arctan_zero] at this
  linarith

theorem arctan_two_fifths : (0.380480 : ℝ) < arctan (2/5) ∧ arctan (2/5) < 0.380511 := by
  have l := arctan_lower (2/5) (by norm_num)
  have u := arctan_upper (2/5) (by norm_num)
  constructor
  · linarith [show (0.380480 : ℝ) < 2/5 - (2/5)^3/3 + (2/5)^5/5 - (2/5)^7/7 by norm_num]
  · linarith [show (2/5 : ℝ) - (2/5)^3/3 + (2/5)^5/5 - (2/5)^7/7 + (2/5)^9/9 < 0.380511 by norm_num]

theorem δ_eq : CKM.δ = π / 2 - arctan (2/5) := by
  unfold CKM.δ
  rw [show (5/2 : ℝ) = (2/5)⁻¹ by norm_num, arctan_inv_of_pos (by norm_num)]

theorem δ_bounds : (1.190284 : ℝ) < CKM.δ ∧ CKM.δ < 1.190317 := by
  rw [δ_eq]
  have h := arctan_two_fifths
  have p1 := pi_gt_d6; have p2 := pi_lt_d6
  constructor <;> linarith [h.1, h.2]

/-- The phase in degrees. -/
def δdeg : ℝ := CKM.δ * 180 / π

theorem δ_degrees : (68.198 : ℝ) < δdeg ∧ δdeg < 68.201 := by
  unfold δdeg
  rw [δ_eq]
  have h := arctan_two_fifths
  have p1 := pi_gt_d6; have p2 := pi_lt_d6
  have hp : 0 < π := pi_pos
  have e : (π / 2 - arctan (2/5)) * 180 / π = 90 - arctan (2/5) * 180 / π := by
    field_simp; ring
  rw [e]
  constructor
  · have : arctan (2/5) * 180 / π < 21.802 := by
      rw [div_lt_iff₀ hp]; nlinarith [h.2]
    linarith
  · have : 21.799 < arctan (2/5) * 180 / π := by
      rw [lt_div_iff₀ hp]; nlinarith [h.1]
    linarith

theorem δ_vs_gamma : 1.28 < (δdeg - 64.6) / 2.8 ∧ (δdeg - 64.6) / 2.8 < 1.29 ∧
    |δdeg - 68| / 5 < 0.05 := by
  have h := δ_degrees
  refine ⟨by rw [lt_div_iff₀ (by norm_num)]; linarith, by rw [div_lt_iff₀ (by norm_num)]; linarith, ?_⟩
  rw [abs_of_pos (by linarith), div_lt_iff₀ (by norm_num)]; linarith

/-- The leptonic phase `360°/φ`. -/
def nuDeg : ℝ := 360 / ((1 + √5) / 2)

theorem nu_phase : (222.492 : ℝ) < nuDeg ∧ nuDeg < 222.493 ∧
    0.94 < (nuDeg - 197) / 27 ∧ (nuDeg - 197) / 27 < 0.95 := by
  have s1 : (2.236067 : ℝ) < √5 := by rw [lt_sqrt (by norm_num)]; norm_num
  have s2 : √5 < (2.236068 : ℝ) := by rw [sqrt_lt' (by norm_num)]; norm_num
  have e : nuDeg = 180 * (√5 - 1) := by
    unfold nuDeg
    have h5 : (√5)^2 = 5 := sq_sqrt (by norm_num)
    have hp : (1 + √5) ≠ 0 := by positivity
    field_simp; nlinarith [h5]
  rw [e]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end PMDynamics.CPPhases
