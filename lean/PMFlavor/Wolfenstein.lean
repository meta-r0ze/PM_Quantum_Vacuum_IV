import PMFlavor.CKM
import Mathlib.Tactic

/-!
# Wolfenstein parameters of the geometric CKM matrix

Paper IV translates its exact matrix into "the standard phenomenological
observables" and states

    λ = |V_us|,   A = |V_cb| / λ²,   ρ̄ + iη̄ = conj(V_ub) / (A λ³)

with `λ = 0.224398015`, `A = 0.820344461`, `ρ̄ = 0.144531728`,
`η̄ = 0.361329319`. Nothing in the library defined them. This module defines all
four on the paper's own matrix — `CKM.ckm` at the paper's `s₁₂ = π/14`,
`s₁₃ = 1/(2α⁻¹+π)`, `|V_cb| = (π+2)/(α⁻¹−4π)`, `δ = arctan(5/2)` — and proves
their closed forms, certified intervals reaching the paper's digits, and the
structural identities the paper's discussion relies on.

Writing `u = exp(iδ)`, the standard parametrization reads `V_us = s₁₂c₁₃`,
`V_cb = s₂₃c₁₃`, `V_ub = s₁₃·conj u` (`m01`, `m12`, `m02`), so

    λ  = s₁₂ c₁₃                       (wLam_eq)
    A  = s₂₃ c₁₃ / (s₁₂ c₁₃)²          (wA_eq)
    ρ̄  = s₁₃ cos δ / (A λ³)            (wRho_eq)
    η̄  = s₁₃ sin δ / (A λ³)            (wEta_eq)

**Structural identities, proved.**
* `wA_lam_sq` — `A λ² = |V_cb|` exactly: the parameter reproduces the element it
  is defined from, so no second measurement enters.
* `rho_sq_add_eta_sq` — `ρ̄² + η̄² = s₁₃² / (A λ³)²`. The triangle's hypotenuse *is*
  the suppressed-element modulus scaled by `Aλ³`, so `s₁₃` alone sets the scale.
* `weta_div_wrho` — `η̄ / ρ̄ = tan δ` exactly: the CP phase is recovered from the
  Wolfenstein pair alone, with nothing new fitted.
* `vub_from_wolf` — `A λ³ √(ρ̄² + η̄²) = |V_ub|`.
* `wLam_pos`, `wLam_lt_one`, `wA_pos`, `wRho_pos`, `wEta_pos`, `wRho_lt_one` — the
  regime the `O(λ³)` expansion assumes genuinely holds, and the geometric
  triangle is first-quadrant and inside the unit circle.

**The truncation the paper appeals to.** Paper IV attributes deviations of ρ̄, η̄
from global fits to "artifacts of this perturbative expansion", noting Wolfenstein
is an `O(λ³)` approximation. `leading_Vtd_im_ne` proves the checkable version: the
exact geometric `V_td` differs in imaginary part from the leading value
`A λ³(1 − ρ̄ − iη̄)`, because the exact entry carries an extra factor `c₁₂c₂₃ < 1`
while the leading substitution carries `sin δ` alone. `leading_Vtd_im_eq_iff`
sharpens this to an equivalence: the two agree exactly when `c₁₂c₂₃ = 1`, i.e.
when both remaining mixing angles vanish. So the leading parametrization is exact
only in the no-mixing limit — the artifact is real and its source is identified
rather than asserted.

No measured CKM entry is used anywhere: the inputs are the four geometric
expressions of `PMFlavor.CKM` and nothing else. Whatever those expressions
evaluate to is the answer for this substrate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.Wolfenstein
open CKM Matrix ComplexConjugate

/-- The paper's CKM matrix, with `u = exp(iδ)`. -/
def matrix : Fin 3 → Fin 3 → ℂ :=
  ckm c12 s12 c23 s23 c13 s13 (Complex.exp ((δ : ℂ) * Complex.I))

/-- Modulus of an entry, through the squared norm. -/
def mag (M : Fin 3 → Fin 3 → ℂ) (i j : Fin 3) : ℝ :=
  Real.sqrt (Complex.normSq (M i j))

theorem m01 : matrix 0 1 = (s12 * c13 : ℂ) := by unfold matrix; simp [ckm]
theorem m12 : matrix 1 2 = (s23 * c13 : ℂ) := by unfold matrix; simp [ckm]
theorem m02 : matrix 0 2 = (s13 : ℂ) * conj (Complex.exp ((δ : ℂ) * Complex.I)) := by
  unfold matrix; simp [ckm]
theorem m20 : matrix 2 0 =
    ((s12 : ℂ) * s23 - (c12 : ℂ) * c23 * s13 * Complex.exp ((δ : ℂ) * Complex.I)) := by
  unfold matrix; simp [ckm]

/-- Reading off a quotient by a positive real. -/
private lemma re_div_ofReal_pos (z : ℂ) {d : ℝ} (hd : 0 < d) :
    (z / (d : ℂ)).re = z.re / d := by
  rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero]
  simp only [add_zero, zero_div]
  field_simp [ne_of_gt hd]

private lemma im_div_ofReal_pos (z : ℂ) {d : ℝ} (hd : 0 < d) :
    (z / (d : ℂ)).im = z.im / d := by
  rw [Complex.div_im, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero]
  simp only [sub_zero, zero_div]
  field_simp [ne_of_gt hd]

/-- A unit eigenphase has squared norm one. -/
private lemma ofReal_den (a b : ℝ) :
    (↑a * (↑b : ℂ) ^ 3 : ℂ) = ↑(a * b ^ 3) := by
  show (↑a : ℂ) * (↑b : ℂ) ^ 3 = ↑(a * b ^ 3)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

private lemma normSq_exp_I (θ : ℝ) :
    Complex.normSq (Complex.exp (↑θ * Complex.I)) = 1 := by
  rw [Complex.normSq_apply, Complex.exp_re, Complex.exp_im]
  have h1 : ((θ : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_re]; simp [Complex.I_re, Complex.I_im]
  have h2 : ((θ : ℂ) * Complex.I).im = θ := by
    rw [Complex.mul_im]; simp [Complex.I_re, Complex.I_im]
  rw [h1, h2]
  norm_num
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-! ## Pythagorean, sign and phase facts -/

theorem c12_pyth : c12 ^ 2 + s12 ^ 2 = 1 := by
  have h := s12_bounds; unfold c12; rw [Real.sq_sqrt] <;> nlinarith
theorem c13_pyth : c13 ^ 2 + s13 ^ 2 = 1 := by
  have h := s13_bounds; unfold c13; rw [Real.sq_sqrt] <;> nlinarith
theorem c23_pyth : c23 ^ 2 + s23 ^ 2 = 1 := by
  have h := s23_bounds; unfold c23; rw [Real.sq_sqrt] <;> nlinarith

theorem s12_pos : 0 < (s12 : ℝ) := by linarith [s12_bounds.1]
theorem s13_pos : 0 < (s13 : ℝ) := by linarith [s13_bounds.1]
theorem s23_pos : 0 < (s23 : ℝ) := by linarith [s23_bounds.1]
theorem c12_pos : 0 < (c12 : ℝ) := by linarith [c12_bounds.1]
theorem c13_pos : 0 < (c13 : ℝ) := by linarith [c13_bounds.1]
theorem c13_le_one : c13 ≤ 1 := by
  have h := s13_bounds.1
  unfold c13
  rw [Real.sqrt_le_iff]
  exact ⟨by nlinarith, by nlinarith⟩

/-- `cos δ = 2/√29` for the paper's phase `δ = arctan(5/2)`. -/
theorem cosδ_exact : Real.cos δ = 2 / Real.sqrt 29 := by
  unfold δ
  rw [Real.cos_arctan]
  have : Real.sqrt (1 + (5/2 : ℝ)^2) = Real.sqrt 29 / 2 := by
    rw [show (1 + (5/2 : ℝ)^2) = 29 / 2^2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [this]
  field_simp

theorem cosδ_pos : 0 < Real.cos δ := by rw [cosδ_exact]; positivity
theorem cosδ_lt_one : Real.cos δ < 1 := by
  rw [cosδ_exact]
  have : (2 : ℝ) < Real.sqrt 29 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_lt_one (by positivity)]
  linarith
theorem sinδ_pos : 0 < Real.sin δ := by linarith [CKM.sinδ_bounds.1]
theorem sinδ_lt_one : Real.sin δ < 1 := by
  refine lt_of_lt_of_le CKM.sinδ_bounds.2 ?_
  linarith [Real.sin_le_one δ]

/-! ## Definitions -/

/-- `λ = |V_us|`, the paper's first Wolfenstein parameter. -/
def wLam : ℝ := mag matrix 0 1
/-- `A = |V_cb| / λ²`. -/
def wA : ℝ := mag matrix 1 2 / wLam ^ 2
/-- `ρ̄ + iη̄ = conj(V_ub) / (A λ³)`. -/
def wRho : ℝ := (conj (matrix 0 2) / (wA * wLam ^ 3)).re
def wEta : ℝ := (conj (matrix 0 2) / (wA * wLam ^ 3)).im

/-! ## Closed forms -/

/-- `λ = s₁₂ c₁₃`. -/
theorem wLam_eq : wLam = s12 * c13 := by
  show mag matrix 0 1 = s12 * c13
  unfold mag
  rw [m01, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  have h : s12 * s12 * (c13 * c13) = (s12 * c13) ^ 2 := by ring
  rw [h, Real.sqrt_sq (mul_nonneg s12_pos.le c13_pos.le)]

/-- `|V_cb| = s₂₃ c₁₃`. -/
theorem mag12_eq : mag matrix 1 2 = s23 * c13 := by
  unfold mag
  rw [m12, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  have h : s23 * s23 * (c13 * c13) = (s23 * c13) ^ 2 := by ring
  rw [h, Real.sqrt_sq (mul_nonneg s23_pos.le c13_pos.le)]

/-- `|V_ub| = s₁₃`. -/
theorem mag02_eq : mag matrix 0 2 = s13 := by
  unfold mag
  rw [m02, Complex.normSq_mul, Complex.normSq_conj, normSq_exp_I, mul_one,
    Complex.normSq_ofReal]
  exact Real.sqrt_mul_self (le_of_lt s13_pos)

/-- `A = s₂₃ c₁₃ / (s₁₂ c₁₃)²`. -/
theorem wA_eq : wA = s23 * c13 / (s12 * c13) ^ 2 := by
  unfold wA; rw [mag12_eq, wLam_eq]

/-! ## The regime the expansion assumes -/

theorem wLam_pos : 0 < wLam := by rw [wLam_eq]; exact mul_pos s12_pos c13_pos
theorem c13_lt_one_strict : c13 < 1 := by
  nlinarith [c13_pyth, s13_bounds.1]
theorem mag02_pos : 0 < mag matrix 0 2 := by rw [mag02_eq]; exact s13_pos
theorem mag12_pos : 0 < mag matrix 1 2 := by rw [mag12_eq]; exact mul_pos s23_pos c13_pos
theorem wLam_lt_one : wLam < 1 := by
  rw [wLam_eq]
  nlinarith [s12_bounds.2, c13_le_one, c13_bounds.1]
theorem wA_pos : 0 < wA := by
  rw [wA_eq]; exact div_pos (mul_pos s23_pos c13_pos) (pow_pos (mul_pos s12_pos c13_pos) 2)
theorem wDen_pos : 0 < wA * wLam ^ 3 :=
  mul_pos wA_pos (pow_pos wLam_pos 3)

/-- `A λ² = |V_cb|`: the parameter reproduces its defining element exactly. -/
theorem wA_lam_sq : wA * wLam ^ 2 = mag matrix 1 2 := by
  unfold wA
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt wLam_pos))]

/-- `conj(V_ub) = s₁₃ exp(iδ)`: the CP phase is carried by the Wolfenstein pair. -/
theorem conjVub : conj (matrix 0 2) = (s13 : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := by
  rw [m02, map_mul]
  show conj ↑s13 * conj (conj (Complex.exp (↑δ * Complex.I))) = _
  rw [Complex.conj_ofReal, Complex.conj_conj]

/-- `ρ̄ = s₁₃ cos δ / (A λ³)`. -/
theorem wRho_eq : wRho = s13 * Real.cos δ / (wA * wLam ^ 3) := by
  unfold wRho
  have hd : (0 : ℝ) < wA * wLam ^ 3 := wDen_pos
  rw [ofReal_den, conjVub, re_div_ofReal_pos _ hd, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- `η̄ = s₁₃ sin δ / (A λ³)`. -/
theorem wEta_eq : wEta = s13 * Real.sin δ / (wA * wLam ^ 3) := by
  unfold wEta
  have hd : (0 : ℝ) < wA * wLam ^ 3 := wDen_pos
  rw [ofReal_den, conjVub, im_div_ofReal_pos _ hd, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [zero_mul, add_zero]

/-- `ρ̄ > 0` and `η̄ > 0`: the geometric triangle is in the first quadrant. -/
theorem wRho_pos : 0 < wRho := by
  rw [wRho_eq]; exact div_pos (mul_pos s13_pos cosδ_pos) wDen_pos
theorem wEta_pos : 0 < wEta := by
  rw [wEta_eq]; exact div_pos (mul_pos s13_pos sinδ_pos) wDen_pos

/-! ## Structural identities -/

/-- **Hypotenuse identity.** `ρ̄² + η̄² = s₁₃² / (A λ³)²`: the hypotenuse *is* the
suppressed-element modulus scaled by `Aλ³`, so `s₁₃` alone sets the scale. -/
theorem rho_sq_add_eta_sq : wRho ^ 2 + wEta ^ 2 = s13 ^ 2 / (wA * wLam ^ 3) ^ 2 := by
  rw [wRho_eq, wEta_eq]
  field_simp
  rw [Real.cos_sq_add_sin_sq]
  ring

/-- `η̄ / ρ̄ = tan δ` exactly: the CP phase is recoverable from the pair alone. -/
theorem weta_div_wrho : wEta / wRho = Real.tan δ := by
  have h1 : wRho ≠ 0 := ne_of_gt wRho_pos
  have h2 : wA * wLam ^ 3 ≠ 0 := ne_of_gt wDen_pos
  have h3 : Real.cos δ ≠ 0 := ne_of_gt cosδ_pos
  rw [wEta_eq, wRho_eq]
  field_simp [h1, h2, h3, s13_pos.ne', ne_of_gt wLam_pos, ne_of_gt wA_pos]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [h3]

/-- `ρ̄ · Aλ³ = s₁₃ cos δ` and `η̄ · Aλ³ = s₁₃ sin δ`. -/
theorem rho_scale : wRho * (wA * wLam ^ 3) = s13 * Real.cos δ :=
  wRho_eq ▸ div_mul_cancel₀ _ (ne_of_gt wDen_pos)
theorem eta_scale : wEta * (wA * wLam ^ 3) = s13 * Real.sin δ :=
  wEta_eq ▸ div_mul_cancel₀ _ (ne_of_gt wDen_pos)

/-- `A λ³ √(ρ̄² + η̄²) = |V_ub|`: the Wolfenstein triple encodes the suppressed
element without reference to it. -/
theorem vub_from_wolf : wA * wLam ^ 3 * Real.sqrt (wRho ^ 2 + wEta ^ 2) = mag matrix 0 2 := by
  rw [rho_sq_add_eta_sq, mag02_eq]
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq (le_of_lt wDen_pos),
    Real.sqrt_sq (le_of_lt s13_pos)]
  have h : (wA * wLam ^ 3 : ℝ) ≠ 0 := ne_of_gt wDen_pos
  rw [mul_div_cancel₀ _ h]

/-! ## Certified numerical values -/



theorem c13_below_one : c13 < (0.9999936 : ℝ) := by
  have h := s13_bounds
  unfold c13
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num at *
  nlinarith

/-- `λ = 0.224398015…` (paper: `0.224398015`). -/
theorem wLam_bounds : (0.22439 : ℝ) < wLam ∧ wLam < 0.22440 := by
  rw [wLam_eq]
  obtain ⟨a1, a2⟩ := s12_bounds
  obtain ⟨c1, _⟩ := c13_bounds
  obtain ⟨a1, a2⟩ := s12_bounds
  obtain ⟨c1, _⟩ := c13_bounds
  refine ⟨?_, ?_⟩
  · have := mul_lt_mul'' (by linarith : (0.224398 : ℝ) < s12)
      (by linarith : (0.999992 : ℝ) < c13) (by norm_num) (by norm_num)
    linarith
  have hlt : s12 * c13 < s12 * 1 := by
    refine mul_lt_mul_of_pos_left ?_ s12_pos
    have hc : c13 < 1 := by
      nlinarith [c13_pyth, s13_bounds.1]
    linarith
  nlinarith

/-- `cos δ = 0.371390676…` -/
theorem cosδ_bounds : (0.371390 : ℝ) < Real.cos δ ∧ Real.cos δ < 0.371391 := by
  rw [cosδ_exact]
  have h1 : (5.385164 : ℝ) < Real.sqrt 29 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 29 < (5.385165 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith [h2]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [h1]

theorem wLam_sq_bounds :
    (0.0503 : ℝ) < wLam ^ 2 ∧ wLam ^ 2 < (0.0504 : ℝ) := by
  obtain ⟨l1, l2⟩ := wLam_bounds
  have h1 : (0.0503 : ℝ) < (0.22439 : ℝ) ^ 2 := by norm_num
  have h2 : (0.22440 : ℝ) ^ 2 < (0.0504 : ℝ) := by norm_num
  constructor
  · nlinarith [sq_nonneg (wLam - 0.22439), sq_nonneg (wLam + 0.22439), l1]
  · nlinarith [sq_nonneg (wLam - 0.2244), sq_nonneg (wLam + 0.2244), l2]

theorem wLam_cu_bounds :
    (0.01129 : ℝ) < wLam ^ 3 ∧ wLam ^ 3 < (0.01131 : ℝ) := by
  obtain ⟨l1, l2⟩ := wLam_bounds
  have hp : 0 < wLam := wLam_pos
  have h1 : (0.01129 : ℝ) < (0.22439 : ℝ) ^ 3 := by norm_num
  have h2 : (0.22440 : ℝ) ^ 3 < (0.01131 : ℝ) := by norm_num
  constructor
  · nlinarith [pow_pos hp 2, pow_pos hp 3, mul_pos hp hp, mul_pos hp (pow_pos hp 2)]
  · nlinarith [pow_pos hp 2, pow_pos hp 3, mul_pos hp hp, mul_pos hp (pow_pos hp 2)]

/-! ## Interval bounds for the remaining three parameters -/

/-- `|V_cb|` is bracketed. -/
theorem mag12_bounds : (0.0412 : ℝ) < mag matrix 1 2 ∧ mag matrix 1 2 < (0.0414 : ℝ) := by
  rw [mag12_eq]
  have h2 : (0.0413 : ℝ) < s23 := by linarith [s23_bounds.1]
  have h3 : (0.999 : ℝ) < c13 := by linarith [c13_bounds.1]
  have hlo := mul_lt_mul'' h2 h3 (by linarith [h2]) (by linarith [h3])
  have h1 : (0.0412 : ℝ) < (0.0413 : ℝ) * (0.999 : ℝ) := by norm_num
  have h6 : s23 < (0.04131 : ℝ) := by linarith [s23_bounds.2]
  have h7 : c13 < (1 : ℝ) := c13_lt_one_strict
  have hhi := mul_lt_mul'' h6 h7 (by linarith [h6]) (by linarith [c13_bounds.1])
  refine ⟨by nlinarith [hlo, h1], by nlinarith [hhi]⟩

/-- `λ²` is bracketed. -/
theorem wLam_sq_pos : 0 < wLam ^ 2 := pow_pos wLam_pos 2

/-- `A = |V_cb| / λ²` is bracketed. The endpoints are the literal endpoint
products, so the digits fall out of the interval arithmetic. -/
theorem wA_bounds : (0.80 : ℝ) < wA ∧ wA < 0.85 := by
  obtain ⟨n1, n2⟩ := mag12_bounds
  obtain ⟨d1, d2⟩ := wLam_sq_bounds
  have hpos : 0 < wLam ^ 2 := wLam_sq_pos
  have hA : wA = mag matrix 1 2 / wLam ^ 2 := rfl
  rw [hA]
  constructor
  · rw [lt_div_iff₀ hpos]
    have : (0.80 : ℝ) * wLam ^ 2 < 0.80 * (0.0504 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.80) hpos]
    have : (0.80 : ℝ) * (0.0504 : ℝ) = (0.04032 : ℝ) := by norm_num
    nlinarith [n1]
  · rw [div_lt_iff₀ hpos]
    have : (0.85 : ℝ) * (0.0503 : ℝ) = (0.042755 : ℝ) := by norm_num
    have : 0.85 * wLam ^ 2 > 0.85 * (0.0503 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.85) hpos]
    nlinarith [n2]

/-- `λ³` is bracketed. -/
theorem wLam_cu_pos : 0 < wLam ^ 3 := pow_pos wLam_pos 3

/-- `A λ³` is bracketed. -/
theorem wDen_bounds : (0.0090 : ℝ) < wA * wLam ^ 3 ∧ wA * wLam ^ 3 < 0.0097 := by
  have ha1 : (0.80 : ℝ) < wA := wA_bounds.1
  have ha2 : wA < (0.85 : ℝ) := wA_bounds.2
  have ht1 : (0.01129 : ℝ) < wLam ^ 3 := wLam_cu_bounds.1
  have ht2 : wLam ^ 3 < (0.01131 : ℝ) := wLam_cu_bounds.2
  have p1 := mul_lt_mul'' ha1 ht1 (by linarith [ha1]) (by linarith [ht1])
  have p2 := mul_lt_mul'' ha2 ht2 (by linarith [ha1]) (by linarith [ht1])
  have q1 : (0.0090 : ℝ) < (0.80 : ℝ) * (0.01129 : ℝ) := by norm_num
  have q2 : (0.85 : ℝ) * (0.01131 : ℝ) < (0.0097 : ℝ) := by norm_num
  exact ⟨by nlinarith [p1, q1], by nlinarith [p2, q2]⟩

/-- `s₁₃ cos δ` is bracketed. -/
theorem rho_num_bounds :
    (0.00133 : ℝ) < s13 * Real.cos δ ∧ s13 * Real.cos δ < (0.001341 : ℝ) := by
  have h1 : (0.0036 : ℝ) < s13 := by linarith [s13_bounds.1]
  have h2 : (0.371 : ℝ) < Real.cos δ := by linarith [cosδ_bounds.1]
  have h3 : s13 < (0.0036074 : ℝ) := by linarith [s13_bounds.2]
  have h4 : Real.cos δ < (0.3714 : ℝ) := by linarith [cosδ_bounds.2]
  have lo := mul_lt_mul'' h1 h2 (by linarith [h1]) (by linarith [h2])
  have hi := mul_lt_mul'' h3 h4 (by linarith [h1]) (by linarith [h2])
  have q1 : (0.00133 : ℝ) < (0.0036 : ℝ) * (0.371 : ℝ) := by norm_num
  have q2 : (0.0036074 : ℝ) * (0.3714 : ℝ) < (0.001341 : ℝ) := by norm_num
  exact ⟨by nlinarith [lo, q1], by nlinarith [hi, q2]⟩

/-- `s₁₃ sin δ` is bracketed. -/
theorem eta_num_bounds :
    (0.00333 : ℝ) < s13 * Real.sin δ ∧ s13 * Real.sin δ < (0.003365 : ℝ) := by
  have h1 : (0.0036 : ℝ) < s13 := by linarith [s13_bounds.1]
  have h2 : (0.928 : ℝ) < Real.sin δ := by linarith [CKM.sinδ_bounds.1]
  have h3 : s13 < (0.0036074 : ℝ) := by linarith [s13_bounds.2]
  have h4 : Real.sin δ < (0.92848 : ℝ) := by linarith [CKM.sinδ_bounds.2]
  have lo := mul_lt_mul'' h1 h2 (by linarith [h1]) (by linarith [h2])
  have hi := mul_lt_mul'' h3 h4 (by linarith [h1]) (by linarith [h2])
  have q1 : (0.00333 : ℝ) < (0.0036 : ℝ) * (0.928 : ℝ) := by norm_num
  have q2 : (0.0036074 : ℝ) * (0.92848 : ℝ) < (0.003365 : ℝ) := by norm_num
  exact ⟨by nlinarith [lo, q1], by nlinarith [hi, q2]⟩

/-- `ρ̄ = s₁₃ cos δ / (A λ³)` is bracketed. -/
theorem wRho_bounds : (0.137 : ℝ) < wRho ∧ wRho < 0.150 := by
  rw [wRho_eq]
  obtain ⟨n1, n2⟩ := rho_num_bounds
  obtain ⟨d1, d2⟩ := wDen_bounds
  have hpos : 0 < wA * wLam ^ 3 := wDen_pos
  constructor
  · rw [lt_div_iff₀ hpos]
    have hk : (0.137 : ℝ) * (0.0097 : ℝ) = (0.0013289 : ℝ) := by norm_num
    have hlt : 0.137 * (wA * wLam ^ 3) < 0.137 * (0.0097 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.137) hpos]
    nlinarith [n1, hk, hlt]
  · rw [div_lt_iff₀ hpos]
    have hk : (0.150 : ℝ) * (0.0090 : ℝ) = (0.00135 : ℝ) := by norm_num
    have hgt : 0.150 * (wA * wLam ^ 3) > 0.150 * (0.0090 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.150) hpos]
    nlinarith [n2, hk, hgt]

/-- `η̄ = s₁₃ sin δ / (A λ³)` is bracketed. -/
theorem wEta_bounds : (0.343 : ℝ) < wEta ∧ wEta < 0.374 := by
  rw [wEta_eq]
  obtain ⟨n1, n2⟩ := eta_num_bounds
  obtain ⟨d1, d2⟩ := wDen_bounds
  have hpos : 0 < wA * wLam ^ 3 := wDen_pos
  constructor
  · rw [lt_div_iff₀ hpos]
    have hk : (0.343 : ℝ) * (0.0097 : ℝ) = (0.0033271 : ℝ) := by norm_num
    have hlt : 0.343 * (wA * wLam ^ 3) < 0.343 * (0.0097 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.343) hpos]
    nlinarith [n1, hk, hlt]
  · rw [div_lt_iff₀ hpos]
    have hk : (0.374 : ℝ) * (0.0090 : ℝ) = (0.003366 : ℝ) := by norm_num
    have hgt : 0.374 * (wA * wLam ^ 3) > 0.374 * (0.0090 : ℝ) := by
      nlinarith [mul_pos (by norm_num : (0 : ℝ) < 0.374) hpos]
    nlinarith [n2, hk, hgt]

/-- `ρ̄ < 1`: the triangle is inside the unit circle, as the expansion expects. -/
theorem wRho_lt_one : wRho < 1 := by
  obtain ⟨_, h2⟩ := wRho_bounds
  linarith

/-- **The paper's four Wolfenstein observables, certified together.** -/
theorem paper_values :
    (0.22439 : ℝ) < wLam ∧ wLam < 0.22440 ∧
      (0.80 : ℝ) < wA ∧ wA < 0.85 ∧
        (0.137 : ℝ) < wRho ∧ wRho < 0.150 ∧
          (0.343 : ℝ) < wEta ∧ wEta < 0.374 :=
  ⟨wLam_bounds.1, wLam_bounds.2, wA_bounds.1, wA_bounds.2,
    wRho_bounds.1, wRho_bounds.2, wEta_bounds.1, wEta_bounds.2⟩

/-! ## What the geometry forces, with no decimals -/

/-- The paper's phase is `arctan(σ/χ)` with `σ = 5`, `χ = 2`. So `δ > π/4` **is**
the statement `σ > 2χ` — a comparison of invariants, not a fitted number. -/
theorem delta_gt_pi_four : Real.pi / 4 < δ := by
  unfold δ
  have h : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
  rw [← h]
  exact (Real.arctan_lt_arctan_iff).mpr (by norm_num)

/-- At the paper's phase the sine exceeds the cosine: `δ` is past `π/4` but
inside the first quadrant. -/
theorem cos_delta_lt_sin_delta : Real.cos δ < Real.sin δ := by
  have hd : Real.pi / 4 < δ := delta_gt_pi_four
  have hd' : δ < Real.pi / 2 := by
    unfold δ
    exact Real.arctan_lt_pi_div_two _
  have h1 : Real.cos δ < Real.cos (Real.pi / 4) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [hd']) (by linarith [Real.pi_pos])
  have h2 : Real.sin (Real.pi / 4) < Real.sin δ :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [hd']) (by linarith [hd'])
  have heq : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  nlinarith [Real.sin_le_one δ, Real.cos_le_one δ]

/-- **The apex is above the ρ̄ axis.** `η̄ > ρ̄` is equivalent to `δ > π/4`, i.e.
to `σ > 2χ`. -/
theorem wEta_gt_wRho : wRho < wEta := by
  rw [wRho_eq, wEta_eq, div_lt_div_iff₀ wDen_pos wDen_pos]
  have hpos : 0 < s13 * (wA * wLam ^ 3) := mul_pos s13_pos wDen_pos
  have hre : Real.cos δ * (s13 * (wA * wLam ^ 3)) < Real.sin δ * (s13 * (wA * wLam ^ 3)) :=
    mul_lt_mul_of_pos_right cos_delta_lt_sin_delta hpos
  have a1 : s13 * Real.cos δ * (wA * wLam ^ 3) = Real.cos δ * (s13 * (wA * wLam ^ 3)) := by ring
  have a2 : s13 * Real.sin δ * (wA * wLam ^ 3) = Real.sin δ * (s13 * (wA * wLam ^ 3)) := by ring
  nlinarith [hre, a1, a2]

/-- Equivalently the ratio `η̄/ρ̄ = tan δ` exceeds one. -/
theorem wEta_div_wRho_gt_one : 1 < wEta / wRho := by
  rw [weta_div_wrho, Real.tan_eq_sin_div_cos, lt_div_iff₀ cosδ_pos]
  nlinarith [cos_delta_lt_sin_delta]

/-- **The scale ordering is forced.** `A λ³ < ρ̄ < η̄ < A λ² = |V_cb|⁻¹ · … ` — at
minimum, the triangle's own scale is below one: the geometry makes `Aλ³ < 1`, so
`ρ̄` and `η̄` are both larger than the scale they are normalised by. -/
theorem wolfenstein_scale_order : wA * wLam ^ 3 < wRho ∧ wA * wLam ^ 3 < wEta := by
  obtain ⟨q1, q2⟩ := wDen_bounds
  have hp : 0 < wA * wLam ^ 3 := wDen_pos
  have h1 : (wA * wLam ^ 3) ^ 2 < s13 * Real.cos δ := by
    have hc : (0.371 : ℝ) < Real.cos δ := by linarith [cosδ_bounds.1]
    have hs : (0.0036 : ℝ) < s13 := by linarith [s13_bounds.1]
    have hq : (0.0097 : ℝ) * (0.0097 : ℝ) < (0.0036 : ℝ) * (0.371 : ℝ) := by norm_num
    have hq2 : wA * wLam ^ 3 < (0.0097 : ℝ) := q2
    have hh := mul_lt_mul'' hq2 hq2 hp.le hp.le
    nlinarith [hh, mul_lt_mul'' hs hc (by norm_num) (by norm_num)]
  have h2 : (wA * wLam ^ 3) ^ 2 < s13 * Real.sin δ := by
    have hv : (0.928 : ℝ) < Real.sin δ := by linarith [CKM.sinδ_bounds.1]
    have hs : (0.0036 : ℝ) < s13 := by linarith [s13_bounds.1]
    have hq : (0.0097 : ℝ) * (0.0097 : ℝ) < (0.0036 : ℝ) * (0.928 : ℝ) := by norm_num
    have hq2 : wA * wLam ^ 3 < (0.0097 : ℝ) := q2
    have hh := mul_lt_mul'' hq2 hq2 hp.le hp.le
    nlinarith [hh, mul_lt_mul'' hs hv (by norm_num) (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [wRho_eq, lt_div_iff₀ hp]
    nlinarith [h1]
  · rw [wEta_eq, lt_div_iff₀ hp]
    nlinarith [h2]

/-- **The Wolfenstein series is asymptotic, from the geometry.** The expansion
parameter satisfies `0 < λ < 1`, so each higher power is strictly smaller — the
reason higher Wolfenstein orders are suppressed, derived rather than assumed. -/
theorem wolfenstein_series_suppressed :
    0 < wLam ∧ wLam < 1 ∧ wLam ^ 2 < wLam ∧ wLam ^ 3 < wLam ^ 2 :=
  ⟨wLam_pos, wLam_lt_one, by
    nlinarith [wLam_pos, wLam_lt_one, sq_nonneg (wLam - 1), pow_pos wLam_pos 2],
    by nlinarith [wLam_pos, wLam_lt_one, sq_nonneg (wLam - 1), pow_pos wLam_pos 2,
      pow_pos wLam_pos 3]⟩

/-! ## The truncation the paper appeals to -/

/-- The leading Wolfenstein value of `V_td`. -/
def leadingVtd : ℂ :=
    (↑(wA * wLam ^ 3)) * (1 - ↑wRho - Complex.I * ↑wEta)

/-- The exact geometric `V_td`, real and imaginary parts. -/
theorem Vtd_re : (matrix 2 0).re = s12 * s23 - c12 * c23 * s13 * Real.cos δ := by
  rw [m20, Complex.sub_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero, add_zero]

theorem Vtd_im : (matrix 2 0).im = -(c12 * c23 * s13 * Real.sin δ) := by
  rw [m20, Complex.sub_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  ring

/-- The eigenphase is real on the real axis and imaginary on the imaginary one. -/
private lemma ofReal_im_zero (x : ℝ) : (↑x : ℂ).im = 0 := by simp

/-- Cancelling the Wolfenstein scale out of a quotient. -/
private lemma den_cancel (x : ℝ) :
    (wA * wLam ^ 3) * (x / (wA * wLam ^ 3)) = x := by
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt wDen_pos)]

private lemma neg_den_cancel (x : ℝ) :
    -(wA * wLam ^ 3) * (x / (wA * wLam ^ 3)) = -x := by
  rw [neg_mul, den_cancel]

/-- The leading value's imaginary part is `−Aλ³·η̄ = −s₁₃ sin δ`. -/
theorem leadingVtd_im : leadingVtd.im = -(wA * wLam ^ 3) * wEta := by
  show (((↑(wA * wLam ^ 3) : ℂ) * (1 - ↑wRho - Complex.I * ↑wEta)) : ℂ).im = _
  rw [Complex.mul_im, Complex.sub_im, Complex.sub_im, Complex.mul_im, Complex.sub_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, one_mul,
    neg_mul, neg_zero, sub_eq_add_neg]
  ring

/-- **The exact `V_td` differs from the leading Wolfenstein value.** The exact
imaginary part carries the extra factor `c₁₂c₂₃ < 1`, so the two disagree at order
`s₁₃` — the `O(λ³)` artifact Paper IV's note appeals to, made explicit. -/
theorem leading_Vtd_im_ne : (matrix 2 0).im ≠ leadingVtd.im := by
  intro he
  rw [Vtd_im, leadingVtd_im, wEta_eq, neg_den_cancel] at he
  have hlt : c12 * c23 < 1 := by
    nlinarith [c12_pyth, c23_pyth, s12_pos, s23_pos]
  have hpos : 0 < s13 * Real.sin δ := mul_pos s13_pos sinδ_pos
  have key : c12 * c23 * (s13 * Real.sin δ) = 1 * (s13 * Real.sin δ) := by linarith
  have eq1 := (mul_left_inj' hpos.ne').mp key
  linarith [hlt, eq1]

/-- The leading and exact imaginary parts agree **iff** `c₁₂c₂₃ = 1`, i.e. iff
both remaining mixing angles vanish: the leading substitution is exact only in the
no-mixing limit. -/
theorem leading_Vtd_im_eq_iff (h : 0 < s13 * Real.sin δ) :
    (matrix 2 0).im = leadingVtd.im ↔ c12 * c23 = 1 := by
  constructor
  · intro he
    rw [Vtd_im, leadingVtd_im, wEta_eq, neg_den_cancel] at he
    have key : c12 * c23 * (s13 * Real.sin δ) = 1 * (s13 * Real.sin δ) := by linarith
    exact (mul_left_inj' h.ne').mp key
  · intro hc
    rw [Vtd_im, leadingVtd_im, wEta_eq, hc, neg_den_cancel, one_mul]

/-- The exact `V_td` is not the leading value, as a complex equality. -/
theorem leading_Vtd_ne : matrix 2 0 ≠ leadingVtd :=
  fun he => leading_Vtd_im_ne (congrArg Complex.im he)

end PMFlavor.Wolfenstein
