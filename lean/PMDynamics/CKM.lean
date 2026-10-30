import PMArch.Impedance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The CKM matrix: unitarity, determinant, Jarlskog invariant and the paper's values

* `ckm`: the standard parametrization with real `cᵢⱼ, sᵢⱼ` and a phase `u` (`u = e^{iδ}`).
* `ckm_unitary`: for `cᵢⱼ² + sᵢⱼ² = 1` and `u ū = 1`, every row pair satisfies
  `Σₖ Vᵢₖ V̄ⱼₖ = δᵢⱼ`: the matrix is exactly unitary. Unitarity holds for every choice of
  the three angles and the phase; it constrains nothing about their values.
* `ckm_det`: `det V = 1`. The mixing is complex while its determinant is real, so CP violation
  in mixing does not by itself feed `arg det` (the strong-CP combination; Paper III `CPPhases`).
* `jarlskog_ckm`: `Im(V_ud V_cs V̄_us V̄_cd) = c₁₂s₁₂c₂₃s₂₃c₁₃²s₁₃ · Im u`.

Paper IV's values: `s₁₂ = π/(ν−χ)`, `|V_cb| = (π+χ)/(α⁻¹ − Dπ)` with `s₂₃ = |V_cb|/c₁₃`,
`s₁₃ = 1/(χα⁻¹ + π)`, `δ = arctan(σ/χ)`, with Paper I's certified `α⁻¹`.

* `pm_jarlskog_matrix`: these values in the unitary matrix give exactly `pmJ`.
* `pmJ_bounds`: `3.02×10⁻⁵ < J < 3.03×10⁻⁵`.
* `pm3J_bounds`: Paper III's separate proposal `J = φ² T_geo η`, with
  `T_geo = χ(R_M − σ)/(N³σR_M)`, `N = 32`, `R_M = 172`, lies in `(3.0848, 3.0850)×10⁻⁵`.
* `papers_disagree`: the two proposals for the same invariant differ by more than 1.6%
  (`1.016 · pmJ < pm3J`). Both lie inside the calculator's comparison value `(3.06 ± 0.20)×10⁻⁵`, but at most
  one of them can be the derivation.
-/

noncomputable section
namespace PMDynamics.CKM
open Complex ComplexConjugate

def ckm (c12 s12 c23 s23 c13 s13 : ℝ) (u : ℂ) : Fin 3 → Fin 3 → ℂ :=
  ![![(c12:ℂ)*c13, (s12:ℂ)*c13, (s13:ℂ)*conj u],
    ![-(s12:ℂ)*c23 - (c12:ℂ)*s23*s13*u, (c12:ℂ)*c23 - (s12:ℂ)*s23*s13*u, (s23:ℂ)*c13],
    ![(s12:ℂ)*s23 - (c12:ℂ)*c23*s13*u, -(c12:ℂ)*s23 - (s12:ℂ)*c23*s13*u, (c23:ℂ)*c13]]

theorem ckm_unitary {c12 s12 c23 s23 c13 s13 : ℝ} {u : ℂ}
    (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1)
    (hu : u * conj u = 1) (i j : Fin 3) :
    (∑ k, ckm c12 s12 c23 s23 c13 s13 u i k * conj (ckm c12 s12 c23 s23 c13 s13 u j k)) =
      if i = j then 1 else 0 := by
  have h12 : (c12:ℂ)^2 + (s12:ℂ)^2 = 1 := by exact_mod_cast r12
  have h23 : (c23:ℂ)^2 + (s23:ℂ)^2 = 1 := by exact_mod_cast r23
  have h13 : (c13:ℂ)^2 + (s13:ℂ)^2 = 1 := by exact_mod_cast r13
  set w := conj u with hw
  have hww : conj w = u := by rw [hw, Complex.conj_conj]
  fin_cases i <;> fin_cases j <;>
    simp [ckm, Fin.sum_univ_three, map_mul, map_sub, map_neg, Complex.conj_ofReal, ← hw, hww]
  · linear_combination ((c13:ℂ)^2) * h12 + (1) * h13 + ((s13:ℂ)^2) * hu
  · linear_combination (-(c13:ℂ)*(s13:ℂ)*(s23:ℂ)*w) * h12
  · linear_combination (-(c13:ℂ)*(c23:ℂ)*(s13:ℂ)*w) * h12
  · linear_combination (-(c13:ℂ)*(s13:ℂ)*(s23:ℂ)*u) * h12
  · linear_combination ((c23:ℂ)^2 + (s13:ℂ)^2*(s23:ℂ)^2*u*w) * h12 + (1) * h23 +
      ((s23:ℂ)^2) * h13 + ((s13:ℂ)^2*(s23:ℂ)^2) * hu
  · linear_combination ((c23:ℂ)*(s13:ℂ)^2*(s23:ℂ)*u*w - (c23:ℂ)*(s23:ℂ)) * h12 +
      ((c23:ℂ)*(s23:ℂ)) * h13 + ((c23:ℂ)*(s13:ℂ)^2*(s23:ℂ)) * hu
  · linear_combination (-(c13:ℂ)*(c23:ℂ)*(s13:ℂ)*u) * h12
  · linear_combination ((c23:ℂ)*(s13:ℂ)^2*(s23:ℂ)*u*w - (c23:ℂ)*(s23:ℂ)) * h12 +
      ((c23:ℂ)*(s23:ℂ)) * h13 + ((c23:ℂ)*(s13:ℂ)^2*(s23:ℂ)) * hu
  · linear_combination ((c23:ℂ)^2*(s13:ℂ)^2*u*w + (s23:ℂ)^2) * h12 +
      ((c13:ℂ)^2 + (s13:ℂ)^2*u*w) * h23 + (1 - (s23:ℂ)^2) * h13 +
      (-(s13:ℂ)^2*(s23:ℂ)^2 + (s13:ℂ)^2) * hu

theorem ckm_det {c12 s12 c23 s23 c13 s13 : ℝ} {u : ℂ}
    (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1)
    (hu : u * conj u = 1) :
    (Matrix.of (ckm c12 s12 c23 s23 c13 s13 u)).det = 1 := by
  have h12 : (c12:ℂ)^2 + (s12:ℂ)^2 = 1 := by exact_mod_cast r12
  have h23 : (c23:ℂ)^2 + (s23:ℂ)^2 = 1 := by exact_mod_cast r23
  have h13 : (c13:ℂ)^2 + (s13:ℂ)^2 = 1 := by exact_mod_cast r13
  set w := conj u with hw
  rw [Matrix.det_fin_three]
  simp [ckm, ← hw]
  linear_combination ((c13:ℂ)^2*(c23:ℂ)^2 + (c13:ℂ)^2*(s23:ℂ)^2 + (c23:ℂ)^2*(s13:ℂ)^2*u*w +
      (s13:ℂ)^2*(s23:ℂ)^2*u*w) * h12 + ((c13:ℂ)^2 + (s13:ℂ)^2*u*w) * h23 + (1) * h13 +
      ((s13:ℂ)^2) * hu

/-- The quartet `Im(V_ud V_cs V̄_us V̄_cd)`. -/
def jarlskog (V : Fin 3 → Fin 3 → ℂ) : ℝ := (V 0 0 * V 1 1 * conj (V 0 1) * conj (V 1 0)).im

theorem jarlskog_ckm {c12 s12 c23 s23 c13 s13 : ℝ} (u : ℂ) (r12 : c12^2 + s12^2 = 1) :
    jarlskog (ckm c12 s12 c23 s23 c13 s13 u) = c12*s12*c23*s23*c13^2*s13 * u.im := by
  simp [jarlskog, ckm, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linear_combination (c12*s12*c23*s23*c13^2*s13*u.im) * r12

/-! ## Paper IV's values -/

def αinv : ℝ := PMArch.geometricIndex
def s12 : ℝ := Real.pi / 14
def c12 : ℝ := Real.sqrt (1 - s12^2)
def s13 : ℝ := 1 / (2*αinv + Real.pi)
def c13 : ℝ := Real.sqrt (1 - s13^2)
def vcb : ℝ := (Real.pi + 2) / (αinv - 4*Real.pi)
def s23 : ℝ := vcb / c13
def c23 : ℝ := Real.sqrt (1 - s23^2)
def δ : ℝ := Real.arctan (5/2)
def pmJ : ℝ := c12*s12*c23*s23*c13^2*s13*Real.sin δ

lemma ai_bounds : (137.0359992 : ℝ) < αinv ∧ αinv < 137.0359993 := by
  have h := PMArch.geometricIndex_bounds
  unfold αinv; constructor <;> linarith [h.1, h.2]

lemma s12_bounds : (0.2243994 : ℝ) < s12 ∧ s12 < 0.2243995 := by
  unfold s12; constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]

lemma s13_bounds : (0.0036073 : ℝ) < s13 ∧ s13 < 0.0036074 := by
  have ha := ai_bounds
  have hp1 := Real.pi_gt_d6; have hp2 := Real.pi_lt_d6
  have hd : 0 < 2*αinv + Real.pi := by linarith
  unfold s13
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

lemma vcb_bounds : (0.041308 : ℝ) < vcb ∧ vcb < 0.0413081 := by
  have ha := ai_bounds
  have hp1 := Real.pi_gt_d6; have hp2 := Real.pi_lt_d6
  have hd : 0 < αinv - 4*Real.pi := by linarith
  unfold vcb
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

lemma c12_bounds : (0.974497 : ℝ) < c12 ∧ c12 < 0.974498 := by
  have h := s12_bounds
  unfold c12
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1, h.2]
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1, h.2]

lemma c13_bounds : (0.999993 : ℝ) < c13 ∧ c13 ≤ 1 := by
  have h := s13_bounds
  unfold c13
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1, h.2]
  · rw [Real.sqrt_le_one]; nlinarith [h.1]

lemma s23_bounds : (0.041308 : ℝ) < s23 ∧ s23 < 0.0413084 := by
  have hv := vcb_bounds
  have hc := c13_bounds
  have hc0 : 0 < c13 := by linarith [hc.1]
  unfold s23
  constructor
  · rw [lt_div_iff₀ hc0]; nlinarith [hv.1, hc.2]
  · rw [div_lt_iff₀ hc0]; nlinarith [hv.2, hc.1]

lemma c23_bounds : (0.999146 : ℝ) < c23 ∧ c23 < 0.999147 := by
  have h := s23_bounds
  unfold c23
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1, h.2]
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1, h.2]

lemma sinδ_bounds : (0.928476 : ℝ) < Real.sin δ ∧ Real.sin δ < 0.928477 := by
  unfold δ
  rw [Real.sin_arctan]
  have hs : Real.sqrt (1 + (5/2 : ℝ)^2) = Real.sqrt 29 / 2 := by
    rw [show (1 + (5/2 : ℝ)^2) = 29 / 2^2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hs]
  have h1 : (5.385164 : ℝ) < Real.sqrt 29 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 29 < (5.385165 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hd : 0 < Real.sqrt 29 / 2 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

lemma mul_bounds {a b la ua lb ub : ℝ} (hla : 0 ≤ la) (hlb : 0 ≤ lb)
    (ha : la < a ∧ a < ua) (hb : lb < b ∧ b < ub) : la*lb < a*b ∧ a*b < ua*ub :=
  ⟨mul_lt_mul'' ha.1 hb.1 hla hlb, mul_lt_mul'' ha.2 hb.2 (by linarith [ha.1]) (by linarith [hb.1])⟩

theorem pmJ_bounds : (3.02e-5 : ℝ) < pmJ ∧ pmJ < 3.03e-5 := by
  have c13' : (0.999993 : ℝ) < c13 ∧ c13 < 1.0000001 := ⟨c13_bounds.1, by linarith [c13_bounds.2]⟩
  have p1 := mul_bounds (by norm_num) (by norm_num) c12_bounds s12_bounds
  have p2 := mul_bounds (by norm_num) (by norm_num) p1 c23_bounds
  have p3 := mul_bounds (by norm_num) (by norm_num) p2 s23_bounds
  have q := mul_bounds (by norm_num) (by norm_num) c13' c13'
  have p4 := mul_bounds (by norm_num) (by norm_num) p3 q
  have p5 := mul_bounds (by norm_num) (by norm_num) p4 s13_bounds
  have p6 := mul_bounds (by norm_num) (by norm_num) p5 sinδ_bounds
  have he : pmJ = c12*s12*c23*s23*(c13*c13)*s13*Real.sin δ := by unfold pmJ; ring
  rw [he]
  constructor
  · refine lt_of_le_of_lt ?_ p6.1; norm_num
  · refine lt_of_lt_of_le p6.2 ?_; norm_num

theorem pm_jarlskog_matrix :
    jarlskog (ckm c12 s12 c23 s23 c13 s13 (Complex.exp ((δ:ℂ) * Complex.I))) = pmJ := by
  have hs := s12_bounds
  have r12 : c12^2 + s12^2 = 1 := by
    unfold c12; rw [Real.sq_sqrt (by nlinarith [hs.1, hs.2])]; ring
  rw [jarlskog_ckm _ r12, Complex.exp_ofReal_mul_I_im]
  rfl

/-! ## Paper III's separate proposal -/

def pm3J : ℝ := ((1 + Real.sqrt 5)/2)^2 * (2*(172 - 5)/(32^3 * 5 * 172)) * (171/172)

theorem pm3J_bounds : (3.0848e-5 : ℝ) < pm3J ∧ pm3J < 3.0850e-5 := by
  have h1 : (2.236067 : ℝ) < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 5 < (2.236068 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold pm3J
  constructor <;> nlinarith [h1, h2]

theorem papers_disagree : 1.016 * pmJ < pm3J := by
  have h1 := pmJ_bounds; have h2 := pm3J_bounds
  linarith [h1.2, h2.1]

end PMDynamics.CKM
