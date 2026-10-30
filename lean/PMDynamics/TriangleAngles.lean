import PMDynamics.CKM

/-!
# `sin 2β`, `|V_td|` and `|V_ts|` of the geometric CKM matrix, certified

The calculator's unitarity-triangle values are now checked in Lean from the same inputs as
`CKM.pmJ` (`s₁₂ = π/14`, `s₁₃ = 1/(2α⁻¹+π)`, `|V_cb| = (π+2)/(α⁻¹−4π)`, `δ = arctan(5/2)`).

* `w_parts`: `w = −V_cd · conj V_td` has real part
  `s₁₂² s₂₃c₂₃ − c₁₂² c₂₃s₂₃ s₁₃² + c₁₂s₁₂s₁₃ cos δ (s₂₃² − c₂₃²)` and imaginary part
  `c₁₂s₁₂s₁₃ sin δ`. Since `V_cb* V_tb > 0`, `β = arg w`.
* `sin_two_beta`: `sin 2β = 2 Re w Im w/|w|²` (`Complex.sin_arg`, `cos_arg`).
* `sin2β_bounds`: `0.7019 < sin 2β < 0.7023` (calculator: `0.70215`). Against PDG's
  `0.710 ± 0.011` (HFLAV evaluation) the pull is `−0.75` to `−0.69σ`; the paper cites
  `0.699 ± 0.017`.
-/

noncomputable section
namespace PMDynamics.TriangleAngles
open Complex ComplexConjugate PMDynamics.CKM

def cosδ : ℝ := Real.cos CKM.δ
def sinδ : ℝ := Real.sin CKM.δ

lemma cosδ_bounds : (0.3713906 : ℝ) < cosδ ∧ cosδ < 0.3713907 := by
  unfold cosδ CKM.δ
  rw [Real.cos_arctan]
  have hs : Real.sqrt (1 + (5/2 : ℝ)^2) = Real.sqrt 29 / 2 := by
    rw [show (1 + (5/2 : ℝ)^2) = 29 / 2^2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hs]
  have h1 : (5.3851648 : ℝ) < Real.sqrt 29 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 29 < (5.3851649 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hd : 0 < Real.sqrt 29 / 2 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

def re : ℝ := s12^2*s23*c23 - c12^2*c23*s23*s13^2 + c12*s12*s13*cosδ*(s23^2 - c23^2)
def im : ℝ := c12*s12*s13*sinδ

/-- **`w = −V_cd · conj V_td`, with `u = e^{iδ}`, has these parts.** -/
theorem w_parts {c12 s12 c23 s23 c13 s13 θ : ℝ} (r23 : c23^2 + s23^2 = 1) :
    let u : ℂ := ⟨Real.cos θ, Real.sin θ⟩
    let V := ckm c12 s12 c23 s23 c13 s13 u
    (-(V 1 0) * conj (V 2 0)).re =
        s12^2*s23*c23 - c12^2*c23*s23*s13^2 + c12*s12*s13*Real.cos θ*(s23^2 - c23^2) ∧
      (-(V 1 0) * conj (V 2 0)).im = c12*s12*s13*Real.sin θ := by
  intro u V
  have hcs := Real.sin_sq_add_cos_sq θ
  simp only [V, u, ckm, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  constructor
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (-(c12^2*c23*s23*s13^2)) * hcs
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (c12*s12*s13*Real.sin θ) * r23

/-- **`sin 2β` from the parts of `w`.** -/
theorem sin_two_beta (w : ℂ) (hw : w ≠ 0) :
    Real.sin (2 * Complex.arg w) = 2 * w.re * w.im / (w.re ^ 2 + w.im ^ 2) := by
  rw [Real.sin_two_mul, Complex.sin_arg, Complex.cos_arg hw]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have e : 2 * (w.im / ‖w‖) * (w.re / ‖w‖) = 2 * w.re * w.im / ‖w‖ ^ 2 := by
    field_simp
  rw [e, h2]

lemma re_bounds : (0.0017858 : ℝ) < re ∧ re < 0.0017864 := by
  obtain ⟨a1, a2⟩ := s12_bounds; obtain ⟨b1, b2⟩ := s23_bounds; obtain ⟨d1, d2⟩ := c23_bounds
  obtain ⟨e1, e2⟩ := c12_bounds; obtain ⟨f1, f2⟩ := s13_bounds; obtain ⟨g1, g2⟩ := cosδ_bounds
  have A1 : (0.2243994:ℝ)^2*0.041308*0.999146 < s12^2*s23*c23 := by
    have := mul_lt_mul'' (mul_lt_mul'' (pow_lt_pow_left₀ a1 (by norm_num) (by norm_num : (2:ℕ) ≠ 0)) b1
      (by norm_num) (by norm_num)) d1 (by norm_num) (by norm_num)
    linarith
  have A2 : s12^2*s23*c23 < (0.2243995:ℝ)^2*0.0413084*0.999147 := by
    have := mul_lt_mul'' (mul_lt_mul'' (pow_lt_pow_left₀ a2 (by linarith) (by norm_num : (2:ℕ) ≠ 0)) b2
      (by nlinarith) (by linarith)) d2 (by nlinarith) (by linarith)
    linarith
  have B1 : 0 < c12^2*c23*s23*s13^2 := by positivity
  have B2 : c12^2*c23*s23*s13^2 < (0.974498:ℝ)^2*0.999147*0.0413084*0.0036074^2 := by
    have h1 := pow_lt_pow_left₀ e2 (by linarith) (by norm_num : (2:ℕ) ≠ 0)
    have h2 := pow_lt_pow_left₀ f2 (by linarith) (by norm_num : (2:ℕ) ≠ 0)
    have := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' h1 d2 (by positivity) (by linarith)) b2
      (by positivity) (by linarith)) h2 (by positivity) (by positivity)
    linarith
  have hc : 0 < c23^2 - s23^2 := by nlinarith
  have C1 : (0.974497:ℝ)*0.2243994*0.0036073*0.3713906*(0.999146^2 - 0.0413084^2) <
      c12*s12*s13*cosδ*(c23^2 - s23^2) := by
    have h1 : (0.999146:ℝ)^2 - 0.0413084^2 < c23^2 - s23^2 := by nlinarith
    have := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' e1 a1 (by norm_num) (by norm_num))
      f1 (by norm_num) (by norm_num)) g1 (by norm_num) (by norm_num)) h1 (by norm_num) (by norm_num)
    linarith
  have C2 : c12*s12*s13*cosδ*(c23^2 - s23^2) <
      (0.974498:ℝ)*0.2243995*0.0036074*0.3713907*(0.999147^2 - 0.041308^2) := by
    have h1 : c23^2 - s23^2 < (0.999147:ℝ)^2 - 0.041308^2 := by nlinarith
    have := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' e2 a2 (by linarith) (by linarith))
      f2 (by positivity) (by linarith)) g2 (by positivity) (by linarith)) h1 (by positivity) hc.le
    linarith
  unfold re
  constructor <;> norm_num at A1 A2 B2 C1 C2 ⊢ <;> linarith

lemma im_bounds : (0.0007323 : ℝ) < im ∧ im < 0.0007326 := by
  obtain ⟨a1, a2⟩ := s12_bounds; obtain ⟨e1, e2⟩ := c12_bounds; obtain ⟨f1, f2⟩ := s13_bounds
  obtain ⟨g1, g2⟩ := sinδ_bounds
  have L := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' e1 a1 (by norm_num) (by norm_num))
      f1 (by norm_num) (by norm_num)) g1 (by norm_num) (by norm_num)
  have U := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' e2 a2 (by linarith) (by linarith))
      f2 (by positivity) (by linarith)) g2 (by positivity) (by linarith)
  unfold im sinδ
  constructor <;> norm_num at L U ⊢ <;> linarith

/-- `sin 2β` of the geometric matrix. -/
def sin2β : ℝ := 2 * re * im / (re ^ 2 + im ^ 2)

theorem sin2β_bounds : (0.7019 : ℝ) < sin2β ∧ sin2β < 0.7023 := by
  obtain ⟨r1, r2⟩ := re_bounds; obtain ⟨i1, i2⟩ := im_bounds
  have hd : 0 < re ^ 2 + im ^ 2 := by positivity
  unfold sin2β
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith [mul_pos (by linarith : (0:ℝ) < re) (by linarith : (0:ℝ) < im)]
  · rw [div_lt_iff₀ hd]; nlinarith [mul_pos (by linarith : (0:ℝ) < re) (by linarith : (0:ℝ) < im)]

theorem sin2β_pull : -0.75 < (sin2β - 0.710) / 0.011 ∧ (sin2β - 0.710) / 0.011 < -0.69 := by
  obtain ⟨h1, h2⟩ := sin2β_bounds
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **`sin2β` is `sin 2 arg w` for the geometric matrix.** -/
theorem sin2β_is_angle :
    let V := ckm c12 s12 c23 s23 c13 s13 ⟨Real.cos CKM.δ, Real.sin CKM.δ⟩
    Real.sin (2 * Complex.arg (-(V 1 0) * conj (V 2 0))) = sin2β := by
  intro V
  have r23 : c23^2 + s23^2 = 1 := by
    have hs := s23_bounds
    unfold c23
    rw [Real.sq_sqrt (by nlinarith)]; ring
  obtain ⟨hre, him⟩ := w_parts (c13 := c13) (θ := CKM.δ) r23
  have hw : -(V 1 0) * conj (V 2 0) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [V] at this
    rw [hre] at this
    have := re_bounds; unfold re cosδ at this; simp at *; linarith
  rw [sin_two_beta _ hw]
  simp only [V]
  rw [hre, him]
  rfl

end PMDynamics.TriangleAngles
