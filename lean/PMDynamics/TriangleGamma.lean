import PMDynamics.TriangleAngles
import PMDynamics.CPPhases

/-! The actual rephasing-invariant CKM triangle gamma, rather than the
parametrization phase delta used as a proxy. All angle formulas remain inputs.
No new premise from Papers I–III is needed. -/
noncomputable section
namespace PMDynamics.TriangleGamma
open Complex ComplexConjugate PMDynamics.CKM

/-- A positive real multiple of -Vud Vub* / (Vcd Vcb*), when its denominator
is nonzero. Using the quartet avoids unnecessary division in the definition. -/
def invariant (V : Fin 3 → Fin 3 → ℂ) : ℂ :=
  -(V 0 0*conj (V 0 2))*conj (V 1 0*conj (V 1 2))

def gamma (V : Fin 3 → Fin 3 → ℂ) : ℝ := Complex.arg (invariant V)

theorem ratio_arg (z w : ℂ) (hw : w ≠ 0) :
    Complex.arg (z/w)=Complex.arg (z*conj w) := by
  have he : z/w=(1/Complex.normSq w : ℝ)*(z*conj w) := by
    apply Complex.ext <;> simp [Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im] <;> ring
  rw [he,Complex.arg_real_mul _ (one_div_pos.mpr (Complex.normSq_pos.mpr hw))]

/-- Agreement with the usual ratio definition on its physical domain. -/
theorem gamma_is_ratio (V : Fin 3 → Fin 3 → ℂ)
    (h : V 1 0*conj (V 1 2) ≠ 0) :
    gamma V=Complex.arg (-(V 0 0*conj (V 0 2))/(V 1 0*conj (V 1 2))) := by
  exact (ratio_arg _ _ h).symm

/-- The quartet, and therefore its argument, is invariant under independent
unit phases on mass and flavour labels. No unitarity assumption is needed. -/
theorem invariant_rephasing (V : Fin 3 → Fin 3 → ℂ) (r c : Fin 3 → ℂ)
    (hr : ∀ i, r i*conj (r i)=1) (hc : ∀ i, c i*conj (c i)=1) :
    invariant (fun i j => r i*V i j*conj (c j))=invariant V := by
  calc
    _ = (r 0*conj (r 0))*(r 1*conj (r 1))*(c 0*conj (c 0))*(c 2*conj (c 2))*
        invariant V := by
      simp only [invariant,map_mul,Complex.conj_conj]
      ring
    _ = _ := by rw [hr 0,hr 1,hc 0,hc 2]; simp

theorem gamma_rephasing (V : Fin 3 → Fin 3 → ℂ) (r c : Fin 3 → ℂ)
    (hr : ∀ i, r i*conj (r i)=1) (hc : ∀ i, c i*conj (c i)=1) :
    gamma (fun i j => r i*V i j*conj (c j))=gamma V :=
  congrArg Complex.arg (invariant_rephasing V r c hr hc)

/-- No trigonometric angle normalization is needed for this factorization. -/
theorem invariant_factor (c12 s12 c23 s23 c13 s13 : ℝ) (u : ℂ) (hu : u*conj u=1) :
    invariant (ckm c12 s12 c23 s23 c13 s13 u) =
      ((c12*s13*s23*c13^2 : ℝ) : ℂ)*
        (((s12*c23 : ℝ) : ℂ)*u+((c12*s23*s13 : ℝ) : ℂ)) := by
  have he : invariant (ckm c12 s12 c23 s23 c13 s13 u) =
      ((c12*s13*s23*c13^2 : ℝ) : ℂ)*
        (((s12*c23 : ℝ) : ℂ)*u+((c12*s23*s13 : ℝ) : ℂ)*(u*conj u)) := by
    simp [invariant, ckm]
    ring
  rw [he,hu,mul_one]

def u : ℂ := ⟨Real.cos CKM.δ,Real.sin CKM.δ⟩
def matrix := ckm c12 s12 c23 s23 c13 s13 u
def direction : ℂ := ((s12*c23 : ℝ) : ℂ)*u+((c12*s23*s13 : ℝ) : ℂ)
def value : ℝ := gamma matrix

lemma positive_inputs : 0<s12 ∧ 0<c23 ∧ 0<c12 ∧ 0<s23 ∧ 0<s13 ∧
    0<c13 ∧ 0<Real.cos CKM.δ ∧ 0<Real.sin CKM.δ := by
  have hc:=TriangleAngles.cosδ_bounds
  unfold TriangleAngles.cosδ at hc
  exact ⟨by linarith [s12_bounds.1], by linarith [c23_bounds.1],
    by linarith [c12_bounds.1], by linarith [s23_bounds.1], by linarith [s13_bounds.1],
    by linarith [c13_bounds.1], by linarith [hc.1], by linarith [sinδ_bounds.1]⟩

lemma factor_positive : 0<c12*s13*s23*c13^2 := by
  obtain ⟨_,_,h1,h2,h3,h4,_,_⟩ := positive_inputs
  positivity

theorem from_direction : value=Complex.arg direction := by
  have hu : u*conj u=1 := by
    apply Complex.ext
    · simpa [u,Complex.mul_re,pow_two] using Real.cos_sq_add_sin_sq CKM.δ
    · simp [u,Complex.mul_im]; ring
  rw [value,gamma,matrix,invariant_factor _ _ _ _ _ _ _ hu]
  exact Complex.arg_real_mul _ factor_positive

lemma direction_parts : direction.re=s12*c23*Real.cos CKM.δ+c12*s23*s13 ∧
    direction.im=s12*c23*Real.sin CKM.δ := by
  simp [direction,u]

lemma direction_positive : 0<direction.re ∧ 0<direction.im := by
  obtain ⟨h1,h2,h3,h4,h5,_,hc,hs⟩ := positive_inputs
  rw [direction_parts.1,direction_parts.2]
  constructor <;> positivity

/-- Argument in the right half-plane, with branch choice checked. -/
theorem arg_arctan (z : ℂ) (hz : 0<z.re) : Complex.arg z=Real.arctan (z.im/z.re) := by
  have hi := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  exact (Real.arctan_eq_of_tan_eq (Complex.tan_arg z) hi).symm

theorem gamma_arctan : value=Real.arctan (direction.im/direction.re) := by
  rw [from_direction,arg_arctan direction direction_positive.1]

/-- The correction to delta has a definite sign; gamma and delta are unequal. -/
theorem gamma_lt_delta : value<CKM.δ := by
  rw [gamma_arctan]
  change Real.arctan _ < Real.arctan (5/2)
  apply Real.arctan_strictMono
  apply (div_lt_iff₀ direction_positive.1).mpr
  obtain ⟨h1,h2,h3,h4,h5,_,hc,_⟩ := positive_inputs
  have ht : Real.sin CKM.δ/Real.cos CKM.δ=5/2 := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan (5/2 : ℝ)
  have hsin := (div_eq_iff hc.ne').mp ht
  rw [direction_parts.1,direction_parts.2,hsin]
  have hp : 0<c12*s23*s13 := by positivity
  nlinarith

/-- Inverse tangent slope, enclosed without substituting floating-point values. -/
theorem inverse_slope_bounds :
    0.40069 < direction.re/direction.im ∧ direction.re/direction.im < 0.40071 := by
  have hB := mul_bounds (by norm_num) (by norm_num)
    (mul_bounds (by norm_num) (by norm_num) c12_bounds s23_bounds) s13_bounds
  have hD := mul_bounds (by norm_num) (by norm_num)
    (mul_bounds (by norm_num) (by norm_num) s12_bounds c23_bounds) sinδ_bounds
  obtain ⟨_,_,_,_,_,_,hc,_⟩ := positive_inputs
  have ht : Real.sin CKM.δ/Real.cos CKM.δ=5/2 := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan (5/2 : ℝ)
  have hcos : Real.cos CKM.δ=(2/5)*Real.sin CKM.δ := by
    have hs := (div_eq_iff hc.ne').mp ht
    linarith
  have hre : direction.re=(2/5)*direction.im+c12*s23*s13 := by
    rw [direction_parts.1,direction_parts.2,hcos]
    ring
  have hd :
      0.2243994*0.999146*0.928476 < direction.im ∧
      direction.im < 0.2243995*0.999147*0.928477 := by
    simpa only [direction_parts.2] using hD
  constructor
  · apply (lt_div_iff₀ direction_positive.2).mpr
    rw [hre]
    nlinarith [hB.1,hB.2,hd.1,hd.2]
  · apply (div_lt_iff₀ direction_positive.2).mpr
    rw [hre]
    nlinarith [hB.1,hB.2,hd.1,hd.2]

theorem complementary_arctan :
    value=Real.pi/2-Real.arctan (direction.re/direction.im) := by
  rw [gamma_arctan,show direction.im/direction.re=(direction.re/direction.im)⁻¹ by
    rw [inv_div],Real.arctan_inv_of_pos (div_pos direction_positive.1 direction_positive.2)]

/-- A certified angle window for the actual matrix triangle. -/
theorem gamma_degrees :
    68.16 < value*180/Real.pi ∧ value*180/Real.pi < 68.17 := by
  have hL := CPPhases.arctan_lower 0.40069 (by norm_num)
  have hU := CPPhases.arctan_upper 0.40071 (by norm_num)
  have h1 := Real.arctan_strictMono inverse_slope_bounds.1
  have h2 := Real.arctan_strictMono inverse_slope_bounds.2
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [complementary_arctan]
  constructor
  · apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith
  · apply (div_lt_iff₀ Real.pi_pos).mpr
    linarith

/-- The proxy delta differs by a small, nonzero amount in this ansatz. -/
theorem delta_minus_gamma_degrees :
    0.028 < CPPhases.δdeg-value*180/Real.pi ∧
    CPPhases.δdeg-value*180/Real.pi < 0.041 := by
  have h1 := CPPhases.δ_degrees
  have h2 := gamma_degrees
  constructor <;> linarith

/-- The concrete ratio denominator is nonzero, certified by the same matrix
angle window. Thus the quartet definition is the actual ratio angle here. -/
theorem value_is_ratio : value=
    Complex.arg (-(matrix 0 0*conj (matrix 0 2))/(matrix 1 0*conj (matrix 1 2))) := by
  apply gamma_is_ratio matrix
  intro h
  have hz : value=0 := by simp [value,gamma,invariant,h]
  have hg := gamma_degrees.1
  rw [hz] at hg
  norm_num at hg

/-- Fixed benchmark already used in CPPhases; this is the actual gamma pull,
not the proxy delta pull. No new experimental input or likelihood is introduced. -/
theorem gamma_pull :
    1.27 < (value*180/Real.pi-64.6)/2.8 ∧
    (value*180/Real.pi-64.6)/2.8 < 1.28 := by
  have h := gamma_degrees
  constructor
  · apply (lt_div_iff₀ (by norm_num : 0<(2.8 : ℝ))).mpr
    linarith [h.1]
  · apply (div_lt_iff₀ (by norm_num : 0<(2.8 : ℝ))).mpr
    linarith [h.2]

end PMDynamics.TriangleGamma
