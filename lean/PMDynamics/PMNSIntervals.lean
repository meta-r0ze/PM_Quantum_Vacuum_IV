import PMDynamics.PMNS
import PMDynamics.OscillationAlgebra

/-! Certified enclosures for every squared PMNS entry and its CP quartet.
The angle ansatz is supplied; the phase is the persistence sum-rule phase, and
the cross term is exactly `(c₁₂² − s₁₂² s₁₃²)(1 − 2 s₂₃²)/2` (`crossTerm_exact`). These intervals are not experimental inputs
or a proof that the proposed values minimize any physical transition cost. -/
noncomputable section
namespace PMDynamics.PMNSIntervals
open Matrix

lemma input_bounds (i : Fin 3) :
    (![0.30901,0.57479,0.0218920] : Fin 3 → ℝ) i<PMNS.sineSquared i ∧
    PMNS.sineSquared i<(![0.30902,0.57481,0.0218921] : Fin 3 → ℝ) i := by
  have hs:=FlavourPulls.sqrt5_b
  have hp:=FlavourPulls.pi_b
  have ha:=CKM.ai_bounds
  fin_cases i
  · change 0.30901<1/(2*FlavourPulls.φ) ∧ 1/(2*FlavourPulls.φ)<0.30902
    have hd : 0<2*FlavourPulls.φ := by unfold FlavourPulls.φ; positivity
    constructor
    · rw [lt_div_iff₀ hd]; unfold FlavourPulls.φ; linarith [hs.2]
    · rw [div_lt_iff₀ hd]; unfold FlavourPulls.φ; linarith [hs.1]
  · change 0.57479<(1+Real.pi/21)/2 ∧ (1+Real.pi/21)/2<0.57481
    constructor <;> linarith
  · change 0.0218920<3/CKM.αinv ∧ 3/CKM.αinv<0.0218921
    have hd : 0<CKM.αinv := by linarith [ha.1]
    constructor
    · rw [lt_div_iff₀ hd]; linarith [ha.2]
    · rw [div_lt_iff₀ hd]; linarith [ha.1]

lemma sine_bounds (i : Fin 3) :
    (![0.5558,0.7581,0.1479] : Fin 3 → ℝ) i<PMNS.sine i ∧
    PMNS.sine i<(![0.5560,0.7582,0.1480] : Fin 3 → ℝ) i := by
  fin_cases i
  · have h : 0.30901<PMNS.sineSquared 0 ∧ PMNS.sineSquared 0<0.30902 := input_bounds 0
    change 0.5558<Real.sqrt (PMNS.sineSquared 0) ∧ Real.sqrt (PMNS.sineSquared 0)<0.5560
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]
  · have h : 0.57479<PMNS.sineSquared 1 ∧ PMNS.sineSquared 1<0.57481 := input_bounds 1
    change 0.7581<Real.sqrt (PMNS.sineSquared 1) ∧ Real.sqrt (PMNS.sineSquared 1)<0.7582
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]
  · have h : 0.0218920<PMNS.sineSquared 2 ∧ PMNS.sineSquared 2<0.0218921 := input_bounds 2
    change 0.1479<Real.sqrt (PMNS.sineSquared 2) ∧ Real.sqrt (PMNS.sineSquared 2)<0.1480
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]

lemma cosine_bounds (i : Fin 3) :
    (![0.8312,0.6520,0.9889] : Fin 3 → ℝ) i<PMNS.cosine i ∧
    PMNS.cosine i<(![0.8313,0.6522,0.9891] : Fin 3 → ℝ) i := by
  fin_cases i
  · have h : 0.30901<PMNS.sineSquared 0 ∧ PMNS.sineSquared 0<0.30902 := input_bounds 0
    change 0.8312<Real.sqrt (1-PMNS.sineSquared 0) ∧ Real.sqrt (1-PMNS.sineSquared 0)<0.8313
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]
  · have h : 0.57479<PMNS.sineSquared 1 ∧ PMNS.sineSquared 1<0.57481 := input_bounds 1
    change 0.6520<Real.sqrt (1-PMNS.sineSquared 1) ∧ Real.sqrt (1-PMNS.sineSquared 1)<0.6522
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]
  · have h : 0.0218920<PMNS.sineSquared 2 ∧ PMNS.sineSquared 2<0.0218921 := input_bounds 2
    change 0.9889<Real.sqrt (1-PMNS.sineSquared 2) ∧ Real.sqrt (1-PMNS.sineSquared 2)<0.9891
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
    · rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]

/-- The product `c₁₂ s₁₂ c₂₃ s₂₃ s₁₃`. -/
def prod5 : ℝ := PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.sine 2

lemma product_bounds : 0.0337727<prod5 ∧ prod5<0.0338267 := by
  have h1:=CKM.mul_bounds (by norm_num) (by norm_num) (cosine_bounds 0) (sine_bounds 0)
  have h2:=CKM.mul_bounds (by norm_num) (by norm_num) h1 (cosine_bounds 1)
  have h3:=CKM.mul_bounds (by norm_num) (by norm_num) h2 (sine_bounds 1)
  have h4:=CKM.mul_bounds (by norm_num) (by norm_num) h3 (sine_bounds 2)
  unfold prod5
  constructor <;> norm_num at h4 ⊢ <;> linarith

/-- The sum-rule numerator `(c₁₂² − s₁₂² s₁₃²) cos 2θ₂₃`. -/
def ruleNum : ℝ :=
  ((1-PMNS.sineSquared 0)-PMNS.sineSquared 0*PMNS.sineSquared 2)*(1-2*PMNS.sineSquared 1)

lemma ruleNum_bounds : -0.102374<ruleNum ∧ ruleNum< -0.102344 := by
  have ha : 0.30901<PMNS.sineSquared 0 ∧ PMNS.sineSquared 0<0.30902 := input_bounds 0
  have hb : 0.57479<PMNS.sineSquared 1 ∧ PMNS.sineSquared 1<0.57481 := input_bounds 1
  have hc : 0.0218920<PMNS.sineSquared 2 ∧ PMNS.sineSquared 2<0.0218921 := input_bounds 2
  have hx : 0.684214<(1-PMNS.sineSquared 0)-PMNS.sineSquared 0*PMNS.sineSquared 2 ∧
      (1-PMNS.sineSquared 0)-PMNS.sineSquared 0*PMNS.sineSquared 2<0.684226 := by
    constructor <;> nlinarith [ha.1,ha.2,hc.1,hc.2]
  have hy : -0.14962<1-2*PMNS.sineSquared 1 ∧ 1-2*PMNS.sineSquared 1< -0.14958 := by
    constructor <;> linarith [hb.1,hb.2]
  unfold ruleNum
  constructor <;> nlinarith [hx.1,hx.2,hy.1,hy.2]

lemma cosDelta_eq : PMNS.cosDelta=ruleNum/(4*prod5) := rfl

lemma cosDelta_bounds : -0.758<PMNS.cosDelta ∧ PMNS.cosDelta< -0.756 := by
  have hp:=product_bounds
  have hn:=ruleNum_bounds
  have h4 : 0<4*prod5 := by linarith [hp.1]
  rw [cosDelta_eq]
  constructor
  · rw [lt_div_iff₀ h4]; nlinarith [hp.1,hp.2,hn.1]
  · rw [div_lt_iff₀ h4]; nlinarith [hp.1,hp.2,hn.2]

/-- `cos δ` is the sum-rule value. -/
theorem cos_delta : Real.cos PMNS.delta=PMNS.cosDelta := by
  have h:=cosDelta_bounds
  unfold PMNS.delta
  rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero,
    Real.cos_arccos (by linarith [h.1]) (by linarith [h.2])]

/-- `sin δ = −√(1 − cos² δ)`. -/
theorem sin_delta : Real.sin PMNS.delta= -Real.sqrt (1-PMNS.cosDelta^2) := by
  unfold PMNS.delta
  rw [Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi, zero_mul, one_mul, zero_sub,
    Real.sin_arccos]

lemma phase_parts_bounds :
    -0.758<Real.cos PMNS.delta ∧ Real.cos PMNS.delta< -0.756 ∧
    -0.655<Real.sin PMNS.delta ∧ Real.sin PMNS.delta< -0.652 := by
  have h:=cosDelta_bounds
  rw [cos_delta, sin_delta]
  have hl : 0.6522<Real.sqrt (1-PMNS.cosDelta^2) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith [h.1,h.2]
  have hu : Real.sqrt (1-PMNS.cosDelta^2)<0.6548 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith [h.1,h.2]
  exact ⟨h.1,h.2,by linarith,by linarith⟩

theorem phase_interval : Real.pi<PMNS.delta ∧ PMNS.delta<2*Real.pi := by
  have h:=cosDelta_bounds
  have h0 : 0<Real.arccos PMNS.cosDelta := Real.arccos_pos.mpr (by linarith [h.2])
  have hπ : Real.arccos PMNS.cosDelta<Real.pi := Real.arccos_lt_pi.mpr (by linarith [h.1])
  unfold PMNS.delta
  constructor <;> linarith

def crossTerm : ℝ := 2*PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.sine 2*
  Real.cos PMNS.delta

/-- **The cross term is rational in the three sines.** -/
theorem crossTerm_exact : crossTerm=ruleNum/2 := by
  have hp:=product_bounds
  have hne : prod5 ≠ 0 := by linarith [hp.1]
  have e : crossTerm=2*prod5*Real.cos PMNS.delta := by unfold crossTerm prod5; ring
  rw [e, cos_delta, cosDelta_eq]
  field_simp
  ring

lemma cross_bounds : -0.051187<crossTerm ∧ crossTerm< -0.051172 := by
  have h:=ruleNum_bounds
  rw [crossTerm_exact]
  constructor <;> linarith [h.1,h.2]

theorem jarlskog_bounds : -0.0217<CKM.jarlskog PMNS.matrix ∧ CKM.jarlskog PMNS.matrix< -0.0215 := by
  have h1:=CKM.mul_bounds (by norm_num) (by norm_num) product_bounds (cosine_bounds 2)
  have h2:=CKM.mul_bounds (by norm_num) (by norm_num) h1 (cosine_bounds 2)
  have hs : 0.652< -Real.sin PMNS.delta ∧ -Real.sin PMNS.delta<0.655 := by
    constructor <;> linarith [phase_parts_bounds.2.2.1,phase_parts_bounds.2.2.2]
  have h:=CKM.mul_bounds (by norm_num) (by norm_num) h2 hs
  norm_num at h
  rw [PMNS.jarlskog]
  have e : PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.cosine 2^2*PMNS.sine 2*
      Real.sin PMNS.delta = -(prod5*PMNS.cosine 2*PMNS.cosine 2*(-Real.sin PMNS.delta)) := by
    unfold prod5; ring
  rw [e]
  constructor <;> nlinarith only [h.1,h.2]

theorem jarlskog_negative : CKM.jarlskog PMNS.matrix<0 := by
  linarith [jarlskog_bounds.2]

/-- Generic squared CKM moduli before inserting any angle formulas. -/
def moduli (c12 s12 c23 s23 c13 s13 θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x := 2*c12*s12*c23*s23*s13*Real.cos θ
  !![c12^2*c13^2,s12^2*c13^2,s13^2;
    s12^2*c23^2+c12^2*s23^2*s13^2+x,c12^2*c23^2+s12^2*s23^2*s13^2-x,s23^2*c13^2;
    s12^2*s23^2+c12^2*c23^2*s13^2-x,c12^2*s23^2+s12^2*c23^2*s13^2+x,c23^2*c13^2]

lemma normSq_ckm (c12 s12 c23 s23 c13 s13 θ : ℝ) (i j : Fin 3) :
    Complex.normSq (CKM.ckm c12 s12 c23 s23 c13 s13 ⟨Real.cos θ,Real.sin θ⟩ i j)=
      moduli c12 s12 c23 s23 c13 s13 θ i j := by
  have h:=Real.cos_sq_add_sin_sq θ
  fin_cases i <;> fin_cases j <;>
    simp [CKM.ckm,moduli,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  all_goals first
    | ring1
    | linear_combination s13^2*h
    | linear_combination (c12*s23*s13)^2*h
    | linear_combination (s12*s23*s13)^2*h
    | linear_combination (c12*c23*s13)^2*h
    | linear_combination (s12*c23*s13)^2*h

def expected : Matrix (Fin 3) (Fin 3) ℝ :=
  let a:=PMNS.sineSquared 0
  let b:=PMNS.sineSquared 1
  let c:=PMNS.sineSquared 2
  !![(1-a)*(1-c),a*(1-c),c;
    a*(1-b)+(1-a)*b*c+crossTerm,(1-a)*(1-b)+a*b*c-crossTerm,b*(1-c);
    a*b+(1-a)*(1-b)*c-crossTerm,(1-a)*b+a*(1-b)*c+crossTerm,(1-b)*(1-c)]

lemma normSq_expected (i j : Fin 3) : Complex.normSq (PMNS.matrix i j)=expected i j := by
  have hc (k : Fin 3) : PMNS.cosine k^2=1-PMNS.sineSquared k := by
    unfold PMNS.cosine
    exact Real.sq_sqrt (by linarith [(PMNS.sineSquared_range k).2])
  have he := normSq_ckm (PMNS.cosine 0) (PMNS.sine 0) (PMNS.cosine 1) (PMNS.sine 1)
    (PMNS.cosine 2) (PMNS.sine 2) PMNS.delta i j
  apply he.trans
  fin_cases i <;> fin_cases j <;>
    simp [moduli,expected,crossTerm,PMNS.sine_square,hc]

/-- Conservative outward rational enclosures; no measured entry is used. -/
def lower : Matrix (Fin 3) (Fin 3) ℝ := !![0.6758,0.3022,0.0218;
    0.0888,0.3488,0.5622;
    0.2352,0.3488,0.4158]
def upper : Matrix (Fin 3) (Fin 3) ℝ := !![0.6759,0.3023,0.0219;
    0.0890,0.3490,0.5623;
    0.2353,0.3490,0.4160]

theorem squared_entry_bounds (i j : Fin 3) :
    lower i j<Complex.normSq (PMNS.matrix i j) ∧ Complex.normSq (PMNS.matrix i j)<upper i j := by
  let a:=PMNS.sineSquared 0
  let b:=PMNS.sineSquared 1
  let c:=PMNS.sineSquared 2
  have ha : 0.30901<a ∧ a<0.30902 := input_bounds 0
  have hb : 0.57479<b ∧ b<0.57481 := input_bounds 1
  have hc : 0.0218920<c ∧ c<0.0218921 := input_bounds 2
  have hna : 0.69098<1-a ∧ 1-a<0.69099 := by constructor <;> linarith [ha.1,ha.2]
  have hnb : 0.42519<1-b ∧ 1-b<0.42521 := by constructor <;> linarith [hb.1,hb.2]
  have hnc : 0.9781079<1-c ∧ 1-c<0.9781080 := by constructor <;> linarith [hc.1,hc.2]
  have hp00:=CKM.mul_bounds (by norm_num) (by norm_num) hna hnc
  have hp01:=CKM.mul_bounds (by norm_num) (by norm_num) ha hnc
  have hp10a:=CKM.mul_bounds (by norm_num) (by norm_num) ha hnb
  have hp10tmp:=CKM.mul_bounds (by norm_num) (by norm_num) hna hb
  have hp10b:=CKM.mul_bounds (by norm_num) (by norm_num) hp10tmp hc
  have hp11a:=CKM.mul_bounds (by norm_num) (by norm_num) hna hnb
  have hp11tmp:=CKM.mul_bounds (by norm_num) (by norm_num) ha hb
  have hp11b:=CKM.mul_bounds (by norm_num) (by norm_num) hp11tmp hc
  have hp12:=CKM.mul_bounds (by norm_num) (by norm_num) hb hnc
  have hp20a:=CKM.mul_bounds (by norm_num) (by norm_num) ha hb
  have hp20tmp:=CKM.mul_bounds (by norm_num) (by norm_num) hna hnb
  have hp20b:=CKM.mul_bounds (by norm_num) (by norm_num) hp20tmp hc
  have hp21a:=CKM.mul_bounds (by norm_num) (by norm_num) hna hb
  have hp21tmp:=CKM.mul_bounds (by norm_num) (by norm_num) ha hnb
  have hp21b:=CKM.mul_bounds (by norm_num) (by norm_num) hp21tmp hc
  have hp22:=CKM.mul_bounds (by norm_num) (by norm_num) hnb hnc
  have hx:=cross_bounds
  rw [normSq_expected i j]
  fin_cases i <;> fin_cases j
  · change 0.6758<(1-a)*(1-c) ∧ (1-a)*(1-c)<0.6759
    constructor <;> linarith only [hp00]
  · change 0.3022<a*(1-c) ∧ a*(1-c)<0.3023
    constructor <;> linarith only [hp01]
  · change 0.0218<c ∧ c<0.0219
    constructor <;> linarith only [hc]
  · change 0.0888<a*(1-b)+(1-a)*b*c+crossTerm ∧ a*(1-b)+(1-a)*b*c+crossTerm<0.0890
    constructor <;> linarith only [hp10a.1,hp10a.2,hp10b.1,hp10b.2,hx.1,hx.2]
  · change 0.3488<(1-a)*(1-b)+a*b*c-crossTerm ∧ (1-a)*(1-b)+a*b*c-crossTerm<0.3490
    constructor <;> linarith only [hp11a.1,hp11a.2,hp11b.1,hp11b.2,hx.1,hx.2]
  · change 0.5622<b*(1-c) ∧ b*(1-c)<0.5623
    constructor <;> linarith only [hp12]
  · change 0.2352<a*b+(1-a)*(1-b)*c-crossTerm ∧ a*b+(1-a)*(1-b)*c-crossTerm<0.2353
    constructor <;> linarith only [hp20a.1,hp20a.2,hp20b.1,hp20b.2,hx.1,hx.2]
  · change 0.3488<(1-a)*b+a*(1-b)*c+crossTerm ∧ (1-a)*b+a*(1-b)*c+crossTerm<0.3490
    constructor <;> linarith only [hp21a.1,hp21a.2,hp21b.1,hp21b.2,hx.1,hx.2]
  · change 0.4158<(1-b)*(1-c) ∧ (1-b)*(1-c)<0.4160
    constructor <;> linarith only [hp22]

end PMDynamics.PMNSIntervals
