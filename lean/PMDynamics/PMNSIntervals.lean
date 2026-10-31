import PMDynamics.PMNS
import PMDynamics.OscillationAlgebra

/-! Certified enclosures for every squared PMNS entry and its CP quartet.
The angle/phase ansatz is supplied. These intervals are not experimental inputs
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

lemma delta_exact : PMNS.delta=Real.pi*(Real.sqrt 5-1) := by
  have hs : Real.sqrt 5^2=5 := Real.sq_sqrt (by norm_num)
  unfold PMNS.delta FlavourPulls.φ
  rw [div_div_eq_mul_div]
  apply (div_eq_iff (show 1+Real.sqrt 5 ≠ 0 by positivity)).mpr
  linear_combination (-Real.pi)*hs

lemma half_angle_sine_window (x : ℝ) (hx : 0.3708<x ∧ x<0.3709) :
    0.3622<Real.sin x ∧ Real.sin x<0.3625 := by
  have hx0 : 0<x := by linarith [hx.1]
  have hsin:=Real.sin_bound (show |x|≤1 by rw [abs_of_pos hx0]; linarith [hx.2])
  rw [abs_of_pos hx0] at hsin
  have hh:=abs_le.mp hsin
  have h3l:=pow_lt_pow_left₀ hx.1 (by norm_num) (by decide : (3:ℕ)≠0)
  have h3u:=pow_lt_pow_left₀ hx.2 hx0.le (by decide : (3:ℕ)≠0)
  have h5u:=pow_lt_pow_left₀ hx.2 hx0.le (by decide : (5:ℕ)≠0)
  constructor <;> nlinarith only [hx.1,hx.2,hh.1,hh.2,h3l,h3u,h5u]

set_option maxHeartbeats 2000000 in
lemma phase_parts_bounds :
    -0.738<Real.cos PMNS.delta ∧ Real.cos PMNS.delta< -0.737 ∧
    -0.676<Real.sin PMNS.delta ∧ Real.sin PMNS.delta< -0.674 := by
  let x := (PMNS.delta-Real.pi)/2
  have hp:=FlavourPulls.pi_b
  have hs:=FlavourPulls.sqrt5_b
  have hr : 0.2360679<Real.sqrt 5-2 ∧ Real.sqrt 5-2<0.2360680 := by
    constructor <;> linarith
  have hpr:=CKM.mul_bounds (by norm_num) (by norm_num) hp hr
  have hx : 0.3708<x ∧ x<0.3709 := by
    dsimp [x]; rw [delta_exact]
    constructor <;> nlinarith only [hpr.1,hpr.2]
  have hsb := half_angle_sine_window x hx
  have hce : Real.cos PMNS.delta=2*Real.sin x^2-1 := by
    rw [show PMNS.delta=Real.pi+2*x by dsimp [x]; ring,Real.cos_add,Real.cos_two_mul]
    simp only [Real.cos_pi,Real.sin_pi,neg_mul,one_mul,zero_mul,sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hsl:=pow_lt_pow_left₀ hsb.1 (by norm_num) (by decide : (2:ℕ)≠0)
  have hsu:=pow_lt_pow_left₀ hsb.2 (by linarith [hsb.1]) (by decide : (2:ℕ)≠0)
  have hc : -0.738<Real.cos PMNS.delta ∧ Real.cos PMNS.delta< -0.737 := by
    constructor <;> nlinarith only [hce,hsl,hsu]
  have hneg : Real.sin PMNS.delta<0 := by
    rw [← Real.sin_sub_two_pi PMNS.delta]
    apply Real.sin_neg_of_neg_of_neg_pi_lt <;>
      linarith [PMNS.phase_interval.1,PMNS.phase_interval.2]
  have hcl:=pow_lt_pow_left₀ (show (0.737:ℝ)< -Real.cos PMNS.delta by linarith [hc.2])
    (by norm_num) (by decide : (2:ℕ)≠0)
  have hcu:=pow_lt_pow_left₀ (show -Real.cos PMNS.delta<(0.738:ℝ) by linarith [hc.1])
    (by linarith [hc.2]) (by decide : (2:ℕ)≠0)
  refine ⟨hc.1,hc.2,?_,?_⟩ <;>
    nlinarith only [hcl,hcu,hneg,Real.sin_sq_add_cos_sq PMNS.delta]

def crossTerm : ℝ := 2*PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.sine 2*
  Real.cos PMNS.delta

lemma product_bounds :
    0.0337727<PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.sine 2 ∧
    PMNS.cosine 0*PMNS.sine 0*PMNS.cosine 1*PMNS.sine 1*PMNS.sine 2<0.0338267 := by
  have h1:=CKM.mul_bounds (by norm_num) (by norm_num) (cosine_bounds 0) (sine_bounds 0)
  have h2:=CKM.mul_bounds (by norm_num) (by norm_num) h1 (cosine_bounds 1)
  have h3:=CKM.mul_bounds (by norm_num) (by norm_num) h2 (sine_bounds 1)
  have h4:=CKM.mul_bounds (by norm_num) (by norm_num) h3 (sine_bounds 2)
  constructor <;> norm_num at h4 ⊢ <;> linarith

lemma cross_bounds : -0.0500<crossTerm ∧ crossTerm< -0.0497 := by
  have hp:=product_bounds
  have hc : 0.737< -Real.cos PMNS.delta ∧ -Real.cos PMNS.delta<0.738 := by
    constructor <;> linarith [phase_parts_bounds.1,phase_parts_bounds.2.1]
  have h:=CKM.mul_bounds (by norm_num) (by norm_num) hp hc
  unfold crossTerm
  constructor <;> nlinarith only [h.1,h.2]

theorem jarlskog_bounds : -0.0224<CKM.jarlskog PMNS.matrix ∧ CKM.jarlskog PMNS.matrix< -0.0222 := by
  have h1:=CKM.mul_bounds (by norm_num) (by norm_num) product_bounds (cosine_bounds 2)
  have h2:=CKM.mul_bounds (by norm_num) (by norm_num) h1 (cosine_bounds 2)
  have hs : 0.674< -Real.sin PMNS.delta ∧ -Real.sin PMNS.delta<0.676 := by
    constructor <;> linarith [phase_parts_bounds.2.2.1,phase_parts_bounds.2.2.2]
  have h:=CKM.mul_bounds (by norm_num) (by norm_num) h2 hs
  norm_num at h
  rw [PMNS.jarlskog]
  constructor <;> nlinarith only [h.1,h.2]

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
    0.0900,0.3473,0.5622;
    0.2337,0.3500,0.4158]
def upper : Matrix (Fin 3) (Fin 3) ℝ := !![0.6759,0.3023,0.0219;
    0.0904,0.3478,0.5623;
    0.2341,0.3504,0.4160]

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
  · change 0.0900<a*(1-b)+(1-a)*b*c+crossTerm ∧ a*(1-b)+(1-a)*b*c+crossTerm<0.0904
    constructor <;> linarith only [hp10a.1,hp10a.2,hp10b.1,hp10b.2,hx.1,hx.2]
  · change 0.3473<(1-a)*(1-b)+a*b*c-crossTerm ∧ (1-a)*(1-b)+a*b*c-crossTerm<0.3478
    constructor <;> linarith only [hp11a.1,hp11a.2,hp11b.1,hp11b.2,hx.1,hx.2]
  · change 0.5622<b*(1-c) ∧ b*(1-c)<0.5623
    constructor <;> linarith only [hp12]
  · change 0.2337<a*b+(1-a)*(1-b)*c-crossTerm ∧ a*b+(1-a)*(1-b)*c-crossTerm<0.2341
    constructor <;> linarith only [hp20a.1,hp20a.2,hp20b.1,hp20b.2,hx.1,hx.2]
  · change 0.3500<(1-a)*b+a*(1-b)*c+crossTerm ∧ (1-a)*b+a*(1-b)*c+crossTerm<0.3504
    constructor <;> linarith only [hp21a.1,hp21a.2,hp21b.1,hp21b.2,hx.1,hx.2]
  · change 0.4158<(1-b)*(1-c) ∧ (1-b)*(1-c)<0.4160
    constructor <;> linarith only [hp22]

end PMDynamics.PMNSIntervals
