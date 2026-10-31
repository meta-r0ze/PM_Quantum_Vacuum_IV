import PMDynamics.CKMDressing
import PMDynamics.FlavourPulls
import PMDynamics.CPPhases

/-! The complete proposed Dirac-PMNS matrix, not only its four input numbers.
All unitarity and CP statements are conditional on the supplied angle/phase
formulas. No generation selection, neutrino mass spectrum or Dirac-only law
is obtained by inserting them in a standard parametrization. -/
noncomputable section
namespace PMDynamics.PMNS
open Matrix

/-- The three supplied squared sines, in 12, 23, 13 order. -/
def sineSquared : Fin 3 → ℝ :=
  ![1/(2*FlavourPulls.φ), (1+Real.pi/21)/2, 3/CKM.αinv]

theorem sineSquared_range (j : Fin 3) : 0<sineSquared j ∧ sineSquared j<1 := by
  have hφ : 1<FlavourPulls.φ := by
    have h:=FlavourPulls.sqrt5_b
    unfold FlavourPulls.φ
    linarith
  have hai := CKM.ai_bounds
  have hp := FlavourPulls.pi_b
  fin_cases j
  · change 0<1/(2*FlavourPulls.φ) ∧ 1/(2*FlavourPulls.φ)<1
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  · change 0<(1+Real.pi/21)/2 ∧ (1+Real.pi/21)/2<1
    constructor <;> linarith
  · change 0<3/CKM.αinv ∧ 3/CKM.αinv<1
    constructor
    · apply div_pos (by norm_num); linarith [hai.1]
    · rw [div_lt_one (by linarith [hai.1])]; linarith [hai.1]

def sine (j : Fin 3) := Real.sqrt (sineSquared j)
def cosine (j : Fin 3) := Real.sqrt (1-sineSquared j)
def delta : ℝ := 2*Real.pi/FlavourPulls.φ
def phase : ℂ := ⟨Real.cos delta, Real.sin delta⟩

theorem sine_square (j : Fin 3) : sine j ^ 2=sineSquared j :=
  Real.sq_sqrt (sineSquared_range j).1.le

theorem normalized (j : Fin 3) : cosine j ^ 2+sine j ^ 2=1 := by
  rw [cosine,Real.sq_sqrt (by linarith [(sineSquared_range j).2]),sine_square]
  ring

theorem sine_pos (j : Fin 3) : 0<sine j := Real.sqrt_pos.mpr (sineSquared_range j).1

theorem cosine_pos (j : Fin 3) : 0<cosine j := Real.sqrt_pos.mpr (by linarith [(sineSquared_range j).2])

theorem phase_unit : phase*star phase=1 := by
  apply Complex.ext
  · simpa [phase,Complex.mul_re,pow_two] using Real.cos_sq_add_sin_sq delta
  · simp [phase,Complex.mul_im]; ring

def matrix : Matrix (Fin 3) (Fin 3) ℂ :=
  CKMDressing.V (cosine 0) (sine 0) (cosine 1) (sine 1) (cosine 2) (sine 2) phase

theorem rows : matrix*matrixᴴ=1 :=
  CKMDressing.ckm_unitary_matrix (normalized 0) (normalized 1) (normalized 2) phase_unit

theorem columns : matrixᴴ*matrix=1 := mul_eq_one_comm.mp rows

theorem matrix_unitary : matrix ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := ⟨columns,rows⟩

theorem determinant : matrix.det=1 :=
  CKM.ckm_det (normalized 0) (normalized 1) (normalized 2) phase_unit

theorem jarlskog : CKM.jarlskog matrix =
    cosine 0*sine 0*cosine 1*sine 1*(cosine 2)^2*sine 2*Real.sin delta := by
  exact CKM.jarlskog_ckm phase (normalized 0)

/-- The radian phase is precisely the degree convention already used by the calculator. -/
theorem phase_degrees : delta*180/Real.pi=CPPhases.nuDeg := by
  unfold delta CPPhases.nuDeg
  change (2*Real.pi/((1+Real.sqrt 5)/2))*180/Real.pi=360/((1+Real.sqrt 5)/2)
  field_simp
  ring

theorem phase_interval : Real.pi<delta ∧ delta<2*Real.pi := by
  have hf : 1<FlavourPulls.φ ∧ FlavourPulls.φ<2 := by
    have h:=FlavourPulls.sqrt5_b
    unfold FlavourPulls.φ
    constructor <;> linarith
  unfold delta
  constructor
  · rw [lt_div_iff₀ (by linarith [hf.1])]
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by linarith [hf.1])]
    nlinarith [Real.pi_pos]

theorem jarlskog_negative : CKM.jarlskog matrix<0 := by
  have hs : Real.sin delta<0 := by
    rw [← Real.sin_sub_two_pi delta]
    apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith [phase_interval.1,phase_interval.2]
  rw [jarlskog]
  have h0:=sine_pos 0
  have h1:=sine_pos 1
  have h2:=sine_pos 2
  have h3:=cosine_pos 0
  have h4:=cosine_pos 1
  have h5:=cosine_pos 2
  exact mul_neg_of_pos_of_neg (by positivity) hs

end PMDynamics.PMNS
