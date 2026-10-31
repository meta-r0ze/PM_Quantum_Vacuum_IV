import PMDynamics.CKMDressing
import PMDynamics.FlavourPulls
import PMDynamics.CPPhases

/-! The complete proposed Dirac-PMNS matrix, not only its four input numbers.
The three angles are supplied formulas. The phase is not: it is fixed by the
persistence sum rule `|U_μ2| = |U_τ2|` (`ReferenceFlavour`), on the `sin δ < 0`
branch. All unitarity and CP statements are conditional on the angle formulas. No generation selection, neutrino mass spectrum or Dirac-only law
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
/-- The persistence sum rule (`ReferenceFlavour`): `|U_μ2| = |U_τ2|` fixes
`cos δ = (c₁₂² − s₁₂² s₁₃²) cos 2θ₂₃ / (s₁₃ sin 2θ₁₂ sin 2θ₂₃)`, written here with
`cos 2θ₂₃ = 1 − 2 s₂₃²` and `sin 2θ = 2 s c`. -/
def cosDelta : ℝ :=
  ((1-sineSquared 0)-sineSquared 0*sineSquared 2)*(1-2*sineSquared 1)/
    (4*(cosine 0*sine 0*cosine 1*sine 1*sine 2))

/-- The branch with `sin δ < 0`. The rule fixes `cos δ` only. -/
def delta : ℝ := 2*Real.pi-Real.arccos cosDelta
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

end PMDynamics.PMNS
