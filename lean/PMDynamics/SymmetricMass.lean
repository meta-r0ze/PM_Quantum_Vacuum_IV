import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Independent matrix algebra: Hermitian and complex-symmetric mass
constructions can have the same squared propagation matrix for every unitary
mixing basis. This supplies no fermionic statistics or physical mass-term law;
oscillation algebra alone cannot exclude the symmetric construction. -/
noncomputable section
namespace PMDynamics.SymmetricMass
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real spectral values as a complex diagonal matrix. -/
def spectrum (m : n → ℝ) : Matrix n n ℂ := diagonal (fun i => (m i : ℂ))

def symmetricMass (U : Matrix n n ℂ) (m : n → ℝ) := U*spectrum m*Uᵀ
def hermitianMass (U : Matrix n n ℂ) (m : n → ℝ) := U*spectrum m*Uᴴ

/-- Transpose symmetry, not Hermiticity, is the relevant algebraic distinction. -/
theorem mass_symmetric (U : Matrix n n ℂ) (m : n → ℝ) :
    (symmetricMass U m)ᵀ=symmetricMass U m := by
  simp [symmetricMass,spectrum,transpose_mul,Matrix.mul_assoc]

omit [Fintype n] in
lemma spectrum_adjoint (m : n → ℝ) : (spectrum m)ᴴ=spectrum m := by
  simp [spectrum,diagonal_conjTranspose]

lemma spectrum_squared (m : n → ℝ) : spectrum m*spectrum m=spectrum (fun i => m i^2) := by
  simp [spectrum,diagonal_mul_diagonal,pow_two]

/-- Entrywise conjugate U is `(Uᵀ)ᴴ`; transpose isometry follows from U†U=I. -/
lemma transpose_isometry (U : Matrix n n ℂ) (hU : Uᴴ*U=1) : Uᵀ*(Uᵀ)ᴴ=1 := by
  have h := congrArg Matrix.transpose hU
  simpa only [transpose_mul,transpose_one,
    ← conjTranspose_transpose_eq_transpose_conjTranspose] using h

/-- The supplied U gives the diagonal congruence of the symmetric construction. -/
theorem diagonal_congruence (U : Matrix n n ℂ) (m : n → ℝ) (hU : Uᴴ*U=1) :
    Uᴴ*symmetricMass U m*(Uᵀ)ᴴ=spectrum m := by
  unfold symmetricMass
  calc
    _ = (Uᴴ*U)*spectrum m*(Uᵀ*(Uᵀ)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU,transpose_isometry U hU,one_mul,mul_one]

/-- Squared propagation sees the same U and m² as the Hermitian construction. -/
theorem symmetric_squared (U : Matrix n n ℂ) (m : n → ℝ) (hU : Uᴴ*U=1) :
    symmetricMass U m*(symmetricMass U m)ᴴ=U*spectrum (fun i => m i^2)*Uᴴ := by
  simp only [symmetricMass,conjTranspose_mul,spectrum_adjoint]
  calc
    _ = U*spectrum m*(Uᵀ*(Uᵀ)ᴴ)*spectrum m*Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [transpose_isometry U hU,mul_one]
      simp only [Matrix.mul_assoc,← spectrum_squared]

theorem hermitian_squared (U : Matrix n n ℂ) (m : n → ℝ) (hU : Uᴴ*U=1) :
    hermitianMass U m*hermitianMass U m=U*spectrum (fun i => m i^2)*Uᴴ := by
  unfold hermitianMass
  calc
    _ = U*spectrum m*(Uᴴ*U)*spectrum m*Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hU,mul_one]
      simp only [Matrix.mul_assoc,← spectrum_squared]

/-- Every supplied orthonormal mixing basis admits both forms with the same
squared propagation matrix. This is not a claim that the mass terms are physically
identical or that processes other than propagation cannot distinguish them. -/
theorem same_squared_propagation (U : Matrix n n ℂ) (m : n → ℝ) (hU : Uᴴ*U=1) :
    symmetricMass U m*(symmetricMass U m)ᴴ=hermitianMass U m*hermitianMass U m := by
  rw [symmetric_squared U m hU,hermitian_squared U m hU]

end PMDynamics.SymmetricMass
