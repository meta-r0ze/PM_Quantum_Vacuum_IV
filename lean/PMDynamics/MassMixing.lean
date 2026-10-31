import PMDynamics.FlavourCurrent
import PMNested.HermitianMass
import PMAction.WallExchange
import Mathlib.Analysis.Matrix.PosDef

/-! What the upstream Hermitian-mass results imply, and what they leave free.
Every unitary mixing can be realized with fixed positive mass eigenvalues and
Hermitian links. Thus these conditions and vanishing mass-determinant phase
alone do not select mixing angles. The construction is not a physical link law. -/
noncomputable section
namespace PMDynamics.MassMixing
open Matrix
open scoped ComplexOrder
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def eigenMass (m : Fin 3 → ℝ) : M := diagonal (fun i => (m i : ℂ))
def mass (U : M) (m : Fin 3 → ℝ) : M := U * eigenMass m * Uᴴ

lemma eigenMass_hermitian (m : Fin 3 → ℝ) : (eigenMass m).IsHermitian := by
  simp [eigenMass, IsHermitian, diagonal_conjTranspose]

theorem mass_hermitian (U : M) (m : Fin 3 → ℝ) : (mass U m).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose U (eigenMass_hermitian m)

theorem mass_posDef (U : M) (m : Fin 3 → ℝ) (hU : U*Uᴴ=1)
    (hm : ∀ i, 0<m i) : (mass U m).PosDef := by
  let u : unitary M := ⟨U,mul_eq_one_comm.mp hU,hU⟩
  have hi : IsUnit U := Unitary.isUnit_coe (U := u)
  have hd : (eigenMass m).PosDef := Matrix.PosDef.diagonal (fun i => (RCLike.ofReal_pos (K := ℂ)).2 (hm i))
  exact hi.posDef_star_right_conjugate_iff.mpr hd

/-- The supplied wall-parity symmetry holds for every constructed Hermitian
link, including arbitrary mixing eigenbases. It does not resolve that freedom. -/
theorem mass_wall_parity (U : M) (m : Fin 3 → ℝ) (k : Fin 3 → ℝ) (δ : ℝ) :
    PMAction.WallExchange.P * PMAction.WallExchange.H k δ (mass U m) * PMAction.WallExchange.P =
      PMAction.WallExchange.H (-k) δ (mass U m) :=
  (PMAction.WallExchange.exchange_symmetry_iff k δ (mass U m)).mpr (mass_hermitian U m).eq

/-- The prescribed complete unitary basis really diagonalizes the mass. -/
theorem diagonalizes (U : M) (m : Fin 3 → ℝ) (hU : U*Uᴴ=1) :
    mass U m * U = U * eigenMass m := by
  have hU' : Uᴴ*U=1 := mul_eq_one_comm.mp hU
  simp [mass, Matrix.mul_assoc, hU']

theorem eigenvector (U : M) (m : Fin 3 → ℝ) (hU : U*Uᴴ=1) (i : Fin 3) :
    mass U m *ᵥ (U *ᵥ Pi.single i 1) = (m i : ℂ) • (U *ᵥ Pi.single i 1) := by
  rw [mulVec_mulVec, diagonalizes U m hU, ← mulVec_mulVec]
  have he : eigenMass m *ᵥ Pi.single i 1 = (m i : ℂ) • Pi.single i 1 := by
    ext j
    by_cases hj : j=i
    · subst j; simp [eigenMass,mulVec_diagonal]
    · simp [eigenMass,mulVec_diagonal,hj]
  rw [he, mulVec_smul]

/-- A complex phase in det U cancels under Hermitian conjugation. It is not
necessary to impose det(mixing)=1 to keep these mass determinants positive. -/
theorem determinant (U : M) (m : Fin 3 → ℝ) (hU : U*Uᴴ=1) :
    (mass U m).det = ((∏ i, m i : ℝ) : ℂ) := by
  have hd := congrArg Matrix.det hU
  rw [det_mul, det_one] at hd
  simp only [mass, det_mul]
  calc
    _ = (U.det * Uᴴ.det) * (eigenMass m).det := by ring
    _ = _ := by rw [hd]; simp [eigenMass, det_diagonal]

theorem determinant_phase (U : M) (m : Fin 3 → ℝ) (hU : U*Uᴴ=1)
    (hm : ∀ i, 0<m i) : ((mass U m).det).arg=0 := by
  rw [determinant U m hU]
  exact Complex.arg_ofReal_of_nonneg (Finset.prod_pos (fun i _ => hm i)).le

/-- The exact upstream strong-CP combination for these constructed positive
mass links, with arbitrary complete unitary eigenbases. -/
theorem thetaBar (Uu Ud : M) (mu md : Fin 3 → ℝ) (hu : Uu*Uuᴴ=1) (hd : Ud*Udᴴ=1)
    (hmu : ∀ i, 0<mu i) (hmd : ∀ i, 0<md i) (θ : ℝ) :
    PMNested.HermitianMass.thetaBar θ (mass Uu mu) (mass Ud md) = θ := by
  unfold PMNested.HermitianMass.thetaBar
  rw [determinant Uu mu hu, determinant Ud md hd, ← Complex.ofReal_mul,
    Complex.arg_ofReal_of_nonneg (mul_pos (Finset.prod_pos (fun i _ => hmu i))
      (Finset.prod_pos (fun i _ => hmd i))).le, sub_zero]

/-- With fixed masses, every unitary V can be the mixing matrix: choose the
up basis I and the down basis V. Hermiticity/conservation do not choose V. -/
theorem arbitrary_mixing (V : M) (hV : V*Vᴴ=1) (mu md : Fin 3 → ℝ) :
    ∃ Uu Ud : M, Uu*Uuᴴ=1 ∧ Ud*Udᴴ=1 ∧ FlavourCurrent.mixing Uu Ud=V ∧
      mass Uu mu * Uu = Uu * eigenMass mu ∧ mass Ud md * Ud = Ud * eigenMass md ∧
      (mass Uu mu).IsHermitian ∧ (mass Ud md).IsHermitian := by
  refine ⟨1,V,by simp,hV,?_,diagonalizes 1 mu (by simp),diagonalizes V md hV,
    mass_hermitian 1 mu,mass_hermitian V md⟩
  simp [FlavourCurrent.mixing]

/-- Even positive masses and zero mass-determinant phase allow every unitary
mixing, with the mass spectra held fixed independently of that mixing. -/
theorem positive_masses_allow_any_mixing (V : M) (hV : V*Vᴴ=1)
    (mu md : Fin 3 → ℝ) (hmu : ∀ i, 0<mu i) (hmd : ∀ i, 0<md i) (θ : ℝ) :
    (mass 1 mu).PosDef ∧ (mass V md).PosDef ∧ FlavourCurrent.mixing 1 V=V ∧
      PMNested.HermitianMass.thetaBar θ (mass 1 mu) (mass V md)=θ := by
  exact ⟨mass_posDef 1 mu (by simp) hmu, mass_posDef V md hV hmd,
    by simp [FlavourCurrent.mixing], thetaBar 1 V mu md (by simp) hV hmu hmd θ⟩

end PMDynamics.MassMixing
