import PMDynamics.NativeMassBasis
import PMDynamics.ReferenceFlavour
import PMDynamics.FlavourEvolution

/-!
# What a persistent reference leaves available to a selection law

A unitary rotation of the two columns complementary to column 1 keeps that
reference exactly fixed, while allowing different positive Hermitian links
with the same supplied spectrum. This applies to the actual proposed PMNS
reference column as well as to arbitrary unitary bases. The links are realized
by the existing native wall/current construction.

No objective is declared to be PM's physical cost here. A cost invariant under
these reference-fixing conjugations cannot distinguish the resulting links.
An independent theorem states the corresponding obstruction for a unique
minimum of a class-permutation-invariant cost. These are tests of candidate
selection laws, not new postulates selecting the desired angles.
-/
noncomputable section
namespace PMDynamics.ReferenceSelection
open Matrix PMAction
open scoped ComplexOrder
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

/-- Rotates only the complement of the reference slot, here column 1. -/
def turn (c s : ℝ) : M := !![(c:ℂ), 0, s; 0, 1, 0; -(s:ℂ), 0, c]
def basis (U : M) (c s : ℝ) : M := U * turn c s
def reference (U : M) : Fin 3 → ℂ := fun i => U i 1

theorem turn_unitary (c s : ℝ) (h : c^2+s^2=1) : turn c s * (turn c s)ᴴ = 1 := by
  have hh : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [turn, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three]
  all_goals first | linear_combination hh | linear_combination -hh | ring

theorem basis_unitary (U : M) (hu : U * Uᴴ = 1) (c s : ℝ) (h : c^2+s^2=1) :
    basis U c s * (basis U c s)ᴴ = 1 := by
  simp only [basis, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (turn c s) (turn c s)ᴴ, turn_unitary c s h, one_mul, hu]

theorem reference_fixed (U : M) (c s : ℝ) : reference (basis U c s) = reference U := by
  ext i
  simp [reference, basis, turn, Matrix.mul_apply, Fin.sum_univ_three]

theorem reference_column (U : M) : U *ᵥ (Pi.single 1 1) = reference U := by
  ext i
  simp [reference, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem column_formula (U : M) (c s : ℝ) (i : Fin 3) :
    basis U c s i 0 = (c:ℂ)*U i 0 - (s:ℂ)*U i 2 ∧
      basis U c s i 2 = (s:ℂ)*U i 0 + (c:ℂ)*U i 2 := by
  simp [basis, turn, Matrix.mul_apply, Fin.sum_univ_three]
  constructor <;> ring

theorem reference_eigenstate (U : M) (hu : U * Uᴴ = 1) (c s : ℝ)
    (h : c^2+s^2=1) (m : Fin 3 → ℝ) :
    MassMixing.mass (basis U c s) m *ᵥ reference U = (m 1:ℂ) • reference U := by
  have he := MassMixing.eigenvector (basis U c s) m (basis_unitary U hu c s h) 1
  simpa only [reference_column, reference_fixed] using he

theorem reference_propagation (U : M) (hu : U * Uᴴ = 1) (c s : ℝ)
    (h : c^2+s^2=1) (energy : Fin 3 → ℝ) (t : ℝ) :
    FlavourEvolution.evolution (basis U c s) energy t *ᵥ reference U =
      Complex.exp (((-t*energy 1:ℝ):ℂ)*Complex.I) • reference U := by
  have hv : reference U = basis U c s *ᵥ (Pi.single 1 1) := by
    rw [reference_column, reference_fixed]
  rw [hv, FlavourEvolution.evolution, mulVec_mulVec]
  have hu' := mul_eq_one_comm.mp (basis_unitary U hu c s h)
  rw [Matrix.mul_assoc, hu', Matrix.mul_one, ← mulVec_mulVec]
  have hd : LinkExpansion.phaseDiag energy (-t) *ᵥ (Pi.single 1 1) =
      Complex.exp (((-t*energy 1:ℝ):ℂ)*Complex.I) • (Pi.single 1 1 : Fin 3 → ℂ) := by
    ext i
    by_cases hi : i=1
    · subst i; simp [LinkExpansion.phaseDiag, mulVec_diagonal]
    · simp [LinkExpansion.phaseDiag, mulVec_diagonal, hi]
  rw [hd, mulVec_smul]

theorem positive_fixed_spectrum (U : M) (hu : U * Uᴴ = 1) (c s : ℝ)
    (h : c^2+s^2=1) (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i) :
    (MassMixing.mass (basis U c s) m).PosDef ∧
    MassMixing.mass (basis U c s) m * basis U c s = basis U c s * MassMixing.eigenMass m ∧
    (MassMixing.mass (basis U c s) m).det = ((∏ i, m i:ℝ):ℂ) :=
  ⟨MassMixing.mass_posDef _ _ (basis_unitary U hu c s h) hm,
    MassMixing.diagonalizes _ _ (basis_unitary U hu c s h),
    MassMixing.determinant _ _ (basis_unitary U hu c s h)⟩

/-- The proposed reference's balance rule survives every such rotation. -/
theorem pmns_balance (c s : ℝ) :
    Complex.normSq (basis PMNS.matrix c s 1 1) =
      Complex.normSq (basis PMNS.matrix c s 2 1) := by
  have hh := reference_fixed PMNS.matrix c s
  change Complex.normSq (reference (basis PMNS.matrix c s) 1) =
    Complex.normSq (reference (basis PMNS.matrix c s) 2)
  rw [hh]
  exact ReferenceFlavour.paper_on_rule

/-- A continuous family, rather than only a relabeling of columns. -/
theorem angle_family (U : M) (hu : U * Uᴴ=1) (θ : ℝ) :
    basis U (Real.cos θ) (Real.sin θ) * (basis U (Real.cos θ) (Real.sin θ))ᴴ = 1 ∧
      reference (basis U (Real.cos θ) (Real.sin θ)) = reference U :=
  ⟨basis_unitary U hu _ _ (Real.cos_sq_add_sin_sq θ), reference_fixed U _ _⟩

/-- The actual reference displacement cost is unchanged, at every time. -/
theorem reference_transition_cost (U : M) (hu : U * Uᴴ=1) (c s : ℝ)
    (h : c^2+s^2=1) (energy : Fin 3 → ℝ) (t : ℝ) :
    CommonResponse.nsq (reference U - FlavourEvolution.evolution (basis U c s) energy t *ᵥ reference U) =
      CommonResponse.nsq (reference U - FlavourEvolution.evolution U energy t *ᵥ reference U) := by
  have hzero : basis U 1 0 = U := by simp [basis, turn, ← Matrix.one_fin_three]
  have hbase := reference_propagation U hu 1 0 (by norm_num) energy t
  rw [hzero] at hbase
  rw [reference_propagation U hu c s h energy t, hbase]

/-- Relative to the original basis, the changed link has a genuine off-diagonal entry. -/
theorem link_entry (U : M) (hu : U * Uᴴ=1) (c s : ℝ) (m : Fin 3 → ℝ) :
    (Uᴴ * MassMixing.mass (basis U c s) m * U) 0 2 =
      ((c*s*(m 2-m 0):ℝ):ℂ) := by
  have hu' := mul_eq_one_comm.mp hu
  have he : Uᴴ * MassMixing.mass (basis U c s) m * U =
      turn c s * MassMixing.eigenMass m * (turn c s)ᴴ := by
    simp only [MassMixing.mass, basis, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ U, hu', one_mul, mul_one]
  rw [he]
  simp [turn, MassMixing.eigenMass, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, Fin.sum_univ_three]
  ring

theorem different_link (U : M) (hu : U * Uᴴ=1) (c s : ℝ)
    (hc : c ≠ 0) (hs : s ≠ 0) (m : Fin 3 → ℝ) (hm : m 0 ≠ m 2) :
    MassMixing.mass (basis U c s) m ≠ MassMixing.mass U m := by
  intro he
  have hh := link_entry U hu c s m
  rw [he] at hh
  have hdiag : Uᴴ * MassMixing.mass U m * U = MassMixing.eigenMass m := by
    simp [MassMixing.mass, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, mul_eq_one_comm.mp hu]
  rw [hdiag] at hh
  have hn : c*s*(m 2-m 0) ≠ 0 := mul_ne_zero (mul_ne_zero hc hs) (sub_ne_zero.mpr (Ne.symm hm))
  have hz : ((c*s*(m 2-m 0):ℝ):ℂ) = 0 := by
    simpa [MassMixing.eigenMass] using hh.symm
  exact hn (Complex.ofReal_eq_zero.mp hz)

/-- This witness mixes two split modes; it is not merely a column phase or relabeling. -/
theorem rational_alternative (U : M) (hu : U * Uᴴ=1) (m : Fin 3 → ℝ) (hm : m 0 ≠ m 2) :
    basis U (3/5) (4/5) * (basis U (3/5) (4/5))ᴴ = 1 ∧
    reference (basis U (3/5) (4/5)) = reference U ∧
    MassMixing.mass (basis U (3/5) (4/5)) m ≠ MassMixing.mass U m :=
  ⟨basis_unitary U hu _ _ (by norm_num), reference_fixed U _ _,
    different_link U hu _ _ (by norm_num) (by norm_num) m hm⟩

/-- A cost invariant under the actual conjugation fixing the reference cannot
distinguish the corresponding links. Invariance is a testable input, not a PM axiom. -/
theorem invariant_cost_tie (U : M) (hu : U * Uᴴ=1) (c s : ℝ) (m : Fin 3 → ℝ)
    (cost : M → ℝ)
    (hcost : ∀ W : M, W * Wᴴ=1 → W *ᵥ reference U = reference U →
      ∀ Y, cost (W * Y * Wᴴ) = cost Y) (h : c^2+s^2=1) :
    cost (MassMixing.mass (basis U c s) m) = cost (MassMixing.mass U m) := by
  let W := U * turn c s * Uᴴ
  have hu' := mul_eq_one_comm.mp hu
  have hw : W * Wᴴ=1 := by
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ U, hu', one_mul,
      ← Matrix.mul_assoc (turn c s) (turn c s)ᴴ, turn_unitary c s h, hu]
  have href : W *ᵥ reference U = reference U := by
    rw [← reference_column U, mulVec_mulVec]
    have he : W * U = basis U c s := by simp [W, basis, Matrix.mul_assoc, hu']
    rw [he, reference_column, reference_fixed]
    exact (reference_column U).symm
  have he : W * MassMixing.mass U m * Wᴴ = MassMixing.mass (basis U c s) m := by
    simp only [W, MassMixing.mass, basis, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hu', one_mul]
  simpa only [he] using hcost W hw href (MassMixing.mass U m)

end PMDynamics.ReferenceSelection
