import PMFlavor.NativeFlavourCurrent
import PMFlavor.MassMixing

/-! The current's complete mass frame also diagonalizes the actual constructed
up/down wall link. Its spectra can be held fixed while every unitary mixing
matrix is realized. This rules out inferring angle selection from the new native
representation alone; it does not impose a cost or breaking law. -/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.NativeMassBasis
open Matrix PMAction NativeFlavourWall NativeFlavourCurrent
open scoped Kronecker

def link (Uu Ud : FlavourCurrent.M) (mu md : Fin 3 → ℝ) : Matrix F F ℂ :=
  fromBlocks (MassMixing.mass Uu mu) 0 0 (MassMixing.mass Ud md)
def spectrum (mu md : Fin 3 → ℝ) : F → ℝ := Sum.elim mu md

theorem link_hermitian (Uu Ud : FlavourCurrent.M) (mu md : Fin 3 → ℝ) :
    (link Uu Ud mu md).IsHermitian := by
  simp [IsHermitian, link, fromBlocks_conjTranspose, (MassMixing.mass_hermitian Uu mu).eq,
    (MassMixing.mass_hermitian Ud md).eq]

private theorem mass_diagonal (U : FlavourCurrent.M) (m : Fin 3 → ℝ) (hU : U * Uᴴ = 1) :
    Uᴴ * MassMixing.mass U m * U = MassMixing.eigenMass m := by
  rw [Matrix.mul_assoc, MassMixing.diagonalizes U m hU, ← Matrix.mul_assoc,
    mul_eq_one_comm.mp hU, Matrix.one_mul]

theorem diagonalizes_link (Uu Ud : FlavourCurrent.M) (mu md : Fin 3 → ℝ)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) :
    (FlavourCurrent.basis Uu Ud)ᴴ * link Uu Ud mu md * FlavourCurrent.basis Uu Ud =
      diagonal (fun i => (spectrum mu md i : ℂ)) := by
  simp only [FlavourCurrent.basis, link, fromBlocks_conjTranspose, conjTranspose_zero,
    fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add, mass_diagonal Uu mu hu,
    mass_diagonal Ud md hd]
  ext i j
  cases i <;> cases j <;> simp [MassMixing.eigenMass, spectrum, diagonal_apply, fromBlocks]

variable (c : Fin 3) {r : Type*} [Fintype r] [DecidableEq r]

theorem compressed_mass_hamiltonian (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Uu Ud : FlavourCurrent.M) (mu md : Fin 3 → ℝ)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) :
    (massFrame (r := r) c Uu Ud)ᴴ * generator c p k δ (link Uu Ud mu md) *
      massFrame (r := r) c Uu Ud =
    WallExchange.H (momentum k) δ (diagonal (fun i => (spectrum mu md i : ℂ))) ⊗ₖ (1 : Matrix r r ℂ) := by
  have hb : (FlavourCurrent.basis Uu Ud)ᴴ * FlavourCurrent.basis Uu Ud = 1 := by
    simp [FlavourCurrent.basis, fromBlocks_conjTranspose, fromBlocks_multiply,
      mul_eq_one_comm.mp hu, mul_eq_one_comm.mp hd, fromBlocks_one]
  have hred := FlavourWallReduction.conjugates (momentum k) δ (link Uu Ud mu md)
    (FlavourCurrent.basis Uu Ud) hb
  rw [diagonalizes_link Uu Ud mu md hu hd] at hred
  have hk : (embedding (r := r) c)ᴴ * generator c p k δ (link Uu Ud mu md) * embedding c =
      WallExchange.H (momentum k) δ (link Uu Ud mu md) ⊗ₖ (1 : Matrix r r ℂ) := by
    rw [Matrix.mul_assoc, (NativeFlavourWall.observed c p hp hp1 k δ (link Uu Ud mu md)).1,
      ← Matrix.mul_assoc, NativeFlavourWall.isometry, one_mul]
  unfold massFrame
  rw [conjTranspose_mul]
  calc
    _ = (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ))ᴴ *
      ((embedding c)ᴴ * generator c p k δ (link Uu Ud mu md) * embedding c) *
      (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hk, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
        ← mul_kronecker_mul, one_mul, one_mul, hred]

theorem arbitrary_mixing_with_fixed_spectra (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (V : FlavourCurrent.M) (hV : V * Vᴴ = 1)
    (mu md : Fin 3 → ℝ) :
    (link 1 V mu md).IsHermitian ∧
    (massFrame (r := r) c 1 V)ᴴ * massFrame (r := r) c 1 V = 1 ∧
    (massFrame (r := r) c 1 V)ᴴ * generator c p k δ (link 1 V mu md) * massFrame (r := r) c 1 V =
      WallExchange.H (momentum k) δ (diagonal (fun i => (spectrum mu md i : ℂ))) ⊗ₖ (1 : Matrix r r ℂ) ∧
    (massFrame (r := r) c 1 V)ᴴ * operator c FlavourCurrent.raising * massFrame (r := r) c 1 V =
      modelCurrent (fromBlocks 0 V 0 0) ⊗ₖ (1 : Matrix r r ℂ) := by
  refine ⟨link_hermitian 1 V mu md, mass_frame_isometry c 1 V (by simp) hV,
    compressed_mass_hamiltonian c p hp hp1 k δ 1 V mu md (by simp) hV, ?_⟩
  exact (NativeFlavourCurrent.arbitrary_mixing_realized (r := r) c V hV).2

end PMFlavor.NativeMassBasis
