import PMDynamics.ReferenceSelection

/-!
# The same native reference eigenstate survives distinct flavour links

The complementary rotations in `ReferenceSelection` fix not just a three-vector
or its readout. Every scalar wall eigenmode in the reference flavour slot lifts
to the same full wall state, and then to the same nonzero register configuration
amplitude, for all rotations. The link can still change. The scalar eigenmode,
flavour identification, coherent admission and physical reference remain inputs.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.NativeReferenceFreedom
open Matrix PMAction ReferenceSelection

theorem wall_reference_fixed (U : M) (c s : ℝ) (v : WallDispersion.Ix → ℂ) :
    FlavourWallReduction.basis (basis U c s) *ᵥ FlavourWallReduction.inject 1 v =
      FlavourWallReduction.basis U *ᵥ FlavourWallReduction.inject 1 v := by
  have ht : FlavourWallReduction.basis (turn c s) *ᵥ FlavourWallReduction.inject 1 v =
      FlavourWallReduction.inject 1 v := by
    ext (⟨a,i⟩ | ⟨a,i⟩) <;> fin_cases i <;>
      simp [FlavourWallReduction.basis, FlavourWallReduction.inject, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, turn,
        Matrix.one_apply, Matrix.kroneckerMap_apply]
  rw [basis, ← FlavourWallReduction.basis_mul, ← mulVec_mulVec, ht]

theorem wall_reference_eigenstate (U : M) (hu : U * Uᴴ=1) (c s : ℝ)
    (h : c^2+s^2=1) (m : Fin 3 → ℝ) (k : Fin 3 → ℝ) (δ : ℝ)
    (v : WallDispersion.Ix → ℂ) (hv : v ≠ 0) (E : ℂ)
    (he : WallDispersion.Hy k δ (m 1) *ᵥ v = E • v) :
    let ψ := FlavourWallReduction.basis U *ᵥ FlavourWallReduction.inject 1 v
    ψ ≠ 0 ∧ WallExchange.H k δ (MassMixing.mass (basis U c s) m) *ᵥ ψ = E • ψ := by
  have hb := basis_unitary U hu c s h
  have hd : (basis U c s)ᴴ * MassMixing.mass (basis U c s) m * basis U c s =
      diagonal (fun j => (m j:ℂ)) := by
    simp [MassMixing.mass, MassMixing.eigenMass, Matrix.mul_assoc,
      ← Matrix.mul_assoc (basis U c s)ᴴ (basis U c s), mul_eq_one_comm.mp hb]
  have hh := FlavourWallReduction.lift_eigenstate k δ _ (basis U c s)
    (mul_eq_one_comm.mp hb) hb m hd 1 v hv E he
  simpa only [wall_reference_fixed] using hh

/-- One fixed configuration amplitude is an eigenstate for the whole family,
not merely a family of different encodings with matching scalar energies. -/
theorem native_reference_eigenstate {r : Type*} [Fintype r] [DecidableEq r]
    (a : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (U : M) (hu : U * Uᴴ=1) (c s : ℝ) (h : c^2+s^2=1)
    (m : Fin 3 → ℝ) (k : Fin 3 → ℝ) (δ : ℝ)
    (v : WallDispersion.Ix → ℂ) (hv : v ≠ 0) (E : ℂ)
    (he : WallDispersion.Hy (NativeFlavourWall.momentum k) δ (m 1) *ᵥ v = E • v)
    (ρ : r → ℂ) (hρ : ρ ≠ 0) :
    let ψ := NativeFlavourWall.encode a
      (FlavourWallReduction.basis U *ᵥ FlavourWallReduction.inject 1 v) ρ
    ψ ≠ 0 ∧ NativeFlavourWall.generator a p k δ (MassMixing.mass (basis U c s) m) *ᵥ ψ = E • ψ := by
  have hh := wall_reference_eigenstate U hu c s h m (NativeFlavourWall.momentum k) δ v hv E he
  exact ⟨NativeFlavourWall.encode_ne_zero a _ hh.1 ρ hρ,
    NativeFlavourWall.encoded_eigenstate a p hp hp1 k δ _ E _ ρ hh.2⟩

end PMDynamics.NativeReferenceFreedom
