import PMAction.ChargedCurrent
import PMDynamics.CKMClosure

/-! Generation mixing in the supplied generation-universal weak current.
The complete mass bases and three-generation state space are inputs; this does
not select the mass links, mixing angles or physical generation count. -/
noncomputable section
namespace PMDynamics.FlavourCurrent
open Matrix
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def basis (Uu Ud : M) := fromBlocks Uu 0 0 Ud
def raising : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := fromBlocks 0 1 0 0
def lowering : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := fromBlocks 0 0 1 0

def doubletLift (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  fromBlocks (T 0 0 • (1 : M)) (T 0 1 • (1 : M))
    (T 1 0 • (1 : M)) (T 1 1 • (1 : M))

theorem upstream_raising : doubletLift PMAction.ChargedCurrent.Tp = raising := by
  rw [PMAction.ChargedCurrent.raising_entries.1]
  simp [doubletLift,raising]

def mixing (Uu Ud : M) := Uuᴴ * Ud

/-- Generation-universal raising in the interaction basis becomes the mixing
matrix in the mass basis. The conjugate vertex contains its adjoint. -/
theorem charged_in_mass_basis (Uu Ud : M) :
    (basis Uu Ud)ᴴ * raising * basis Uu Ud = fromBlocks 0 (mixing Uu Ud) 0 0 := by
  simp [basis, raising, mixing, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem lowering_in_mass_basis (Uu Ud : M) :
    (basis Uu Ud)ᴴ * lowering * basis Uu Ud = fromBlocks 0 0 (mixing Uu Ud)ᴴ 0 := by
  simp [basis, lowering, mixing, fromBlocks_conjTranspose, fromBlocks_multiply,
    conjTranspose_mul]

theorem mixing_unitary (Uu Ud : M) (hu : Uu*Uuᴴ=1) (hd : Ud*Udᴴ=1) :
    mixing Uu Ud ∈ unitary M := by
  have h := CKMClosure.basis_change_unitary Uu Ud hu hd
  exact ⟨mul_eq_one_comm.mp h, h⟩

/-- A universal scalar coefficient commutes with generation basis changes;
this is a conditional neutral-current flavour-diagonality statement. -/
theorem neutral_in_mass_basis (Uu Ud : M) (hu : Uu*Uuᴴ=1) (hd : Ud*Udᴴ=1)
    (cu cd : ℂ) :
    (basis Uu Ud)ᴴ * fromBlocks (cu • (1 : M)) 0 0 (cd • (1 : M)) * basis Uu Ud =
      fromBlocks (cu • (1 : M)) 0 0 (cd • (1 : M)) := by
  have hu' : Uuᴴ*Uu=1 := mul_eq_one_comm.mp hu
  have hd' : Udᴴ*Ud=1 := mul_eq_one_comm.mp hd
  simp [basis, fromBlocks_conjTranspose, fromBlocks_multiply, hu', hd']

/-- The previously derived chiral charged-vertex factor is retained when
changing generation bases; the change supplies mixing, not a new coupling. -/
theorem charged_coefficient (Uu Ud : M) (g : ℂ) :
    (basis Uu Ud)ᴴ * ((g/(2*Real.sqrt 2)) • raising) * basis Uu Ud =
      (g/(2*Real.sqrt 2)) • fromBlocks 0 (mixing Uu Ud) 0 0 := by
  rw [Matrix.mul_smul, Matrix.smul_mul, charged_in_mass_basis]

end PMDynamics.FlavourCurrent
