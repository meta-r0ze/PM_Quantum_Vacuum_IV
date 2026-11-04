import PMFlavor.NativeFlavourWall
import PMFlavor.FlavourCurrent

/-!
# Chiral flavour currents on the same native wall/register space

The native gamma word supplies the spin projector. Any supplied flavour
operator has exact all-state current readout on the multi-flavour wall model.
The charged-current mass-basis block is Uu†Ud and the neutral universal current
remains diagonal, now at the encoded bilinear as well as the abstract matrix.
The current is an operator, not a global identification of wall/flavour tags.
Physical generation/current attachment, charge values and the link-selection
law remain inputs. These charge operators do not select a mediator or statistics.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.NativeFlavourCurrent
open Matrix PMAction NativeObservation NativeFlavourWall
open scoped Kronecker
variable (c : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

def spinProjector : ConcreteFermion.Spin := (1/2 : ℂ) • (1-ConcreteFermion.gamma)

def nativeSpinProjector : Matrix (CarrierEvents.Carrier c) (CarrierEvents.Carrier c) ℂ :=
  (1/2 : ℂ) • (1-(1/2 : ℂ) •
    (CarrierVacuumSector.gamma c + (CarrierVacuumSector.gamma c)ᴴ))

theorem projector_observed : Obs (CarrierParity.embedding c) (nativeSpinProjector c) spinProjector :=
  NativeObservation.smul (1/2) (NativeObservation.sub NativeObservation.one
    (NativeObservation.herm (NativeSector.gamma_obs c) ConcreteFermion.gamma_hermitian))

def nativeOperator (G : Matrix f f ℂ) : Matrix (Labels (f := f) c) (Labels (f := f) c) ℂ :=
  fromBlocks (nativeSpinProjector c ⊗ₖ G) 0 0 (nativeSpinProjector c ⊗ₖ G)

def modelCurrent (G : Matrix f f ℂ) : Matrix (Modes (f := f)) (Modes (f := f)) ℂ :=
  fromBlocks (spinProjector ⊗ₖ G) 0 0 (spinProjector ⊗ₖ G)

theorem native_observed (G : Matrix f f ℂ) :
    Obs (coordinate c) (nativeOperator c G) (modelCurrent G) := by
  have hh := NativeObservation.tensor (projector_observed c)
    (show Obs (1 : Matrix f f ℂ) G G from ⟨by simp, by simp⟩)
  exact NativeObservation.blocks hh NativeObservation.zero NativeObservation.zero hh

def operator (G : Matrix f f ℂ) : Matrix (Config (f := f) (r := r) c) (Config (f := f) (r := r) c) ℂ :=
  RegisterHamiltonian.raw (nativeOperator c G)

theorem observed (G : Matrix f f ℂ) :
    Obs (embedding (r := r) c) (operator c G) (modelCurrent G ⊗ₖ (1 : Matrix r r ℂ)) := by
  apply NativeObservation.compose (RegisterHamiltonian.raw_observed (nativeOperator c G))
  exact NativeObservation.tensor (native_observed c G)
    (NativeObservation.one : Obs (1 : Matrix r r ℂ) 1 1)

/-- Native bilinears equal their coordinate currents, with the record retained. -/
theorem compressed (G : Matrix f f ℂ) :
    (embedding (r := r) c)ᴴ * operator c G * embedding c = modelCurrent G ⊗ₖ (1 : Matrix r r ℂ) := by
  rw [Matrix.mul_assoc, (observed c G).1, ← Matrix.mul_assoc, NativeFlavourWall.isometry, one_mul]

section Doublets
abbrev F := Fin 3 ⊕ Fin 3

def massFrame (Uu Ud : FlavourCurrent.M) : Matrix (Config (f := F) (r := r) c) (Modes (f := F) × r) ℂ :=
  embedding c * (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ))

theorem mass_frame_isometry (Uu Ud : FlavourCurrent.M)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) :
    (massFrame (r := r) c Uu Ud)ᴴ * massFrame (r := r) c Uu Ud = 1 := by
  have hb : (FlavourCurrent.basis Uu Ud)ᴴ * FlavourCurrent.basis Uu Ud = 1 := by
    simp [FlavourCurrent.basis, fromBlocks_conjTranspose, fromBlocks_multiply,
      mul_eq_one_comm.mp hu, mul_eq_one_comm.mp hd, fromBlocks_one]
  exact NativeObservation.compose_isometry _ _ (NativeFlavourWall.isometry (f := F) (r := r) c)
    (NativeObservation.tensor_isometry _ _ (FlavourWallReduction.basis_left _ hb) (by simp))

private theorem charged_matrix (Uu Ud : FlavourCurrent.M) :
    (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud))ᴴ *
      modelCurrent FlavourCurrent.raising *
      FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) =
    modelCurrent (fromBlocks 0 (FlavourCurrent.mixing Uu Ud) 0 0) := by
  simp only [FlavourWallReduction.basis, modelCurrent, fromBlocks_conjTranspose,
    fromBlocks_multiply, conjTranspose_zero, conjTranspose_kronecker, conjTranspose_one,
    mul_zero, zero_mul, zero_add, add_zero, ← mul_kronecker_mul, one_mul, mul_one,
    FlavourCurrent.charged_in_mass_basis]

theorem charged_in_mass_basis (Uu Ud : FlavourCurrent.M) :
    (massFrame (r := r) c Uu Ud)ᴴ * operator c FlavourCurrent.raising * massFrame (r := r) c Uu Ud =
      modelCurrent (fromBlocks 0 (FlavourCurrent.mixing Uu Ud) 0 0) ⊗ₖ (1 : Matrix r r ℂ) := by
  unfold massFrame
  rw [conjTranspose_mul]
  have hh := compressed (r := r) c FlavourCurrent.raising
  calc
    _ = (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ))ᴴ *
      ((embedding c)ᴴ * operator c FlavourCurrent.raising * embedding c) *
      (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hh, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
        ← mul_kronecker_mul, one_mul, one_mul, charged_matrix]

theorem neutral_in_mass_basis (Uu Ud : FlavourCurrent.M)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) (cu cd : ℂ) :
    let G := fromBlocks (cu • (1 : FlavourCurrent.M)) 0 0 (cd • (1 : FlavourCurrent.M))
    (massFrame (r := r) c Uu Ud)ᴴ * operator c G * massFrame (r := r) c Uu Ud =
      modelCurrent G ⊗ₖ (1 : Matrix r r ℂ) := by
  dsimp only
  unfold massFrame
  rw [conjTranspose_mul]
  have hh := compressed (r := r) c
    (fromBlocks (cu • (1 : FlavourCurrent.M)) 0 0 (cd • (1 : FlavourCurrent.M)))
  calc
    _ = (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ))ᴴ *
      ((embedding c)ᴴ * operator c (fromBlocks (cu • (1 : FlavourCurrent.M)) 0 0 (cd • (1 : FlavourCurrent.M))) * embedding c) *
      (FlavourWallReduction.basis (FlavourCurrent.basis Uu Ud) ⊗ₖ (1 : Matrix r r ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hh]
      simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul,
        FlavourWallReduction.basis, modelCurrent, fromBlocks_conjTranspose,
        fromBlocks_multiply, conjTranspose_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one,
        FlavourCurrent.neutral_in_mass_basis Uu Ud hu hd]

/-- Native realization still permits every supplied unitary mixing: the new
carrier/current construction is not an angle-selection law. -/
theorem arbitrary_mixing_realized (V : FlavourCurrent.M) (hV : V * Vᴴ = 1) :
    (massFrame (r := r) c 1 V)ᴴ * massFrame (r := r) c 1 V = 1 ∧
    (massFrame (r := r) c 1 V)ᴴ * operator c FlavourCurrent.raising * massFrame (r := r) c 1 V =
      modelCurrent (fromBlocks 0 V 0 0) ⊗ₖ (1 : Matrix r r ℂ) := by
  refine ⟨mass_frame_isometry c 1 V (by simp) hV, ?_⟩
  simpa [FlavourCurrent.mixing] using charged_in_mass_basis (r := r) c 1 V

end Doublets
end PMFlavor.NativeFlavourCurrent
