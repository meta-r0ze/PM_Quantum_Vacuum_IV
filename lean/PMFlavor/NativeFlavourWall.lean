import PMFlavor.FlavourWallReduction
import PMAction.RegisterHamiltonian
import PMAction.GaugeRecordEmbedding

/-!
# The actual multi-flavour wall Hamiltonian on native carriers and registers

Every supplied finite flavour space and link Y have an explicit native model,
built from the existing root/phase diagonal and wall-hop operators. Its coordinate
readout is the full `WallExchange.H`, not a separately added flavour Hamiltonian.
The Boolean lift gives unitary configuration evolution and realizes every allowed
light-branch energy. The flavour labels, link, records and coherent admission
remain inputs. Neither three physical generations nor a breaking law is selected.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.NativeFlavourWall
open Matrix PMAction NativeObservation
open scoped Kronecker
variable (c : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

abbrev Labels := (CarrierEvents.Carrier c × f) ⊕ (CarrierEvents.Carrier c × f)
abbrev Modes := FlavourWallReduction.Ix f
abbrev Config := IndependentRegisters.Configuration (Labels (f := f) c) r

def coordinate : Matrix (Labels (f := f) c) (Modes (f := f)) ℂ :=
  fromBlocks (CarrierParity.embedding c ⊗ₖ (1 : Matrix f f ℂ)) 0 0
    (CarrierParity.embedding c ⊗ₖ (1 : Matrix f f ℂ))

theorem coordinate_isometry : (coordinate (f := f) c)ᴴ * coordinate (f := f) c = 1 := by
  have hi := tensor_isometry (CarrierParity.embedding c) (1 : Matrix f f ℂ)
    (CarrierParity.isometry c) (by simp)
  simp [coordinate, fromBlocks_conjTranspose, fromBlocks_multiply, hi, fromBlocks_one]

def momentum (k : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => Real.sin (k j)

def nativeHamiltonian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    Matrix (Labels (f := f) c) (Labels (f := f) c) ℂ :=
  let D := NativeSector.diag c p k δ ⊗ₖ (1 : Matrix f f ℂ)
  let T := NativeSector.hopN c ⊗ₖ Y
  fromBlocks D T Tᴴ D

omit [Fintype f] in
theorem native_hermitian (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    (nativeHamiltonian c p k δ Y).IsHermitian := by
  have hd : (NativeSector.diag c p k δ).IsHermitian := by
    unfold IsHermitian NativeSector.diag
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    norm_num
  unfold IsHermitian nativeHamiltonian
  rw [fromBlocks_conjTranspose, conjTranspose_kronecker, conjTranspose_one, hd.eq,
    conjTranspose_conjTranspose]

theorem native_observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    Obs (coordinate c) (nativeHamiltonian c p k δ Y) (WallExchange.H (momentum k) δ Y) := by
  have hI : Obs (1 : Matrix f f ℂ) 1 1 := NativeObservation.one
  have hY : Obs (1 : Matrix f f ℂ) Y Y := ⟨by simp, by simp⟩
  have hd := NativeObservation.tensor (NativeSector.diag_obs (c := c) hp hp1 k δ) hI
  have ht := NativeObservation.tensor (NativeSector.hop_obs (c := c)) hY
  have hh := NativeObservation.blocks hd ht (NativeObservation.star ht) hd
  have hdEq : DomainWallSpectrum.momentum ConcreteFermion.alpha k + δ • ConcreteFermion.beta =
      WallExchange.diag (momentum k) δ := by
    simp only [WallExchange.diag, WallExchange.K, momentum, DomainWallSpectrum.momentum,
      Complex.coe_smul]
  have hhop : DomainWallSpectrum.hop ConcreteFermion.beta ConcreteFermion.gamma =
      WallExchange.hop := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [DomainWallSpectrum.hop, DomainWallSpectrum.plus, WallExchange.hop,
        ConcreteFermion.beta, ConcreteFermion.gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  have hback : DomainWallSpectrum.back ConcreteFermion.beta ConcreteFermion.gamma =
      WallExchange.back := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [DomainWallSpectrum.back, DomainWallSpectrum.minus, WallExchange.back,
        ConcreteFermion.beta, ConcreteFermion.gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  have hhAdj : WallExchange.hopᴴ = WallExchange.back := by
    rw [← hhop, NativeSector.hop_adjoint, hback]
  simpa only [coordinate, nativeHamiltonian, WallExchange.H, hdEq,
    conjTranspose_kronecker, hhAdj, hhop, hback] using hh

def embedding : Matrix (Config (f := f) (r := r) c) (Modes (f := f) × r) ℂ :=
  IndependentRegisters.embedding * (coordinate c ⊗ₖ (1 : Matrix r r ℂ))

theorem native_encoded_eigen_iff (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (E : ℂ) (ψ : Modes (f := f) → ℂ) :
    nativeHamiltonian c p k δ Y *ᵥ (coordinate c *ᵥ ψ) = E • (coordinate c *ᵥ ψ) ↔
      WallExchange.H (momentum k) δ Y *ᵥ ψ = E • ψ := by
  have hinj : Function.Injective (fun v => coordinate (f := f) c *ᵥ v) := by
    intro v w h
    have hh := congrArg (fun z => (coordinate c)ᴴ *ᵥ z) h
    simpa only [mulVec_mulVec, coordinate_isometry, one_mulVec] using hh
  rw [mulVec_mulVec, (native_observed c p hp hp1 k δ Y).1, ← mulVec_mulVec, ← mulVec_smul]
  exact hinj.eq_iff

/-- The complete encoded native spectrum, including every supplied flavour. -/
theorem native_energy_iff (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (hY : Y.IsHermitian) (E : ℂ) :
    (∃ ψ : Modes (f := f) → ℂ, ψ ≠ 0 ∧
      nativeHamiltonian c p k δ Y *ᵥ (coordinate c *ᵥ ψ) = E • (coordinate c *ᵥ ψ)) ↔
    ∃ j : f, ∃ v : WallDispersion.Ix → ℂ, v ≠ 0 ∧
      WallDispersion.Hy (momentum k) δ (hY.eigenvalues j) *ᵥ v = E • v := by
  simp_rw [native_encoded_eigen_iff c p hp hp1 k δ Y E]
  exact FlavourWallReduction.hermitian_energy_iff (momentum k) δ Y hY E

theorem isometry : (embedding (f := f) (r := r) c)ᴴ * embedding (f := f) (r := r) c = 1 :=
  compose_isometry _ _ IndependentRegisters.isometry
    (tensor_isometry _ _ (coordinate_isometry c) (by simp))

def generator (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) :
    Matrix (Config (f := f) (r := r) c) (Config (f := f) (r := r) c) ℂ :=
  RegisterHamiltonian.generator (nativeHamiltonian c p k δ Y)

theorem observed (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ)
    (δ : ℝ) (Y : Matrix f f ℂ) :
    Obs (embedding (r := r) c) (generator c p k δ Y)
      (WallExchange.H (momentum k) δ Y ⊗ₖ (1 : Matrix r r ℂ)) := by
  apply NativeObservation.compose
    (RegisterHamiltonian.generator_observed _ (native_hermitian c p k δ Y))
  exact NativeObservation.tensor (native_observed c p hp hp1 k δ Y)
    (NativeObservation.one : Obs (1 : Matrix r r ℂ) 1 1)

theorem evolution_unitary (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • generator (r := r) c p k δ Y) ∈ unitary _ :=
  RegisterHamiltonian.evolution_unitary _ t

theorem evolution_readout (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ)
    (δ : ℝ) (Y : Matrix f f ℂ) (z : ℂ) (ψ : Config (f := f) (r := r) c → ℂ) :
    (embedding c)ᴴ *ᵥ (NormedSpace.exp (z • generator c p k δ Y) *ᵥ ψ) =
      NormedSpace.exp (z • (WallExchange.H (momentum k) δ Y ⊗ₖ (1 : Matrix r r ℂ))) *ᵥ
        ((embedding c)ᴴ *ᵥ ψ) :=
  NativeObservation.readout (NativeObservation.exp (observed c p hp hp1 k δ Y) z) ψ

def encode (ψ : Modes (f := f) → ℂ) (ρ : r → ℂ) : Config (f := f) (r := r) c → ℂ :=
  embedding c *ᵥ (fun q => ψ q.1 * ρ q.2)

theorem encode_ne_zero (ψ : Modes (f := f) → ℂ) (hψ : ψ ≠ 0)
    (ρ : r → ℂ) (hρ : ρ ≠ 0) : encode c ψ ρ ≠ 0 := by
  intro he
  have hr := congrArg (fun v => (embedding c)ᴴ *ᵥ v) he
  simp only [encode, mulVec_mulVec, isometry, one_mulVec, mulVec_zero] at hr
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hψ
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hρ
  exact (mul_ne_zero hi hj) (congrFun hr (i,j))

theorem encoded_eigenstate (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (E : ℂ)
    (ψ : Modes (f := f) → ℂ) (ρ : r → ℂ) (he : WallExchange.H (momentum k) δ Y *ᵥ ψ = E • ψ) :
    generator c p k δ Y *ᵥ encode c ψ ρ = E • encode c ψ ρ := by
  rw [encode, mulVec_mulVec, (observed c p hp hp1 k δ Y).1, ← mulVec_mulVec]
  have hh : (WallExchange.H (momentum k) δ Y ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ
      (fun q => ψ q.1 * ρ q.2) = E • (fun q => ψ q.1 * ρ q.2) := by
    ext ⟨i,j⟩
    rw [GaugeRecordEmbedding.tensor_packet, one_mulVec, he]
    simp [mul_assoc]
  rw [hh, mulVec_smul]

theorem light_state_realized (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (hY : Y.IsHermitian) (j : f)
    (hj : hY.eigenvalues j ≠ 0)
    (hM : 0 < WallDispersion.msq3 (momentum k) + WallDispersion.massSqM δ (hY.eigenvalues j))
    (ρ : r → ℂ) (hρ : ρ ≠ 0) :
    ∃ v : Config (f := f) (r := r) c → ℂ, v ≠ 0 ∧ generator c p k δ Y *ᵥ v =
      (Real.sqrt (WallDispersion.msq3 (momentum k) + WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) • v := by
  obtain ⟨ψ,hψ,he⟩ := FlavourWallReduction.hermitian_light_state (momentum k) δ Y hY j hj hM
  exact ⟨encode c ψ ρ, encode_ne_zero c ψ hψ ρ hρ,
    encoded_eigenstate c p hp hp1 k δ Y _ ψ ρ he⟩

omit [DecidableEq f] [DecidableEq r] in
theorem register_count : Fintype.card (Labels (f := f) c ⊕ r) =
    16 * Fintype.card f + Fintype.card r := by
  simp [Labels, CarrierEvents.carrier_card]
  omega

end PMFlavor.NativeFlavourWall
