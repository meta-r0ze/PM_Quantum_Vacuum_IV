import PMFlavor.NativeFlavourWall
import PMFlavor.FlavourEvolution
import PMAction.IsometricDynamics

/-!
# Flavour propagation in prepared eigenmodes of the native wall generator

Columns are actual wall eigenmodes, encoded by `NativeFlavourWall`. Their
orthonormality and a unit record amplitude make an isometric preparation.
The full native generator then gives exactly the existing flavour evolution
and probabilities in any supplied unitary flavour basis. Energies must be the
prepared eigenenergies: no extra additive flavour Hamiltonian is introduced.
Selecting/preparing this subspace, its masses/mixing and its physical clock
remains an application contract.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.NativeFlavourPropagation
open Matrix PMAction NativeFlavourWall
variable (c : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

def preparation (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) :
    Matrix (Modes (f := f) × r) (Fin 3) ℂ := fun q j => Ψ q.1 j * ρ q.2

def packet (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) :
    Matrix (Config (f := f) (r := r) c) (Fin 3) ℂ := embedding c * preparation Ψ ρ

omit [DecidableEq f] [DecidableEq r] in
theorem preparation_isometry (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
    (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1) :
    (preparation Ψ ρ)ᴴ * preparation Ψ ρ = 1 := by
  ext i j
  have he : ((preparation Ψ ρ)ᴴ * preparation Ψ ρ) i j =
      (Ψᴴ * Ψ) i j * (∑ k, star (ρ k) * ρ k) := by
    simp only [Matrix.mul_apply, conjTranspose_apply, preparation, Fintype.sum_prod_type,
      star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he, hΨ, hρ, mul_one]

theorem packet_isometry (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
    (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1) :
    (packet c Ψ ρ)ᴴ * packet c Ψ ρ = 1 :=
  NativeObservation.compose_isometry _ _ (NativeFlavourWall.isometry c)
    (preparation_isometry Ψ ρ hΨ hρ)

theorem packet_intertwining (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) (E : Fin 3 → ℝ)
    (he : ∀ j, WallExchange.H (momentum k) δ Y *ᵥ (fun x => Ψ x j) = (E j : ℂ) • (fun x => Ψ x j)) :
    generator c p k δ Y * packet c Ψ ρ = packet c Ψ ρ * MassMixing.eigenMass E := by
  ext q j
  have hh := encoded_eigenstate c p hp hp1 k δ Y (E j) (fun x => Ψ x j) ρ (he j)
  have hcol : (fun x => packet c Ψ ρ x j) = encode c (fun x => Ψ x j) ρ := rfl
  change (generator c p k δ Y *ᵥ (fun x => packet c Ψ ρ x j)) q = _
  rw [hcol, hh]
  simp only [MassMixing.eigenMass, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [← congrFun hcol q, mul_comm]

def frame (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) (U : FlavourCurrent.M) :=
  packet c Ψ ρ * Uᴴ

theorem frame_isometry (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
    (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
    (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) : (frame c Ψ ρ U)ᴴ * frame c Ψ ρ U = 1 := by
  simp only [frame, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (packet c Ψ ρ)ᴴ (packet c Ψ ρ),
    packet_isometry c Ψ ρ hΨ hρ, one_mul, hU]

def evolve (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ) (t : ℝ) : Matrix (Config (f := f) (r := r) c) (Config (f := f) (r := r) c) ℂ :=
  NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • generator c p k δ Y)


section Dynamics
variable (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ)
  (Y : Matrix f f ℂ) (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
  (E : Fin 3 → ℝ)
  (he : ∀ j, WallExchange.H (momentum k) δ Y *ᵥ (fun x => Ψ x j) = (E j : ℂ) • (fun x => Ψ x j))
include hp hp1 he

theorem frame_intertwining (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) :
    generator c p k δ Y * frame c Ψ ρ U = frame c Ψ ρ U * MassMixing.mass U E := by
  have h := packet_intertwining c p hp hp1 k δ Y Ψ ρ E he
  have hl : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [frame, MassMixing.mass]
  rw [← Matrix.mul_assoc, h]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hl, one_mul]


theorem evolution_intertwining (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) :
    evolve (r := r) c p k δ Y t * frame c Ψ ρ U = frame c Ψ ρ U * FlavourEvolution.evolution U E t := by
  have h := RectangularEvolution.scaled (generator c p k δ Y) (MassMixing.mass U E)
    (frame c Ψ ρ U) (frame_intertwining c p hp hp1 k δ Y Ψ ρ E he U hU)
    (((-t : ℝ) : ℂ) * Complex.I)
  rwa [← FlavourEvolution.equals_exponential U E hU t] at h

theorem compressed_evolution (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
    (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) :
    (frame c Ψ ρ U)ᴴ * evolve (r := r) c p k δ Y t * frame c Ψ ρ U = FlavourEvolution.evolution U E t := by
  rw [Matrix.mul_assoc, evolution_intertwining c p hp hp1 k δ Y Ψ ρ E he U hU t,
    ← Matrix.mul_assoc, frame_isometry c Ψ ρ hΨ hρ U hU, one_mul]

theorem probability_eq (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
    (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) (a b : Fin 3) :
    Complex.normSq (((frame c Ψ ρ U)ᴴ * evolve (r := r) c p k δ Y t * frame c Ψ ρ U) a b) =
      FlavourEvolution.probability U E t a b := by
  rw [compressed_evolution c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU t]
  rfl

theorem total_probability (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
    (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) (b : Fin 3) :
    ∑ a, Complex.normSq (((frame c Ψ ρ U)ᴴ * evolve (r := r) c p k δ Y t * frame c Ψ ρ U) a b) = 1 := by
  simp_rw [probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU t]
  exact FlavourEvolution.total_probability U E hU t b

/-- Exact finite samples of this specified native exponential, with the supplied tick. -/
theorem tick_intertwining (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (τ : ℝ) (m : ℕ) :
    (evolve (r := r) c p k δ Y τ)^m * frame c Ψ ρ U =
      frame c Ψ ρ U * FlavourEvolution.evolution U E ((m : ℝ) * τ) := by
  induction m with
  | zero => simp [FlavourEvolution.zero U E hU]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_assoc, evolution_intertwining c p hp hp1 k δ Y Ψ ρ E he U hU τ,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc, FlavourEvolution.composition U E hU]
    have ht : ((m+1 : ℕ) : ℝ) * τ = (m : ℝ) * τ + τ := by push_cast; ring
    rw [ht]

theorem compressed_ticks (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
    (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (τ : ℝ) (m : ℕ) :
    (frame c Ψ ρ U)ᴴ * (evolve (r := r) c p k δ Y τ)^m * frame c Ψ ρ U =
      FlavourEvolution.evolution U E ((m : ℝ) * τ) := by
  rw [Matrix.mul_assoc, tick_intertwining c p hp hp1 k δ Y Ψ ρ E he U hU τ m,
    ← Matrix.mul_assoc, frame_isometry c Ψ ρ hΨ hρ U hU, one_mul]

end Dynamics
end PMFlavor.NativeFlavourPropagation
