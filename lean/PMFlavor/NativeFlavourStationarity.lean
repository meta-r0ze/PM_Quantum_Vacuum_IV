import PMFlavor.NativeFlavourPropagation
import PMFlavor.FlavourStationarity

/-!
# The reference stationarity residual on actual configuration amplitudes

For an orthonormal prepared family of actual wall eigenmodes, the complete
configuration-space residual is exactly the existing flavour residual. Its
variance, gap lower bound and full-support PMNS obstruction therefore hold
before readout as well. No residual is declared a priced physical workload;
the prepared family, physical reference identification and link remain inputs.
-/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.NativeFlavourStationarity
open Matrix PMAction NativeFlavourWall NativeFlavourPropagation
variable (c : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

def residual (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
    (U : FlavourCurrent.M) (a : Fin 3) (ω : ℝ) : ℝ :=
  ∑ q : Config (f := f) (r := r) c,
    Complex.normSq ((generator c p k δ Y *ᵥ (frame c Ψ ρ U *ᵥ Pi.single a 1) -
      (ω : ℂ) • (frame c Ψ ρ U *ᵥ Pi.single a 1)) q)

def rayPersists (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) (v : Fin 3 → ℂ) : Prop :=
  ∀ t : ℝ, ∃ z : ℂ, evolve (r := r) c p k δ Y t *ᵥ (packet c Ψ ρ *ᵥ v) =
    z • (packet c Ψ ρ *ᵥ v)

private theorem diagonal_phase (E : Fin 3 → ℝ) (t : ℝ) (v : Fin 3 → ℂ) :
    FlavourEvolution.evolution 1 E t *ᵥ v =
      fun i => v i * Complex.exp (-((E i*t : ℝ) : ℂ) * Complex.I) := by
  ext i
  simp only [FlavourEvolution.evolution, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
    LinkExpansion.phaseDiag, Matrix.mulVec_diagonal]
  have hs : (((-t * E i : ℝ) : ℂ) * Complex.I) = -((E i*t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hs, mul_comm]

variable (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ)
  (Y : Matrix f f ℂ) (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
  (E : Fin 3 → ℝ)
  (he : ∀ j, WallExchange.H (momentum k) δ Y *ᵥ (fun x => Ψ x j) = (E j : ℂ) • (fun x => Ψ x j))
  (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
include hp hp1 he hΨ hρ

private theorem one_step_ray_iff (v : Fin 3 → ℂ) (t : ℝ) :
    (∃ z : ℂ, evolve (r := r) c p k δ Y t *ᵥ (packet c Ψ ρ *ᵥ v) = z • (packet c Ψ ρ *ᵥ v)) ↔
    ∃ z : ℂ, ∀ i, v i * Complex.exp (-((E i*t : ℝ) : ℂ) * Complex.I) = z * v i := by
  have hm : evolve (r := r) c p k δ Y t * packet c Ψ ρ =
      packet c Ψ ρ * FlavourEvolution.evolution 1 E t := by
    simpa [frame] using evolution_intertwining c p hp hp1 k δ Y Ψ ρ E he 1 (by simp) t
  have hinj : Function.Injective (fun w => packet c Ψ ρ *ᵥ w) := by
    intro v w h
    have hh := congrArg (fun z => (packet c Ψ ρ)ᴴ *ᵥ z) h
    simpa only [mulVec_mulVec, packet_isometry c Ψ ρ hΨ hρ, one_mulVec] using hh
  have hs : evolve (r := r) c p k δ Y t *ᵥ (packet c Ψ ρ *ᵥ v) =
      packet c Ψ ρ *ᵥ (FlavourEvolution.evolution 1 E t *ᵥ v) := by
    rw [mulVec_mulVec, hm, ← mulVec_mulVec]
  constructor
  · rintro ⟨z,hz⟩
    have hh : FlavourEvolution.evolution 1 E t *ᵥ v = z • v := by
      apply hinj
      change packet c Ψ ρ *ᵥ (FlavourEvolution.evolution 1 E t *ᵥ v) = packet c Ψ ρ *ᵥ (z • v)
      rw [← hs, mulVec_smul]
      exact hz
    refine ⟨z,?_⟩
    intro i
    simpa only [diagonal_phase, Pi.smul_apply, smul_eq_mul] using congrFun hh i
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hh : FlavourEvolution.evolution 1 E t *ᵥ v = z • v := by
      rw [diagonal_phase]
      exact funext hz
    rw [hs, hh, mulVec_smul]

theorem ray_iff_diagonal (v : Fin 3 → ℂ) :
    rayPersists c p k δ Y Ψ ρ v ↔ ReferenceSpectrum.Persists E v := by
  unfold rayPersists
  simp_rw [one_step_ray_iff c p hp hp1 k δ Y Ψ ρ E he hΨ hρ v]
  rfl

theorem ray_iff_single_energy (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    rayPersists c p k δ Y Ψ ρ v ↔ ∃ e : ℝ, ∀ i, v i ≠ 0 → E i = e := by
  rw [ray_iff_diagonal c p hp hp1 k δ Y Ψ ρ E he hΨ hρ v]
  exact ReferenceSpectrum.persists_iff_single_energy E v hv

theorem pmns_ray_iff_constant (a : Fin 3) :
    rayPersists c p k δ Y Ψ ρ (fun i => star (PMNS.matrix a i)) ↔ ∃ e, ∀ i, E i = e := by
  rw [ray_iff_diagonal c p hp hp1 k δ Y Ψ ρ E he hΨ hρ]
  exact ReferenceSpectrum.pmns_flavour_persists_iff E a

theorem sampled_iff_of_band (v : Fin 3 → ℂ) (hv : v ≠ 0) (tick : ℝ) (ht : tick ≠ 0)
    (hband : ∀ i, v i ≠ 0 → -Real.pi ≤ E i*tick ∧ E i*tick < Real.pi) :
    (∃ z : ℂ, evolve (r := r) c p k δ Y tick *ᵥ (packet c Ψ ρ *ᵥ v) = z • (packet c Ψ ρ *ᵥ v)) ↔
      rayPersists c p k δ Y Ψ ρ v := by
  rw [one_step_ray_iff c p hp hp1 k δ Y Ψ ρ E he hΨ hρ v,
    ray_iff_diagonal c p hp hp1 k δ Y Ψ ρ E he hΨ hρ v]
  exact ReferenceSpectrum.one_tick_iff_of_band E v hv tick ht hband

theorem residual_eq (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (a : Fin 3) (ω : ℝ) :
    residual c p k δ Y Ψ ρ U a ω = FlavourStationarity.residual U E a ω := by
  let v := MassMixing.mass U E *ᵥ Pi.single a 1 - (ω : ℂ) • Pi.single a 1
  have hv : generator c p k δ Y *ᵥ (frame c Ψ ρ U *ᵥ Pi.single a 1) -
      (ω : ℂ) • (frame c Ψ ρ U *ᵥ Pi.single a 1) = frame c Ψ ρ U *ᵥ v := by
    simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      frame_intertwining c p hp hp1 k δ Y Ψ ρ E he U hU]
  have hi := frame_isometry c Ψ ρ hΨ hρ U hU
  have hn := IsometricDynamics.population (frame c Ψ ρ U) hi v
  have hs : (∑ q, Complex.normSq ((frame c Ψ ρ U *ᵥ v) q)) =
      ∑ i, Complex.normSq (v i) := by
    simpa only [CommonResponse.nsq, dotProduct, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re] using hn
  rw [residual, hv, hs]
  exact (FlavourStationarity.physical_residual U hU E a ω).symm

theorem variance_identity (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (a : Fin 3) (ω : ℝ) :
    residual c p k δ Y Ψ ρ U a ω =
      SpectralVariance.variance (FlavourStationarity.weights U a) E +
        (SpectralVariance.mean (FlavourStationarity.weights U a) E - ω)^2 := by
  rw [residual_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU]
  exact FlavourStationarity.minimum_residual U hU E a ω

theorem gap_lower_bound (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (a : Fin 3) (ω : ℝ) :
    Complex.normSq (U a 0) * Complex.normSq (U a 1) * (E 0-E 1)^2 ≤
      residual c p k δ Y Ψ ρ U a ω := by
  rw [residual_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU]
  exact FlavourStationarity.gap_lower_bound U hU E a ω

theorem pmns_zero_iff (a : Fin 3) (ω : ℝ) :
    residual c p k δ Y Ψ ρ PMNS.matrix a ω = 0 ↔ ∀ i, E i = ω := by
  rw [residual_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ PMNS.matrix PMNS.rows]
  exact FlavourStationarity.pmns_zero_iff_constant E a ω

theorem pmns_positive (hgap : E 0 ≠ E 1) (a : Fin 3) (ω : ℝ) :
    0 < residual c p k δ Y Ψ ρ PMNS.matrix a ω := by
  rw [residual_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ PMNS.matrix PMNS.rows]
  exact FlavourStationarity.pmns_residual_positive E hgap a ω

end PMFlavor.NativeFlavourStationarity
