import PMDynamics.WallSpectrumLink

/-! Exact sine-momentum specialization of the wall Hamiltonian and branch
phase bridge. This does not identify a finite-tick update with its Hamiltonian
exponential, nor select detuning, link strengths or physical branch access. -/
noncomputable section
namespace PMDynamics.WallLatticeSpectrum
open Matrix PMAction PMAction.WallDispersion

def latticeMomentum (k : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => Real.sin (k j)

lemma kinetic_identification (k : Fin 3 → ℝ) :
    WallExchange.K (latticeMomentum k)=DomainWallSpectrum.momentum ConcreteFermion.alpha k := by
  ext i j
  simp [WallExchange.K,latticeMomentum,DomainWallSpectrum.momentum,Fin.sum_univ_three]

lemma hop_identification : WallExchange.hop=
    DomainWallSpectrum.hop ConcreteFermion.beta ConcreteFermion.gamma := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [WallExchange.hop,DomainWallSpectrum.hop,DomainWallSpectrum.plus,
      ConcreteFermion.beta,ConcreteFermion.gamma,mul_apply,vecMul,dotProduct,Fin.sum_univ_four]

lemma back_identification : WallExchange.back=
    DomainWallSpectrum.back ConcreteFermion.beta ConcreteFermion.gamma := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [WallExchange.back,DomainWallSpectrum.back,DomainWallSpectrum.minus,
      ConcreteFermion.beta,ConcreteFermion.gamma,mul_apply,vecMul,dotProduct,Fin.sum_univ_four]

/-- This is exactly the chosen concrete two-wall Hamiltonian, not just a
Hamiltonian with a similar dispersion relation. -/
theorem concrete_hamiltonian (k : Fin 3 → ℝ) (δ : ℝ) :
    Hy (latticeMomentum k) δ 1=ConcreteFermion.hamiltonian k δ := by
  simp only [Hy,ConcreteFermion.hamiltonian,DomainWallSpectrum.H,WallExchange.diag,
    kinetic_identification,hop_identification,back_identification,Complex.ofReal_one,one_smul]
  congr 1

/-- The exact one-flavour theorem applies at every lattice momentum for
which the light energy is positive. Its cardinality is a projector trace. -/
theorem lattice_branches (k : Fin 3 → ℝ) (δ y : ℝ) (hy : y ≠ 0)
    (hM : 0<msq3 (latticeMomentum k)+massSqM δ y) :
    (∀ σ : ℂ, σ*σ=1 →
      Hy (latticeMomentum k) δ y * R (latticeMomentum k) δ y (rhoP δ y) (rhoM δ y) σ=
        (σ*(Real.sqrt (msq3 (latticeMomentum k)+massSqP δ y) : ℂ)) •
          R (latticeMomentum k) δ y (rhoP δ y) (rhoM δ y) σ ∧
      (R (latticeMomentum k) δ y (rhoP δ y) (rhoM δ y) σ).trace=2) ∧
    (∀ σ : ℂ, σ*σ=1 →
      Hy (latticeMomentum k) δ y * R (latticeMomentum k) δ y (rhoM δ y) (rhoP δ y) σ=
        (σ*(Real.sqrt (msq3 (latticeMomentum k)+massSqM δ y) : ℂ)) •
          R (latticeMomentum k) δ y (rhoM δ y) (rhoP δ y) σ ∧
      (R (latticeMomentum k) δ y (rhoM δ y) (rhoP δ y) σ).trace=2) :=
  two_dirac_particles (latticeMomentum k) δ y hy hM

/-- At collinear lattice momentum, the exact mass-squared half-phase error
uses sin(p), not p. The domain sin(p)>0 is explicit. -/
theorem lattice_half_phase_error (p δ yi yj t : ℝ) (hi : yi ≠ 0) (hj : yj ≠ 0)
    (hp : 0<Real.sin p) :
    |t*(Eb ![Real.sin p,0,0] δ (rhoM δ yi)-Eb ![Real.sin p,0,0] δ (rhoM δ yj))/2-
      t*(massSqM δ yi-massSqM δ yj)/(4*Real.sin p)| ≤
      |t| *(massSqM δ yi^2+massSqM δ yj^2)/(16*(Real.sin p)^3) := by
  rw [(WallSpectrumLink.wall_energies (Real.sin p) δ yi hi).2,
    (WallSpectrumLink.wall_energies (Real.sin p) δ yj hj).2]
  have hmi := (branch_masses δ yi hi).2.2.2
  have hmj := (branch_masses δ yj hj).2.2.2
  convert RelativisticPhase.half_phase_error (Real.sin p)
    (Real.sqrt (massSqM δ yi)) (Real.sqrt (massSqM δ yj)) t hp using 1 <;>
    simp only [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt hmi,Real.sq_sqrt hmj]

end PMDynamics.WallLatticeSpectrum
