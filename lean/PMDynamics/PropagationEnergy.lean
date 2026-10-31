import PMAction.DiracEnergy
import PMDynamics.RelativisticPhase
import PMDynamics.OscillationObservables
import PMDynamics.CPObservables

/-! Reuse Paper II's eigenstate energy-shell theorem, then control the usual
mass-squared phase approximation. The chosen first-order Hamiltonian, nonzero
positive-branch eigenstates, common momentum and masses are supplied. This does
not identify the full finite-tick two-wall dispersion or choose neutrino masses. -/
noncomputable section
namespace PMDynamics.PropagationEnergy
open Matrix
open PMAction

/-- For collinear momentum, the exact energy is the scalar relativistic law. -/
theorem collinear_energy (p m : ℝ) :
    DiracEnergy.positiveEnergy ![p,0,0] m=RelativisticPhase.energy p m := by
  simp [DiracEnergy.positiveEnergy,DiracEnergy.momentumSq,RelativisticPhase.energy]

/-- The required positive-branch spinors exist for each supplied mass and
positive common momentum. This is mathematical existence, not preparation or
identification of the substrate's physical one-particle states. -/
theorem positive_family_exists (p : ℝ) (hp : 0<p) (m : Fin 3 → ℝ) :
    ∃ v : Fin 3 → Fin 4 → ℂ, ∀ i, v i ≠ 0 ∧
      Dirac.H ConcreteFermion.alpha ConcreteFermion.beta ![p,0,0] (m i) *ᵥ v i=
        RelativisticPhase.energy p (m i) • v i := by
  have h (i : Fin 3) := DiracEnergy.concrete_positive_state_exists ![p,0,0] (m i)
    (by simp [DiracEnergy.momentumSq]; positivity)
  refine ⟨fun i => Classical.choose (h i), fun i => ?_⟩
  have hi := Classical.choose_spec (h i)
  simpa only [collinear_energy] using hi

/-- A supplied family of actual eigenstates fixes its three energies by the
already checked Paper II Clifford representation. Masses themselves stay free. -/
theorem eigenstate_energies (p : ℝ) (m E : Fin 3 → ℝ) (v : Fin 3 → Fin 4 → ℂ)
    (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, Dirac.H ConcreteFermion.alpha ConcreteFermion.beta ![p,0,0] (m i) *ᵥ v i=E i • v i)
    (hE : ∀ i, 0 ≤ E i) : E=fun i => RelativisticPhase.energy p (m i) := by
  funext i
  rw [← collinear_energy]
  exact DiracEnergy.concrete_positive_branch _ _ _ _ (hv i) (he i) (hE i)

/-- The finite flavour probability can use those exact, spectrally determined
energies, conditional on the supplied family of external eigenstates. -/
theorem eigenstate_probability (U : OscillationObservables.M) (p t : ℝ)
    (m E : Fin 3 → ℝ) (v : Fin 3 → Fin 4 → ℂ) (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, Dirac.H ConcreteFermion.alpha ConcreteFermion.beta ![p,0,0] (m i) *ᵥ v i=E i • v i)
    (hE : ∀ i, 0 ≤ E i) (a b : Fin 3) :
    FlavourEvolution.probability U E t a b=
      FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b := by
  rw [eigenstate_energies p m E v hv he hE]

/-- The common momentum contributes no probability change. This removes an
exact common phase before making any approximation. -/
theorem momentum_offset (U : OscillationObservables.M) (p t : ℝ) (m : Fin 3 → ℝ) (a b : Fin 3) :
    FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b=
      FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)-p) t a b := by
  have h := OscillationObservables.energy_shift U
    (fun i => RelativisticPhase.energy p (m i)-p) p t a b
  simpa only [sub_add_cancel] using h

/-- Controlled half-phase for the supplied on-shell eigenstates. It does not
calibrate t as a baseline, choose m, or assert a probability-error bound. -/
theorem eigenstate_half_phase_error (p t : ℝ) (hp : 0<p)
    (m E : Fin 3 → ℝ) (v : Fin 3 → Fin 4 → ℂ) (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, Dirac.H ConcreteFermion.alpha ConcreteFermion.beta ![p,0,0] (m i) *ᵥ v i=E i • v i)
    (hE : ∀ i, 0 ≤ E i) (i j : Fin 3) :
    |t*(E i-E j)/2-t*(m i^2-m j^2)/(4*p)| ≤
      |t| *(m i^4+m j^4)/(16*p^3) := by
  rw [eigenstate_energies p m E v hv he hE]
  exact RelativisticPhase.half_phase_error p (m i) (m j) t hp

/-- Combine the on-shell energy law with the exact CP result: an equal
mass-squared pair removes the vacuum asymmetry at common momentum. -/
theorem degenerate_mass_pair_no_asymmetry (U : OscillationObservables.M) (hU : U*Uᴴ=1)
    (p t : ℝ) (m : Fin 3 → ℝ) (a b : Fin 3)
    (hm : m 0^2=m 1^2 ∨ m 1^2=m 2^2 ∨ m 0^2=m 2^2) :
    FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b=
      FlavourEvolution.probability (OscillationObservables.conjugated U)
        (fun i => RelativisticPhase.energy p (m i)) t a b := by
  apply CPObservables.degenerate_pair_no_asymmetry U hU _ t a b
  rcases hm with hm | hm | hm
  · left
    simp only [RelativisticPhase.energy,hm]
  · right; left
    simp only [RelativisticPhase.energy,hm]
  · right; right
    simp only [RelativisticPhase.energy,hm]

end PMDynamics.PropagationEnergy
