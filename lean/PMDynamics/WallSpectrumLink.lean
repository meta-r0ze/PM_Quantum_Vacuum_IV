import PMAction.WallDispersion
import PMDynamics.RelativisticPhase

/-!
# The two-wall spectrum gives Paper IV's relativistic energies

Paper II's `WallDispersion.two_dirac_particles` shows that the eight-component one-flavour
two-wall Hamiltonian is exactly two Dirac particles. Their energies are `±√(|k|² + m±²)`, each with
two spin states, where `m₊² m₋² = δ⁴` and `m₊² + m₋² = y² + 2δ²`.

* `wall_energy_collinear`: for collinear momentum `k = (p, 0, 0)`, each branch energy is
  `RelativisticPhase.energy p m` with `m = √(m±²)`. This is the law `PropagationEnergy` uses.
* `wall_seesaw`: the light mass is `m₋² = δ⁴/m₊²`.

Still inputs: which flavour link `y` (or matrix `Y`) is physical, the identification of
accessible states, and preparation and readout. Several flavours with a Hermitian `Y` reduce to
this case eigenvalue by eigenvalue, but that reduction is not formalized here.
-/

noncomputable section
namespace PMDynamics.WallSpectrumLink
open PMAction.WallDispersion

theorem wall_energy_collinear (p δ : ℝ) (b : ℝ) (hb : 0 ≤ δ ^ 2 + b) :
    Eb ![p, 0, 0] δ b = RelativisticPhase.energy p (Real.sqrt (δ ^ 2 + b)) := by
  simp only [Eb, RelativisticPhase.energy, msq3, Real.sq_sqrt hb]
  congr 1; simp; ring

theorem wall_energies (p δ y : ℝ) (hy : y ≠ 0) :
    Eb ![p, 0, 0] δ (rhoP δ y) = RelativisticPhase.energy p (Real.sqrt (massSqP δ y)) ∧
      Eb ![p, 0, 0] δ (rhoM δ y) = RelativisticPhase.energy p (Real.sqrt (massSqM δ y)) := by
  obtain ⟨-, -, hP, hM⟩ := branch_masses δ y hy
  exact ⟨wall_energy_collinear p δ _ hP.le, wall_energy_collinear p δ _ hM⟩

theorem wall_seesaw (δ y : ℝ) (hy : y ≠ 0) : massSqM δ y = δ ^ 4 / massSqP δ y := by
  obtain ⟨h, -, hP, -⟩ := branch_masses δ y hy
  rw [eq_div_iff hP.ne', mul_comm, h]

end PMDynamics.WallSpectrumLink
