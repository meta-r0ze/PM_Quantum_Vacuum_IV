import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The variational obligation behind a positive flavour-transfer rate

Paper IV writes the dissipation density as impedance × mismatch × flux.
For fixed positive impedance and mismatch this is strictly increasing in flux.
It does not select a positive admittance by unconstrained minimization. With a
required-work/period constraint it selects the least permitted throughput.
Deriving that work from a physical update, and relating flux to an amplitude,
are separate obligations. The squared-amplitude version has the same zero-flux
unconstrained minimum. No particular flavour ratio is postulated here.
-/
namespace PMDynamics.TransitionSelection

def dissipation (impedance mismatch flux : ℝ) : ℝ := impedance * mismatch * flux

theorem strict_flux (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    StrictMono (dissipation c K) := by
  intro f g h
  exact mul_lt_mul_of_pos_left h (mul_pos hc hK)

theorem minimum_at_required_flux (c K required f : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hf : required ≤ f) :
    dissipation c K required ≤ dissipation c K f ∧
      (dissipation c K f = dissipation c K required ↔ f = required) := by
  have hs := strict_flux c K hc hK
  exact ⟨hs.monotone hf, hs.injective.eq_iff⟩

theorem zero_flux_minimum (c K f : ℝ) (hc : 0 < c) (hK : 0 < K) (hf : 0 ≤ f) :
    0 ≤ dissipation c K f ∧ (dissipation c K f = 0 ↔ f = 0) := by
  simpa only [dissipation, mul_zero] using minimum_at_required_flux c K 0 f hc hK hf

/-- The proposed admittance ratio is positive and costs more than zero flux;
an independent workload constraint is needed to make it optimal. -/
theorem admittance_not_unconstrained_minimum (c K : ℝ) (hc : 0 < c) (hK : 0 < K) :
    dissipation c K 0 < dissipation c K (K/c) :=
  strict_flux c K hc hK (div_pos hK hc)

theorem required_work_optimum (c K work period f : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hperiod : 0 < period) (hwork : work ≤ period*f) :
    dissipation c K (work/period) ≤ dissipation c K f ∧
      (dissipation c K f = dissipation c K (work/period) ↔ f = work/period) := by
  exact minimum_at_required_flux c K _ f hc hK ((div_le_iff₀ hperiod).mpr (by nlinarith [hwork]))

/-- Using a squared amplitude instead of flux cannot supply a nonzero optimum. -/
theorem amplitude_zero_minimum (c K a : ℝ) (hc : 0 < c) (hK : 0 < K) :
    0 ≤ dissipation c K (a^2) ∧ (dissipation c K (a^2) = 0 ↔ a = 0) := by
  simpa only [sq_eq_zero_iff] using zero_flux_minimum c K (a^2) hc hK (sq_nonneg a)

end PMDynamics.TransitionSelection
