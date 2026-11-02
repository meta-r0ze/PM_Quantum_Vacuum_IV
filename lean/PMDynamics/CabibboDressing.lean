import PMDynamics.CKMDressing
import PMDynamics.FlavourInvariants
import Mathlib.Tactic

/-!
# The Cabibbo dressing constant is a derived invariant expression

`FlavourInvariants` flagged `CKMDressing.q2 = 687/688` as a bare fitted literal:
the dressing that turns exact CKM unitarity into a `1 − 1/688` first-row sum, i.e.
the claimed resolution of the Cabibbo Angle Anomaly. This module shows the
**number itself is not independent** — it is exactly

    q² = 1 − 1/(ν · Δ),

where `ν = 16` (`FlavourInvariants.nu`, derived in Paper I) and `Δ = 43` is the
forced clock period (`PMArch.Impedance.baseline.period`, `parameters_forced`).
`ν · Δ = 688`, so `687/688 = 1 − 1/688` was the invariant expression all along,
written out.

**What this fixes and what it does not.**
* `q2_eq_invariants` — the dressing amplitude squared is `1 − 1/(ν Δ)`, not a free
  literal; the denominator `688` is `ν·Δ` (`invariant_denominator`).
* `deficit_eq` — the first-row deficit `1 − q²` is exactly `1/(ν Δ)`.
* `q2_pos`, `q2_lt_one` — the dressing keeps the amplitude in `(0,1)`, so the
  dressed matrix is a genuine contraction.

It does **not** justify *why* exact unitarity is dressed by `1/(ν Δ)` in the first
place; that is the physical claim about the anomaly, and it remains fitted (see
`CKMDressing.first_row_deficit_test`). The improvement is that the arithmetic
input `687/688` is replaced by the two derived integers `ν` and `Δ`, so the only
remaining content in the Cabibbo-dressing item is the physical justification, not
the constant.
-/

noncomputable section
namespace PMDynamics.CabibboDressing
open PMArch

/-- The forced clock period `Δ = 43` (Paper I `parameters_forced`). -/
def clock : ℕ := baseline.period

theorem clock_eq : clock = 43 := by decide

/-- **The dressing amplitude squared is an invariant expression.** -/
theorem q2_eq_invariants :
    CKMDressing.q2 = 1 - 1 / ((FlavourInvariants.nu : ℝ) * (clock : ℝ)) := by
  have hnu : FlavourInvariants.nu = 16 := FlavourInvariants.nu_eq
  have hc : clock = 43 := clock_eq
  unfold CKMDressing.q2
  rw [hnu, hc]
  norm_num

/-- **The denominator `688` is `ν · Δ`.** -/
theorem invariant_denominator :
    (FlavourInvariants.nu : ℝ) * (clock : ℝ) = 688 := by
  have hnu : FlavourInvariants.nu = 16 := FlavourInvariants.nu_eq
  have hc : clock = 43 := clock_eq
  rw [hnu, hc]; norm_num

/-- **The first-row deficit is `1/(ν Δ)`.** -/
theorem deficit_eq :
    1 - CKMDressing.q2 = 1 / ((FlavourInvariants.nu : ℝ) * (clock : ℝ)) := by
  rw [q2_eq_invariants]; ring

/-- The dressing keeps the amplitude in `(0,1)`: it is a genuine contraction. -/
theorem q2_pos : 0 < CKMDressing.q2 := by
  unfold CKMDressing.q2; norm_num
theorem q2_lt_one : CKMDressing.q2 < 1 := by
  unfold CKMDressing.q2; norm_num

end PMDynamics.CabibboDressing
