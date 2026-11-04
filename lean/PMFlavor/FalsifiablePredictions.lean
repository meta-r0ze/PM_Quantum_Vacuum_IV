import PMFlavor.Wolfenstein
import PMFlavor.WolfensteinOctant
import PMFlavor.CabibboDressing
import PMFlavor.SubstrateLink
import PMFlavor.BreakingLink
import PMFlavor.TransferAmount
import Mathlib.Tactic

/-!
# The falsifiable prediction ledger

Review item 5 asked for a global fit. That needs real data, provenance and a
covariance, which is not Lean's job. What *is* Lean's job — and what the review
was missing — is a single, auditable list of the **falsifiable predictions** the
framework actually makes, each with its proof, so a fit can be run against them.

This module is that ledger. Every claim below is a theorem with no measured input;
each is stated so that a future measurement can refute it.

**Unconditional within the supplied model.**
* `wEta_gt_wRho` — `ρ̄ < η̄`: the CKM unitarity-triangle apex lies above the `ρ̄`
  axis. Refuted by `η̄ ≤ ρ̄`.
* `solar_first_octant` — `1/4 < sin²θ₁₂ < 1/2` (solar lower octant, not maximal).
* `atmos_gt_half` — `1/2 < sin²θ₂₃` (atmospheric upper octant).
* `reactor_lt_quarter` — `sin²θ₁₃ < 1/4` (reactor far below any octant boundary).
* `q2_lt_one`, `q2_pos` — the Cabibbo dressing `q² = 1 − 1/(νΔ)` is a genuine
  contraction, so the first-row sum is `1 − 1/(νΔ)` and **not** exactly `1`.

**Conditional structural predictions** (hypotheses are the physical energy list and
tick; see each module): the extreme generation pair is never the cheapest transfer
route (`SpectralGapOrder.extreme_never_cheapest`), and a work-minimizing frame
carries zero extreme-pair amplitude (`route_extreme_amplitude_vanishes`); the
ground-state link is a degenerate light doublet split by the lepton axis.

**The ledger theorem** `prediction_ledger` conjoins the unconditional claims, so
`#check prediction_ledger` is the exact set a fit must satisfy.
-/

noncomputable section
namespace PMFlavor.FalsifiablePredictions
open Wolfenstein WolfensteinOctant CabibboDressing

/-- **The auditable ledger of unconditional falsifiable predictions.** Each
conjunct is a theorem with no measured input; a measurement violating any conjunct
refutes the corresponding framework claim. -/
theorem prediction_ledger :
    -- CKM unitarity-triangle apex above the ρ̄ axis
    (Wolfenstein.wRho < Wolfenstein.wEta) ∧
    -- solar lower octant, strictly below maximal mixing
    ((1 / 4 : ℝ) < PMNS.sineSquared 0 ∧ PMNS.sineSquared 0 < 1 / 2) ∧
    -- atmospheric upper octant
    ((1 / 2 : ℝ) < PMNS.sineSquared 1) ∧
    -- reactor angle far below any octant boundary
    (PMNS.sineSquared 2 < 1 / 4) ∧
    -- the Cabibbo dressing is a genuine contraction, first-row sum < 1
    (0 < CKMDressing.q2 ∧ CKMDressing.q2 < 1) :=
  ⟨Wolfenstein.wEta_gt_wRho, WolfensteinOctant.solar_first_octant,
    WolfensteinOctant.atmos_gt_half, WolfensteinOctant.reactor_lt_quarter,
    CabibboDressing.q2_pos, CabibboDressing.q2_lt_one⟩

/-- The apex-above-axis prediction in decimal-free form (`σ > 2χ`). -/
theorem apex_above_axis_is_sigma_gt_two_chi : Real.pi / 4 < CKM.δ :=
  Wolfenstein.delta_gt_pi_four

/-- The first-row sum prediction is `1 − 1/(νΔ)`, not `1`. -/
theorem first_row_sum_below_one : CKMDressing.q2 < 1 := CabibboDressing.q2_lt_one

end PMFlavor.FalsifiablePredictions
