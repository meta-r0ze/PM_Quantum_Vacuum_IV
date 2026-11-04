import PMFlavor.TransferWorkLaw
import PMFlavor.RelativeFrameCost
import Mathlib.Tactic

/-!
# Any actual transfer costs strictly positive work

`TransferWorkLaw` proved the total weight `W` is **not selected** by minimization:
`zero_weight_minimum` shows zero transfer is a free minimum, and
`weight_not_selected` shows the price is blind to the sign of the amplitude. That
left the "mixing amount" open. This module adds the one half that *is* forced: the
required work is strictly positive for **any** nonzero transfer, so the zero-flux
minimum is isolated and a positive transfer can never be free.

* `workPrice_pos_of_transfer` — if the smallest gap has a positive lower bound `g`
  and the frame carries positive total weight, the price is `> 0`. This is
  `min_cost_is_min_gap` sharpened: `price ≥ g·W/12` with both factors positive.
* `plane_price_pos` — concretely, a plane rotation through a nonzero angle at a
  nondegenerate pair has strictly positive price (`gap·s²/6 > 0`).
* `zero_is_only_free_route` — the price vanishes **iff** the total weight does, so
  the free route is exactly no transfer.

So the mixing amount still needs an external update rule to fix its value, but the
framework is not vacuous: a required positive transfer forces a positive work bill,
and only the trivial (no-transfer) policy is free.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.TransferAmount
open Matrix RelativeFrameCost TransferWorkLaw

/-- **Any transfer with a positive minimal gap costs positive work.** -/
theorem workPrice_pos_of_transfer (phase : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (g : ℝ)
    (hg : 0 < g) (h01 : g ≤ gap phase 0 1) (h02 : g ≤ gap phase 0 2)
    (h12 : g ≤ gap phase 1 2) (hW : 0 < totalWeight B) :
    0 < workPrice phase B := by
  have h := min_cost_is_min_gap phase B g h01 h02 h12
  have hgt : 0 < g * totalWeight B / 12 := by positivity
  linarith

/-- **A nonzero plane rotation at a nondegenerate pair has strictly positive
price.** Concretely `gap·s²/6`, with `gap > 0` and `s ≠ 0`. -/
theorem plane_price_pos (phase : Fin 3 → ℂ) (c s : ℝ)
    (hgap : 0 < gap phase 0 1) (hs : s ≠ 0) :
    0 < frameCost (diagonal phase) (rot01 c s) := by
  rw [plane_cost01]
  have hs2 : 0 < s ^ 2 := by positivity
  have : 0 < gap phase 0 1 * s ^ 2 := mul_pos hgap hs2
  positivity

/-- **The price vanishes iff the frame carries no transfer.** The free route is
exactly the zero-weight policy, so `zero_weight_minimum` is isolated. -/
theorem zero_is_only_free_route (phase : Fin 3 → ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (g : ℝ)
    (hg : 0 < g) (h01 : g ≤ gap phase 0 1) (h02 : g ≤ gap phase 0 2)
    (h12 : g ≤ gap phase 1 2) :
    workPrice phase B = 0 ↔ totalWeight B ≤ 0 := by
  constructor
  · intro hz
    by_contra hpos
    have hW : 0 < totalWeight B := lt_of_not_ge hpos
    have := workPrice_pos_of_transfer phase B g hg h01 h02 h12 hW
    linarith
  · intro hle
    have hw : totalWeight B ≤ 0 := hle
    have hnn : 0 ≤ totalWeight B := by
      show 0 ≤ pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2
      have a := pairWeight_nonneg B 0 1
      have b := pairWeight_nonneg B 0 2
      have c := pairWeight_nonneg B 1 2
      linarith
    have hzero : totalWeight B = 0 := le_antisymm hw hnn
    have ht : totalWeight B = pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2 := rfl
    have hpw : pairWeight B 0 1 = 0 ∧ pairWeight B 0 2 = 0 ∧ pairWeight B 1 2 = 0 := by
      refine ⟨?_, ?_, ?_⟩ <;>
        nlinarith [pairWeight_nonneg B 0 1, pairWeight_nonneg B 0 2, pairWeight_nonneg B 1 2]
    have hkey := workPrice_sum phase B
    rw [hpw.1, hpw.2.1, hpw.2.2] at hkey
    linarith

end PMFlavor.TransferAmount
