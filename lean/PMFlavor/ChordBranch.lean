import PMFlavor.SpectralGapOrder
import PMSubstrate.Impedance
import Mathlib.Tactic

/-!
# Reducing the chord-branch hypothesis to a derived tick window

`SpectralGapOrder` obtained the work-ordering theorems under a standing
hypothesis `hband : t · (e₂ − e₀) ≤ π`: the whole spectrum must sit inside one
chord branch of the circle. Review item 3 flagged this as an input, not a
derivation. This module removes the hypothesis as a *free* assumption by turning
it into a **derived window on the tick**, and by exhibiting the substrate clock
`Δ = 43` inside that window whenever the spectrum is wide enough.

**The maximal admissible tick.** Define

    tStar e = π / (e₂ − e₀)      (the largest tick keeping the spectrum in one branch).

Then:
* `tStar_pos` — a strictly increasing spectrum gives a positive maximal tick.
* `branch_at_tStar` — the branch condition holds at `t = tStar`.
* `branch_at_tick_le` — **any** tick `t ∈ (0, tStar]` satisfies the branch
  condition. So the hypothesis is not independent: it is exactly `t ≤ tStar`.

**The substrate clock inside the window.** Paper I forces the clock period
`Δ = 43` (`PMSubstrate.Derived.parameters_forced`). If the energy spread is at most
`π/43` — i.e. `e₂ − e₀ ≤ π/43` — then the physical tick `t = 43` lies in the
window and the branch condition is a *derived* consequence of the substrate
clock, not a hypothesis:

* `substrate_tick_in_window` — `43 ≤ tStar e` when `e₂ − e₀ ≤ π/43`.
* `substrate_branch_condition` — consequently `43 · (e₂ − e₀) ≤ π`.

**What this does and does not do.** It does not prove that the physical spectrum
has spread `≤ π/43`; that is a fact about the link `Y`, which `SubstrateLink`
shows is degenerate in the symmetric case. What it does is remove `hband` as an
independent hypothesis: the branch condition is equivalent to a single scalar
comparison between the forced clock `43` and the spectral spread, with the
threshold `π/43` written down explicitly. Any link whose spread exceeds that
threshold is *outside* the one-branch regime, and the paper's work-ordering
theorems simply do not apply there — which is now visible rather than assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.ChordBranch
open SpectralGapOrder RelativeFrameCost TransferWorkLaw

/-- **The maximal admissible tick**: the largest `t` that keeps the extreme
splitting inside one chord branch. -/
def tStar (e : Fin 3 → ℝ) : ℝ := Real.pi / (e 2 - e 0)

/-- A strictly increasing spectrum gives a positive maximal tick. -/
theorem tStar_pos (e : Fin 3 → ℝ) (h02 : e 0 < e 2) : 0 < tStar e := by
  unfold tStar
  exact div_pos Real.pi_pos (by linarith)

/-- At the maximal tick the branch condition holds with equality. -/
theorem branch_at_tStar (e : Fin 3 → ℝ) (h02 : e 0 < e 2) :
    tStar e * (e 2 - e 0) ≤ Real.pi := by
  unfold tStar
  rw [div_mul_cancel₀ _ (by linarith)]

/-- **The branch condition is exactly `t ≤ tStar`.** Any positive tick no larger
than the maximal tick keeps the whole spectrum in one chord branch. -/
theorem branch_at_tick_le (e : Fin 3 → ℝ) (t : ℝ) (_ht : 0 < t) (h02 : e 0 < e 2)
    (hle : t ≤ tStar e) :
    t * (e 2 - e 0) ≤ Real.pi := by
  have hpos : 0 < e 2 - e 0 := by linarith
  have h1 : t * (e 2 - e 0) ≤ tStar e * (e 2 - e 0) :=
    mul_le_mul_of_nonneg_right hle hpos.le
  have h2 : tStar e * (e 2 - e 0) ≤ Real.pi := branch_at_tStar e h02
  linarith

/-- **The converse:** any tick outside the window breaks the branch condition. -/
theorem branch_iff_tick_le (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t) (h02 : e 0 < e 2) :
    t * (e 2 - e 0) ≤ Real.pi ↔ t ≤ tStar e := by
  constructor
  · intro h
    unfold tStar
    rw [le_div_iff₀ (by linarith)]
    linarith
  · exact branch_at_tick_le e t ht h02

/-! ## Putting the substrate clock `43` inside the window -/

/-- Paper I's forced clock period. -/
def clock : ℝ := 43

/-- The clock is positive. -/
theorem clock_pos : 0 < clock := by unfold clock; norm_num

/-- **The clock sits inside the window** when the spectral spread is at most
`π/43`. -/
theorem substrate_tick_in_window (e : Fin 3 → ℝ) (h02 : e 0 < e 2)
    (hspread : e 2 - e 0 ≤ Real.pi / clock) :
    clock ≤ tStar e := by
  unfold tStar
  rw [le_div_iff₀ (by linarith)]
  have hc : 0 < clock := clock_pos
  calc clock * (e 2 - e 0) ≤ clock * (Real.pi / clock) :=
        mul_le_mul_of_nonneg_left hspread hc.le
    _ = Real.pi := by field_simp

/-- **The branch condition follows from the substrate clock and the spread
bound** — no independent `hband` hypothesis. -/
theorem substrate_branch_condition (e : Fin 3 → ℝ) (h02 : e 0 < e 2)
    (hspread : e 2 - e 0 ≤ Real.pi / clock) :
    clock * (e 2 - e 0) ≤ Real.pi :=
  branch_at_tick_le e clock clock_pos h02 (substrate_tick_in_window e h02 hspread)

/-- **The window is nonempty**: a positive tick always exists that keeps the
spectrum in one chord branch. The branch hypothesis is never vacuous. -/
theorem window_nonempty (e : Fin 3 → ℝ) (h02 : e 0 < e 2) :
    ∃ t : ℝ, 0 < t ∧ t * (e 2 - e 0) ≤ Real.pi :=
  ⟨tStar e, tStar_pos e h02, branch_at_tStar e h02⟩

/-- **The branch hypothesis is discharged at `tStar`.** Feeding the maximal tick
into `SpectralGapOrder.extreme_is_widest` shows the extreme pair is the widest
without any standing `hband` assumption — the window computed here supplies it. -/
theorem extreme_is_widest_at_tStar (e : Fin 3 → ℝ)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) :
    gap (eigenphase e (tStar e)) 0 1 < gap (eigenphase e (tStar e)) 0 2 ∧
      gap (eigenphase e (tStar e)) 1 2 < gap (eigenphase e (tStar e)) 0 2 := by
  have h02 : e 0 < e 2 := lt_trans h01 h12
  exact extreme_is_widest e (tStar e) (tStar_pos e h02) h01 h12 (branch_at_tStar e h02)

/-- **The least-work route is an adjacent pair at `tStar`**, again with the branch
condition supplied by the window rather than assumed. -/
theorem route_at_tStar (e : Fin 3 → ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2)
    (hsplit : splitting e (tStar e) 0 1 < splitting e (tStar e) 1 2)
    (hmin : workPrice (eigenphase e (tStar e)) B
        = gap (eigenphase e (tStar e)) 0 1 * totalWeight B / 12) :
    pairWeight B 1 2 = 0 ∧ pairWeight B 0 2 = 0 := by
  have h02 : e 0 < e 2 := lt_trans h01 h12
  exact route_is_tightest_adjacent e (tStar e) B (tStar_pos e h02) h01 h12
    (branch_at_tStar e h02) hsplit hmin

/-- The window threshold `π/43` is a concrete positive number. -/
theorem spread_threshold_pos : 0 < Real.pi / clock := by
  unfold clock; positivity

/-- The threshold is exactly `π/43`. -/
theorem spread_threshold_eq : Real.pi / clock = Real.pi / 43 := by
  unfold clock; norm_num

end PMFlavor.ChordBranch
