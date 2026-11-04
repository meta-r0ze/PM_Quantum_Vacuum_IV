import PMFlavor.RelativeFrameCost
import PMFlavor.GenerationPersistence
import PMFlavor.RestorationBudget
import Mathlib.Tactic

/-!
# Required work for an actual inter-generation transfer

`GenerationPersistence` shows that a transfer policy with nonzero net drift at
some generation cannot persist. `RelativeFrameCost` shows that the joint
comparison of two sector frames prices each generation pair by its own spectral
gap. Together these give the required-work law the five selection tests asked
for.

**Work per transfer.** `workPrice_sum` writes the joint price of a frame as a
linear form over the three unordered generation pairs,

    price = (gap₀₁ · w₀₁ + gap₀₂ · w₀₂ + gap₁₂ · w₁₂) / 12,

where `w_ij` is the frame's transfer weight on pair `ij` (both directions
together), and `price_is_work_per_period` bills `requiredWork = period · price`
over one period — the same shape as `RestorationBudget.minimum_density`'s
`c · K / period`, with the spectral gap in the role of the impedance.

**What it selects.** `min_cost_is_min_gap`: for any frame the price is at least
`gap · W / 12`, where `gap` is any lower bound on the three pair gaps and `W` is
the total delivered transfer weight. `wasted_work`: weight on a strictly wider
pair costs strictly more for the same delivered transfer.
`unique_min_concentrates`: under a strictly ordered gap the lower bound is
attained exactly when the two wider pairs carry nothing. So **which pair
transfers is fixed by the gap ordering, not by symmetry** — the cost-side half
of the mixing-selection obligation. `plane_concentrates` shows a plane rotation
is exactly such an extremal frame.

**What it does not select.** The total weight `W` itself, and hence the mixing
*angle*, is not fixed by minimization: `zero_weight_minimum` exhibits a
price-minimal frame of price zero in any admissible family containing an aligned
pair, exactly the zero-flux obstruction of
`TransitionSelection.zero_flux_minimum`; and `weight_not_selected` shows the
price is blind to the sign of the transfer amplitude. A positive `W` must come
from the persistence contract `GenerationPersistence.persistence_selects_balanced`
together with a required transfer whose physical source is still open.
`policyOf_balanced` shows why: the frame policy is balanced automatically, so
persistence constrains the pair weights no further than symmetry does.
`persists_and_minimizes` states what the two obligations give jointly and no
more. The gaps are inputs here rather than derived numbers, and the frames are
three-mode rotations rather than the full wall. No measured angle is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.TransferWorkLaw
open Matrix RelativeFrameCost GenerationPersistence
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

/-- **The work-price of a frame**: the joint comparison cost of the two sector
frames, i.e. the work billed per joint comparison. -/
def workPrice (phase : Fin 3 → ℂ) (B : M) : ℝ := frameCost (diagonal phase) B

theorem workPrice_nonneg (phase : Fin 3 → ℂ) (B : M) : 0 ≤ workPrice phase B :=
  frameCost_nonneg _ _

/-- **Price as a linear form over the three generation pairs.** -/
theorem workPrice_sum (phase : Fin 3 → ℂ) (B : M) :
    12 * workPrice phase B =
      gap phase 0 1 * pairWeight B 0 1
        + gap phase 0 2 * pairWeight B 0 2
        + gap phase 1 2 * pairWeight B 1 2 := by
  have key := frame_price phase B
  show 12 * frameCost (diagonal phase) B = _
  linarith

/-- Total transfer weight carried by a frame: the three pair weights added. -/
def totalWeight (B : M) : ℝ :=
  pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2

/-- Required work billed over one period. -/
def requiredWork (period : ℝ) (phase : Fin 3 → ℂ) (B : M) : ℝ :=
  period * workPrice phase B

theorem requiredWork_nonneg (period : ℝ) (hperiod : 0 ≤ period)
    (phase : Fin 3 → ℂ) (B : M) : 0 ≤ requiredWork period phase B :=
  mul_nonneg hperiod (workPrice_nonneg phase B)

/-- **Required work per period, in gaps and weights.** -/
theorem price_is_work_per_period (period : ℝ) (phase : Fin 3 → ℂ) (B : M) :
    12 * requiredWork period phase B =
      period * (gap phase 0 1 * pairWeight B 0 1
        + gap phase 0 2 * pairWeight B 0 2
        + gap phase 1 2 * pairWeight B 1 2) := by
  have key := workPrice_sum phase B
  calc 12 * requiredWork period phase B
      = period * (12 * workPrice phase B) := by
        show 12 * (period * workPrice phase B) = _
        ring
    _ = period * (gap phase 0 1 * pairWeight B 0 1
        + gap phase 0 2 * pairWeight B 0 2
        + gap phase 1 2 * pairWeight B 1 2) := by rw [key]

/-! ## Least work selects the pair -/

/-- **Least work, smallest gap.** Any lower bound on the three pair gaps is a
lower bound on the price per unit of delivered transfer weight. -/
theorem min_cost_is_min_gap (phase : Fin 3 → ℂ) (B : M) (g : ℝ)
    (h01 : g ≤ gap phase 0 1) (h02 : g ≤ gap phase 0 2) (h12 : g ≤ gap phase 1 2) :
    workPrice phase B ≥ g * totalWeight B / 12 := by
  have w0 : 0 ≤ pairWeight B 0 1 := pairWeight_nonneg B 0 1
  have w1 : 0 ≤ pairWeight B 0 2 := pairWeight_nonneg B 0 2
  have w2 : 0 ≤ pairWeight B 1 2 := pairWeight_nonneg B 1 2
  have h1 : gap phase 0 1 * pairWeight B 0 1 ≥ g * pairWeight B 0 1 :=
    mul_le_mul_of_nonneg_right h01 w0
  have h2 : gap phase 0 2 * pairWeight B 0 2 ≥ g * pairWeight B 0 2 :=
    mul_le_mul_of_nonneg_right h02 w1
  have h3 : gap phase 1 2 * pairWeight B 1 2 ≥ g * pairWeight B 1 2 :=
    mul_le_mul_of_nonneg_right h12 w2
  have hd : g * totalWeight B = g * pairWeight B 0 1 + g * pairWeight B 0 2
      + g * pairWeight B 1 2 := by
    show g * (pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2) = _
    ring
  rw [ge_iff_le, div_le_iff₀ (by norm_num : (0:ℝ) < 12), hd]
  show g * pairWeight B 0 1 + g * pairWeight B 0 2 + g * pairWeight B 1 2 ≤ _
  have hk := workPrice_sum phase B
  nlinarith

/-- **Wasted work.** Weight on a strictly wider pair buys the same delivered
transfer at strictly higher price. -/
theorem wasted_work (phase : Fin 3 → ℂ) (B : M)
    (h01 : gap phase 0 1 < gap phase 1 2) (hw : 0 < pairWeight B 1 2)
    (h02 : gap phase 0 1 ≤ gap phase 0 2) :
    workPrice phase B > gap phase 0 1 * totalWeight B / 12 := by
  have hd : gap phase 0 1 * totalWeight B
      = gap phase 0 1 * pairWeight B 0 1 + gap phase 0 1 * pairWeight B 0 2
        + gap phase 0 1 * pairWeight B 1 2 := by
    show gap phase 0 1 * (pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2) = _
    ring
  rw [gt_iff_lt, div_lt_iff₀ (by norm_num : (0:ℝ) < 12), hd]
  have hk := workPrice_sum phase B
  nlinarith [pairWeight_nonneg B 0 1, pairWeight_nonneg B 0 2]

/-- **Three-term concentration.** With one strictly smallest coefficient, a
linear form attains its lower bound exactly when the two wider weights vanish.
This is the algebra behind `unique_min_concentrates`, stated for an arbitrary
choice of which of the three terms is smallest. -/
theorem concentrate_three (a1 a2 a3 w1 w2 w3 : ℝ)
    (h12 : a1 < a2) (h13 : a1 < a3) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) :
    a1 * w1 + a2 * w2 + a3 * w3 = a1 * (w1 + w2 + w3) ↔ w2 = 0 ∧ w3 = 0 := by
  constructor
  · intro H
    have key : (a2 - a1) * w2 + (a3 - a1) * w3 = 0 := by linarith
    have p2 : 0 ≤ (a2 - a1) * w2 := mul_nonneg (by linarith) hw2
    have p3 : 0 ≤ (a3 - a1) * w3 := mul_nonneg (by linarith) hw3
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h2, h3⟩
    rw [h2, h3]
    ring

/-- **Unique concentration.** Under a strictly ordered gap the price attains the
smallest-gap lower bound exactly when the two wider pairs carry nothing. -/
theorem unique_min_concentrates (phase : Fin 3 → ℂ) (B : M)
    (h01 : gap phase 0 1 < gap phase 1 2) (h02 : gap phase 0 1 < gap phase 0 2) :
    workPrice phase B = gap phase 0 1 * totalWeight B / 12 ↔
      pairWeight B 1 2 = 0 ∧ pairWeight B 0 2 = 0 := by
  have key := workPrice_sum phase B
  have w1 : 0 ≤ pairWeight B 0 2 := pairWeight_nonneg B 0 2
  have w2 : 0 ≤ pairWeight B 1 2 := pairWeight_nonneg B 1 2
  constructor
  · intro H
    have hd : gap phase 0 1 * totalWeight B
        = gap phase 0 1 * pairWeight B 0 1 + gap phase 0 1 * pairWeight B 0 2
          + gap phase 0 1 * pairWeight B 1 2 := by
      show gap phase 0 1 * (pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2) = _
      ring
    rw [hd] at H
    have e1 : (gap phase 1 2 - gap phase 0 1) * pairWeight B 1 2 = 0 := by nlinarith
    have e2 : (gap phase 0 2 - gap phase 0 1) * pairWeight B 0 2 = 0 := by nlinarith
    exact ⟨(mul_eq_zero.mp e1).resolve_left (by linarith),
      (mul_eq_zero.mp e2).resolve_left (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have hk := key
    rw [h1, h2] at hk
    have hd : gap phase 0 1 * totalWeight B = gap phase 0 1 * pairWeight B 0 1 := by
      show gap phase 0 1 * (pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2) = _
      rw [h1, h2]
      ring
    show workPrice phase B = gap phase 0 1 * totalWeight B / 12
    rw [hd]
    linarith

/-- **Concentration on any chosen pair.** The same statement with the roles of
the three generation pairs permuted: whichever pair has the strictly smallest
gap is the only one that can carry weight at the price bound. -/
theorem concentrate_on_pair (phase : Fin 3 → ℂ) (B : M) (a1 a2 a3 : ℝ)
    (w1 w2 w3 : ℝ) (hw : 12 * workPrice phase B = a1 * w1 + a2 * w2 + a3 * w3)
    (hwt : totalWeight B = w1 + w2 + w3) (h12 : a1 < a2) (h13 : a1 < a3)
    (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) :
    workPrice phase B = a1 * totalWeight B / 12 ↔ w2 = 0 ∧ w3 = 0 := by
  constructor
  · intro H
    have h : (12 : ℝ) * workPrice phase B = a1 * (w1 + w2 + w3) := by
      rw [← hwt, H]; ring
    rw [hw] at h
    exact (concentrate_three a1 a2 a3 w1 w2 w3 h12 h13 hw2 hw3).mp h
  · rintro ⟨rfl, rfl⟩
    rw [hwt]
    show workPrice phase B = a1 * (w1 + 0 + 0) / 12
    have h : (12 : ℝ) * workPrice phase B = a1 * w1 := by
      rw [hw]
      ring
    linarith

/-- A plane rotation is an extremal frame: all its weight sits on its own pair,
split equally over the two directions. -/
theorem plane_concentrates (c s : ℝ) :
    pairWeight (rot01 c s) 0 1 = 2 * s^2 ∧ pairWeight (rot01 c s) 0 2 = 0 ∧
      pairWeight (rot01 c s) 1 2 = 0 :=
  pairWeight_rot01 c s

/-- **The zero-work obstruction survives.** In any admissible family containing
an aligned pair of frames, price minimization selects a frame of price zero:
exactly the zero-flux minimum of `TransitionSelection.zero_flux_minimum`. -/
theorem zero_weight_minimum (phase : Fin 3 → ℂ) (P : Set M)
    (halign : ∃ p q : Fin 3 → ℂ, diagonal p * diagonal q ∈ P) :
    ∃ C ∈ P, (∀ D ∈ P, workPrice phase C ≤ workPrice phase D) ∧
      workPrice phase C = 0 := by
  obtain ⟨p, q, hpq⟩ := halign
  have h0 : workPrice phase (diagonal p * diagonal q) = 0 := by
    show frameCost (diagonal phase) (diagonal p * diagonal q) = 0
    rw [Matrix.diagonal_mul_diagonal]
    exact aligned_zero phase (fun i => p i * q i)
  exact ⟨diagonal p * diagonal q, hpq, fun D _ => h0 ▸ workPrice_nonneg phase D, h0⟩

/-! ## The link with the persistence contract -/

/-- A frame's pair weights define a transfer policy on the three generations. -/
def policyOf (B : M) : Fin 3 → Fin 3 → ℝ := fun i j => pairWeight B i j

theorem policyOf_isTransferPolicy (B : M) : IsTransferPolicy (policyOf B) :=
  fun i j => pairWeight_nonneg B i j

/-- **The frame policy is balanced automatically**: inflow equals outflow at
every generation, because a pair weight is symmetric in its two directions. So
persistence constrains the pair weights no further than symmetry does. -/
theorem policyOf_balanced (B : M) : Balanced (policyOf B) := by
  intro i
  show ∑ j, pairWeight B j i = ∑ j, pairWeight B i j
  apply Finset.sum_congr rfl
  intro j _
  exact (pairWeight_symm B i j).symm

/-- **Persistence plus least work.** The two obligations together fix *which*
generation pair carries the transfer and say nothing about how much: the
surviving policy is balanced, the cheapest policy is concentrated, and the total
weight stays free. -/
theorem persists_and_minimizes (B : M) (phase : Fin 3 → ℂ)
    (h01 : gap phase 0 1 < gap phase 1 2) (h02 : gap phase 0 1 < gap phase 0 2)
    (hmin : workPrice phase B = gap phase 0 1 * totalWeight B / 12) :
    Balanced (policyOf B) ∧ pairWeight B 1 2 = 0 ∧ pairWeight B 0 2 = 0 :=
  ⟨policyOf_balanced B, (unique_min_concentrates phase B h01 h02).mp hmin⟩

/-- **The transfer amplitude is not selected.** The price is even in the
amplitude, so the surviving level set is not a point. -/
theorem weight_not_selected (phase : Fin 3 → ℂ) (c s : ℝ) :
    totalWeight (rot01 c s) = totalWeight (rot01 c (-s)) ∧
      workPrice phase (rot01 c s) = workPrice phase (rot01 c (-s)) := by
  refine ⟨?_, ?_⟩
  · show pairWeight (rot01 c s) 0 1 + pairWeight (rot01 c s) 0 2
        + pairWeight (rot01 c s) 1 2
      = pairWeight (rot01 c (-s)) 0 1 + pairWeight (rot01 c (-s)) 0 2
        + pairWeight (rot01 c (-s)) 1 2
    obtain ⟨a1, a2, a3⟩ := plane_concentrates c s
    obtain ⟨b1, b2, b3⟩ := plane_concentrates c (-s)
    rw [a1, a2, a3, b1, b2, b3]
    ring
  · show frameCost (diagonal phase) (rot01 c s) = frameCost (diagonal phase) (rot01 c (-s))
    rw [sign_tie01]

end PMFlavor.TransferWorkLaw
