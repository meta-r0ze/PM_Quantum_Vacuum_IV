import PMDynamics.TransferWorkLaw
import PMDynamics.FlavourEvolution
import PMDynamics.GenerationLink
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The three pair gaps are ordered by the spectrum, not free

`RelativeFrameCost` prices each generation pair by its eigenphase gap
`gap φ i j = |φ i − φ j|²`, and `TransferWorkLaw` shows the least-work transfer
route is the smallest-gap pair. Both took the three gaps as **inputs**. This
module derives their ordering from the spectral data Paper IV already uses.

Writing the mass-basis eigenphases `φ_j = exp(−i t e_j)` for the energy list
`e : Fin 3 → ℝ` and tick `t` — exactly the diagonal of
`FlavourEvolution.evolution 1 e t` (`eigenphase_is_evolution_diagonal`) — the
chord laws `splitting_chord`, `gap_of_splitting` give

    gap i j = 2 − 2 cos(|t · (e i − e j)|).

**One increasing function of two numbers.** `gap_eq_of_splitting_eq`: equal
energy splittings price equally whatever the rest of the spectrum does. The
splittings telescope (`splitting_telescope`): the extreme splitting is the sum of
the two adjacent ones. Inside one chord branch the price is strictly monotone in
the splitting (`gap_lt_iff_splitting_lt`), so **price order is exactly splitting
order** (`gap_order_iff_splitting_order`).

**The widest pair is an extreme pair.** For a strictly increasing spectrum in one
branch, `extreme_is_widest` derives `gap 0 1 < gap 0 2` and `gap 1 2 < gap 0 2`.
With `TransferWorkLaw.unique_min_concentrates` that becomes a selection
statement: **the least-work transfer route is an adjacent pair, never the extreme
pair** (`route_extreme_carries_nothing`), and **which adjacent pair is chosen is
exactly which splitting is tighter** (`route_selects_tighter_splitting`). No
measured angle is used.

**Degeneracy makes a route free.** `degenerate_route_free`: equal energies give
zero gap, hence `doublet_free` prices any weight on that pair at zero. Applied to
the doubly degenerate light branch of `GenerationLink.sumzero_eigen`, the cost
side cannot separate the two members of a degenerate doublet —
`GenerationLink.light_mixing_free` re-derived from the price.

**The gaps are not three free numbers.** `gap_budget` writes their sum as a
function of the two adjacent splittings alone; `gap_not_independent` proves two
vanishing adjacent gaps force the third to vanish; `gap_le_four` bounds each.

Still inputs: the physical energy list `e`, the tick `t`, the requirement that a
comparison be executed at all, and the link `Y` that fixes `e`. Nothing here
produces measured angles. The result is that the *ordering* data the work law
needs is a theorem about the spectrum rather than a free choice.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.SpectralGapOrder
open Matrix RelativeFrameCost TransferWorkLaw GenerationLink
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

/-- The mass-basis eigenphase list of an energy assignment at tick `t`. -/
def eigenphase (e : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℂ :=
  fun j => Complex.exp ((-(t * e j) : ℝ) * Complex.I)

/-- **These are the phases the existing flavour evolution already uses.** No new
dynamical input is introduced here. -/
theorem eigenphase_is_evolution_diagonal (e : Fin 3 → ℝ) (t : ℝ) :
    FlavourEvolution.evolution 1 e t = Matrix.diagonal (eigenphase e t) := by
  show (1 : M) * PMAction.LinkExpansion.phaseDiag e (-t) * (1 : M)ᴴ = _
  rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  congr 1
  ring_nf

/-- The energy splitting a generation pair carries, in absolute value. -/
def splitting (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) : ℝ := |t * (e i - e j)|

theorem splitting_nonneg (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    0 ≤ splitting e t i j := abs_nonneg _

/-- A nonzero tick and distinct energies give a strictly positive splitting. -/
theorem splitting_pos {e : Fin 3 → ℝ} {t : ℝ} (ht : 0 < t) (i j : Fin 3)
    (h : e i ≠ e j) : 0 < splitting e t i j :=
  abs_pos.mpr (mul_ne_zero (ne_of_gt ht) (sub_ne_zero.mpr h))

theorem splitting_symm (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    splitting e t i j = splitting e t j i := by
  show |t * (e i - e j)| = |t * (e j - e i)|
  rw [show (t * (e j - e i) : ℝ) = -(t * (e i - e j)) by ring, abs_neg]

/-! ## The chord law -/

private lemma re_exp (x : ℝ) : (Complex.exp (↑x * Complex.I)).re = Real.cos x := by
  rw [Complex.exp_re]; simp
private lemma im_exp (x : ℝ) : (Complex.exp (↑x * Complex.I)).im = Real.sin x := by
  rw [Complex.exp_im]; simp

/-- **Chord law for unit eigenphases.** -/
theorem chord (x y : ℝ) :
    Complex.normSq (Complex.exp (↑x * Complex.I) - Complex.exp (↑y * Complex.I))
      = 2 - 2 * Real.cos (x - y) := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, re_exp x, im_exp x,
    re_exp y, im_exp y]
  have p1 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have p2 : Real.cos y ^ 2 + Real.sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y
  have cs : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y :=
    Real.cos_sub x y
  ring_nf
  nlinarith [p1, p2, cs]

/-- **The gap is a function of the splitting only.** -/
theorem gap_of_splitting (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    gap (eigenphase e t) i j = 2 - 2 * Real.cos (splitting e t i j) := by
  show Complex.normSq (Complex.exp ((-(t * e i) : ℝ) * Complex.I)
      - Complex.exp ((-(t * e j) : ℝ) * Complex.I)) = _
  rw [chord (-(t * e i)) (-(t * e j))]
  have hsub : (-(t * e i) : ℝ) - (-(t * e j)) = t * (e j - e i) := by ring
  rw [hsub]
  congr 1
  rw [splitting, Real.cos_abs,
    show (t * (e j - e i) : ℝ) = -(t * (e i - e j)) by ring, Real.cos_neg]

/-- The same law with the signed splitting, used by the budget identities. -/
theorem gap_chord (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    gap (eigenphase e t) i j = 2 - 2 * Real.cos (t * (e i - e j)) := by
  rw [gap_of_splitting, splitting, Real.cos_abs]

/-- **Equal splittings price equally**, whatever else the spectrum does. -/
theorem gap_eq_of_splitting_eq (e : Fin 3 → ℝ) (t : ℝ) (i j k l : Fin 3)
    (h : splitting e t i j = splitting e t k l) :
    gap (eigenphase e t) i j = gap (eigenphase e t) k l := by
  rw [gap_of_splitting, gap_of_splitting, h]

/-- The chord is at most four. -/
theorem chord_le_four (θ : ℝ) : 2 - 2 * Real.cos θ ≤ 4 := by
  nlinarith [Real.neg_one_le_cos θ]

/-- **Each gap is at most four**: a chord of the unit circle is at most two. -/
theorem gap_le_four (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    gap (eigenphase e t) i j ≤ 4 := by
  rw [gap_of_splitting]
  exact chord_le_four _

/-- **Splittings telescope.** The extreme splitting is the sum of the two
adjacent ones, so the three gaps come from two numbers. -/
theorem splitting_telescope (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) :
    splitting e t 0 2 = splitting e t 0 1 + splitting e t 1 2 := by
  show |t * (e 0 - e 2)| = |t * (e 0 - e 1)| + |t * (e 1 - e 2)|
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (by linarith)),
    abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (by linarith)),
    abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (by linarith))]
  ring

private lemma splitting_le_splitting_extreme (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) :
    splitting e t 0 1 ≤ splitting e t 0 2 ∧
      splitting e t 1 2 ≤ splitting e t 0 2 := by
  have tel := splitting_telescope e t ht h01 h12
  exact ⟨by nlinarith [splitting_nonneg e t 1 2], by nlinarith [splitting_nonneg e t 0 1]⟩

/-! ## One branch: price order is splitting order -/

/-- The chord is strictly increasing on one branch. -/
theorem chord_lt {x y : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (hxy : x < y) : 2 - 2 * Real.cos x < 2 - 2 * Real.cos y := by
  have h1 : Real.cos y < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hx.1 (by linarith [hy.2]) hxy
  nlinarith [Real.cos_le_one x, Real.cos_le_one y]

theorem chord_le {x y : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (hxy : x ≤ y) : 2 - 2 * Real.cos x ≤ 2 - 2 * Real.cos y := by
  have h1 : Real.cos y ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [hy.2]) hxy
  nlinarith

theorem chord_strictMono :
    StrictMonoOn (fun θ : ℝ => 2 - 2 * Real.cos θ) (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  exact chord_lt hx hy hxy

theorem chord_mono :
    MonotoneOn (fun θ : ℝ => 2 - 2 * Real.cos θ) (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  exact chord_le hx hy hxy

theorem chord_zero : (2 : ℝ) - 2 * Real.cos 0 = 0 := by norm_num

/-- **Price order is exactly splitting order** inside one chord branch. -/
theorem gap_lt_iff_splitting_lt (e : Fin 3 → ℝ) (t : ℝ) (i j k l : Fin 3)
    (hij : splitting e t i j ∈ Set.Icc 0 Real.pi)
    (hkl : splitting e t k l ∈ Set.Icc 0 Real.pi) :
    gap (eigenphase e t) i j < gap (eigenphase e t) k l ↔
      splitting e t i j < splitting e t k l := by
  constructor
  · intro H
    rw [gap_of_splitting, gap_of_splitting] at H
    by_contra h
    have := chord_le hkl hij (by linarith)
    linarith
  · intro H
    rw [gap_of_splitting, gap_of_splitting]
    exact chord_lt hij hkl H

theorem gap_le_iff_splitting_le (e : Fin 3 → ℝ) (t : ℝ) (i j k l : Fin 3)
    (hij : splitting e t i j ∈ Set.Icc 0 Real.pi)
    (hkl : splitting e t k l ∈ Set.Icc 0 Real.pi) :
    gap (eigenphase e t) i j ≤ gap (eigenphase e t) k l ↔
      splitting e t i j ≤ splitting e t k l := by
  constructor
  · intro H
    rw [gap_of_splitting, gap_of_splitting] at H
    by_contra h
    have := chord_lt hkl hij (by linarith)
    linarith
  · intro H
    rw [gap_of_splitting, gap_of_splitting]
    exact chord_le hij hkl H

/-- The whole spectrum sits in one branch. -/
private lemma branch (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) (hband : t * (e 2 - e 0) ≤ Real.pi) :
    splitting e t 0 1 ∈ Set.Icc 0 Real.pi ∧ splitting e t 1 2 ∈ Set.Icc 0 Real.pi
      ∧ splitting e t 0 2 ∈ Set.Icc 0 Real.pi := by
  have h02 : splitting e t 0 2 ≤ Real.pi := by
    show |t * (e 0 - e 2)| ≤ Real.pi
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (by linarith))]
    show -(t * (e 0 - e 2)) ≤ Real.pi
    nlinarith
  have hh := splitting_le_splitting_extreme e t ht h01 h12
  exact ⟨⟨splitting_nonneg e t 0 1, hh.1.trans h02⟩, ⟨splitting_nonneg e t 1 2,
      hh.2.trans h02⟩, ⟨splitting_nonneg e t 0 2, h02⟩⟩

/-- **The widest pair is an extreme pair.** For a strictly increasing spectrum
inside one chord branch, the `(0,2)` pair carries the largest gap. -/
theorem extreme_is_widest (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi) :
    gap (eigenphase e t) 0 1 < gap (eigenphase e t) 0 2 ∧
      gap (eigenphase e t) 1 2 < gap (eigenphase e t) 0 2 := by
  have hb := branch e t ht.le (le_of_lt h01) (le_of_lt h12) hband
  have tel := splitting_telescope e t ht.le (le_of_lt h01) (le_of_lt h12)
  constructor
  · refine (gap_lt_iff_splitting_lt e t 0 1 0 2 hb.1 hb.2.2).mpr ?_
    nlinarith [splitting_pos ht 1 2 (ne_of_lt h12)]
  · refine (gap_lt_iff_splitting_lt e t 1 2 0 2 hb.2.1 hb.2.2).mpr ?_
    nlinarith [splitting_pos ht 0 1 (ne_of_lt h01)]

/-- **Price order is splitting order for the two adjacent pairs.** -/
theorem gap_order_iff_splitting_order (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi) :
    gap (eigenphase e t) 0 1 ≤ gap (eigenphase e t) 1 2 ↔
      splitting e t 0 1 ≤ splitting e t 1 2 := by
  have hb := branch e t ht.le (le_of_lt h01) (le_of_lt h12) hband
  exact gap_le_iff_splitting_le e t 0 1 1 2 hb.1 hb.2.1

/-! ## The selection consequence -/

/-- **The extreme pair is never the cheapest route.** Its price bound is
strictly worse than either adjacent pair's, for any positive delivered weight. -/
theorem extreme_never_cheapest (e : Fin 3 → ℝ) (t : ℝ) (W : ℝ) (hW : 0 < W) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi) :
    gap (eigenphase e t) 0 1 * W / 12 < gap (eigenphase e t) 0 2 * W / 12 ∧
      gap (eigenphase e t) 1 2 * W / 12 < gap (eigenphase e t) 0 2 * W / 12 := by
  have hw := extreme_is_widest e t ht h01 h12 hband
  have q : 0 < W / 12 := by positivity
  have g1 : gap (eigenphase e t) 0 1 * (W / 12) < gap (eigenphase e t) 0 2 * (W / 12) :=
    mul_lt_mul_of_pos_right hw.1 q
  have g2 : gap (eigenphase e t) 1 2 * (W / 12) < gap (eigenphase e t) 0 2 * (W / 12) :=
    mul_lt_mul_of_pos_right hw.2 q
  have c1 : gap (eigenphase e t) 0 1 * W / 12 = gap (eigenphase e t) 0 1 * (W / 12) := by ring
  have c2 : gap (eigenphase e t) 0 2 * W / 12 = gap (eigenphase e t) 0 2 * (W / 12) := by ring
  have c3 : gap (eigenphase e t) 1 2 * W / 12 = gap (eigenphase e t) 1 2 * (W / 12) := by ring
  exact ⟨by rw [c1, c2]; exact g1, by rw [c3, c2]; exact g2⟩

/-- **The least-work route is the tightest adjacent pair.** For a strictly
increasing spectrum inside one chord branch whose two adjacent splittings are
unequal, a frame attaining the smallest-gap price bound carries weight on that
adjacent pair alone: the extreme pair and the wider adjacent pair carry nothing.
The `(0,2)` half of the ordering is supplied by `extreme_is_widest`, so the only
remaining choice is which adjacent splitting is tighter — a statement about the
energy list, not a free input. -/
theorem route_is_tightest_adjacent (e : Fin 3 → ℝ) (t : ℝ) (B : M) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi)
    (hsplit : splitting e t 0 1 < splitting e t 1 2)
    (hmin : workPrice (eigenphase e t) B
        = gap (eigenphase e t) 0 1 * totalWeight B / 12) :
    pairWeight B 1 2 = 0 ∧ pairWeight B 0 2 = 0 := by
  have hb := branch e t ht.le (le_of_lt h01) (le_of_lt h12) hband
  have g01 : gap (eigenphase e t) 0 1 < gap (eigenphase e t) 1 2 :=
    (gap_lt_iff_splitting_lt e t 0 1 1 2 hb.1 hb.2.1).mpr hsplit
  have g02 := (extreme_is_widest e t ht h01 h12 hband).1
  exact (unique_min_concentrates (eigenphase e t) B g01 g02).mp hmin

/-- The mirrored case: a tighter `(1,2)` splitting routes the transfer there. -/
theorem route_is_tightest_adjacent' (e : Fin 3 → ℝ) (t : ℝ) (B : M) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi)
    (hsplit : splitting e t 1 2 < splitting e t 0 1)
    (hmin : workPrice (eigenphase e t) B
        = gap (eigenphase e t) 1 2 * totalWeight B / 12) :
    pairWeight B 0 1 = 0 ∧ pairWeight B 0 2 = 0 := by
  have hb := branch e t ht.le (le_of_lt h01) (le_of_lt h12) hband
  have g12 : gap (eigenphase e t) 1 2 < gap (eigenphase e t) 0 1 :=
    (gap_lt_iff_splitting_lt e t 1 2 0 1 hb.2.1 hb.1).mpr hsplit
  have g02 := (extreme_is_widest e t ht h01 h12 hband).2
  have ht' : totalWeight B = pairWeight B 1 2 + pairWeight B 0 1 + pairWeight B 0 2 := by
    show pairWeight B 0 1 + pairWeight B 0 2 + pairWeight B 1 2 = _
    ring
  have hw' : 12 * workPrice (eigenphase e t) B
      = gap (eigenphase e t) 1 2 * pairWeight B 1 2
        + gap (eigenphase e t) 0 1 * pairWeight B 0 1
        + gap (eigenphase e t) 0 2 * pairWeight B 0 2 := by
    rw [workPrice_sum (eigenphase e t) B]
    ring
  have h := (concentrate_on_pair (eigenphase e t) B (gap (eigenphase e t) 1 2)
    (gap (eigenphase e t) 0 1) (gap (eigenphase e t) 0 2)
    (pairWeight B 1 2) (pairWeight B 0 1) (pairWeight B 0 2)
    hw' ht' g12 g02 (pairWeight_nonneg B 0 1) (pairWeight_nonneg B 0 2)).mp hmin
  exact ⟨h.1, h.2⟩

/-- **A work-minimizing frame is block-diagonal on the extreme pair.** The
selection statement in observable form: the frame that attains the smallest-gap
price bound has no `(0,2)` transfer amplitude at all. -/
theorem route_extreme_amplitude_vanishes (e : Fin 3 → ℝ) (t : ℝ) (B : M) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi)
    (hsplit : splitting e t 0 1 < splitting e t 1 2)
    (hmin : workPrice (eigenphase e t) B
        = gap (eigenphase e t) 0 1 * totalWeight B / 12) :
    Complex.normSq (B 0 2) = 0 ∧ Complex.normSq (B 2 0) = 0 := by
  have h := route_is_tightest_adjacent e t B ht h01 h12 hband hsplit hmin
  show Complex.normSq (B 0 2) = 0 ∧ Complex.normSq (B 2 0) = 0
  have h02 : Complex.normSq (B 0 2) + Complex.normSq (B 2 0) = 0 := h.2
  exact ⟨by nlinarith [Complex.normSq_nonneg (B 0 2), Complex.normSq_nonneg (B 2 0)],
    by nlinarith [Complex.normSq_nonneg (B 0 2), Complex.normSq_nonneg (B 2 0)]⟩

/-! ## What the reduction leaves -/

/-- **The tick cancels.** For a strictly increasing spectrum in one branch the
comparison that decides the route is scale-free: the tick `t` divides out. -/
theorem splitting_comparison_scalefree (e : Fin 3 → ℝ) (t₁ t₂ : ℝ) (h1 : 0 < t₁)
    (h2 : 0 < t₂) (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) :
    (splitting e t₁ 0 1 ≤ splitting e t₁ 1 2) ↔ (splitting e t₂ 0 1 ≤ splitting e t₂ 1 2) := by
  have a1 : splitting e t₁ 0 1 = t₁ * (e 1 - e 0) := by
    show |t₁ * (e 0 - e 1)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith))]
    ring
  have b1 : splitting e t₁ 1 2 = t₁ * (e 2 - e 1) := by
    show |t₁ * (e 1 - e 2)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith))]
    ring
  have a2 : splitting e t₂ 0 1 = t₂ * (e 1 - e 0) := by
    show |t₂ * (e 0 - e 1)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h2.le (by linarith))]
    ring
  have b2 : splitting e t₂ 1 2 = t₂ * (e 2 - e 1) := by
    show |t₂ * (e 1 - e 2)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h2.le (by linarith))]
    ring
  rw [a1, b1, a2, b2]
  have d1 : 0 ≤ e 1 - e 0 := by linarith
  have d2 : 0 ≤ e 2 - e 1 := by linarith
  have p1 : 0 < t₁ * t₂ := mul_pos h1 h2
  constructor
  · intro H
    have : t₂ * (t₁ * (e 1 - e 0)) ≤ t₂ * (t₁ * (e 2 - e 1)) := by
      nlinarith
    nlinarith
  · intro H
    have : t₁ * (t₂ * (e 1 - e 0)) ≤ t₁ * (t₂ * (e 2 - e 1)) := by
      nlinarith
    nlinarith

/-- The comparison is exactly the ordering of the two adjacent energy
splittings, with the tick removed entirely. -/
theorem splitting_comparison_is_spectral (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) :
    splitting e t 0 1 ≤ splitting e t 1 2 ↔ e 1 - e 0 ≤ e 2 - e 1 := by
  have a : splitting e t 0 1 = t * (e 1 - e 0) := by
    show |t * (e 0 - e 1)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith))]
    ring
  have b : splitting e t 1 2 = t * (e 2 - e 1) := by
    show |t * (e 1 - e 2)| = _
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith))]
    ring
  rw [a, b]
  exact ⟨fun H => by nlinarith [mul_pos ht ht], fun H => mul_le_mul_of_nonneg_left H ht.le⟩

/-- **What the reduction leaves.** The work law needed three pair gaps as
inputs. `extreme_is_widest` derives that the extreme pair is the widest, so a
minimizing route is an adjacent pair, and `splitting_comparison_is_spectral`
shows the remaining choice is exactly which adjacent energy splitting is
tighter — one comparison of the supplied spectrum, independent of the tick. -/
theorem reduction_leaves_one_comparison (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (h01 : e 0 < e 1) (h12 : e 1 < e 2) (hband : t * (e 2 - e 0) ≤ Real.pi) :
    (splitting e t 0 1 ≤ splitting e t 1 2 ↔ e 1 - e 0 ≤ e 2 - e 1) ∧
      gap (eigenphase e t) 0 1 < gap (eigenphase e t) 0 2 ∧
        gap (eigenphase e t) 1 2 < gap (eigenphase e t) 0 2 := by
  have hw := extreme_is_widest e t ht h01 h12 hband
  exact ⟨splitting_comparison_is_spectral e t ht (le_of_lt h01) (le_of_lt h12), hw.1, hw.2⟩

/-! ## Degeneracy: a free route -/

/-- Equal energies make a route free of charge. -/
theorem degenerate_route_free (e : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) (h : e i = e j) :
    gap (eigenphase e t) i j = 0 := by
  rw [gap_of_splitting]
  show 2 - 2 * Real.cos |t * (e i - e j)| = 0
  have : t * (e i - e j) = 0 := by rw [h, sub_self, mul_zero]
  rw [this, abs_zero, Real.cos_zero]
  ring

/-- An aligned pair of generations contributes nothing to the price. -/
theorem price_ignores_aligned_pair (phase : Fin 3 → ℂ) (B : M) (i j : Fin 3)
    (h : gap phase i j = 0) :
    gap phase i j * pairWeight B i j = 0 := by
  rw [h, zero_mul]

/-- **The degenerate doublet route is free.** The symmetric link has a doubly
degenerate light branch (`GenerationLink.sumzero_eigen`), so its internal gap is
zero and weight on that pair is unpriced. The cost side cannot separate the two
members of a degenerate doublet — `GenerationLink.light_mixing_free` re-derived
from the price. -/
theorem doublet_free (e : Fin 3 → ℝ) (t : ℝ) (hdeg : e 1 = e 2) (c s : ℝ) :
    workPrice (eigenphase e t) (rot12 c s) = 0 := by
  show frameCost (diagonal (eigenphase e t)) (rot12 c s) = 0
  rw [plane_cost12, degenerate_route_free e t 1 2 hdeg]
  ring

/-- At a degenerate doublet the price cannot rank the doublet against an aligned
frame: both are zero. -/
theorem doublet_price_tie (e : Fin 3 → ℝ) (t : ℝ) (hdeg : e 1 = e 2) (c s : ℝ) :
    workPrice (eigenphase e t) (rot12 c s) = workPrice (eigenphase e t) (rot12 1 0) := by
  rw [doublet_free e t hdeg c s, doublet_free e t hdeg 1 0]

/-! ## The gaps are not three free numbers -/

/-- **Gap budget.** The sum of the three gaps is a function of the two adjacent
splittings alone. -/
theorem gap_budget (e : Fin 3 → ℝ) (t : ℝ) :
    gap (eigenphase e t) 0 1 + gap (eigenphase e t) 1 2 + gap (eigenphase e t) 0 2
      = 6 - 2 * (Real.cos (t * (e 0 - e 1)) + Real.cos (t * (e 1 - e 2))
        + Real.cos (t * (e 0 - e 2))) := by
  have tel : t * (e 0 - e 2) = t * (e 0 - e 1) + t * (e 1 - e 2) := by ring
  have g1 : gap (eigenphase e t) 0 1 = 2 - 2 * Real.cos (t * (e 0 - e 1)) :=
    gap_chord e t 0 1
  have g2 : gap (eigenphase e t) 1 2 = 2 - 2 * Real.cos (t * (e 1 - e 2)) :=
    gap_chord e t 1 2
  have g3 : gap (eigenphase e t) 0 2 = 2 - 2 * Real.cos (t * (e 0 - e 2)) :=
    gap_chord e t 0 2
  rw [g1, g2, g3, tel]
  ring

/-- **The gaps are not independent.** Two vanishing adjacent gaps force the
third to vanish: one cannot price the extreme pair while treating both adjacent
pairs as free. -/
theorem gap_not_independent (e : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (h01 : e 0 ≤ e 1) (h12 : e 1 ≤ e 2) (hband : t * (e 2 - e 0) ≤ Real.pi)
    (hg1 : gap (eigenphase e t) 0 1 = 0) (hg2 : gap (eigenphase e t) 1 2 = 0) :
    gap (eigenphase e t) 0 2 = 0 := by
  have hb := branch e t ht.le h01 h12 hband
  have hzero : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl 0, Real.pi_pos.le⟩
  have z1 : splitting e t 0 1 = 0 := by
    rw [gap_of_splitting] at hg1
    refine le_antisymm ?_ (splitting_nonneg e t 0 1)
    by_contra hgt
    have := chord_lt hzero hb.1 (by linarith)
    linarith [this, chord_zero]
  have z2 : splitting e t 1 2 = 0 := by
    rw [gap_of_splitting] at hg2
    refine le_antisymm ?_ (splitting_nonneg e t 1 2)
    by_contra hgt
    have := chord_lt hzero hb.2.1 (by linarith)
    linarith [this, chord_zero]
  have tel := splitting_telescope e t ht.le h01 h12
  rw [gap_of_splitting, tel, z1, z2]
  show 2 - 2 * Real.cos (0 + 0) = 0
  rw [add_zero, Real.cos_zero]
  ring

end PMDynamics.SpectralGapOrder
