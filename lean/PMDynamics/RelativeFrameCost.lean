import PMDynamics.FlavourOrderComparison
import PMDynamics.ReferenceSelection
import Mathlib.Tactic

/-!
# A cost that prices relative sector frames by spectral gap

The five selection tests of Paper IV fail for one structural reason. Every
readout used so far either divides the reference out completely
(`ReferenceSelection.invariant_cost_tie`), sees only one sector's spectrum
(`FlavourResponseSelection.uniform_tie`), or is minimized at zero throughput
(`TransitionSelection.zero_flux_minimum`). None of them can price one
generation pair against another, so `SelectionSymmetry.unique_minimum_form`
applies and any unique minimum of such a cost is `S₃`-invariant.

The joint-order readout of `FlavourOrderComparison` is different. Its response
is the squared Frobenius norm of the commutator of two updates,

    frameCost A B = ‖A B − B A‖² / 12.

**Why it is a relative-frame cost.**
* `common_relabel` — one class permutation applied to *both* sectors divides
  out, so the value is a function of the relative configuration only.
* `aligned_zero`, `frameCost_zero_iff` — it vanishes exactly when the two
  frames are simultaneously diagonal, i.e. when there is no mixing.
* `gap_weighted` — in one sector's eigenbasis the cost is the other frame's
  entries, each weighted by the squared gap of its own eigenphase pair.
  Distinct gaps price distinct entries: **this is the `S₃`-breaking weighting.**

**What it selects.** For the primitive rotation `rot_ij c s` acting in one
generation plane, `plane_cost01`/`plane_cost02`/`plane_cost12` give the closed
form

    frameCost (diagonal phase) (rot_ij c s) = gap_ij · s² / 6,  gap_ij = |φ i − φ j|².

The rotation size and the pair gap factorize. Hence at fixed rotation size the
cheapest transfer runs through the pair with the smallest gap
(`cost_lt_of_gap_lt`, `cost_le_iff_gap_le`, `least_cost_le_min`,
`wasted_transfer`), and at a fixed required signal `σ` the amplitude needed
obeys `s² = 6σ / gap` (`amplitude_largest_gap_le`): the largest gap needs the
least mixing. `signal_range01`/`signal_max01`/`signal_attainable` give the exact
range and show every value up to the plane maximum `gap/6` is reached.

**What it still does not do.** For one plane the response is even in `s`
(`sign_tie01`) and it is CP-even (`conjugation_tie`, inherited from
`FlavourOrderComparison`), so it fixes `s²` but neither its sign nor a
conjugation branch. A required signal therefore determines a level set, not a
point. The gap ordering selects *which pair* transfers most cheaply; the amount
still needs the gaps, the period and the signal budget as inputs, and the plane
rotations here are an orthonormal three-mode model, not the full wall. No
measured angle is used anywhere in this file.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.RelativeFrameCost
open Matrix PMAction FlavourOrderComparison
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

/-- The **relative-frame cost** of two sector updates: the mean joint-order
comparison response over a complete coordinate ensemble. -/
def frameCost (A B : M) : ℝ := meanFlag A B

theorem frameCost_formula (A B : M) :
    frameCost A B = (∑ i, ∑ j, Complex.normSq ((A*B - B*A) i j))/12 :=
  mean_formula A B

theorem frameCost_nonneg (A B : M) : 0 ≤ frameCost A B := by
  rw [frameCost_formula]
  refine div_nonneg (Finset.sum_nonneg (fun i _ => ?_)) (by norm_num)
  exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)

/-- Exactly an alignment obstruction. -/
theorem frameCost_zero_iff (A B : M) : frameCost A B = 0 ↔ A*B = B*A :=
  mean_zero_iff A B

/-- Reversing the two readout orders does not change the price. -/
theorem frameCost_symm (A B : M) : frameCost A B = frameCost B A := by
  rw [frameCost_formula, frameCost_formula]
  refine congrArg (fun x => x/12) ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply]
  rw [← neg_sub, Complex.normSq_neg]

/-! ## Reference covariance -/

/-- Relabeling a frame by one class permutation. -/
def relabel (σ : Equiv.Perm (Fin 3)) (Y : M) : M := fun i j => Y (σ i) (σ j)

/-- Relabeling is multiplicative and additive, so it carries commutators to
commutators. -/
theorem relabel_mul (σ : Equiv.Perm (Fin 3)) (A B : M) :
    relabel σ (A * B) = relabel σ A * relabel σ B := by
  ext i j
  show (A*B) (σ i) (σ j) = ∑ k, A (σ i) (σ k) * B (σ k) (σ j)
  rw [Matrix.mul_apply]
  exact (Equiv.sum_comp (σ : Fin 3 ≃ Fin 3) (fun k => A (σ i) k * B k (σ j))).symm

theorem relabel_sub (σ : Equiv.Perm (Fin 3)) (A B : M) :
    relabel σ (A - B) = relabel σ A - relabel σ B := by
  ext i j
  show (A - B) (σ i) (σ j) = (A (σ i) (σ j) : ℂ) - B (σ i) (σ j)
  exact Matrix.sub_apply A B _ _

theorem comm_relabel (σ : Equiv.Perm (Fin 3)) (A B : M) :
    relabel σ A * relabel σ B - relabel σ B * relabel σ A = relabel σ (A*B - B*A) := by
  rw [← relabel_mul σ A B, ← relabel_mul σ B A, relabel_sub]

/-- The squared Frobenius norm is unchanged by a relabeling. -/
theorem frobenius_relabel (σ : Equiv.Perm (Fin 3)) (X : M) :
    (∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (relabel σ X i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (X i j) := by
  have hi : (∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (X (σ i) (σ j))) =
      ∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (X (σ i) j) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Equiv.sum_comp (σ : Fin 3 ≃ Fin 3) (fun j => Complex.normSq (X (σ i) j))
  show (∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (X (σ i) (σ j))) = _
  rw [hi]
  exact Equiv.sum_comp (σ : Fin 3 ≃ Fin 3) (fun i => ∑ j : Fin 3, Complex.normSq (X i j))

/-- **The cost is a function of the relative frame.** A common class relabeling
of both sectors divides out. -/
theorem common_relabel (σ : Equiv.Perm (Fin 3)) (A B : M) :
    frameCost (relabel σ A) (relabel σ B) = frameCost A B := by
  rw [frameCost_formula, frameCost_formula]
  refine congrArg (fun x => x/12) ?_
  rw [comm_relabel]
  exact frobenius_relabel σ (A*B - B*A)

/-! ## Alignment -/

/-- Frames diagonal in one basis cost nothing. -/
theorem aligned_zero (p q : Fin 3 → ℂ) : frameCost (diagonal p) (diagonal q) = 0 := by
  rw [frameCost_zero_iff, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

/-- A positive cost proves genuine relative mixing: the two frames are not
simultaneously diagonal. -/
theorem mixes_of_positive (A B : M) (h : 0 < frameCost A B) :
    ¬ ∃ p q : Fin 3 → ℂ, A = diagonal p ∧ B = diagonal q := by
  rintro ⟨p, q, rfl, rfl⟩
  linarith [aligned_zero p q, h]

/-! ## Gap weighting: the symmetry-breaking ingredient -/

/-- The gap of a generation pair in an eigenphase assignment. -/
def gap (phase : Fin 3 → ℂ) (i j : Fin 3) : ℝ := Complex.normSq (phase i - phase j)

theorem gap_symm (phase : Fin 3 → ℂ) (i j : Fin 3) :
    gap phase i j = gap phase j i := by
  show Complex.normSq (phase i - phase j) = Complex.normSq (phase j - phase i)
  rw [← Complex.normSq_neg (phase i - phase j)]
  congr 1
  abel

theorem gap_nonneg (phase : Fin 3 → ℂ) (i j : Fin 3) : 0 ≤ gap phase i j :=
  Complex.normSq_nonneg _

theorem gap_self (phase : Fin 3 → ℂ) (i : Fin 3) : gap phase i i = 0 := by
  show Complex.normSq (phase i - phase i) = 0
  rw [sub_self]
  exact Complex.normSq_zero

/-- A distinct eigenphase pair carries a strictly positive price. -/
theorem gap_pos (phase : Fin 3 → ℂ) (i j : Fin 3) (h : phase i ≠ phase j) :
    0 < gap phase i j := by
  apply Complex.normSq_pos.mpr
  intro he
  exact h (sub_eq_zero.mp he)

/-- **Gap-weighted mixing.** In one sector's eigenphase basis the cost is the
other frame's entries, each priced by its own eigenphase gap. -/
theorem gap_weighted (phase : Fin 3 → ℂ) (B : M) :
    frameCost (diagonal phase) B =
      (∑ i, ∑ j, gap phase i j * Complex.normSq (B i j))/12 :=
  diagonal_response phase B

/-- The diagonal carries no price: only off-diagonal mixing entries are charged. -/
theorem diagonal_free (phase : Fin 3 → ℂ) (B : M) :
    frameCost (diagonal phase) B =
      (∑ i : Fin 3, ∑ j : Fin 3,
        if i = j then 0 else gap phase i j * Complex.normSq (B i j))/12 := by
  rw [gap_weighted]
  refine congrArg (fun x => x/12) ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · subst h
    simp [gap_self]
  · simp [h]

/-! ## The primitive plane rotations -/

/-- Relative rotation acting in the `(0,1)` generation plane. -/
def rot01 (c s : ℝ) : M :=
  !![(c:ℂ), (-s:ℂ), 0; (s:ℂ), (c:ℂ), 0; 0, 0, 1]

/-- Relative rotation acting in the `(0,2)` generation plane. -/
def rot02 (c s : ℝ) : M :=
  !![(c:ℂ), 0, (-s:ℂ); 0, 1, 0; (s:ℂ), 0, (c:ℂ)]

/-- Relative rotation acting in the `(1,2)` generation plane. -/
def rot12 (c s : ℝ) : M :=
  !![1, 0, 0; 0, (c:ℂ), (-s:ℂ); 0, (s:ℂ), (c:ℂ)]

/-- A reversed eigenphase difference carries the same price. -/
theorem normSq_flip (u v : ℂ) : Complex.normSq (v + -u) = Complex.normSq (u + -v) := by
  rw [← Complex.normSq_neg (u + -v)]
  congr 1
  abel

/-- The commutator of an eigenphase frame with the `(0,1)` plane rotation is
carried entirely by that one generation pair. -/
theorem comm_diag_rot01 (phase : Fin 3 → ℂ) (c s : ℝ) :
    diagonal phase * rot01 c s - rot01 c s * diagonal phase =
      !![0, -((s:ℂ)*(phase 0 - phase 1)), 0;
          ((s:ℂ)*(phase 1 - phase 0)), 0, 0;
          0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot01, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

theorem comm_diag_rot02 (phase : Fin 3 → ℂ) (c s : ℝ) :
    diagonal phase * rot02 c s - rot02 c s * diagonal phase =
      !![0, 0, -((s:ℂ)*(phase 0 - phase 2));
          0, 0, 0;
          ((s:ℂ)*(phase 2 - phase 0)), 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot02, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

theorem comm_diag_rot12 (phase : Fin 3 → ℂ) (c s : ℝ) :
    diagonal phase * rot12 c s - rot12 c s * diagonal phase =
      !![0, 0, 0;
          0, 0, -((s:ℂ)*(phase 1 - phase 2));
          0, ((s:ℂ)*(phase 2 - phase 1)), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot12, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- **Closed form: the `(0,1)` plane rotation costs its own gap times its
squared off-diagonal amplitude.** -/
theorem plane_cost01 (phase : Fin 3 → ℂ) (c s : ℝ) :
    frameCost (diagonal phase) (rot01 c s) = gap phase 0 1 * s^2 / 6 := by
  rw [frameCost_formula, comm_diag_rot01, gap]
  simp only [Fin.sum_univ_three, sq, sub_eq_add_neg]
  simp
  simp only [normSq_flip]
  ring

/-- **Closed form for the `(0,2)` plane rotation.** -/
theorem plane_cost02 (phase : Fin 3 → ℂ) (c s : ℝ) :
    frameCost (diagonal phase) (rot02 c s) = gap phase 0 2 * s^2 / 6 := by
  rw [frameCost_formula, comm_diag_rot02, gap]
  simp only [Fin.sum_univ_three, sq, sub_eq_add_neg]
  simp
  simp only [normSq_flip]
  ring

/-- **Closed form for the `(1,2)` plane rotation.** -/
theorem plane_cost12 (phase : Fin 3 → ℂ) (c s : ℝ) :
    frameCost (diagonal phase) (rot12 c s) = gap phase 1 2 * s^2 / 6 := by
  rw [frameCost_formula, comm_diag_rot12, gap]
  simp only [Fin.sum_univ_three, sq, sub_eq_add_neg]
  simp
  simp only [normSq_flip]
  ring

/-! ## The selection statement -/

/-- Gap times amplitude: the price of a plane transfer factorizes. -/
theorem cost_times_six01 (phase : Fin 3 → ℂ) (c s : ℝ) :
    6 * frameCost (diagonal phase) (rot01 c s) = gap phase 0 1 * s^2 := by
  rw [plane_cost01]; field_simp

theorem cost_times_six02 (phase : Fin 3 → ℂ) (c s : ℝ) :
    6 * frameCost (diagonal phase) (rot02 c s) = gap phase 0 2 * s^2 := by
  rw [plane_cost02]; field_simp

theorem cost_times_six12 (phase : Fin 3 → ℂ) (c s : ℝ) :
    6 * frameCost (diagonal phase) (rot12 c s) = gap phase 1 2 * s^2 := by
  rw [plane_cost12]; field_simp

/-- **Distinct gaps strictly separate equal-size rotations.** -/
theorem cost_lt_of_gap_lt (phase : Fin 3 → ℂ) (c s : ℝ) (hs : s ≠ 0)
    (h : gap phase 0 1 < gap phase 1 2) :
    frameCost (diagonal phase) (rot01 c s) < frameCost (diagonal phase) (rot12 c s) := by
  rw [plane_cost01, plane_cost12]
  have hk : gap phase 0 1 * s^2 < gap phase 1 2 * s^2 :=
    mul_lt_mul_of_pos_right h (sq_pos_of_ne_zero hs)
  linarith

/-- **Gap order is exactly cost order** at fixed nonzero rotation size. -/
theorem cost_le_iff_gap_le (phase : Fin 3 → ℂ) (c s : ℝ) (hs : 0 < s^2) :
    frameCost (diagonal phase) (rot01 c s) ≤ frameCost (diagonal phase) (rot12 c s) ↔
      gap phase 0 1 ≤ gap phase 1 2 := by
  rw [plane_cost01, plane_cost12]
  constructor
  · intro H
    by_contra hgt
    have hne : s ≠ 0 := by intro he; rw [he] at hs; linarith
    have hlt : gap phase 1 2 < gap phase 0 1 := lt_of_not_ge hgt
    have hk : gap phase 1 2 * s^2 < gap phase 0 1 * s^2 :=
      mul_lt_mul_of_pos_right hlt (sq_pos_of_ne_zero hne)
    linarith
  · intro H
    have hk : gap phase 0 1 * s^2 ≤ gap phase 1 2 * s^2 :=
      mul_le_mul_of_nonneg_right H (le_of_lt hs)
    linarith

/-- The cheapest of the three planes is a smallest-gap plane. -/
theorem least_cost_le_min (phase : Fin 3 → ℂ) (c s : ℝ)
    (h01 : gap phase 0 1 ≤ gap phase 0 2) (h12 : gap phase 1 2 ≤ gap phase 0 2) :
    frameCost (diagonal phase) (rot01 c s) ≤ frameCost (diagonal phase) (rot02 c s) ∧
      frameCost (diagonal phase) (rot12 c s) ≤ frameCost (diagonal phase) (rot02 c s) := by
  rw [plane_cost01, plane_cost02, plane_cost12]
  have hk1 : gap phase 0 1 * s^2 ≤ gap phase 0 2 * s^2 :=
    mul_le_mul_of_nonneg_right h01 (sq_nonneg s)
  have hk2 : gap phase 1 2 * s^2 ≤ gap phase 0 2 * s^2 :=
    mul_le_mul_of_nonneg_right h12 (sq_nonneg s)
  exact ⟨by linarith, by linarith⟩

/-- A transfer through a wider gap at the same amplitude buys no additional
alignment: it is pure extra cost. -/
theorem wasted_transfer (phase : Fin 3 → ℂ) (c s t : ℝ) (hs : s ≠ 0)
    (h : gap phase 0 1 < gap phase 1 2) (ht : t^2 = s^2) :
    frameCost (diagonal phase) (rot01 c s) < frameCost (diagonal phase) (rot12 c t) := by
  rw [plane_cost01, plane_cost12, ht]
  have hk : gap phase 0 1 * s^2 < gap phase 1 2 * s^2 :=
    mul_lt_mul_of_pos_right h (sq_pos_of_ne_zero hs)
  linarith

/-- **Required-signal law.** Delivering a joint signal `σ` needs `6σ / gap` of
squared off-diagonal amplitude: the largest gap needs the least mixing. -/
theorem amplitude_largest_gap_le (phase : Fin 3 → ℂ) (σ : ℝ)
    (hσ : 0 ≤ σ) (h1 : 0 < gap phase 0 1)
    (h2 : gap phase 0 1 ≤ gap phase 1 2) :
    6*σ / gap phase 1 2 ≤ 6*σ / gap phase 0 1 := by
  have hg : 0 < gap phase 1 2 := lt_of_lt_of_le h1 h2
  have hk : (6*σ) * gap phase 0 1 ≤ (6*σ) * gap phase 1 2 :=
    mul_le_mul_of_nonneg_left h2 (by nlinarith)
  rw [div_le_div_iff₀ hg h1]
  nlinarith

/-! ## The whole frame: three generation pairs, three prices -/

/-- The transfer weight a frame puts on one unordered generation pair: both
directions together. -/
def pairWeight (B : M) (i j : Fin 3) : ℝ :=
  Complex.normSq (B i j) + Complex.normSq (B j i)

theorem pairWeight_nonneg (B : M) (i j : Fin 3) : 0 ≤ pairWeight B i j := by
  show Complex.normSq (B i j) + Complex.normSq (B j i) ≥ 0
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem pairWeight_symm (B : M) (i j : Fin 3) :
    pairWeight B i j = pairWeight B j i := by
  show Complex.normSq (B i j) + Complex.normSq (B j i)
      = Complex.normSq (B j i) + Complex.normSq (B i j)
  ring

/-- **Three-pair decomposition.** For an arbitrary relative frame the double
sum collapses to the three unordered generation pairs, each carrying its own
gap times its own total weight. -/
theorem sum_three_pairs (phase : Fin 3 → ℂ) (B : M) :
    (∑ i, ∑ j, gap phase i j * Complex.normSq (B i j)) =
      gap phase 0 1 * pairWeight B 0 1
        + gap phase 0 2 * pairWeight B 0 2
        + gap phase 1 2 * pairWeight B 1 2 := by
  have r0 : (∑ j : Fin 3, gap phase 0 j * Complex.normSq (B 0 j))
      = gap phase 0 1 * Complex.normSq (B 0 1) + gap phase 0 2 * Complex.normSq (B 0 2) := by
    rw [Fin.sum_univ_three, gap_self]
    simp only [zero_mul]
    ring
  have r1 : (∑ j : Fin 3, gap phase 1 j * Complex.normSq (B 1 j))
      = gap phase 1 0 * Complex.normSq (B 1 0) + gap phase 1 2 * Complex.normSq (B 1 2) := by
    rw [Fin.sum_univ_three, gap_self]
    simp only [zero_mul]
    ring
  have r2 : (∑ j : Fin 3, gap phase 2 j * Complex.normSq (B 2 j))
      = gap phase 2 0 * Complex.normSq (B 2 0) + gap phase 2 1 * Complex.normSq (B 2 1) := by
    rw [Fin.sum_univ_three, gap_self]
    simp only [zero_mul]
    ring
  calc (∑ i : Fin 3, ∑ j : Fin 3, gap phase i j * Complex.normSq (B i j))
      = (gap phase 0 1 * Complex.normSq (B 0 1) + gap phase 0 2 * Complex.normSq (B 0 2))
        + (gap phase 1 0 * Complex.normSq (B 1 0) + gap phase 1 2 * Complex.normSq (B 1 2))
        + (gap phase 2 0 * Complex.normSq (B 2 0) + gap phase 2 1 * Complex.normSq (B 2 1)) := by
        rw [Fin.sum_univ_three, r0, r1, r2]
    _ = gap phase 0 1 * (Complex.normSq (B 0 1) + Complex.normSq (B 1 0))
        + gap phase 0 2 * (Complex.normSq (B 0 2) + Complex.normSq (B 2 0))
        + gap phase 1 2 * (Complex.normSq (B 1 2) + Complex.normSq (B 2 1)) := by
        rw [gap_symm phase 0 1, gap_symm phase 0 2, gap_symm phase 1 2]
        ring

/-- **The frame price in closed form**: a linear program in the three pair
weights, with the three spectral gaps as coefficients. -/
theorem frame_price (phase : Fin 3 → ℂ) (B : M) :
    frameCost (diagonal phase) B =
      (gap phase 0 1 * pairWeight B 0 1
        + gap phase 0 2 * pairWeight B 0 2
        + gap phase 1 2 * pairWeight B 1 2) / 12 := by
  rw [gap_weighted, sum_three_pairs]

/-- **Least-cost routing.** With a transfer weight spread over two generation
pairs, the joint price is at least the price of putting all of it on the
smaller gap. -/
theorem route_price_ge (g1 g2 x1 x2 : ℝ) (h12 : g1 ≤ g2) (hx2 : 0 ≤ x2) :
    g1 * x1 + g2 * x2 ≥ g1 * (x1 + x2) := by
  have hd : 0 ≤ g2 - g1 := by linarith
  nlinarith [mul_nonneg hx2 hd]

/-- Under a strictly ordered gap the concentration is unique: the wider pair
must carry nothing. -/
theorem route_price_eq_iff (g1 g2 x1 x2 : ℝ) (h12 : g1 < g2) (hx2 : 0 ≤ x2) :
    g1 * x1 + g2 * x2 = g1 * (x1 + x2) ↔ x2 = 0 := by
  constructor
  · intro H
    have hd : 0 ≤ g2 - g1 := by linarith
    have hs : 0 ≤ (g2 - g1) * x2 := mul_nonneg hd hx2
    have key : (g2 - g1) * x2 = 0 := by nlinarith
    exact (mul_eq_zero.mp key).resolve_left (by linarith)
  · intro H
    rw [H]
    ring

/-- **Applied to a frame.** If the two wider generation pairs carry no transfer,
the whole price is the smallest gap times its own pair weight. -/
theorem frame_route_min (phase : Fin 3 → ℂ) (B : M)
    (h02 : pairWeight B 0 2 = 0) (h12 : pairWeight B 1 2 = 0) :
    frameCost (diagonal phase) B = gap phase 0 1 * pairWeight B 0 1 / 12 := by
  rw [frame_price, h02, h12]
  simp only [mul_zero, add_zero]

/-- A plane rotation puts all its weight on its own pair, split equally over
both directions. -/
theorem pairWeight_rot01 (c s : ℝ) :
    pairWeight (rot01 c s) 0 1 = 2 * s^2 ∧ pairWeight (rot01 c s) 0 2 = 0 ∧
      pairWeight (rot01 c s) 1 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show Complex.normSq (rot01 c s 0 1) + Complex.normSq (rot01 c s 1 0) = 2 * s^2
    simp only [rot01]; simp; ring
  · show Complex.normSq (rot01 c s 0 2) + Complex.normSq (rot01 c s 2 0) = 0
    simp only [rot01]; simp
  · show Complex.normSq (rot01 c s 1 2) + Complex.normSq (rot01 c s 2 1) = 0
    simp only [rot01]; simp

/-- Consistency: the pair-price formula reproduces the plane closed form. -/
theorem plane_cost01_from_price (phase : Fin 3 → ℂ) (c s : ℝ) :
    frameCost (diagonal phase) (rot01 c s) = gap phase 0 1 * s^2 / 6 := by
  have hw := pairWeight_rot01 c s
  rw [frame_price, hw.1, hw.2.1, hw.2.2]
  ring

/-! ## Range, attainability and the ties that remain -/

/-- The signal of one plane is bounded by that plane's gap over six. -/
theorem signal_range01 (phase : Fin 3 → ℂ) (c s : ℝ) (h : c^2 + s^2 = 1) :
    frameCost (diagonal phase) (rot01 c s) ≤ gap phase 0 1 / 6 := by
  rw [plane_cost01]
  have hk : gap phase 0 1 * s^2 ≤ gap phase 0 1 * 1 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (gap_nonneg phase 0 1)
  linarith

/-- Endpoint at maximal mixing `c² = s² = 1/2`. -/
theorem signal_max01 (phase : Fin 3 → ℂ) :
    frameCost (diagonal phase)
      (rot01 (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)) = gap phase 0 1 / 12 := by
  have h : (Real.sqrt 2 / 2 : ℝ)^2 = 1/2 := by
    rw [div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  rw [plane_cost01, h]
  ring

/-- **Attainability.** Every signal up to the maximum is reached by some
normalized rotation, so a required signal determines a level set, not a point. -/
theorem signal_attainable (phase : Fin 3 → ℂ) (σ : ℝ)
    (h0 : 0 < gap phase 0 1) (hσ : 0 ≤ σ) (hσ2 : σ ≤ gap phase 0 1 / 6) :
    ∃ c s : ℝ, c^2 + s^2 = 1 ∧ frameCost (diagonal phase) (rot01 c s) = σ := by
  have hle : 6*σ / gap phase 0 1 ≤ 1 := (div_le_one h0).mpr (by nlinarith)
  have hn : 0 ≤ 6*σ / gap phase 0 1 := div_nonneg (by nlinarith) h0.le
  refine ⟨Real.sqrt (1 - 6*σ / gap phase 0 1), Real.sqrt (6*σ / gap phase 0 1), ?_, ?_⟩
  · rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt hn]
    exact sub_add_cancel _ _
  · rw [plane_cost01, Real.sq_sqrt hn]
    field_simp

/-- Even in the amplitude: the response fixes `s²`, not its sign. -/
theorem sign_tie01 (phase : Fin 3 → ℂ) (c s : ℝ) :
    frameCost (diagonal phase) (rot01 c (-s)) = frameCost (diagonal phase) (rot01 c s) := by
  rw [plane_cost01, plane_cost01]
  ring

/-- **CP-even.** The response cannot select a conjugation branch. -/
theorem conjugation_tie (A B : M) :
    frameCost (OscillationObservables.conjugated A)
      (OscillationObservables.conjugated B) = frameCost A B :=
  FlavourOrderComparison.conjugation_tie A B

end PMDynamics.RelativeFrameCost
