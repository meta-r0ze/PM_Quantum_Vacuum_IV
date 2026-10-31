import PMDynamics.CKM
import PMDynamics.Mixing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# What the 1/688 dressing predicts, and what it needs

The calculator multiplies every CKM amplitude by `q = √(1 − 1/688)`, `688 = νΔ`.

* `ckm_unitary_matrix`, `ckm_unitary_cols`: the undressed matrix satisfies `VV† = V†V = 1`.
* `dressed_gram`, `dressed_gram_cols`: the dressed matrix `A = qV` has `AA† = A†A = (687/688)·1`.
  Every row and every column loses the same `1/688`; `first_row_sum` states it for the first row.
* `first_row_deficit_test`: the first-row sum measured from `|V_ud|`, `|V_us|`, `|V_ub|`,
  `0.9984 ± 0.0007` (CKM 2023 workshop), is within `0.22σ` of the dressed prediction and more
  than `2.28σ` from exact unitarity. This is a fixed benchmark test of the dressing alternative, not a selection of it.
* `dilation_needs_three`: if a dressed block `A` with `AA† = c·1`, `c ≠ 1`, is the
  upper-left `3×3` block of any unitary matrix of size `3 + m`, then `m ≥ 3`. The lost `1/688`
  cannot go into one extra outcome: Conservation requires at least three further channels
  (by the same argument applied to `A†A`, three more on the input side).
* `arg_dressing_invariant`, `jarlskog_dressed`: phases, hence the unitarity-triangle angles,
  are unchanged; the Jarlskog invariant scales by `(687/688)²` to `(3.011, 3.022)×10⁻⁵`, and
  Paper III's `φ²T_geo η` then exceeds it by more than 2% (`papers_disagree_dressed`).

So the dressing and the paper's stated exact unitarity ("probability cannot be lost") cannot
both hold for the three-generation matrix. The dressing is close to that fixed first-row benchmark; keeping
it requires naming the three or more channels that carry the `1/688`.
-/

noncomputable section
namespace PMDynamics.CKMDressing
open Matrix Complex ComplexConjugate PMDynamics.CKM

def V (c12 s12 c23 s23 c13 s13 : ℝ) (u : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of (ckm c12 s12 c23 s23 c13 s13 u)

variable {c12 s12 c23 s23 c13 s13 : ℝ} {u : ℂ}

theorem ckm_unitary_matrix (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1)
    (r13 : c13^2 + s13^2 = 1) (hu : u * conj u = 1) :
    V c12 s12 c23 s23 c13 s13 u * (V c12 s12 c23 s23 c13 s13 u)ᴴ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [V, Matrix.conjTranspose_apply] using ckm_unitary r12 r23 r13 hu i j

theorem ckm_unitary_cols (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1)
    (r13 : c13^2 + s13^2 = 1) (hu : u * conj u = 1) :
    (V c12 s12 c23 s23 c13 s13 u)ᴴ * V c12 s12 c23 s23 c13 s13 u = 1 :=
  mul_eq_one_comm.mp (ckm_unitary_matrix r12 r23 r13 hu)

/-- The dressing amplitude squared. -/
def q2 : ℝ := 687/688

theorem dressed_gram (q : ℝ) (hq : q^2 = q2) (r12 : c12^2 + s12^2 = 1)
    (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1) (hu : u * conj u = 1) :
    ((q:ℂ) • V c12 s12 c23 s23 c13 s13 u) * ((q:ℂ) • V c12 s12 c23 s23 c13 s13 u)ᴴ =
      ((q2:ℝ):ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ckm_unitary_matrix r12 r23 r13 hu, smul_smul]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← hq]; push_cast; ring

theorem dressed_gram_cols (q : ℝ) (hq : q^2 = q2) (r12 : c12^2 + s12^2 = 1)
    (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1) (hu : u * conj u = 1) :
    ((q:ℂ) • V c12 s12 c23 s23 c13 s13 u)ᴴ * ((q:ℂ) • V c12 s12 c23 s23 c13 s13 u) =
      ((q2:ℝ):ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ckm_unitary_cols r12 r23 r13 hu, smul_smul]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← hq]; push_cast; ring

theorem first_row_sum (q : ℝ) (hq : q^2 = q2) (r12 : c12^2 + s12^2 = 1)
    (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1) (hu : u * conj u = 1) :
    (∑ k, Complex.normSq (((q:ℂ) • V c12 s12 c23 s23 c13 s13 u) 0 k) : ℂ) = ((687/688 : ℝ) : ℂ) := by
  have h := congrFun (congrFun (dressed_gram q hq r12 r23 r13 hu) 0) 0
  rw [Matrix.mul_apply] at h
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj] at h
  rw [h]; simp [q2]

/-- Measured first-row sum `0.9984 ± 0.0007` against the two hypotheses. -/
theorem first_row_deficit_test :
    |(1 - 1/688 : ℝ) - 0.9984| / 0.0007 < 0.22 ∧ 2.28 < |(1 : ℝ) - 0.9984| / 0.0007 := by
  constructor
  · rw [abs_of_pos (by norm_num)]; norm_num
  · rw [abs_of_pos (by norm_num)]; norm_num

/-- A unitary dilation of a uniformly dressed `3×3` block needs at least three extra channels. -/
theorem dilation_needs_three {m : ℕ} (W : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) ℂ)
    (hW : W * Wᴴ = 1) {c : ℂ} (hc : c ≠ 1)
    (hA : W.toBlocks₁₁ * (W.toBlocks₁₁)ᴴ = c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) : 3 ≤ m := by
  rw [← Matrix.fromBlocks_toBlocks W, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hW
  have h11 := hW.1
  set B := W.toBlocks₁₂
  have hB : B * Bᴴ = (1 - c) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [sub_smul, one_smul, ← hA, ← h11]; abel
  have hunit : IsUnit ((1 - c) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hc))).pow _
  have hr : (B * Bᴴ).rank = 3 := by
    rw [hB, Matrix.rank_of_isUnit _ hunit]; simp
  have h1 := Matrix.rank_mul_le_left B Bᴴ
  have h2 := Matrix.rank_le_width B
  omega

theorem arg_dressing_invariant {q : ℝ} (hq : 0 < q) (z : ℂ) : ((q:ℂ) * z).arg = z.arg :=
  Complex.arg_real_mul z hq

theorem jarlskog_dressed :
    (3.011e-5 : ℝ) < q2^2 * pmJ ∧ q2^2 * pmJ < 3.022e-5 := by
  have h := pmJ_bounds
  unfold q2
  constructor <;> nlinarith [h.1, h.2]

theorem papers_disagree_dressed : 1.02 * (q2^2 * pmJ) < pm3J := by
  have h1 := jarlskog_dressed; have h2 := pm3J_bounds
  linarith [h1.2, h2.1]

end PMDynamics.CKMDressing
