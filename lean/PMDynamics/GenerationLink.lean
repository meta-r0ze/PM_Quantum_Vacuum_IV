import PMNested.Generations
import PMArch.ChannelSymmetry
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The generation update, its symmetric link, and what that selects

Review items 1–3. Paper III derives three generations as the unordered pairs of distinct
nontrivial glue classes (`Generations.three_pairs`). Paper I's substrate symmetries permute the
three classes as `S₃` (`ChannelSymmetry.hada_class`, `flip_class`).

**Item 1: the generation carrier and its primitive transitions.**
* A generation is the pair of classes it uses. Equivalently, it is the one class it omits
  (`pair_of_missing`), so the generation label lives in `Fin 3`.
* A primitive generation transition replaces one class of the pair. `share_one`: any two distinct
  generations share exactly one class, so every generation is one primitive step from every other
  (the complete graph on three generations).
* Class permutations act on generations by the same permutation of the missing class
  (`act_pair`). A link built from substrate data alone is invariant under them.

**Items 2–3: what an invariant link selects.**
* `invariant_form`: an `S₃`-invariant link on three generations is `α·1 + β·(J − 1)`.
* `democratic_eigen`, `sumzero_eigen`: `(1,1,1)` has eigenvalue `α + 2β`, and every sum-zero vector
  has `α − β`. So at the symmetric point the two other generations are **degenerate**.
* `heavy_is_democratic`: for `β ≠ 0`, every eigenvector at `α + 2β` is a multiple of `(1,1,1)`.
* `heavy_unmixed`: if up and down links are both invariant, the mixing matrix `U_uᴴ U_d` has no
  entries between the democratic generation and the other two. That generation does not mix.
* `light_mixing_free`: any rotation inside the sum-zero plane is still an eigenbasis. So the light
  mixing angle is **not** selected by the symmetric link.

* `heavy_inaccessible`: below the heavy wall threshold only the light branch can be prepared.

So the symmetric update selects the structure (one distinct generation unmixed with a degenerate
pair). The observed light-sector mixing, the `V_cb`/`V_ub` entries and the light mass splitting all
require `S₃` breaking. The supplied CKM/PMNS formulas are not derived here.
-/

noncomputable section
namespace PMDynamics.GenerationLink
open Matrix

/-! ## Item 1 -/

/-- The generation omitting class `c`: its two classes. -/
def pair_of_missing (c : Fin 3) : Finset (Fin 3) := Finset.univ.erase c

theorem pair_card (c : Fin 3) : (pair_of_missing c).card = 2 := by
  fin_cases c <;> decide

/-- The three generations are exactly the three pairs of distinct classes. -/
theorem pairs_are_generations :
    (∀ s : Finset (Fin 3), s.card = 2 → ∃ c, pair_of_missing c = s) ∧
      Function.Injective pair_of_missing := by
  decide

/-- **Every two generations are one primitive step apart.** -/
theorem share_one (c d : Fin 3) (h : c ≠ d) :
    (pair_of_missing c ∩ pair_of_missing d).card = 1 := by
  revert c d; decide

/-- Class permutations act on generations through the missing class. -/
theorem act_pair (σ : Equiv.Perm (Fin 3)) (c : Fin 3) :
    (pair_of_missing c).map σ.toEmbedding = pair_of_missing (σ c) := by
  ext x
  simp [pair_of_missing]

/-! ## Items 2–3 -/

variable {Y : Matrix (Fin 3) (Fin 3) ℂ}

/-- **An invariant link is `α·1 + β·(J − 1)`.** -/
theorem invariant_form (h : ∀ (σ : Equiv.Perm (Fin 3)) i j, Y (σ i) (σ j) = Y i j) :
    ∀ i j, Y i j = if i = j then Y 0 0 else Y 0 1 := by
  have e11 := h (Equiv.swap 0 1) 0 0
  have e22 := h (Equiv.swap 0 2) 0 0
  have e10 := h (Equiv.swap 0 1) 0 1
  have e02 := h (Equiv.swap 1 2) 0 1
  have e20 := h (Equiv.swap 0 2) 0 2
  have e12 := h (Equiv.swap 0 1) 0 2
  have e21 := h (Equiv.swap 0 2) 0 1
  simp [Equiv.swap_apply_of_ne_of_ne] at e11 e22 e10 e02 e20 e12 e21
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- The democratic vector `(1,1,1)`. -/
def w : Fin 3 → ℂ := fun _ => 1

theorem democratic_eigen (a b : ℂ) :
    (of fun i j : Fin 3 => if i = j then a else b) *ᵥ w = (a + 2 * b) • w := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, w] <;> ring

theorem sumzero_eigen (a b : ℂ) (v : Fin 3 → ℂ) (hv : v 0 + v 1 + v 2 = 0) :
    (of fun i j : Fin 3 => if i = j then a else b) *ᵥ v = (a - b) • v := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] <;> linear_combination b * hv

/-- **The heavy state is democratic.** -/
theorem heavy_is_democratic (a b : ℂ) (hb : b ≠ 0) (v : Fin 3 → ℂ)
    (hv : (of fun i j : Fin 3 => if i = j then a else b) *ᵥ v = (a + 2 * b) • v) :
    v = ((v 0 + v 1 + v 2) / 3) • w := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  have k0 : b * (3 * v 0 - (v 0 + v 1 + v 2)) = 0 := by linear_combination -h0
  have k1 : b * (3 * v 1 - (v 0 + v 1 + v 2)) = 0 := by linear_combination -h1
  have k2 : b * (3 * v 2 - (v 0 + v 1 + v 2)) = 0 := by linear_combination -h2
  have m0 := (mul_eq_zero.mp k0).resolve_left hb
  have m1 := (mul_eq_zero.mp k1).resolve_left hb
  have m2 := (mul_eq_zero.mp k2).resolve_left hb
  ext i; fin_cases i
  · simp [w]; linear_combination m0 / 3
  · simp [w]; linear_combination m1 / 3
  · simp [w]; linear_combination m2 / 3

/-- **The democratic generation does not mix.** If both mass bases put the same unit vector in
slot `k` (up to a phase `c`), the mixing matrix `U_uᴴ U_d` has row and column `k` equal to `c` on the
diagonal and zero elsewhere. -/
theorem heavy_unmixed {n : Type*} [Fintype n] [DecidableEq n] (Uu Ud : Matrix n n ℂ)
    (hu : Uuᴴ * Uu = 1) (hd : Udᴴ * Ud = 1) (k : n) (c : ℂ) (hc : star c * c = 1)
    (hcol : ∀ i, Ud i k = c * Uu i k) :
    (∀ i, i ≠ k → (Uuᴴ * Ud) i k = 0) ∧ (∀ j, j ≠ k → (Uuᴴ * Ud) k j = 0) := by
  constructor
  · intro i hi
    have : (Uuᴴ * Ud) i k = c * (Uuᴴ * Uu) i k := by
      simp only [mul_apply, hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hu, one_apply_ne hi, mul_zero]
  · intro j hj
    have hcol' : ∀ i, Uu i k = star c * Ud i k := by
      intro i; rw [hcol, ← mul_assoc, hc, one_mul]
    have : (Uuᴴ * Ud) k j = c * (Udᴴ * Ud) k j := by
      simp only [mul_apply, conjTranspose_apply, hcol', star_mul, star_star, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hd, one_apply_ne hj.symm, mul_zero]

/-- **The light mixing angle is free.** Every vector in the sum-zero plane is an eigenvector, so
any rotation of a light eigenbasis is again one. -/
theorem light_mixing_free (a b : ℂ) (θ : ℝ) (v₁ v₂ : Fin 3 → ℂ) (h₁ : v₁ 0 + v₁ 1 + v₁ 2 = 0)
    (h₂ : v₂ 0 + v₂ 1 + v₂ 2 = 0) :
    (of fun i j : Fin 3 => if i = j then a else b) *ᵥ ((Real.cos θ : ℂ) • v₁ + (Real.sin θ : ℂ) • v₂) =
      (a - b) • ((Real.cos θ : ℂ) • v₁ + (Real.sin θ : ℂ) • v₂) := by
  apply sumzero_eigen
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (Real.cos θ : ℂ) * h₁ + (Real.sin θ : ℂ) * h₂

/-- **Below the heavy threshold only the light branch is accessible.** A preparation of energy `E`
with `E² < m₊²` cannot populate a heavy-branch state at any momentum, since its energy squared is
`p² + m₊²` (`WallSpectrumLink.wall_energies`). -/
theorem heavy_inaccessible (E mP : ℝ) (h : E ^ 2 < mP) (p : ℝ) : E ^ 2 < p ^ 2 + mP := by
  nlinarith [sq_nonneg p]

end PMDynamics.GenerationLink
