import PMDynamics.GenerationLink
import PMDynamics.PMNSIntervals

/-!
# How far the lepton axis breaks the generation symmetry, and a no-go for the leptons

`GenerationLink` showed that a fully `S₃`-symmetric link leaves one generation unmixed, with the
others degenerate, so observed mixing measures `S₃` breaking. The natural breaking source already
in the framework is the lepton axis (`CarrierRepresentation`: axis `0`). Only the vector class has
axes. Its carriers are `±2eᵢ`; the spinor classes are `(±1,±1,±1,±1)`.

**What the lepton axis leaves.**
* `stabilizer_of_fixed`: a class permutation fixing the vector class is the identity or the swap
  of the two spinor classes. A substrate symmetry fixing a lepton-axis carrier fixes the class
  that carrier belongs to, so **at most a `Z₂` survives** (μ–τ type).
* `flip_keeps_axis`: Paper I's `flip` keeps axis `0` and swaps the spinor classes
  (`ChannelSymmetry.flip_class`). `hada_leaves_axis`: `hada` sends `2e₀` into a spinor class, so it
  is broken.

**What a residual `Z₂` would do.**
* `z2_form`: a link invariant under exchanging generations `1, 2` has `Y₁₁ = Y₂₂`, `Y₀₁ = Y₀₂`,
  `Y₁₀ = Y₂₀`, `Y₁₂ = Y₂₁`.
* `antisym_eigen`, `antisym_protected`: `(0, 1, −1)` is an eigenvector, and, when its eigenvalue
  is not shared with the symmetric block, the only one at that eigenvalue.
* `shared_state_zero`: if two sectors share a mass state (in any slots), the mixing matrix vanishes
  in that state's column away from its partner row.

**The no-go.** `pmns_all_nonzero`: every entry of the supplied PMNS matrix is nonzero
(`PMNSIntervals.squared_entry_bounds`). `pmns_no_shared_state`: so no two lepton mass bases sharing
a state produce it. The charged-lepton and neutrino links cannot both keep the protected `Z₂` state.
The lepton sector must break the residual `Z₂` too, so the lepton axis alone cannot be the whole
breaking law. For quarks, an exact shared state would make `V_ub = V_cb = 0`. The observed entries
are small but nonzero, so there the `Z₂` is at best approximate.
-/

noncomputable section
namespace PMDynamics.GenerationBreaking
open Matrix

/-- **At most a `Z₂` fixes a class.** -/
theorem stabilizer_of_fixed :
    ∀ σ : Equiv.Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = Equiv.swap 1 2 := by decide

/-- `flip` keeps the lepton axis. -/
theorem flip_keeps_axis :
    PMArch.ChannelSymmetry.flip ![2, 0, 0, 0] = ![-2, 0, 0, 0] := by decide

/-- `hada` takes the lepton carrier into a spinor class. -/
theorem hada_leaves_axis :
    PMArch.ChannelSymmetry.hada ![2, 0, 0, 0] = ![1, 1, 1, 1] ∧
      ![1, 1, 1, 1] ∈ PMArch.ChannelSymmetry.carriers 2 := by
  decide +kernel

variable {Y : Matrix (Fin 3) (Fin 3) ℂ}

/-- **The `Z₂`-invariant form.** -/
theorem z2_form (h : ∀ i j, Y (Equiv.swap 1 2 i) (Equiv.swap 1 2 j) = Y i j) :
    Y 1 1 = Y 2 2 ∧ Y 0 1 = Y 0 2 ∧ Y 1 0 = Y 2 0 ∧ Y 1 2 = Y 2 1 := by
  have a := h 2 2
  have b := h 0 2
  have c := h 2 0
  have d := h 2 1
  simp [Equiv.swap_apply_of_ne_of_ne] at a b c d
  exact ⟨a, b, c, d⟩

/-- The antisymmetric vector `(0, 1, −1)`. -/
def anti : Fin 3 → ℂ := ![0, 1, -1]

theorem antisym_eigen (a b c d : ℂ) :
    !![a, b, b; b, c, d; b, d, c] *ᵥ anti = (c - d) • anti := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, anti] <;> ring

/-- **The antisymmetric state is protected.** -/
theorem antisym_protected (a b c d : ℂ) (v : Fin 3 → ℂ)
    (hdet : (a - (c - d)) * (c + d - (c - d)) - 2 * b ^ 2 ≠ 0)
    (hv : !![a, b, b; b, c, d; b, d, c] *ᵥ v = (c - d) • v) : v = v 1 • anti := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  -- q = v 0, p = v 1 + v 2
  have e1 : (a - (c - d)) * v 0 + b * (v 1 + v 2) = 0 := by linear_combination h0
  have e2 : 2 * b * v 0 + (c + d - (c - d)) * (v 1 + v 2) = 0 := by linear_combination h1 + h2
  have hq : (((a - (c - d)) * (c + d - (c - d)) - 2 * b ^ 2)) * v 0 = 0 := by
    linear_combination (c + d - (c - d)) * e1 - b * e2
  have hp : (((a - (c - d)) * (c + d - (c - d)) - 2 * b ^ 2)) * (v 1 + v 2) = 0 := by
    linear_combination (a - (c - d)) * e2 - 2 * b * e1
  have q0 := (mul_eq_zero.mp hq).resolve_left hdet
  have p0 := (mul_eq_zero.mp hp).resolve_left hdet
  ext i; fin_cases i
  · simp [anti, q0]
  · simp [anti]
  · simp [anti]; linear_combination p0

/-- **A shared state does not mix.** If `Ud`'s column `k'` is `c` times `Uu`'s column `k`, the
mixing matrix vanishes in column `k'` away from row `k`. -/
theorem shared_state_zero {n : Type*} [Fintype n] [DecidableEq n] (Uu Ud : Matrix n n ℂ)
    (hu : Uuᴴ * Uu = 1) (k k' : n) (c : ℂ) (hcol : ∀ i, Ud i k' = c * Uu i k) :
    ∀ i, i ≠ k → (Uuᴴ * Ud) i k' = 0 := by
  intro i hi
  have : (Uuᴴ * Ud) i k' = c * (Uuᴴ * Uu) i k := by
    simp only [mul_apply, hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this, hu, one_apply_ne hi, mul_zero]

/-- **Every PMNS entry is nonzero.** -/
theorem pmns_all_nonzero (i j : Fin 3) : PMNS.matrix i j ≠ 0 := by
  intro h
  have hb := (PMNSIntervals.squared_entry_bounds i j).1
  rw [h, Complex.normSq_zero] at hb
  fin_cases i <;> fin_cases j <;> norm_num [PMNSIntervals.lower] at hb

/-- **No-go: the supplied PMNS has no shared lepton state.** -/
theorem pmns_no_shared_state (Ue Uν : Matrix (Fin 3) (Fin 3) ℂ) (he : Ueᴴ * Ue = 1)
    (hmix : Ueᴴ * Uν = PMNS.matrix) (k k' : Fin 3) (c : ℂ) :
    ¬ ∀ i, Uν i k' = c * Ue i k := by
  intro hcol
  have hz := shared_state_zero Ue Uν he k k' c hcol (k + 1) (by fin_cases k <;> decide)
  rw [hmix] at hz
  exact pmns_all_nonzero _ _ hz

end PMDynamics.GenerationBreaking
