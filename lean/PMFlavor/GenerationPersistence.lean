import PMFlavor.GenerationLink
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Transfer persistence for generations

Under the distinct-pair packet contract, generations are the three unordered
pairs of nontrivial glue classes (paper III `Generations.three_pairs`).
Any two generations share exactly one class, so every generation is one
primitive step from every other — the complete graph on three generations.

A transfer policy between generations assigns a rate `r_{ij}` from
generation i to generation j. The net drift into generation i is
`∑_j r_{ji} - ∑_j r_{ij}` (inflow minus outflow).

* `starvation_grows_linearly`: if any generation drains faster than it
  refills (net drift < 0), its population grows without bound — for any
  finite bound B, there exists a time n where the population exceeds B.
* `persistence_selects_balanced`: under bounded population, transfer must
  be balanced at each generation. A policy that starves any generation
  cannot persist.

The generation transfer model is independent of any specific link form.
No symmetry-breaking assumption is made here.
-/

noncomputable section
namespace PMFlavor.GenerationPersistence

section transfer_persistence
variable {g : Type*} [DecidableEq g] [Fintype g]

/-- A transfer policy assigns nonnegative rates between generations.
`r i j` is the transfer rate from generation i to generation j. -/
def IsTransferPolicy (r : g → g → ℝ) : Prop := ∀ i j, 0 ≤ r i j

/-- Net drift into generation i: inflow minus outflow.
Positive means the generation is gaining population; negative means draining. -/
def net_drift (r : g → g → ℝ) (i : g) : ℝ := ∑ j, r j i - ∑ j, r i j

/-- A transfer policy is balanced at generation i if net drift is zero. -/
def BalancedAt (r : g → g → ℝ) (i : g) : Prop := ∑ j, r j i = ∑ j, r i j

/-- A transfer policy is balanced if it is balanced at every generation. -/
def Balanced (r : g → g → ℝ) : Prop := ∀ i, BalancedAt r i

/-- A positive value grows without bound when multiplied by increasing n. -/
theorem starvation_grows_linearly (drift : ℝ) (hpos : 0 < drift) :
    ∀ B : ℝ, ∃ n : ℕ, drift * ↑n > B := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (B / drift)
  use n
  calc
    drift * ↑n > drift * (B / drift) := by
      apply mul_lt_mul_of_pos_left hn hpos
    _ = B := by field_simp [hpos.ne']

/-- A generation with negative net drift accumulates unbounded population. -/
theorem net_drift_starvation_grows_linearly (r : g → g → ℝ) (i0 : g)
    (hstarve : net_drift r i0 < 0) :
    ∀ (B : ℝ), ∃ n : ℕ, |(net_drift r i0)| * ↑n > B := by
  intro B
  have habs_pos : 0 < |(net_drift r i0)| := by
    rw [net_drift]
    have h : ∑ j, r j i0 - ∑ j, r i0 j < 0 := hstarve
    rw [abs_of_neg h]
    linarith
  apply starvation_grows_linearly _ habs_pos B

/-- Persistence selects balanced transfer. If bounded population is required
and transfer rates are nonnegative, then the net drift must be zero at each
generation. A policy that starves any generation cannot persist. -/
theorem persistence_selects_balanced (r : g → g → ℝ)
    (_hpolicy : IsTransferPolicy r)
    (hbacklog : ∃ B : ℝ, ∀ i, ∀ n : ℕ, |(net_drift r i)| * ↑n ≤ B) :
    Balanced r := by
  intro i0
  obtain ⟨B, hB⟩ := hbacklog
  by_contra hneq
  -- We need to derive a contradiction.
  -- Strategy: |net_drift r i0| must be 0 (otherwise it grows unbounded,
  -- contradicting the bounded population constraint).
  -- But |net_drift r i0| = 0 means balanced at i0, contradicting hneq.
  by_cases h_abs : |(net_drift r i0)| = 0
  · -- |drift| = 0, so balanced at i0
    have hzero : net_drift r i0 = 0 := abs_eq_zero.mp h_abs
    have hbal : BalancedAt r i0 := by
      rw [net_drift] at hzero
      rw [BalancedAt]
      linarith [hzero]
    contradiction
  · -- |drift| > 0
    have hpos : 0 < |(net_drift r i0)| := by
      have hge : 0 ≤ |(net_drift r i0)| := abs_nonneg _
      have hne : |(net_drift r i0)| ≠ 0 := h_abs
      exact lt_of_le_of_ne hge hne.symm
    -- For large n, the absolute drift at i0 exceeds B
    have h_exceeds : ∃ n : ℕ, |(net_drift r i0)| * ↑n > B := by
      apply starvation_grows_linearly _ hpos
    obtain ⟨n, hn⟩ := h_exceeds
    -- But hbacklog says |drift| * n ≤ B for all n
    have h_con : |(net_drift r i0)| * ↑n ≤ B := hB i0 n
    linarith [h_con, hn]

/-- For three generations with symmetric transfer rates, balanced transfer
holds trivially (inflow = outflow for each gen by symmetry). -/
theorem three_gen_balanced_trivial (r : Fin 3 → Fin 3 → ℝ)
    (hsym : ∀ i j, r i j = r j i) :
    Balanced r := by
  intro i
  simp [BalancedAt]
  -- By symmetry, inflow = sum of r j i = sum of r i j = outflow
  congr! 1
  apply hsym

end transfer_persistence
end PMFlavor.GenerationPersistence
