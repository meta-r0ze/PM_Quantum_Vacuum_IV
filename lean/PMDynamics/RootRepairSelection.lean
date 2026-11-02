import PMDynamics.ReferenceSafeRestoration
import PMAction.PersistenceSelection

/-!
# Persistence selects a concrete required native repair

For the reference-preserving order loop, use the stated three-simple-root
alphabet and require exact restoration on every input. Uniform native-carrier
counting gives the actual change-event price, not an assigned angle score.
The unique cheapest word is [1,0]: two root calls and mean one carrier-change
event. Under the existing positive-hazard survival law and shared baseline,
it is exactly the most persistent admissible word.

This closes a specified operational selection problem. The task's necessity,
choice of alphabet, uniform counting and common baseline remain explicit.
No correspondence between these colour-root coordinates and generations,
or global CKM/PMNS angle-selection theorem, is asserted.
-/
noncomputable section
namespace PMDynamics.RootRepairSelection
open PMAction ReferenceSafeRestoration

theorem two_letter_classification : ∀ (a : Fin 3) (j k : Fin 3),
    Restores a [j,k] ↔ j=1 ∧ k=0 := by
  intro a j k
  unfold Restores
  fin_cases a <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem shortest_iff (a : Fin 3) (word : List (Fin 3)) :
    (Restores a word ∧ word.length=2) ↔ word=[1,0] := by
  constructor
  · rintro ⟨hw,hn⟩
    obtain ⟨j,k,rfl⟩ := List.length_eq_two.mp hn
    obtain ⟨rfl,rfl⟩ := (two_letter_classification a j k).mp hw
    rfl
  · rintro rfl
    exact ⟨two_repairs a, rfl⟩

theorem cheapest_iff (a : Fin 3) (c : ℝ) (hc : 0 < c) (word : List (Fin 3)) :
    (Restores a word ∧ ∀ v, Restores a v → price a c word ≤ price a c v) ↔ word=[1,0] := by
  constructor
  · rintro ⟨hw,hmin⟩
    have hn := restoring_length a word hw
    have hbound := hmin [1,0] (two_repairs a)
    rw [price_formula, price_formula] at hbound
    have hle : (word.length:ℝ) ≤ 2 := by norm_num at hbound; nlinarith
    have hnat : word.length ≤ 2 := by exact_mod_cast hle
    exact (shortest_iff a word).mp ⟨hw, by omega⟩
  · rintro rfl
    refine ⟨two_repairs a, fun v hv => ?_⟩
    have hb := (minimum_price a c hc).2 ⟨v,hv,rfl⟩
    simpa [price_formula] using hb

/-- This retains the actual admissible restoring family and common baseline. -/
theorem most_persistent_iff (a : Fin 3) (c : ℝ) (hc : 0 < c)
    (β : ℝ) (hβ : 0 < β) (baseline : ℝ) (word : List (Fin 3)) :
    (Restores a word ∧ ∀ v, Restores a v →
      Real.exp (-β*(baseline+price a c v)) ≤ Real.exp (-β*(baseline+price a c word))) ↔
      word=[1,0] := by
  have h := PersistenceSelection.within_family_iff_cheapest β hβ (price a c)
    {v | Restores a v} baseline word
  exact h.trans (cheapest_iff a c hc word)

end PMDynamics.RootRepairSelection
