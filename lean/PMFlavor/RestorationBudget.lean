import PMFlavor.RootRepairSelection
import PMFlavor.TransitionSelection

/-!
# Required-work and capacity bounds for the reference-safe native repair

The specified exact-restoration task is feasible exactly with a call budget
of at least two, or a uniform change-event price budget of at least one toll.
Its minimum expected event flux is 1/period. Thus c K f has a positive
attained minimum c K/period for this actual task; the zero-transfer option
does not restore it. The task's recurrence, physical period, event law and
choice of allowed roots remain inputs. No physical generation/mixing law
is obtained merely by assigning this task to a flavour transition.
-/
noncomputable section
namespace PMFlavor.RestorationBudget
open ReferenceSafeRestoration

theorem call_budget_iff (a : Fin 3) (N : ℕ) :
    (∃ word, Restores a word ∧ word.length ≤ N) ↔ 2 ≤ N := by
  constructor
  · rintro ⟨word,hw,hn⟩
    exact (restoring_length a word hw).trans hn
  · intro hn
    exact ⟨[1,0], two_repairs a, hn⟩

theorem price_budget_iff (a : Fin 3) (c B : ℝ) (hc : 0 < c) :
    (∃ word, Restores a word ∧ price a c word ≤ B) ↔ c ≤ B := by
  constructor
  · rintro ⟨word,hw,hb⟩
    exact ((minimum_price a c hc).2 ⟨word,hw,rfl⟩).trans hb
  · intro hb
    refine ⟨[1,0],two_repairs a,?_⟩
    simpa [price_formula] using hb

/-- Flux of actual changed-carrier events under the stated uniform law. -/
def flux (a : Fin 3) (word : List (Fin 3)) (period : ℝ) : ℝ := price a 1 word / period

theorem required_flux (a : Fin 3) (word : List (Fin 3)) (hw : Restores a word)
    (period : ℝ) (ht : 0 < period) : 1/period ≤ flux a word period := by
  have he := (minimum_price a 1 (by norm_num)).2 ⟨word,hw,rfl⟩
  exact div_le_div_of_nonneg_right he ht.le

theorem minimum_density (a : Fin 3) (c K period : ℝ) (hc : 0 < c) (hK : 0 < K)
    (ht : 0 < period) :
    IsLeast {d : ℝ | ∃ word, Restores a word ∧
      TransitionSelection.dissipation c K (flux a word period) = d} (c*K/period) := by
  have he : TransitionSelection.dissipation c K (flux a [1,0] period) = c*K/period := by
    simp [TransitionSelection.dissipation, flux, price_formula]
    ring
  constructor
  · exact ⟨[1,0],two_repairs a,he⟩
  · rintro d ⟨word,hw,rfl⟩
    have hb := (TransitionSelection.strict_flux c K hc hK).monotone
      (required_flux a word hw period ht)
    simpa only [TransitionSelection.dissipation, mul_one_div] using hb

theorem positive_minimum_density (c K period : ℝ) (hc : 0 < c) (hK : 0 < K)
    (ht : 0 < period) : 0 < c*K/period := div_pos (mul_pos hc hK) ht

end PMFlavor.RestorationBudget
