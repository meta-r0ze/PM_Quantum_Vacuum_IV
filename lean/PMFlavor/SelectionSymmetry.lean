import PMFlavor.GenerationLink

/-!
# A unique optimum must inherit the symmetries of its admissible cost

This is a necessary test of a proposed flavour-selection functional. If both
admissibility and cost are invariant under class relabelings, a unique minimizing
link is invariant too, hence has the already-classified symmetric form. It cannot
be a uniquely selected symmetry-breaking link. Degenerate minima, additional
background data or a noninvariant physical cost require separate treatment.
No such cost or uniqueness premise is derived here from persistence.
-/
noncomputable section
namespace PMFlavor.SelectionSymmetry
open Matrix
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def relabel (σ : Equiv.Perm (Fin 3)) (Y : M) : M := fun i j => Y (σ i) (σ j)

def UniqueMinimum (admissible : M → Prop) (cost : M → ℝ) (Y : M) : Prop :=
  admissible Y ∧ (∀ Z, admissible Z → cost Y ≤ cost Z) ∧
    ∀ Z, admissible Z → cost Z = cost Y → Z = Y

theorem unique_minimum_invariant (admissible : M → Prop) (cost : M → ℝ) (Y : M)
    (hadm : ∀ σ Z, admissible Z → admissible (relabel σ Z))
    (hcost : ∀ σ Z, cost (relabel σ Z) = cost Z)
    (hmin : UniqueMinimum admissible cost Y) :
    ∀ (σ : Equiv.Perm (Fin 3)) i j, Y (σ i) (σ j) = Y i j := by
  intro σ i j
  exact congrFun (congrFun (hmin.2.2 _ (hadm σ Y hmin.1) (hcost σ Y)) i) j

theorem unique_minimum_form (admissible : M → Prop) (cost : M → ℝ) (Y : M)
    (hadm : ∀ σ Z, admissible Z → admissible (relabel σ Z))
    (hcost : ∀ σ Z, cost (relabel σ Z) = cost Z)
    (hmin : UniqueMinimum admissible cost Y) :
    ∀ i j, Y i j = if i=j then Y 0 0 else Y 0 1 :=
  GenerationLink.invariant_form (unique_minimum_invariant admissible cost Y hadm hcost hmin)

/-- An explicit broken class symmetry rules out a unique minimum for such a cost. -/
theorem broken_symmetry_not_unique (admissible : M → Prop) (cost : M → ℝ) (Y : M)
    (hadm : ∀ σ Z, admissible Z → admissible (relabel σ Z))
    (hcost : ∀ σ Z, cost (relabel σ Z) = cost Z)
    (hbroken : ∃ (σ : Equiv.Perm (Fin 3)) (i j : Fin 3), Y (σ i) (σ j) ≠ Y i j) :
    ¬ UniqueMinimum admissible cost Y := by
  intro hmin
  obtain ⟨σ,i,j,hne⟩ := hbroken
  exact hne (unique_minimum_invariant admissible cost Y hadm hcost hmin σ i j)

end PMFlavor.SelectionSymmetry
