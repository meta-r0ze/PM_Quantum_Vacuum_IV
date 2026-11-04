import PMAction.OrderRestoration
import PMAction.RootOrderComparison
import PMFlavor.FlavourOrderComparison

/-!
# An executable reference-preserving order repair and its minimum ledger

Use the three native D4 simple roots avoiding coordinate 0. Their words
preserve every carrier's lepton coordinate. Two adjacent roots in this set
have a nontrivial order loop, with mean coordinate flag 3/8. The loop is
repaired by two such primitive letters; no zero- or one-letter repair exists
in the stated alphabet. Under uniform native-carrier sampling each letter moves
four of eight carriers, including after any preceding permutation. With positive
toll c per actual carrier change, the minimum expected repair price is c.
Preparation, comparison/control and record costs are excluded; this is not a
claim about all possible coherent E8 implementations.

The requirement to undo the loop on every state is explicit. Persistence of
the lepton reference alone does not require it: the loop already fixes that
reference. Nor are colour coordinates identified with physical generations.
The endpoint comparison flag is kept separate from an event-by-event ledger.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.ReferenceSafeRestoration
open Matrix PMAction NativePacketLinks CarrierEvents CarrierParity NativeRootGenerators

def index (j : Fin 3) : Fin 4 := ⟨j.val+1, by omega⟩
def gate (a : Fin 3) (j : Fin 3) : Action a := root a (index j)
def run (a : Fin 3) (word : List (Fin 3)) : Action a := (word.map (gate a)).prod
def loop (a : Fin 3) : Action a := (gate a 0*gate a 1)⁻¹*(gate a 1*gate a 0)
def Restores (a : Fin 3) (word : List (Fin 3)) : Prop := run a word * loop a = 1

theorem root_fixes_reference : ∀ j : Fin 3,
    PMSubstrate.ChannelSymmetry.refl (PMSubstrate.ChannelSymmetry.simple (index j)) ![2,0,0,0] = ![2,0,0,0] := by
  decide +kernel

theorem gate_keeps_axis : ∀ (a : Fin 3) (j : Fin 3) (v : Carrier a),
    vector ((gate a j : Equiv.Perm (Carrier a)) v) 0 = vector v 0 := by
  decide +kernel

theorem run_keeps_axis (a : Fin 3) (word : List (Fin 3)) (v : Carrier a) :
    vector ((run a word : Equiv.Perm (Carrier a)) v) 0 = vector v 0 := by
  induction word generalizing v with
  | nil => rfl
  | cons j word ih =>
    change vector ((gate a j : Equiv.Perm (Carrier a)) ((run a word : Equiv.Perm (Carrier a)) v)) 0 = _
    exact (gate_keeps_axis a j _).trans (ih v)

theorem run_keeps_lepton_membership (a : Fin 3) (word : List (Fin 3)) (v : Carrier a) :
    (vector ((run a word : Equiv.Perm (Carrier a)) v) 0 ≠ 0) ↔ vector v 0 ≠ 0 := by
  rw [run_keeps_axis]

theorem loop_eq (a : Fin 3) : loop a = gate a 0*gate a 1 := by
  apply Subtype.ext
  fin_cases a <;> decide +kernel

theorem loop_nontrivial (a : Fin 3) : loop a ≠ 1 := by
  intro h
  have hh := congrArg Subtype.val h
  fin_cases a <;> revert hh <;> decide +kernel

theorem no_single_repair (a : Fin 3) (j : Fin 3) : ¬ Restores a [j] := by
  intro h
  have hh := congrArg Subtype.val h
  fin_cases a <;> fin_cases j <;> revert hh <;> decide +kernel

theorem two_repairs (a : Fin 3) : Restores a [1,0] := by
  apply Subtype.ext
  fin_cases a <;> decide +kernel

theorem restoring_length (a : Fin 3) (word : List (Fin 3)) (h : Restores a word) :
    2 ≤ word.length := by
  cases word with
  | nil =>
    have hh : loop a = 1 := by simpa [Restores, run] using h
    exact False.elim (loop_nontrivial a hh)
  | cons j word =>
    cases word with
    | nil => exact False.elim (no_single_repair a j h)
    | cons k rest => simp

/-- Actual changes along the executed word; the suffix runs before its head. -/
def eventCount (a : Fin 3) : List (Fin 3) → Carrier a → ℕ
  | [], _ => 0
  | j::word, v => eventCount a word v +
      if (gate a j : Equiv.Perm (Carrier a)) ((run a word : Equiv.Perm (Carrier a)) v) ≠
        (run a word : Equiv.Perm (Carrier a)) v then 1 else 0

theorem changed_card : ∀ (a : Fin 3) (j : Fin 3),
    (CarrierCost.changed (gate a j : Equiv.Perm (Carrier a))).card = 4 := by
  decide +kernel

theorem activation_sum (a : Fin 3) (j : Fin 3) (P : Equiv.Perm (Carrier a)) :
    (∑ v, if (gate a j : Equiv.Perm (Carrier a)) (P v) ≠ P v then (1:ℕ) else 0) = 4 := by
  rw [Equiv.sum_comp P (fun v => if (gate a j : Equiv.Perm (Carrier a)) v ≠ v then (1:ℕ) else 0)]
  simpa [CarrierCost.changed, Finset.card_filter] using changed_card a j

/-- No independence of successive activation events is assumed. -/
theorem event_count_sum (a : Fin 3) (word : List (Fin 3)) :
    (∑ v : Carrier a, eventCount a word v) = 4*word.length := by
  induction word with
  | nil => simp [eventCount]
  | cons j word ih =>
    simp only [eventCount, Finset.sum_add_distrib, ih, activation_sum,
      List.length_cons]
    omega

/-- Uniform counting prices actual changes, not invocation count or endpoint flags. -/
def price (a : Fin 3) (c : ℝ) (word : List (Fin 3)) : ℝ :=
  c * (∑ v : Carrier a, eventCount a word v) / Fintype.card (Carrier a)

theorem price_formula (a : Fin 3) (c : ℝ) (word : List (Fin 3)) :
    price a c word = c*word.length/2 := by
  rw [price, event_count_sum, carrier_card]
  push_cast
  ring

theorem minimum_price (a : Fin 3) (c : ℝ) (hc : 0 < c) :
    IsLeast {x : ℝ | ∃ word, Restores a word ∧ price a c word = x} c := by
  constructor
  · exact ⟨[1,0], two_repairs a, by rw [price_formula]; simp⟩
  · rintro x ⟨word, hw, rfl⟩
    have hn : (2:ℝ) ≤ word.length := by exact_mod_cast restoring_length a word hw
    rw [price_formula]
    nlinarith

theorem loop_observed (a : Fin 3) :
    OrderComparison.compareLoop (physical a (gate a 0)) (physical a (gate a 1)) = physical a (loop a) := by
  simp only [loop, OrderComparison.compareLoop, physical_mul, physical_star]

theorem native_restore (a : Fin 3) :
    physical a (run a [1,0]) *
      OrderComparison.compareLoop (physical a (gate a 0)) (physical a (gate a 1)) = 1 := by
  rw [loop_observed, ← physical_mul, two_repairs a, physical_one]

/-- A demanded exact repair has this endpoint flag on the actual evolved state. -/
theorem native_required_response (a : Fin 3) (ψ : Carrier a → ℂ) :
    CommonResponse.stateFlag (physical a (run a [1,0]))
      (OrderComparison.compareLoop (physical a (gate a 0)) (physical a (gate a 1)) *ᵥ ψ) =
    OrderComparison.flag (physical a (gate a 0)) (physical a (gate a 1)) ψ :=
  OrderRestoration.order_repair_response _ _ _ (physical_unitary a (gate a 0))
    (physical_unitary a (gate a 1)) (native_restore a) ψ

theorem coordinate_mean (a : Fin 3) :
    OrderComparison.total (link a (gate a 0)) (link a (gate a 1))/4 = (3/8:ℝ) := by
  norm_num [OrderComparison.total_formula, gate, index, root_link, rootMatrix, rootMatrixZ,
    Matrix.mul_apply, PMSubstrate.ChannelSymmetry.refl, PMSubstrate.ChannelSymmetry.simple,
    PMSubstrate.ChannelSymmetry.dot4, Fin.sum_univ_four, Pi.single_apply]

theorem required_mean (a : Fin 3) :
    (∑ i : Fin 4, CommonResponse.stateFlag (physical a (run a [1,0]))
      (OrderComparison.compareLoop (physical a (gate a 0)) (physical a (gate a 1)) *ᵥ
        (embedding a *ᵥ Pi.single i 1)))/4 = (3/8:ℝ) := by
  simp_rw [native_required_response,
    OrderComparison.encoded_flag (embedding a) (isometry a) _ _ _ _
      (observed a (gate a 0)) (observed a (gate a 1))]
  exact coordinate_mean a

def coordinate (a : Fin 3) (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := link a (gate a j)
def coordinateLoop (a : Fin 3) := OrderComparison.compareLoop (coordinate a 0) (coordinate a 1)

theorem coordinate_keeps_reference (a : Fin 3) (j : Fin 3) :
    coordinate a j *ᵥ (Pi.single 0 1) = (Pi.single 0 1 : Fin 4 → ℂ) := by
  ext i
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinate, gate, index, root_link, rootMatrix, rootMatrixZ, Matrix.mulVec,
      dotProduct, PMSubstrate.ChannelSymmetry.refl, PMSubstrate.ChannelSymmetry.simple,
      PMSubstrate.ChannelSymmetry.dot4, Fin.sum_univ_four, Pi.single_apply]

theorem loop_keeps_reference (a : Fin 3) :
    coordinateLoop a *ᵥ (Pi.single 0 1) = (Pi.single 0 1 : Fin 4 → ℂ) := by
  have h0 : (coordinate a 0)ᴴ = coordinate a 0 := (packet_hermitian a (index 0)).eq
  have h1 : (coordinate a 1)ᴴ = coordinate a 1 := (packet_hermitian a (index 1)).eq
  simp only [coordinateLoop, OrderComparison.compareLoop, conjTranspose_mul, h0, h1,
    ← mulVec_mulVec, coordinate_keeps_reference]

/-- The reference can persist while the nontrivial order loop remains unrepaired.
The full-restoration task therefore does not follow from this reference alone. -/
theorem reference_persistence_not_repair (a : Fin 3) :
    coordinateLoop a *ᵥ (Pi.single 0 1) = (Pi.single 0 1 : Fin 4 → ℂ) ∧ ¬ Restores a [] := by
  refine ⟨loop_keeps_reference a, fun h => ?_⟩
  have hn := restoring_length a [] h
  norm_num at hn

theorem root_mean_flag (a : Fin 3) (j : Fin 3) :
    ReferenceSampling.refFlag (1:Matrix (Fin 4) (Fin 4) ℂ) (coordinate a j) = (1/4:ℝ) := by
  change ReferenceSampling.refFlag (1:Matrix (Fin 4) (Fin 4) ℂ) (link a (gate a j)) = 1/4
  rw [ReferenceSampling.ref_flag _ (by simp) _ (link_unitary a (gate a j))]
  fin_cases j <;>
    norm_num [gate, index, root_link, rootMatrix, rootMatrixZ, trace,
      PMSubstrate.ChannelSymmetry.refl, PMSubstrate.ChannelSymmetry.simple,
      PMSubstrate.ChannelSymmetry.dot4, Fin.sum_univ_four, Pi.single_apply]

/-- Sum the actual two comparisons at their actual input frames. This is
different from comparing only the compound repair's endpoints. -/
def sequentialFlag (a : Fin 3) : ℝ :=
  ReferenceSampling.refFlag (coordinateLoop a) (coordinate a 0) +
    ReferenceSampling.refFlag (coordinate a 0*coordinateLoop a) (coordinate a 1)

theorem sequential_flag (a : Fin 3) : sequentialFlag a = (1/2:ℝ) := by
  have h0 : coordinate a 0 ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := link_unitary a (gate a 0)
  have h1 : coordinate a 1 ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := link_unitary a (gate a 1)
  have hL : coordinateLoop a ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) :=
    OrderComparison.loop_unitary _ _ h0 h1
  have hF := (unitary (Matrix (Fin 4) (Fin 4) ℂ)).mul_mem h0 hL
  rw [sequentialFlag, OrderRestoration.uniform_preparation_invariant _ _ hL h0,
    OrderRestoration.uniform_preparation_invariant _ _ hF h1, root_mean_flag, root_mean_flag]
  norm_num

theorem endpoint_understates_sequential (a : Fin 3) :
    OrderComparison.total (coordinate a 0) (coordinate a 1)/4 < sequentialFlag a := by
  change OrderComparison.total (link a (gate a 0)) (link a (gate a 1))/4 < sequentialFlag a
  rw [coordinate_mean, sequential_flag]
  norm_num

end PMFlavor.ReferenceSafeRestoration
