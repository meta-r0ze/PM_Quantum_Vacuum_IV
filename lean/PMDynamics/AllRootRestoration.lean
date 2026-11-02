import PMDynamics.ReferenceSafeRestoration
import PMAction.PersistenceSelection
import PMDynamics.TransitionSelection

/-!
# Restoration using every reference-preserving D4 root

The declared D4 sector has six distinct root reflections avoiding axis 0;
the twelve signed roots give these six actions. All are retained here, rather
than only the three simple generators. Each action is certified against the
actual carrier reflection and has an integral norm-two E8 lift.

The same required order loop has minimum two calls and minimum expected
change-event price c under uniform native-carrier counting. There are exactly
three cheapest words, all implementing the same inverse operator. Thus the
unique-word claim of the smaller generator alphabet does not extend to the
full D4-root alphabet. No claim of exhaustion of all E8/coherent/adaptive
protocols, or of a physical generation identification, is made.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.AllRootRestoration
open Matrix PMAction NativePacketLinks CarrierEvents

def rootVector : Fin 6 → PMArch.ChannelSymmetry.V4 :=
  ![![0,1,-1,0], ![0,0,1,-1], ![0,1,0,-1],
    ![0,1,1,0], ![0,0,1,1], ![0,1,0,1]]
def doubled (j : Fin 6) : PMArch.ChannelSymmetry.V4 := fun i => 2*rootVector j i

theorem roots_admitted : ∀ j : Fin 6,
    doubled j ∈ PMArch.ChannelSymmetry.roots ∧ rootVector j 0=0 := by decide +kernel

theorem roots_exhaustive : ∀ R ∈ PMArch.ChannelSymmetry.roots, R 0=0 →
    ∃ j : Fin 6, R=doubled j ∨ R= -doubled j := by decide +kernel

theorem reflection_sign (r y : PMArch.ChannelSymmetry.V4) :
    PMArch.ChannelSymmetry.refl (-r) y = PMArch.ChannelSymmetry.refl r y := by
  ext i
  simp [PMArch.ChannelSymmetry.refl, PMArch.ChannelSymmetry.dot4, Finset.sum_neg_distrib]

def coefficients : Fin 6 → Fin 4 → ℤ :=
  ![![0,1,0,0], ![0,0,1,0], ![0,1,1,0],
    ![0,1,1,1], ![0,0,0,1], ![0,1,0,1]]
def liftRoot (s : Bool) (j : Fin 6) : SubstrateWeylRoots.Lattice :=
  ∑ k : Fin 4, coefficients j k • SubstrateWeylRoots.root s k

theorem lift_norm : ∀ s j, PMArch.Lattices.pairing (liftRoot s j) (liftRoot s j)=2 := by decide +kernel
theorem sector_coordinates : ∀ j, PMArch.Lattices.d4Roots (coefficients j)=rootVector j := by decide +kernel

/-- Conjugate-word certificates identify the action; a certified root itself
is one letter of this expanded primitive-root alphabet. -/
def expansion : Fin 6 → List (Fin 3) :=
  ![[0], [1], [0,1,0], [1,0,2,0,1], [2], [0,2,0]]
def gate (a : Fin 3) (j : Fin 6) : Action a := ReferenceSafeRestoration.run a (expansion j)
def run (a : Fin 3) (word : List (Fin 6)) : Action a := (word.map (gate a)).prod
def Restores (a : Fin 3) (word : List (Fin 6)) : Prop := run a word * ReferenceSafeRestoration.loop a = 1

theorem gate_is_reflection : ∀ (a : Fin 3) (j : Fin 6) (v : Carrier a),
    vector ((gate a j : Equiv.Perm (Carrier a)) v) =
      PMArch.ChannelSymmetry.refl (rootVector j) (vector v) := by decide +kernel

/-- Every root surviving the reference-axis filter has one of these actions. -/
theorem covers_allowed_root (R : PMArch.ChannelSymmetry.V4)
    (hR : R ∈ PMArch.ChannelSymmetry.roots) (h0 : R 0=0) :
    ∃ j : Fin 6, ∀ (a : Fin 3) (v : Carrier a),
      vector ((gate a j : Equiv.Perm (Carrier a)) v) =
        PMArch.ChannelSymmetry.refl (fun i => R i / 2) (vector v) := by
  obtain ⟨j,hj|hj⟩ := roots_exhaustive R hR h0
  · subst R
    have hh : (fun i => doubled j i / 2) = rootVector j := by ext i; unfold doubled; omega
    exact ⟨j, fun a v => by rw [hh]; exact gate_is_reflection a j v⟩
  · subst R
    have hh : (fun i => (-doubled j) i / 2) = -rootVector j := by
      ext i
      simp only [doubled, Pi.neg_apply]
      omega
    exact ⟨j, fun a v => by rw [hh, reflection_sign]; exact gate_is_reflection a j v⟩

theorem gate_keeps_axis (a : Fin 3) (j : Fin 6) (v : Carrier a) :
    vector ((gate a j : Equiv.Perm (Carrier a)) v) 0 = vector v 0 :=
  ReferenceSafeRestoration.run_keeps_axis a (expansion j) v

theorem run_keeps_axis (a : Fin 3) (word : List (Fin 6)) (v : Carrier a) :
    vector ((run a word : Equiv.Perm (Carrier a)) v) 0 = vector v 0 := by
  induction word generalizing v with
  | nil => rfl
  | cons j word ih =>
    change vector ((gate a j : Equiv.Perm (Carrier a)) ((run a word : Equiv.Perm (Carrier a)) v)) 0 = _
    exact (gate_keeps_axis a j _).trans (ih v)

theorem two_repairs (a : Fin 3) : Restores a [1,0] := by
  apply Subtype.ext
  fin_cases a <;> decide +kernel

theorem no_single_repair (a : Fin 3) (j : Fin 6) : ¬ Restores a [j] := by
  intro h
  have hh := congrArg Subtype.val h
  fin_cases a <;> fin_cases j <;> revert hh <;> decide +kernel

theorem restoring_length (a : Fin 3) (word : List (Fin 6)) (h : Restores a word) : 2 ≤ word.length := by
  cases word with
  | nil =>
    have hh : ReferenceSafeRestoration.loop a = 1 := by simpa [Restores,run] using h
    exact False.elim (ReferenceSafeRestoration.loop_nontrivial a hh)
  | cons j word =>
    cases word with
    | nil => exact False.elim (no_single_repair a j h)
    | cons k rest => simp

def eventCount (a : Fin 3) : List (Fin 6) → Carrier a → ℕ
  | [], _ => 0
  | j::word, v => eventCount a word v +
      if (gate a j : Equiv.Perm (Carrier a)) ((run a word : Equiv.Perm (Carrier a)) v) ≠
        (run a word : Equiv.Perm (Carrier a)) v then 1 else 0

theorem changed_card : ∀ (a : Fin 3) (j : Fin 6),
    (CarrierCost.changed (gate a j : Equiv.Perm (Carrier a))).card=4 := by decide +kernel

theorem activation_sum (a : Fin 3) (j : Fin 6) (P : Equiv.Perm (Carrier a)) :
    (∑ v, if (gate a j : Equiv.Perm (Carrier a)) (P v) ≠ P v then (1:ℕ) else 0)=4 := by
  rw [Equiv.sum_comp P (fun v => if (gate a j : Equiv.Perm (Carrier a)) v ≠ v then (1:ℕ) else 0)]
  simpa [CarrierCost.changed, Finset.card_filter] using changed_card a j

theorem event_count_sum (a : Fin 3) (word : List (Fin 6)) :
    (∑ v : Carrier a, eventCount a word v)=4*word.length := by
  induction word with
  | nil => simp [eventCount]
  | cons j word ih =>
    simp only [eventCount, Finset.sum_add_distrib, ih, activation_sum, List.length_cons]
    omega

def price (a : Fin 3) (c : ℝ) (word : List (Fin 6)) : ℝ :=
  c*(∑ v : Carrier a, eventCount a word v)/Fintype.card (Carrier a)

theorem price_formula (a : Fin 3) (c : ℝ) (word : List (Fin 6)) : price a c word=c*word.length/2 := by
  rw [price,event_count_sum,carrier_card]
  push_cast
  ring

def Optimal (word : List (Fin 6)) : Prop := word=[1,0] ∨ word=[0,2] ∨ word=[2,1]

set_option maxHeartbeats 2000000 in
theorem two_letter_classification : ∀ (a : Fin 3) (j k : Fin 6),
    Restores a [j,k] ↔ (j=1 ∧ k=0) ∨ (j=0 ∧ k=2) ∨ (j=2 ∧ k=1) := by
  unfold Restores
  decide +kernel

theorem shortest_iff (a : Fin 3) (word : List (Fin 6)) :
    (Restores a word ∧ word.length=2) ↔ Optimal word := by
  constructor
  · rintro ⟨hw,hn⟩
    obtain ⟨j,k,rfl⟩ := List.length_eq_two.mp hn
    rcases (two_letter_classification a j k).mp hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [Optimal]
  · rintro (rfl|rfl|rfl) <;> exact ⟨(two_letter_classification _ _ _).mpr (by decide), rfl⟩

theorem minimum_price (a : Fin 3) (c : ℝ) (hc : 0 < c) :
    IsLeast {x : ℝ | ∃ word, Restores a word ∧ price a c word=x} c := by
  constructor
  · exact ⟨[1,0],two_repairs a,by rw [price_formula]; simp⟩
  · rintro x ⟨word,hw,rfl⟩
    have hn : (2:ℝ) ≤ word.length := by exact_mod_cast restoring_length a word hw
    rw [price_formula]
    nlinarith

theorem cheapest_iff (a : Fin 3) (c : ℝ) (hc : 0 < c) (word : List (Fin 6)) :
    (Restores a word ∧ ∀ v, Restores a v → price a c word ≤ price a c v) ↔ Optimal word := by
  constructor
  · rintro ⟨hw,hmin⟩
    have hn := restoring_length a word hw
    have hb := hmin [1,0] (two_repairs a)
    rw [price_formula,price_formula] at hb
    have hle : (word.length:ℝ) ≤ 2 := by norm_num at hb; nlinarith
    have hnat : word.length ≤ 2 := by exact_mod_cast hle
    exact (shortest_iff a word).mp ⟨hw,by omega⟩
  · intro ho
    obtain ⟨hw,hn⟩ := (shortest_iff a word).mpr ho
    refine ⟨hw,fun v hv => ?_⟩
    have hb := (minimum_price a c hc).2 ⟨v,hv,rfl⟩
    simpa [price_formula,hn] using hb

theorem most_persistent_iff (a : Fin 3) (c : ℝ) (hc : 0 < c) (β : ℝ) (hβ : 0 < β)
    (baseline : ℝ) (word : List (Fin 6)) :
    (Restores a word ∧ ∀ v, Restores a v →
      Real.exp (-β*(baseline+price a c v)) ≤ Real.exp (-β*(baseline+price a c word))) ↔ Optimal word := by
  exact (PersistenceSelection.within_family_iff_cheapest β hβ (price a c)
    {v | Restores a v} baseline word).trans (cheapest_iff a c hc word)

theorem optimal_same_operator (a : Fin 3) (word : List (Fin 6)) (ho : Optimal word) :
    run a word = ReferenceSafeRestoration.run a [1,0] := by
  have hw := ((shortest_iff a word).mpr ho).1
  exact mul_right_cancel (hw.trans (ReferenceSafeRestoration.two_repairs a).symm)

theorem call_budget_iff (a : Fin 3) (N : ℕ) :
    (∃ word, Restores a word ∧ word.length ≤ N) ↔ 2 ≤ N := by
  constructor
  · rintro ⟨word,hw,hn⟩
    exact (restoring_length a word hw).trans hn
  · intro hn
    exact ⟨[1,0],two_repairs a,hn⟩

theorem price_budget_iff (a : Fin 3) (c B : ℝ) (hc : 0 < c) :
    (∃ word, Restores a word ∧ price a c word ≤ B) ↔ c ≤ B := by
  constructor
  · rintro ⟨word,hw,hb⟩
    exact ((minimum_price a c hc).2 ⟨word,hw,rfl⟩).trans hb
  · intro hb
    refine ⟨[1,0],two_repairs a,?_⟩
    simpa [price_formula] using hb

theorem required_flux (a : Fin 3) (word : List (Fin 6)) (hw : Restores a word)
    (period : ℝ) (ht : 0 < period) : 1/period ≤ price a 1 word / period :=
  div_le_div_of_nonneg_right ((minimum_price a 1 (by norm_num)).2 ⟨word,hw,rfl⟩) ht.le

theorem minimum_density (a : Fin 3) (c K period : ℝ) (hc : 0 < c) (hK : 0 < K)
    (ht : 0 < period) :
    IsLeast {d : ℝ | ∃ word, Restores a word ∧
      TransitionSelection.dissipation c K (price a 1 word / period)=d} (c*K/period) := by
  have he : TransitionSelection.dissipation c K (price a 1 [1,0] / period)=c*K/period := by
    simp [TransitionSelection.dissipation,price_formula]
    ring
  constructor
  · exact ⟨[1,0],two_repairs a,he⟩
  · rintro d ⟨word,hw,rfl⟩
    have hb := (TransitionSelection.strict_flux c K hc hK).monotone (required_flux a word hw period ht)
    simpa only [TransitionSelection.dissipation,mul_one_div] using hb

end PMDynamics.AllRootRestoration
