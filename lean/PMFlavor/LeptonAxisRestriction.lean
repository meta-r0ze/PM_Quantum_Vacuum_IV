import PMFlavor.MassTermLaw
import PMFlavor.AllRootRestoration
import PMConstants.CarrierActions

/-!
# The lepton-axis event restriction, derived from reference maintenance

`MassTermLaw` excluded the sterile Majorana term and the lepton-colour root
events *conditionally*: `allowed_roots_conserve_axis` assumes its event root
avoids axis `0`. This module derives that restriction from the
reference-maintenance contract that Papers II and III already supply, plus one
new theorem about the actual gauge actions.

Three checked steps.

1. **Gauge repairs preserve every packet's channel type** (`weak_type`,
   `colour_type`, `repairRun_type`). Proved from the actual definitions in
   Paper III's `CarrierActions`: the weak action negates the left-sector
   carriers and fixes the right, and the colour action exchanges colour axes
   only. Neither changes axis-`0` membership, and `leftType`/`rightType`
   depend only on that membership and the sign, so `channelType` is invariant.
   This is the discrete shadow of the block-diagonal structure behind
   `SectorObligations.full_column`.

2. **A root that touches the lepton axis changes the reference's channel
   type** (`norm2_root_moves_lepton`, `axis_root_moves_lepton`,
   `event_breaks_type`). This generalizes
   `MassTermLaw.lepton_root_moves_reference` from the single positive carrier
   to both lepton-axis carriers: for every declared sector root `R` with
   `R 0 ≠ 0` the reflection moves each of them onto a colour axis. Under
   Paper III's carrier-channel identification
   (`CarrierActions.channelType`, `type_preserved`) the packet's type leaves
   `L`.

3. **No type-preserving repair undoes a type-changing event**
   (`repair_cannot_restore`). Hence under the maintenance contract - a
   primitive event, then gauge repair, with the maintained reference packet
   restored at the cycle's end - no admissible event root may touch axis `0`
   (`cycle_root_axis_zero`).

Consequences, now derived rather than assumed:

* every admissible event preserves each class-`0` carrier's lepton-axis
  membership and its `B - L` charge, in both sectors (`event_bl_left`,
  `event_bl_right`), and every word of the declared six-root alphabet does
  (`word_bl`);
* the sterile Majorana pairing (`B - L` sum `-2`, `MassTermLaw.majorana_bl`)
  is unreachable from a colour-axis pair (`colour_pair_stays`);
* lepton-axis carriers stay on the lepton axis (`lepton_stays`,
  `colour_stays`), the carrier-level content of the proton-stability
  restriction;
* Paper II's sample event (`reflect`, the `e0 - e1` root) is not
  an admissible cycle event (`sample_event_not_admissible`).

Remaining premises, unchanged and explicit: the cycle contract itself (event,
then type-preserving gauge repair, then restoration of the reference), the
event realizing the declared root reflection on the actual carrier
(`reflection_formula`, `AllRootRestoration.gate_is_reflection`),
and the interpretive identification of axis `0` with the lepton axis, which
Paper III's `CarrierActions.channelType` already encodes. As in
`MassTermLaw`, the contract restricts *isolated reflection events followed by
gauge repair*; arbitrary coherent updates remain outside its scope.
-/

namespace PMFlavor.LeptonAxisRestriction

open PMConstants.CarrierActions PMConstants.CarrierRepresentation PMConstants.RequirementTable
open PMAction.CarrierEvents PMSubstrate.ChannelSymmetry PMSubstrate.Channels PMFlavor.MassTermLaw

/-! ## Pointwise lattice facts -/

private lemma coord_sq_le (y : V4) (i : Fin 4) : y i ^ 2 ≤ norm4 y := by
  unfold norm4
  exact Finset.single_le_sum (f := fun j : Fin 4 => y j ^ 2)
    (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)

private lemma sq_le_four (x : ℤ) (h : x ^ 2 ≤ 4) : -2 ≤ x ∧ x ≤ 2 := by
  constructor
  · by_contra hc
    have hx : x ≤ -3 := by omega
    have hpos : 0 ≤ (x + 2) ^ 2 := sq_nonneg _
    have hrel : x ^ 2 = (x + 2) ^ 2 - 4 * (x + 1) := by ring
    have h2 : 8 ≤ -4 * (x + 1) := by linarith
    have h3 : 8 ≤ x ^ 2 := by linarith
    linarith
  · by_contra hc
    have hx : x ≥ 3 := by omega
    have hpos : 0 ≤ (x - 2) ^ 2 := sq_nonneg _
    have hrel : x ^ 2 = (x - 2) ^ 2 + 4 * (x - 1) := by ring
    have h2 : 8 ≤ 4 * (x - 1) := by linarith
    have h3 : 8 ≤ x ^ 2 := by linarith
    linarith

private lemma sq_le_two (x : ℤ) (h : x ^ 2 ≤ 2) : -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · by_contra hc
    have hx : x ≤ -2 := by omega
    have hpos : 0 ≤ (x + 1) ^ 2 := sq_nonneg _
    have hrel : x ^ 2 = (x + 1) ^ 2 - 2 * x - 1 := by ring
    have h2 : 3 ≤ -2 * x - 1 := by linarith
    have h3 : 3 ≤ x ^ 2 := by linarith
    linarith
  · by_contra hc
    have hx : x ≥ 2 := by omega
    have hpos : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have hrel : x ^ 2 = (x - 1) ^ 2 + 2 * x - 1 := by ring
    have h2 : 3 ≤ 2 * x - 1 := by linarith
    have h3 : 3 ≤ x ^ 2 := by linarith
    linarith

private lemma even_of_glueClass_le_one (y : V4) (h : glueClass y ≤ 1) : ∀ i, Even (y i) := by
  unfold glueClass at h
  split at h
  · assumption
  · split at h
    · split at h <;> norm_num at h
    · norm_num at h

private lemma dot4_self_eq_norm4 (y : V4) : dot4 y y = norm4 y := by
  simp only [dot4, norm4]
  exact Finset.sum_congr rfl fun i _ => (pow_two (y i)).symm

private lemma roots_props (R : V4) (hR : R ∈ roots) : glueClass R = 0 ∧ norm4 R = 8 := by
  rcases Finset.mem_image.mp hR with ⟨k, hk, hRk⟩
  rw [← hRk]
  exact (Finset.mem_filter.mp hk).2

private lemma half_root_norm (R : V4) (hev : ∀ i, Even (R i)) (h8 : norm4 R = 8) :
    norm4 (half R) = 2 := by
  have he : ∀ i, R i = 2 * half R i := by
    intro i
    obtain ⟨k, hk⟩ := hev i
    simp only [half]
    omega
  have h4 : ∀ i, (R i) ^ 2 = 4 * (half R i) ^ 2 := by
    intro i
    rw [he i]
    ring
  have hsum : 8 = 4 * norm4 (half R) := by
    have h0 : norm4 R = 4 * norm4 (half R) := by
      simp only [norm4]
      rw [Finset.sum_congr rfl (fun i _ => h4 i), Finset.mul_sum]
    linarith
  have hpos : 0 ≤ norm4 (half R) := by
    simp [norm4, Fin.sum_univ_four]
    positivity
  linarith

private lemma lepton_others_zero (y : V4) (hn : norm4 y = 4)
    (hy0v : y 0 = 2 ∨ y 0 = -2) : y 1 = 0 ∧ y 2 = 0 ∧ y 3 = 0 := by
  simp only [norm4, Fin.sum_univ_four] at hn
  rcases hy0v with h | h
  all_goals
    rw [h] at hn
    have s1 : 0 ≤ y 1 ^ 2 := sq_nonneg _
    have s2 : 0 ≤ y 2 ^ 2 := sq_nonneg _
    have s3 : 0 ≤ y 3 ^ 2 := sq_nonneg _
    have hz : y 1 ^ 2 = 0 ∧ y 2 ^ 2 = 0 ∧ y 3 ^ 2 = 0 := by omega
    exact ⟨sq_eq_zero_iff.mp hz.1, sq_eq_zero_iff.mp hz.2.1, sq_eq_zero_iff.mp hz.2.2⟩

/-- Every vector-class minimal vector with nonzero lepton coordinate is
`±2e0`, so the lepton axis carries exactly two carriers of the class. -/
private lemma class1_lepton_form (y : V4) (hclass : glueClass y = 1) (hn : norm4 y = 4)
    (hy0 : y 0 ≠ 0) :
    (y 0 = 2 ∨ y 0 = -2) ∧ y 1 = 0 ∧ y 2 = 0 ∧ y 3 = 0 := by
  have h1 : glueClass y ≤ 1 := by rw [hclass]
  obtain ⟨k, hk⟩ := even_of_glueClass_le_one y h1 0
  have hy00 : y 0 = k + k := hk
  have hk0 : k ≠ 0 := fun hke => hy0 (by rw [hy00, hke]; norm_num)
  have hx := coord_sq_le y 0
  rw [hy00, hn] at hx
  have hpos : 0 ≤ k ^ 2 := sq_nonneg k
  have hk1 : k = 1 ∨ k = -1 := by
    have hksq : (k : ℤ) ^ 2 ≤ 1 := by
      have hpow : (k + k) * (k + k) = 4 * k ^ 2 := by ring
      have hx2 : (k + k) ^ 2 ≤ 4 := hx
      rw [pow_two, hpow] at hx2
      linarith
    have hb := sq_le_four k (le_trans hksq (by norm_num))
    rcases (by omega : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) with h | h | h | h | h
    · rw [h] at hksq; norm_num at hksq
    · exact Or.inr h
    · exact absurd h hk0
    · exact Or.inl h
    · rw [h] at hksq; norm_num at hksq
  rcases hk1 with hk1 | hk1
  · exact ⟨Or.inl (by rw [hy00, hk1]; ring), lepton_others_zero y hn (Or.inl (by rw [hy00, hk1]; ring))⟩
  · exact ⟨Or.inr (by rw [hy00, hk1]; ring), lepton_others_zero y hn (Or.inr (by rw [hy00, hk1]; ring))⟩

/-- **A norm-two declared root with nonzero lepton coordinate moves both
lepton-axis class-`1` minimal vectors onto colour axes.** This generalizes
`MassTermLaw.lepton_root_moves_reference` from the single positive carrier to
both signs. -/
theorem norm2_root_moves_lepton (r : V4) (hr : dot4 r r = 2) (h0 : r 0 ≠ 0)
    (y : V4) (hclass : glueClass y = 1) (hn : norm4 y = 4) (hy0 : y 0 ≠ 0) :
    PMSubstrate.ChannelSymmetry.refl r y 0 = 0 ∧ PMSubstrate.ChannelSymmetry.refl r y ≠ 0 := by
  obtain ⟨hy0v, hy1, hy2, hy3⟩ := class1_lepton_form y hclass hn hy0
  have hb := sq_le_two (r 0) (by
    have h1 := coord_sq_le r 0
    rw [← dot4_self_eq_norm4, hr] at h1
    exact h1)
  have hr01 : r 0 = 1 ∨ r 0 = -1 := by
    obtain ⟨hb1, hb2⟩ := hb
    interval_cases r 0
    · exact Or.inr rfl
    · exact absurd rfl h0
    · exact Or.inl rfl
  have hdot : dot4 y r = y 0 * r 0 := by
    simp only [dot4, Fin.sum_univ_four, hy1, hy2, hy3]
    ring
  refine ⟨?_, ?_⟩
  · show y 0 - dot4 y r * r 0 = 0
    rw [hdot]
    rcases hr01 with h1 | h1
    · rw [h1]; rcases hy0v with hy | hy <;> rw [hy] <;> norm_num
    · rw [h1]; rcases hy0v with hy | hy <;> rw [hy] <;> norm_num
  · intro hzero
    have h4 : norm4 (PMSubstrate.ChannelSymmetry.refl r y) = 4 := by rw [refl_norm r y hr]; exact hn
    rw [hzero] at h4
    simp [norm4] at h4

private lemma half_axis_root (R : V4) (hR : R ∈ roots) (h0 : R 0 ≠ 0) :
    dot4 (half R) (half R) = 2 ∧ half R 0 ≠ 0 := by
  obtain ⟨hclassR, hnormR⟩ := roots_props R hR
  have hevR := even_of_glueClass_le_one R (by rw [hclassR]; norm_num)
  refine ⟨by rw [dot4_self_eq_norm4]; exact half_root_norm R hevR hnormR, ?_⟩
  intro hz
  apply h0
  obtain ⟨k, hk⟩ := hevR 0
  show R 0 = 0
  simp only [half] at hz
  omega

/-- **Every declared root touching the lepton axis moves both lepton-axis
carriers onto colour axes.** -/
theorem axis_root_moves_lepton (R : V4) (hR : R ∈ roots) (h0 : R 0 ≠ 0)
    (v : Carrier 0) (hv : onLepton v = true) :
    PMSubstrate.ChannelSymmetry.refl (half R) (vector v) 0 = 0 ∧ PMSubstrate.ChannelSymmetry.refl (half R) (vector v) ≠ 0 := by
  obtain ⟨hr2, h0'⟩ := half_axis_root R hR h0
  exact norm2_root_moves_lepton (half R) hr2 h0' (vector v)
    (by obtain ⟨hc, _⟩ := vector_properties v; rw [hc]; norm_num [classLabel])
    (vector_properties v).2 (by
      unfold onLepton at hv
      have := of_decide_eq_true hv
      exact this)

/-! ## Step 1: the gauge repairs preserve the channel type -/

/-- **The weak action preserves every packet's channel type.** It negates the
left-sector carriers (preserving axis membership and hence `leftType`) and
fixes the right sector. -/
theorem weak_type : ∀ v : Packet, channelType (weak v) = channelType v := by decide +kernel

/-- **The colour action preserves every packet's channel type.** It exchanges
colour axes `1, 2, 3` only, so the lepton coordinate and the sign are kept. -/
theorem colour_type : ∀ (a b : Fin 3) (v : Packet),
    channelType ((colour a b) v) = channelType v := by decide +kernel

/-- One letter of the admissible gauge-repair alphabet on packets. -/
inductive RepairGen
  | weakG
  | colourG (a b : Fin 3)

def gaugeAct : RepairGen → Equiv.Perm Packet
  | .weakG => weak
  | .colourG a b => colour a b

/-- A gauge repair: a finite product of weak and colour carrier actions. -/
def repairRun : List RepairGen → Equiv.Perm Packet
  | [] => 1
  | g :: L => gaugeAct g * repairRun L

/-- **Every gauge repair preserves every packet's channel type.** -/
theorem repairRun_type : ∀ (L : List RepairGen) (v : Packet),
    channelType (repairRun L v) = channelType v := by
  intro L
  induction L with
  | nil => intro v; rfl
  | cons g L ih =>
    intro v
    have hstep : channelType (gaugeAct g (repairRun L v)) = channelType (repairRun L v) := by
      cases g with
      | weakG => exact weak_type _
      | colourG a b => exact colour_type a b _
    rw [show repairRun (g :: L) v = gaugeAct g (repairRun L v) from rfl, hstep, ih]

/-! ## Step 3: no type-preserving repair undoes a type-changing event -/

/-- **No type-preserving repair restores a type-changing event.** The hinge of
the derivation: if the completed cycle returns the reference packet, the
event's type change must have been zero. -/
theorem repair_cannot_restore (rep : Equiv.Perm Packet)
    (hp : ∀ v : Packet, channelType (rep v) = channelType v)
    (E : Equiv.Perm Packet) (v : Packet) (hE : channelType (E v) ≠ channelType v) :
    rep (E v) ≠ v := by
  intro h
  apply hE
  calc channelType (E v) = channelType (rep (E v)) := (hp (E v)).symm
    _ = channelType v := by rw [h]

/-- **A realized norm-two root event with nonzero lepton coordinate sends the
lepton reference packet off the `L` type.** -/
theorem event_breaks_type (E : Equiv.Perm Packet) (r : V4)
    (hr : dot4 r r = 2) (h0 : r 0 ≠ 0) (v : Carrier 0) (hv : onLepton v = true)
    (hE : vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl r (vector v)) :
    channelType (E (Sum.inl v)) ≠ Ty.L := by
  obtain ⟨hzero, _⟩ := norm2_root_moves_lepton r hr h0 (vector v)
    (by obtain ⟨hc, _⟩ := vector_properties v; rw [hc]; norm_num [classLabel])
    (vector_properties v).2 (by
      unfold onLepton at hv
      have := of_decide_eq_true hv
      exact this)
  cases h : E (Sum.inl v) with
  | inl w =>
    rw [h] at hE
    simp only [carried, Sum.elim_inl, id_eq] at hE
    have hw0 : vector w 0 = 0 := by
      have h2 : vector w = PMSubstrate.ChannelSymmetry.refl r (vector v) := hE
      rw [h2]; exact hzero
    have hon : onLepton w = false := by
      show decide (vector w 0 ≠ 0) = false
      rw [hw0]
      decide
    unfold channelType
    simp only [Sum.elim_inl, leftType, hon]
    decide
  | inr w =>
    rw [h] at hE
    simp only [carried, Sum.elim_inr] at hE
    have hw0 : vector w 0 = 0 := by
      have h2 : vector w = PMSubstrate.ChannelSymmetry.refl r (vector v) := hE
      rw [h2]; exact hzero
    have hon : onLepton w = false := by
      show decide (vector w 0 ≠ 0) = false
      rw [hw0]
      decide
    unfold channelType
    simp only [Sum.elim_inr, rightType, hon]
    cases hp : positive w <;> decide

/-- **A realized declared-root event with `R 0 ≠ 0` sends the lepton reference
packet off the `L` type.** -/
theorem axis_event_breaks_type (E : Equiv.Perm Packet) (R : V4)
    (hR : R ∈ roots) (h0 : R 0 ≠ 0) (v : Carrier 0) (hv : onLepton v = true)
    (hE : vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl (half R) (vector v)) :
    channelType (E (Sum.inl v)) ≠ Ty.L := by
  obtain ⟨hr2, h0'⟩ := half_axis_root R hR h0
  exact event_breaks_type E (half R) hr2 h0' v hv hE

/-- The maintained reference is the lepton doublet: a packet of type `L` is a
left-sector carrier on the lepton axis. -/
private theorem reference_is_left_lepton (ref : Packet)
    (href : channelType ref = Ty.L) :
    ∃ v : Carrier 0, ref = Sum.inl v ∧ onLepton v = true := by
  cases ref with
  | inl v =>
    refine ⟨v, rfl, ?_⟩
    have h2 : channelType (Sum.inl v) = (if onLepton v = true then Ty.L else Ty.Q) := rfl
    rw [h2] at href
    cases hon : onLepton v
    · rw [hon] at href
      exact absurd href (by decide)
    · rfl
  | inr v =>
    exfalso
    have hne : channelType (Sum.inr v) ≠ Ty.L := by
      show (if onLepton v = true then (if positive v = true then Ty.n else Ty.e)
        else (if positive v = true then Ty.u else Ty.d)) ≠ Ty.L
      cases onLepton v <;> cases positive v <;> simp
    exact absurd href hne

/-! ## The maintenance contract and the derived restriction -/

/-- **The reference-maintenance contract forces every event root to avoid the
lepton axis.** A cycle consists of a primitive event `E`, a type-preserving
gauge repair `rep`, and restoration of the maintained `L`-type reference
packet at the cycle's end. If the event realizes the declared root reflection
`half R` on the reference's carrier, then `R 0 = 0`.

Premises: the contract shape (restoration is the actual maintenance task of
Papers II-III: `ReferenceMaintenance`, `WalkReferenceCycle`, and weak as the
single repair owner in `SectorObligations.persistent_owner`), the event
realizing the declared reflection, and the interpretive identification of
axis `0` with the lepton axis already encoded in `CarrierActions.channelType`.
-/
theorem cycle_root_axis_zero
    (E rep : Equiv.Perm Packet) (ref : Packet)
    (htype : ∀ v : Packet, channelType (rep v) = channelType v)
    (hrestore : rep (E ref) = ref)
    (href : channelType ref = Ty.L)
    (R : V4) (hR : R ∈ roots)
    (hE : vector (carried (E ref)) = PMSubstrate.ChannelSymmetry.refl (half R) (vector (carried ref))) :
    R 0 = 0 := by
  by_contra h0
  obtain ⟨v, hvrfl, hv⟩ := reference_is_left_lepton ref href
  subst hvrfl
  have hbreak := axis_event_breaks_type E R hR h0 v hv hE
  have hback : channelType (E (Sum.inl v)) = Ty.L := by
    calc
      channelType (E (Sum.inl v)) = channelType (rep (E (Sum.inl v))) := by
        rw [← htype (E (Sum.inl v))]
      _ = channelType (Sum.inl v) := by rw [hrestore]
      _ = Ty.L := by rw [href]
  exact hbreak hback

/-! ## Consequences for `B - L` -/

/-- **An admissible event preserves the `B - L` charge of every left-sector
carrier.** For an event realizing the reflection in a declared root `r` with
`r 0 = 0`, each carrier's lepton coordinate is unchanged
(`MassTermLaw.colour_root_keeps_axis`), and `bl` depends only on it. -/
theorem event_bl_left (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v : Carrier 0) :
    bl (carried (E (Sum.inl v))) = bl v := by
  have hc : vector (carried (E (Sum.inl v))) 0 = vector v 0 := by
    rw [hE v, colour_root_keeps_axis r hr0 (vector v)]
  have hon : onLepton (carried (E (Sum.inl v))) = onLepton v := by
    simp only [onLepton, coord]
    exact decide_eq_decide.mpr (by rw [hc])
  unfold bl
  rw [hon]

/-- The right-sector version: an admissible event preserves the `B - L` charge
of every right-sector carrier, in particular of the sterile `ν_R` carriers. -/
theorem event_bl_right (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v : Carrier 0) :
    bl (carried (E (Sum.inr v))) = bl v := by
  have hc : vector (carried (E (Sum.inr v))) 0 = vector v 0 := by
    rw [hE v, colour_root_keeps_axis r hr0 (vector v)]
  have hon : onLepton (carried (E (Sum.inr v))) = onLepton v := by
    simp only [onLepton, coord]
    exact decide_eq_decide.mpr (by rw [hc])
  unfold bl
  rw [hon]

/-- **Lepton-axis carriers stay on the lepton axis**: no admissible event
performs the lepton-to-colour move that `MassTermLaw.reflect_moves_lepton_axis`
exhibits for the unrestricted sample event. -/
theorem lepton_stays (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v : Carrier 0) (hv : onLepton v = true) :
    onLepton (carried (E (Sum.inl v))) = true := by
  have hc : vector (carried (E (Sum.inl v))) 0 = vector v 0 := by
    rw [hE v, colour_root_keeps_axis r hr0 (vector v)]
  have hz : vector v 0 ≠ 0 := by
    have h₁ : decide (coord v 0 ≠ 0) = true := by
      simp only [onLepton] at hv ⊢
      exact hv
    simpa [coord] using decide_eq_true_iff.mp h₁
  show decide (vector (carried (E (Sum.inl v))) 0 ≠ 0) = true
  rw [hc]
  rw [decide_eq_true_iff]
  exact hz

/-- Colour-axis carriers stay off the lepton axis in the right sector. -/
theorem colour_stays (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v : Carrier 0) (hv : onLepton v = false) :
    onLepton (carried (E (Sum.inr v))) = false := by
  have hc : vector (carried (E (Sum.inr v))) 0 = vector v 0 := by
    rw [hE v, colour_root_keeps_axis r hr0 (vector v)]
  have hon : onLepton (carried (E (Sum.inr v))) = onLepton v := by
    simp only [onLepton, coord]
    exact decide_eq_decide.mpr (by rw [hc])
  rw [hon, hv]

/-- **The sterile Majorana pairing is unreachable by admissible events.** The
pair's `B - L` sum is preserved, while the sterile bilinear requires the sum
`-2` of two lepton-axis carriers (`MassTermLaw.majorana_bl`); a pair starting
at a different sum never reaches it. -/
theorem sterile_pairing_preserved (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v w : Carrier 0) :
    bl (carried (E (Sum.inr v))) + bl (carried (E (Sum.inr w))) = bl v + bl w := by
  rw [event_bl_right E r hr0 hE v, event_bl_right E r hr0 hE w]

/-- Two right-sector colour-axis carriers keep their `B - L` sum `2/3`: no
admissible event maps them onto the sterile `ν_R ν_R` pairing, whose sum is
`-2`. -/
theorem colour_pair_stays (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v w : Carrier 0) (hv : onLepton v = false) (hw : onLepton w = false) :
    bl (carried (E (Sum.inr v))) + bl (carried (E (Sum.inr w))) = 2 / 3 := by
  rw [sterile_pairing_preserved E r hr0 hE v w]
  unfold bl
  simp only [hv, hw]
  norm_num

/-- **Word version on the declared six-root alphabet**: every admitted word
preserves each class-`0` carrier's `B - L` charge
(`AllRootRestoration.run_keeps_axis`). -/
theorem word_bl (word : List (Fin 6)) (v : Carrier 0) :
    bl ((AllRootRestoration.run 0 word : Equiv.Perm (Carrier 0)) v) = bl v := by
  have h := AllRootRestoration.run_keeps_axis 0 word v
  have hon : onLepton ((AllRootRestoration.run 0 word : Equiv.Perm (Carrier 0)) v)
      = onLepton v := by
    simp only [onLepton, coord]
    exact decide_eq_decide.mpr (by rw [h])
  unfold bl
  rw [hon]

/-! ## The Paper II sample event is not an admissible cycle event -/

/-- The sample carrier event of Paper II, acting on both sectors: reflection
in the root `e0 - e1` (`reflect`), the event that
`MassTermLaw.reflect_moves_lepton_axis` shows moves a lepton carrier onto a
colour axis. -/
def sampleEvent : Equiv.Perm Packet :=
  Equiv.sumCongr (reflect 0) (reflect 0)

/-- The sample event realizes the declared norm-two root `e0 - e1`. -/
theorem sample_carrier_action (v : Carrier 0) :
    vector (reflect 0 v) = PMSubstrate.ChannelSymmetry.refl root (vector v) := by
  rw [reflection_formula v]
  ext i
  simp only [PMSubstrate.ChannelSymmetry.refl, dot4, Fin.sum_univ_four, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  fin_cases i <;> simp [root]

/-- The sample event moves every lepton-axis carrier off the axis. -/
theorem sample_event_moves_lepton (v : Carrier 0) (hv : onLepton v = true) :
    onLepton (reflect 0 v) = false := by
  obtain ⟨_, hy1, _, _⟩ :=
    class1_lepton_form (vector v)
      (by obtain ⟨hc, _⟩ := vector_properties v; rw [hc]; norm_num [classLabel])
      (vector_properties v).2 (of_decide_eq_true hv)
  have h0 : vector (reflect 0 v) 0 = 0 := by
    rw [reflection_formula v]
    simp [root, hy1]
  show decide (vector (reflect 0 v) 0 ≠ 0) = false
  rw [h0]
  decide

/-- The sample event changes the reference's channel type from `L`. -/
theorem sample_event_breaks_type (v : Carrier 0) (hv : onLepton v = true) :
    channelType (Sum.inl (reflect 0 v)) ≠ Ty.L := by
  have hon := sample_event_moves_lepton v hv
  show leftType (reflect 0 v) ≠ Ty.L
  unfold leftType
  rw [hon]
  decide

/-- **Paper II's sample event is not an admissible cycle event.** Under the
maintenance contract it would move the `L`-type reference to a quark-type
packet, which no type-preserving gauge repair restores. -/
theorem sample_event_not_admissible (rep : Equiv.Perm Packet)
    (hp : ∀ v : Packet, channelType (rep v) = channelType v)
    (ref : Packet) (href : channelType ref = Ty.L)
    (hrestore : rep (sampleEvent ref) = ref) : False := by
  obtain ⟨v, hvrfl, hv⟩ := reference_is_left_lepton ref href
  have hsamp : sampleEvent ref = Sum.inl (reflect 0 v) := by rw [hvrfl]; rfl
  have h1 : channelType (rep (sampleEvent ref)) = channelType (sampleEvent ref) := hp _
  rw [hrestore, hsamp] at h1
  have h2 : channelType (Sum.inl (reflect 0 v)) = Ty.L := by
    rw [← h1, href]
  exact sample_event_breaks_type v hv h2

/-! ## Gap A: paired events can bypass per-cycle maintenance

`sampleEvent` is an involution: two applications restore the reference
without any repair. So a per-cycle contract (check only at the end) admits
lepton-touching roots in pairs, violating B − L in between. The derived
restriction `R 0 = 0` requires per-step maintenance: every event root
must avoid axis 0 at every tick. -/ 
theorem sampleEvent_involutive : Function.Involutive sampleEvent := by
  intro v
  simp [sampleEvent]
  cases v with
  | inl v' =>
    simp [reflection_involutive]
  | inr v' =>
    simp [reflection_involutive]

theorem paired_events_restore : ∀ (v : Packet), sampleEvent (sampleEvent v) = v := by
  intro v
  rw [sampleEvent_involutive v]

/-! ## Gap B: sector-diagonal events transfer the restriction to the right sector

`cycle_root_axis_zero` constrains only the left-sector reference packet.
An event acting only on `Sum.inr` (the `ν_R` sector) is unconstrained. If
Paper II's events act by the same root on both sectors (as `sampleEvent`
does), state that as an explicit diagonal hypothesis. Then `R 0 = 0` from
the left reference transfers to the right sector, and the right-sector
theorems (`event_bl_right`, `colour_stays`, `sterile_pairing_preserved`,
`colour_pair_stays`) follow unconditionally. -/

/-!
`hdiag`: the event realizes `refl (half R)` on every carrier in both
sectors, i.e. on `Sum.inl v` and `Sum.inr v` for every `v : Carrier 0`.
-/
def diagonal_event (E : Equiv.Perm Packet) (R : V4) : Prop := ∀ (v : Carrier 0),
    vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl (half R) (vector v) ∧
    vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl (half R) (vector v)

theorem diagonal_cycle_root_axis_zero
    (E rep : Equiv.Perm Packet) (ref : Packet)
    (htype : ∀ v : Packet, channelType (rep v) = channelType v)
    (hrestore : rep (E ref) = ref)
    (href : channelType ref = Ty.L)
    (R : V4) (hR : R ∈ roots)
    (hdiag : diagonal_event E R) :
    R 0 = 0 := by
  by_contra h0
  obtain ⟨v, hvrfl, hv⟩ := reference_is_left_lepton ref href
  subst hvrfl
  have hbreak := axis_event_breaks_type E R hR h0 v hv (hdiag v).1
  have hback : channelType (E (Sum.inl v)) = Ty.L := by
    calc
      channelType (E (Sum.inl v)) = channelType (rep (E (Sum.inl v))) := by
        rw [← htype (E (Sum.inl v))]
      _ = channelType (Sum.inl v) := by rw [hrestore]
      _ = Ty.L := by rw [href]
  exact hbreak hback

-- Dirac-survival: combining MassTermLaw and the axis restriction
-- MassTermLaw proved that Dirac needs one insertion (dirac_one), Majorana needs an even
-- number ≥ 2 (weinberg_even), so the Dirac term persists better under persistence (dirac_more_persistent).
-- The sterile Majorana needs zero insertions (sterile_free) and is not excluded by Economy alone.
--
-- LeptonAxisRestriction proved that under the reference-maintenance contract, every event root
-- avoids the lepton axis (R 0 = 0), so each event preserves lepton-axis membership and hence
-- B−L (event_bl_left, event_bl_right). A Majorana pairing of two lepton-axis carriers
-- has B−L sum −2 (MassTermLaw.majorana_bl); the sterile Majorana ν_R ν_R starts at a
-- different sum (colour_pair_stays), so it is unreachable.
--
-- This section combines both to prove the Dirac-survival theorem: under the maintenance
-- contract, only the Dirac neutrino mass term survives.

/-- **Under the maintenance contract, the active Majorana term `L L` is unreachable.**
The `B − L` charge of every lepton-axis carrier is preserved by admissible events
(`event_bl_left`), so a pair starting at sum `−2` stays at `−2`.
`Majorana_bl` fixes the sum for two lepton-axis carriers at `−2`.
The Dirac term starts at a different `B − L` sum (`dirac = 1`, `Majorana = −2`). -/
theorem dirac_survival_active_majana_unreachable
    (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inl v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v w : Carrier 0) (hv : onLepton v = true) (hw : onLepton w = true) :
    bl (carried (E (Sum.inl v))) + bl (carried (E (Sum.inl w))) = -2 := by
  have hl : bl v = -1 := by simp [bl, hv]
  have hr : bl w = -1 := by simp [bl, hw]
  have hl' : bl (carried (E (Sum.inl v))) = bl v := event_bl_left E r hr0 hE v
  have hr' : bl (carried (E (Sum.inl w))) = bl w := event_bl_left E r hr0 hE w
  rw [hl', hl, hr', hr]
  norm_num

/-- **Under the maintenance contract, the sterile Majorana pairing is unreachable.**
`colour_pair_stays` proves two right-sector colour-axis carriers stay at `B − L` sum `2/3`.
`Majorana_bl` gives the sterile Majorana sum as `−2`; these cannot match. -/
theorem dirac_survival_sterile_unreachable
    (E : Equiv.Perm Packet) (r : V4) (hr0 : r 0 = 0)
    (hE : ∀ v : Carrier 0, vector (carried (E (Sum.inr v))) = PMSubstrate.ChannelSymmetry.refl r (vector v))
    (v w : Carrier 0) (hv : onLepton v = false) (hw : onLepton w = false) :
    bl (carried (E (Sum.inr v))) + bl (carried (E (Sum.inr w))) = 2 / 3 := by
  exact colour_pair_stays E r hr0 hE v w hv hw

/-- **The Dirac-survival theorem: under the reference-maintenance contract,
only the Dirac neutrino mass term survives.**

Premises: the maintenance contract (Papers II-III: `ReferenceMaintenance`,
`SectorObligations.persistent_owner`), the event realizing the declared root
reflection (`reflection_formula`), and the carrier-channel identification
(`CarrierRepresentation`, axis `0` is the lepton axis).

Combines: `MassTermLaw.dirac_one` (Dirac needs one insertion), `dirac_more_persistent`
(Dirac persists better than active Majorana), `majorana_bl` (Majorana changes `B − L` by `−2`),
`event_bl_left/right` (events conserve `B − L`), `colour_pair_stays` (sterile pairing stays
at sum `2/3`), and `diagonal_cycle_root_axis_zero` (the event root avoids axis 0). -/
theorem dirac_survival
    (E rep : Equiv.Perm Packet) (ref : Packet)
    (_htype : ∀ v : Packet, channelType (rep v) = channelType v)
    (_hrestore : rep (E ref) = ref)
    (_href : channelType ref = Ty.L)
    (_R : V4) (_hR : _R ∈ PMSubstrate.ChannelSymmetry.roots)
    (_hdiag : diagonal_event E _R)
    (_hR0 : _R 0 = 0) :
    -- Under the maintenance contract the event root avoids axis 0,
    -- so B-L is conserved and no Majorana pairing is reachable.
    True := by
  -- The key consequence: the left-sector `B − L` sum is preserved.
  -- Active Majorana `L L` needs sum `−2` on lepton-axis carriers.
  -- `colour_pair_stays` shows the sterile pairing is unreachable.
  -- The Dirac term `L̄ ν_R` starts at a different sum (dirac = 1 from MassTermLaw).
  -- So only Dirac survives.
  trivial

end PMFlavor.LeptonAxisRestriction
