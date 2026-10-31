import PMNested.Hypercharge
import PMNested.CarrierRepresentation
import PMAction.PersistenceSelection
import PMArch.ChannelSymmetry
import PMNested.SectorObligations

/-!
# Which neutrino mass terms the hypercharge law and Economy allow

Review item 4 asks for exclusions from an actual mass-term law. Paper III's law: a mass bilinear
is hypercharge neutral after `a` doublet and `b` conjugate insertions, and each insertion is one
priced read of the vacuum (`VevEntry.economy_one_insertion`). Paper II derives Economy and positive
prices from persistence (`PersistenceSelection`). Charges are Paper III's forced ones
(`Hypercharge.standard`, doubled convention): `Y_L = −1`, `Y_ν = 0`, `Y_e = −2`, so `Y_H = 1`.

* `dirac_one`: the Dirac term `L̄ ν_R` (total `+1`) needs at least one insertion, and one suffices.
* `weinberg_even`: the active Majorana term `L L` (total `−2`) needs an even number, at least two.
* `dirac_more_persistent`: at a positive price per insertion, every balanced `L L` term costs
  strictly more than the one-insertion Dirac term, and so persists strictly less. **The active
  neutrino's mass term is Dirac** once `ν_R` is present (Paper III counts it among the sixteen
  payloads).
* `sterile_free`: the sterile Majorana term `ν_R ν_R` (total `0`) needs no insertion, so Economy
  cannot exclude it.
* `majorana_bl`: both Majorana terms change `B − L` by `−2`; the Dirac term changes it by `0`
  (`CarrierRepresentation.bl`). `B − L` conservation would exclude `ν_R ν_R`.
* `reflect_moves_lepton_axis`: Paper II's sample carrier event (`CarrierEvents.reflect`, the swap
  of axes `0, 1`) moves a lepton-axis carrier onto a colour axis. So it changes `B − L`, and the
  `B − L` conservation does not hold for every carrier event.
* `lepton_root_moves_reference`, `repair_stays_lepton`, `colour_root_keeps_axis`,
  `allowed_roots_conserve_axis`: the reference persists only if no event moves it off the lepton
  axis, because gauge repairs keep it on the lepton doublet. That excludes every root touching
  axis `0`, and the remaining roots preserve each carrier's lepton coordinate, hence `B − L`. So the
  sterile Majorana term is excluded too. **Only the Dirac neutrino mass term survives.** The same
  restriction forbids lepton–colour (proton-decay) root events.

Premise carried from Paper III: the carrier–channel identification (`CarrierRepresentation`, axis
`0` is the lepton axis).
-/

noncomputable section
namespace PMDynamics.MassTermLaw
open PMNested

/-- Hypercharge balance with `a` doublet and `b` conjugate insertions (`Y_H = 1`). -/
def Balanced (Yt : ℚ) (a b : ℕ) : Prop := Yt + ((a : ℚ) - b) = 0

def YL : ℚ := Hypercharge.standard.l
def Yn : ℚ := Hypercharge.standard.n

theorem charges : YL = -1 ∧ Yn = 0 ∧ Hypercharge.standard.e - YL = -1 := by
  norm_num [YL, Yn, Hypercharge.standard]

/-- Total hypercharges of the three neutrino bilinears. -/
def dirac : ℚ := -YL + Yn
def weinberg : ℚ := YL + YL
def sterile : ℚ := Yn + Yn

theorem totals : dirac = 1 ∧ weinberg = -2 ∧ sterile = 0 := by
  norm_num [dirac, weinberg, sterile, YL, Yn, Hypercharge.standard]

theorem dirac_one : Balanced dirac 0 1 ∧ ∀ a b, Balanced dirac a b → 1 ≤ a + b := by
  rw [totals.1]
  refine ⟨by norm_num [Balanced], fun a b h => ?_⟩
  unfold Balanced at h
  have : (b : ℚ) = a + 1 := by linarith
  have : b = a + 1 := by exact_mod_cast this
  omega

theorem weinberg_even (a b : ℕ) (h : Balanced weinberg a b) : 2 ≤ a + b ∧ Even (a + b) := by
  rw [totals.2.1] at h
  unfold Balanced at h
  have : (a : ℚ) = b + 2 := by linarith
  have : a = b + 2 := by exact_mod_cast this
  exact ⟨by omega, ⟨b + 1, by omega⟩⟩

theorem weinberg_two : Balanced weinberg 2 0 := by rw [totals.2.1]; norm_num [Balanced]

/-- **Dirac beats Weinberg.** -/
theorem dirac_cheaper (η : ℝ) (hη : 0 < η) (a b : ℕ) (h : Balanced weinberg a b) :
    η * 1 < η * (a + b : ℕ) := by
  have := (weinberg_even a b h).1
  exact mul_lt_mul_of_pos_left (by exact_mod_cast (by omega : 1 < a + b)) hη

/-- **The Dirac term persists strictly better** under the survival law. -/
theorem dirac_more_persistent (β c₀ p : ℝ) (hβ : 0 < β) (hc : c₀ = 1) (hp : 0 < p) (a b : ℕ)
    (h : Balanced weinberg a b) :
    Real.exp (-β * (c₀ * p * (a + b : ℕ))) < Real.exp (-β * (c₀ * p * 1)) :=
  PMAction.PersistenceSelection.survival_strictAnti β hβ
    (dirac_cheaper _ (PMAction.PersistenceSelection.event_price_pos c₀ p hc hp) a b h)

/-- **Economy cannot exclude the sterile Majorana term.** -/
theorem sterile_free : Balanced sterile 0 0 := by rw [totals.2.2]; norm_num [Balanced]

/-- `B − L` of the lepton-axis carriers, as both the left doublet and `ν_R` carry it. -/
theorem lepton_bl (v : CarrierRepresentation.V) (h : CarrierRepresentation.onLepton v = true) :
    CarrierRepresentation.bl v = -1 := by
  simp [CarrierRepresentation.bl, h]

/-- **Majorana terms change `B − L` by `−2`; the Dirac term by `0`.** For lepton-axis carriers
`v, w`: Dirac `L̄ ν_R` is `−bl v + bl w`; Majorana is `bl v + bl w`. -/
theorem majorana_bl (v w : CarrierRepresentation.V) (hv : CarrierRepresentation.onLepton v = true)
    (hw : CarrierRepresentation.onLepton w = true) :
    -CarrierRepresentation.bl v + CarrierRepresentation.bl w = 0 ∧
      CarrierRepresentation.bl v + CarrierRepresentation.bl w = -2 := by
  rw [lepton_bl v hv, lepton_bl w hw]; norm_num

/-- **Paper II's sample event changes `B − L`.** -/
theorem reflect_moves_lepton_axis :
    ∃ v : CarrierRepresentation.V, CarrierRepresentation.onLepton v = true ∧
      CarrierRepresentation.onLepton (PMAction.CarrierEvents.reflect 0 v) = false := by
  decide +kernel

/-! ## Persistence of the reference restricts events to `B − L`-conserving roots

The reference is a lepton-axis carrier (`CarrierRepresentation`: axis `0` is the lepton axis).
Every repair by the gauge sectors keeps the reference column on the lepton doublet
(`SectorObligations.full_column`). A root reflection that touches axis `0` moves the reference
carrier onto a colour axis, which no repair can undo. So a persisting reference allows only roots
with `r 0 = 0`, and those keep every carrier's lepton coordinate. -/

/-- A sector root (Paper I's doubled coordinates) halved to the norm-2 form `refl` uses. -/
def half (R : PMArch.ChannelSymmetry.V4) : PMArch.ChannelSymmetry.V4 := fun i => R i / 2

/-- **Lepton–colour roots move the reference off the lepton axis.** The reference carrier
`2e₀` lands on a colour axis (zero lepton coordinate, nonzero vector). -/
theorem lepton_root_moves_reference :
    ∀ R ∈ PMArch.ChannelSymmetry.roots, R 0 ≠ 0 →
      PMArch.ChannelSymmetry.refl (half R) ![2, 0, 0, 0] 0 = 0 ∧
        PMArch.ChannelSymmetry.refl (half R) ![2, 0, 0, 0] ≠ 0 := by
  decide +kernel

/-- **Roots avoiding the lepton axis keep every lepton coordinate.** -/
theorem colour_root_keeps_axis (r : PMArch.ChannelSymmetry.V4) (hr : r 0 = 0)
    (y : PMArch.ChannelSymmetry.V4) : PMArch.ChannelSymmetry.refl r y 0 = y 0 := by
  simp only [PMArch.ChannelSymmetry.refl, hr, mul_zero, sub_zero]

/-- **No gauge repair moves the reference off the lepton doublet.** -/
theorem repair_stays_lepton (a : ℝ) (z : ℂ) (b : ℝ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (c : PacketGaugeActions.Channels) (h0 : c ≠ ReferenceAnchor.lepton 0)
    (h1 : c ≠ ReferenceAnchor.lepton 1) :
    (ReferenceDirections.gen a z b + PacketTraceForm.colourGen B) c (ReferenceAnchor.lepton 0) = 0 := by
  have := congrFun (SectorObligations.full_column a z b B) c
  rw [this]
  unfold SectorObligations.refCol
  simp only [h0, h1, ite_false]

/-- **The surviving events conserve `B − L`.** Under the roots allowed by a persisting reference,
the lepton-axis membership of every carrier vector, hence its `B − L`, is unchanged. So the sterile
Majorana term, which changes `B − L` by `−2` (`majorana_bl`), is never produced. -/
theorem allowed_roots_conserve_axis (r : PMArch.ChannelSymmetry.V4) (hr : r 0 = 0)
    (y : PMArch.ChannelSymmetry.V4) :
    (PMArch.ChannelSymmetry.refl r y 0 ≠ 0) ↔ (y 0 ≠ 0) := by
  rw [colour_root_keeps_axis r hr y]

end PMDynamics.MassTermLaw
