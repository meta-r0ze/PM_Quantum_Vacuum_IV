import PMArch.DerivedParameters
import PMDynamics.CKM
import PMDynamics.FlavourPulls
import PMDynamics.PMNS
import Mathlib.Tactic

/-!
# The flavour formulas in terms of the derived invariants, not numerals

Paper IV writes its six flavour inputs as functions of the substrate invariants
(Lean: `PMArch.Channels.nu_eq`, `PMArch.Derived.parameters_forced`,
`PMArch.Derived.boundary_sphere`):

    s₁₂  = π/(ν − χ)        s₁₃  = 1/(χ α⁻¹ + π)     |V_cb| = (π + χ)/(α⁻¹ − Dπ)
    sin²θ₁₂ = 1/(2φ)        sin²θ₂₃ = (1/χ)(1 + π/(ν + σ))    sin²θ₁₃ = (σ − χ)/α⁻¹
    δ_CP = arctan(σ/χ)

`CKM`, `FlavourPulls` and `PMNS` previously spelled these with the **evaluated
numerals** — `Real.pi / 14`, `2 * αinv + Real.pi`, `Real.pi + 2`, `21`, `3`,
`5/2` — with no Lean statement tying `14` to `ν − χ` and so on. The invariants
themselves are not assumptions: `parameters_forced` derives
`D = 4`, `Δ = 43`, `ν = 16`, `σ = 5`, `χ = 2` from the substrate, clock, sector,
signature and boundary postulates. But that derivation was never cited at the use
site, so the flavour numbers were plugged in twice over: once honestly in Paper I,
once silently here.

This module closes that gap. `χ`, `σ`, `ν`, `D` name the derived
`PMArch.Parameters` fields of `baseline`, and each formula is restated in terms of
them. The bridge theorems below then prove the invariant form **equals** the
literal form already used downstream, so nothing else has to change and the
numerals become conclusions rather than inputs:

* `s12_eq`, `s13_eq`, `vcb_eq_`, `delta_eq_` — CKM side
* `solar_eq`, `atmos_eq`, `reactor_eq` — PMNS side, i.e. `PMNS.sineSquared`

## What this does NOT fix

Three inputs remain genuinely underived, and stating them as open is the point of
this file:

* **φ.** `FlavourPulls.φ = (1 + √5)/2` occurs nowhere else in Papers I–III; no
  theorem derives the golden ratio from the lattice. The solar angle is therefore
  still a postulated form, and `solar_eq` only relabels it.
* **q² = 687/688.** `CKMDressing.q2` is the dressing that turns the geometrically
  exact first-row sum `1` into `1 − 1/688`, i.e. the entire claimed resolution of
  the Cabibbo Angle Anomaly (`first_row_deficit_test` shows the undressed value is
  2.28σ from the measured deficit, the dressed one 0.22σ). It is a literal, so the
  anomaly is fitted rather than derived.
* **The octant.** Paper IV §IV claims the geometric running "resolves the apparent
  octant anomaly"; there is no Lean statement of that claim at all.
-/

noncomputable section
namespace PMDynamics.FlavourInvariants
open PMArch

/-! ## The invariants, named from Paper I -/

/-- Spacetime dimension `D`. Derived: `parameters_forced`. -/
def D : ℕ := baseline.dimension
/-- Chiral channel count `ν`. Derived: `Channels.nu_eq`. -/
def nu : ℕ := baseline.sectorChannels
/-- Interaction symmetry order `σ`. Derived: `parameters_forced`. -/
def sigma : ℕ := baseline.embeddingDimension
/-- Topological boundary invariant `χ`. Derived: `Derived.boundary_sphere`. -/
def chi : ℕ := baseline.eulerCharacteristic

/-- The invariants really are the Paper I values, so these are computations and
not definitions of convenience. -/
theorem D_eq : D = 4 := rfl
theorem nu_eq : nu = 16 := by show baseline.sectorChannels = 16; rfl
theorem sigma_eq : sigma = 5 := by show baseline.embeddingDimension = 5; rfl
theorem chi_eq : chi = 2 := by show baseline.eulerCharacteristic = 2; rfl

/-! ## The formulas, written the paper's way -/

/-- `s₁₂ = π/(ν − χ)`, the Chiral Leak Bound. -/
def s12f : ℝ := Real.pi / (nu - chi)
/-- `s₁₃ = 1/(χ α⁻¹ + π)`, the Non-Adjacent Subspace Transition Penalty. -/
def s13f : ℝ := 1 / (chi * CKM.αinv + Real.pi)
/-- `|V_cb| = (π + χ)/(α⁻¹ − Dπ)`, the Dimensional Promotion Admittance. -/
def vcbf : ℝ := (Real.pi + chi) / (CKM.αinv - D * Real.pi)
/-- `δ_CP = arctan(σ/χ)`. -/
def deltaf : ℝ := Real.arctan (sigma / chi)
/-- `sin²θ₁₂ = 1/(2φ)`. φ is **not** derived — see the header. -/
def solarf : ℝ := 1 / (2 * FlavourPulls.φ)
/-- `sin²θ₂₃ = (1/χ)(1 + π/(ν + σ))`. -/
def atmosf : ℝ := (1 / chi) * (1 + Real.pi / (nu + sigma))
/-- `sin²θ₁₃ = (σ − χ)/α⁻¹`. -/
def reactorf : ℝ := (sigma - chi) / CKM.αinv

/-! ## Bridges: the numerals downstream are these formulas evaluated -/

theorem s12_eq : s12f = CKM.s12 := by
  unfold s12f CKM.s12; rw [nu_eq, chi_eq]; norm_num
theorem s13_eq : s13f = CKM.s13 := by
  unfold s13f CKM.s13; rw [chi_eq]; norm_num
theorem vcb_eq_ : vcbf = CKM.vcb := by
  unfold vcbf CKM.vcb; rw [chi_eq, D_eq]; norm_num
theorem delta_eq_ : deltaf = CKM.δ := by
  unfold deltaf CKM.δ; rw [sigma_eq, chi_eq]; norm_num

theorem solar_eq : solarf = PMNS.sineSquared 0 := rfl
theorem sineSq_1 : PMNS.sineSquared 1 = (1 + Real.pi / 21) / 2 := rfl
theorem sineSq_2 : PMNS.sineSquared 2 = 3 / CKM.αinv := rfl
theorem sineSq_0 : PMNS.sineSquared 0 = 1 / (2 * FlavourPulls.φ) := rfl

theorem atmos_eq : atmosf = PMNS.sineSquared 1 := by
  rw [sineSq_1]
  unfold atmosf
  rw [nu_eq, sigma_eq, chi_eq]
  show (1 / (2 : ℝ)) * (1 + Real.pi / (16 + 5)) = (1 + Real.pi / 21) / 2
  rw [show (16 : ℝ) + 5 = 21 by norm_num]
  ring
theorem reactor_eq : reactorf = PMNS.sineSquared 2 := by
  rw [sineSq_2]
  unfold reactorf
  rw [sigma_eq, chi_eq]
  norm_num

/-- The three chiral-capacity denominators are pure invariant arithmetic, so the
`14` and `21` used downstream are computed, not assumed. -/
@[simp] theorem nu_R : (nu : ℝ) = 16 := by rw [nu_eq]; norm_num
@[simp] theorem sigma_R : (sigma : ℝ) = 5 := by rw [sigma_eq]; norm_num
@[simp] theorem chi_R : (chi : ℝ) = 2 := by rw [chi_eq]; norm_num
@[simp] theorem D_R : (D : ℝ) = 4 := by rw [D_eq]; norm_num

theorem nu_minus_chi_eq : (nu : ℝ) - chi = 14 := by norm_num
theorem nu_plus_sigma_eq : (nu : ℝ) + sigma = 21 := by norm_num
theorem sigma_minus_chi_eq : (sigma : ℝ) - chi = 3 := by norm_num

/-- No CKM or PMNS measurement enters any of the six formulas: they are built
from `π`, `α⁻¹`, `φ` and the invariants above. -/
theorem no_measurement_input :
    s12f = Real.pi / (nu - chi) ∧ s13f = 1 / (chi * CKM.αinv + Real.pi) ∧
      vcbf = (Real.pi + chi) / (CKM.αinv - D * Real.pi) ∧
        solarf = 1 / (2 * FlavourPulls.φ) ∧
          atmosf = (1 / chi) * (1 + Real.pi / (nu + sigma)) ∧
            reactorf = (sigma - chi) / CKM.αinv :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end PMDynamics.FlavourInvariants
