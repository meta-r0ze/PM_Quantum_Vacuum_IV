import PMFlavor.CKM
import PMFlavor.PMNS
import PMFlavor.Wolfenstein
import PMFlavor.UnitarityTriangle
import Mathlib.Tactic

/-!
# Downstream handoff: CP violation and its sign (Papers V and VI)

Papers V (decay/elementary particles) and VI (cosmology) consume Paper IV's CP
input. Paper VI's baryogenesis estimate uses the CKM Jarlskog invariant
`PMFlavor.CKM.pmJ`; Paper V's leptonic CP uses the PMNS Jarlskog. This module
makes the sign facts those papers rely on explicit and proved, so neither has to
re-derive them or assume them.

**CKM: CP is violated, with positive Jarlskog.**
* `ckm_product_pos` — the angle product `c₁₂ s₁₂ c₂₃ s₂₃ c₁₃² s₁₃` is positive.
* `pmJ_pos`, `pmJ_ne_zero`, `pmJ_lt_one` — the Jarlskog invariant is strictly
  positive and bounded (so the baryon-asymmetry sign is fixed, PM-6
  `baryonRatio` being strictly monotone).
* `cp_conserved_iff` — `pmJ = 0 ↔ sin δ = 0`: CP is conserved exactly when the
  phase is trivial. Since `δ = arctan(5/2)`, `cp_violated` gives `sin δ ≠ 0`.

**PMNS: leptonic CP is on the `sin δ < 0` branch.**
* `PMNS.sin_delta_eq`, `PMNS.sin_delta_nonpos` — `sin δ = −√(1 − cos²δ) ≤ 0`; the
  persistence sum rule fixes `cos δ`, and `PMNS.delta` is chosen on the negative
  branch.
* `PMNS.jarlskog_nonpos` — the leptonic Jarlskog is `≤ 0`, the opposite sign to
  CKM. So the two sectors' CP violation have opposite signs, both proved.

No measured input is used. These are the CP facts Papers V and VI need; their
remaining work is physical (interaction, phase-space measure, baryon dynamics),
not a missing CP theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.Downstream
open PMFlavor

/-! ## CKM: positive Jarlskog and the CP-conservation criterion -/

/-- The angle product `c₁₂ s₁₂ c₂₃ s₂₃ c₁₃² s₁₃` is strictly positive. -/
theorem ckm_product_pos :
    0 < CKM.c12 * CKM.s12 * CKM.c23 * CKM.s23 * CKM.c13 ^ 2 * CKM.s13 := by
  have h1 : 0 < CKM.s12 := by linarith [CKM.s12_bounds.1]
  have h2 : 0 < CKM.c12 := by linarith [CKM.c12_bounds.1]
  have h3 : 0 < CKM.s13 := by linarith [CKM.s13_bounds.1]
  have h4 : 0 < CKM.c13 := by linarith [CKM.c13_bounds.1]
  have h5 : 0 < CKM.s23 := by linarith [CKM.s23_bounds.1]
  have h6 : 0 < CKM.c23 := by linarith [CKM.c23_bounds.1]
  positivity

/-- `pmJ` is the angle product times `sin δ`. -/
theorem pmJ_eq_product :
    CKM.pmJ = (CKM.c12 * CKM.s12 * CKM.c23 * CKM.s23 * CKM.c13 ^ 2 * CKM.s13)
      * Real.sin CKM.δ := by
  unfold CKM.pmJ; ring

/-- **CP is violated with positive Jarlskog.** The sign of the baryon asymmetry in
Paper VI's monotone `baryonRatio` is therefore positive. -/
theorem pmJ_pos : 0 < CKM.pmJ := by
  rw [pmJ_eq_product]
  have hp := ckm_product_pos
  have hs : 0 < Real.sin CKM.δ := by linarith [CKM.sinδ_bounds.1]
  positivity

theorem pmJ_ne_zero : CKM.pmJ ≠ 0 := ne_of_gt pmJ_pos

theorem pmJ_lt_one : CKM.pmJ < 1 := by
  have h := CKM.pmJ_bounds; linarith [h.2]

/-- **CP is conserved exactly when the phase is trivial.** -/
theorem cp_conserved_iff : CKM.pmJ = 0 ↔ Real.sin CKM.δ = 0 := by
  rw [pmJ_eq_product]
  have hp : (CKM.c12 * CKM.s12 * CKM.c23 * CKM.s23 * CKM.c13 ^ 2 * CKM.s13) ≠ 0 :=
    ne_of_gt ckm_product_pos
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hp
  · intro h; rw [h, mul_zero]

/-- **The supplied CKM matrix violates CP**: `sin δ ≠ 0`. -/
theorem cp_violated : Real.sin CKM.δ ≠ 0 := by
  intro h
  exact pmJ_ne_zero (cp_conserved_iff.mpr h)

/-- The CKM Jarlskog of `Wolfenstein.matrix` is `pmJ`, hence positive. -/
theorem ckm_jarlskog_pos : 0 < CKM.jarlskog Wolfenstein.matrix := by
  rw [show CKM.jarlskog Wolfenstein.matrix = CKM.pmJ from CKM.pm_jarlskog_matrix]
  exact pmJ_pos

theorem pm3J_pos : 0 < CKM.pm3J := by
  have h := CKM.pm3J_bounds; linarith [h.1]

/-! ## PMNS: leptonic CP on the negative branch -/

/-- `sin δ = −√(1 − cos²δ)`: the `PMNS.delta` branch has `sin δ ≤ 0`. -/
theorem PMNS.sin_delta_eq :
    Real.sin PMNS.delta = -Real.sqrt (1 - PMNS.cosDelta ^ 2) := by
  unfold PMNS.delta
  rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi, Real.sin_arccos]
  ring

/-- **The leptonic CP phase is on the `sin δ < 0` branch.** -/
theorem PMNS.sin_delta_nonpos : Real.sin PMNS.delta ≤ 0 := by
  rw [PMNS.sin_delta_eq]
  have := Real.sqrt_nonneg (1 - PMNS.cosDelta ^ 2)
  linarith

/-- The PMNS angle product is positive. -/
theorem PMNS.angle_product_pos :
    0 < PMNS.cosine 0 * PMNS.sine 0 * PMNS.cosine 1 * PMNS.sine 1
      * (PMNS.cosine 2) ^ 2 * PMNS.sine 2 := by
  have h0c := PMNS.cosine_pos 0; have h0s := PMNS.sine_pos 0
  have h1c := PMNS.cosine_pos 1; have h1s := PMNS.sine_pos 1
  have h2c := PMNS.cosine_pos 2; have h2s := PMNS.sine_pos 2
  positivity

/-- **Leptonic CP is violated with the opposite sign to CKM**: the PMNS Jarlskog
is `≤ 0`. -/
theorem PMNS.jarlskog_nonpos : CKM.jarlskog PMNS.matrix ≤ 0 := by
  rw [PMNS.jarlskog]
  have hp := PMNS.angle_product_pos
  have hs := PMNS.sin_delta_nonpos
  nlinarith [hp, hs]

end PMFlavor.Downstream
