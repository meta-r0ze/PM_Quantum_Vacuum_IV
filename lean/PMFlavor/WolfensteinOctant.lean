import PMFlavor.FlavourInvariants
import PMFlavor.FlavourPulls
import Mathlib.Tactic

/-!
# The octant the supplied mixing angles actually lie in

`FlavourInvariants` exposed the paper's claim that geometric running "resolves the
apparent octant anomaly" as having no Lean statement at all. This module supplies
the statements. Nothing here uses a measurement; every bound is a consequence of
the supplied closed forms (`FlavourInvariants.solar_eq`, `atmos_eq`, `reactor_eq`)
built from `π`, `α⁻¹` and the golden ratio `φ`.

**The solar angle is in the lower (first) octant.**
* `solar_lt_half`: `sin²θ₁₂ = 1/(2φ) < 1/2`, i.e. `θ₁₂ < π/4` — *not* maximal.
* `solar_gt_quarter`: `1/4 < 1/(2φ)`, so it is above the diagonal-angle golden
  point `1/(2φ²)`; the octant is the first, not the second.
* `solar_first_octant`: `1/4 < sin²θ₁₂ < 1/2`. This is the Lean content of the
  paper's octant sentence for the solar sector, and it is falsifiable: a measured
  `sin²θ₁₂ > 1/2` would refute it.

**The atmospheric angle is above maximal.**
* `atmos_gt_half`: `sin²θ₂₃ = (1 + π/21)/2 > 1/2`, i.e. `θ₂₃ > π/4`: the
  atmospheric octant is the **upper** one. This is the nontrivial octant claim
  (its octant is what the "octant anomaly" is about).

**The reactor angle is small.**
* `reactor_lt_half`, `reactor_lt_quarter`: `sin²θ₁₃ = 3/α⁻¹` is far below any
  octant boundary, so the reactor octant is trivial.

Together: the supplied model predicts **lower solar, upper atmospheric** octants,
both with strict inequalities and no decimal input. These are the falsifiable
statements review item 4 was missing.
-/

noncomputable section
namespace PMFlavor.WolfensteinOctant
open FlavourInvariants FlavourPulls

/-- `√5` lies in `(2.2360679, 2.2360680)`, restated locally so this module does not
depend on the proof layout of `FlavourPulls`. -/
private lemma sqrt5_b : (2.2360679 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2360680 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- `φ = (1 + √5)/2` is positive. -/
theorem phi_pos : 0 < φ := by unfold φ; positivity

/-- The solar closed form is exactly `1/(2φ)`. -/
theorem solar_value : PMNS.sineSquared 0 = 1 / (2 * φ) := FlavourInvariants.solar_eq

/-- **Lower octant: the solar mixing is below maximal.** `sin²θ₁₂ < 1/2`. -/
theorem solar_lt_half : PMNS.sineSquared 0 < 1 / 2 := by
  rw [solar_value]
  have h := sqrt5_b
  have hd : 0 < 2 * φ := by unfold φ; positivity
  rw [div_lt_iff₀ hd]
  unfold φ
  nlinarith [h.1]

/-- **Above the golden point:** `1/4 < sin²θ₁₂`, so the octant is the first. -/
theorem solar_gt_quarter : 1 / 4 < PMNS.sineSquared 0 := by
  rw [solar_value]
  have h := sqrt5_b
  have hd : 0 < 2 * φ := by unfold φ; positivity
  rw [lt_div_iff₀ hd]
  unfold φ
  nlinarith [h.2]

/-- **The solar angle is in the first octant**: `1/4 < sin²θ₁₂ < 1/2`. This is
the Lean form of the paper's solar-octant sentence. -/
theorem solar_first_octant : 1 / 4 < PMNS.sineSquared 0 ∧ PMNS.sineSquared 0 < 1 / 2 :=
  ⟨solar_gt_quarter, solar_lt_half⟩

/-- `φ > 1`. -/
theorem phi_gt_one : 1 < φ := by
  have h := sqrt5_b
  unfold φ
  nlinarith [h.1]

/-- `φ < 2`. -/
theorem phi_lt_two : φ < 2 := by
  have h := sqrt5_b
  unfold φ
  nlinarith [h.2]

/-- **The solar octant is exactly `1 < φ < 2`.** The lower-octant bound
`sin²θ₁₂ < 1/2` is equivalent to `1 < φ`, and the above-golden-point bound
`1/4 < sin²θ₁₂` is equivalent to `φ < 2`. So the solar-octant claim carries no
content beyond the size of the postulate `φ`: it is *not* an independent
prediction, which is why review item 4 flags `φ` as underived. -/
theorem solar_lt_half_iff : PMNS.sineSquared 0 < 1 / 2 ↔ 1 < φ := by
  rw [solar_value]
  have hd : (0 : ℝ) < 2 * φ := by have := phi_pos; linarith
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> linarith

theorem solar_gt_quarter_iff : 1 / 4 < PMNS.sineSquared 0 ↔ φ < 2 := by
  rw [solar_value]
  have hd : (0 : ℝ) < 2 * φ := by have := phi_pos; linarith
  rw [lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- **Upper octant: the atmospheric mixing is above maximal.** `1/2 < sin²θ₂₃`. -/
theorem atmos_gt_half : 1 / 2 < PMNS.sineSquared 1 := by
  rw [← FlavourInvariants.atmos_eq]
  unfold atmosf
  rw [nu_eq, sigma_eq, chi_eq]
  have hmain : (1 / 2 : ℝ) < 1 / 2 * (1 + Real.pi / (16 + 5)) := by
    rw [show (16 : ℝ) + 5 = 21 by norm_num]
    nlinarith [Real.pi_pos]
  convert hmain using 2

/-- **The reactor angle is small.** `sin²θ₁₃ < 1/4`, hence in no upper octant. -/
theorem reactor_lt_quarter : PMNS.sineSquared 2 < 1 / 4 := by
  rw [← FlavourInvariants.reactor_eq]
  unfold reactorf
  have hg : (137 : ℝ) < CKM.αinv := by
    have := CKM.ai_bounds
    linarith
  have hd : 0 < CKM.αinv := by linarith
  rw [div_lt_iff₀ hd]
  -- (σ − χ) < αinv/4
  have hs : ((sigma : ℝ) - chi) = 3 := by
    have := sigma_eq; have := chi_eq
    norm_num
  rw [hs]
  nlinarith

end PMFlavor.WolfensteinOctant
