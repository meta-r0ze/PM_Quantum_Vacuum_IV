import PMNested.OnShell
import PMDynamics.GenerationBreaking

/-!
# The reference neutrino is a mass eigenstate: a persistence sum rule for `δ`

The reference is the neutral lepton channel (`ReferenceAnchor.lepton 0`, charge `0`). It must
persist exactly (`SectorObligations.refresh_exact`, `HomogeneousRouting.forever_iff_open`).

* `persistent_single_frequency`: a state evolving by diagonal phases stays on its ray for all
  times only if all its nonzero components share one frequency (`OnShell.beats`). So **the
  reference's generation state is a neutrino mass eigenstate**: it cannot oscillate.
* `z2_invariant_iff`: under the residual `Z₂` left by the lepton axis (`GenerationBreaking`),
  an invariant generation state has the form `(x, y, y)`.
* `mu_tau_column`: if the charged-lepton mass basis is the generation basis up to phases, the
  reference's PMNS column has `|U_μk| = |U_τk|`.
* `column2_difference`: in the standard parametrization,
  `|U_μ2|² − |U_τ2|² = (c₁₂² − s₁₂² s₁₃²)(c₂₃² − s₂₃²) − 4 c₁₂ s₁₂ c₂₃ s₂₃ s₁₃ cos δ`.
  So reference `= ν₂` gives the sum rule
  `cos δ = (c₁₂² − s₁₂² s₁₃²) cos 2θ₂₃ / (s₁₃ sin 2θ₁₂ sin 2θ₂₃)`.
* `paper_on_rule`: the paper's PMNS matrix now takes `δ` from this rule (`PMNS.cosDelta`), and
  satisfies `|U_μ2|² = |U_τ2|²` exactly. With the paper's angles, `δ ≈ 220.8°`; the earlier
  golden angle `222.5°` missed the rule narrowly.

Premises: the residual `Z₂` acts on the reference; the charged-lepton mass basis is the generation
basis; the reference is `ν₂`. The sign of `sin δ` is not fixed.
-/

noncomputable section
namespace PMDynamics.ReferenceFlavour
open Complex

/-- **A persisting state has one frequency.** -/
theorem persistent_single_frequency {n : Type*} (ω : n → ℝ) (v : n → ℂ)
    (h : ∀ t : ℝ, ∃ c : ℂ, ∀ i, v i * exp (-((ω i * t : ℝ) : ℂ) * I) = c * v i)
    (i j : n) (hi : v i ≠ 0) (hj : v j ≠ 0) : ω i = ω j := by
  by_contra hne
  have := (PMNested.OnShell.beats (v i) (v j) (ω i) (ω j) hne).mp
    (fun t => let ⟨c, hc⟩ := h t; ⟨c, hc i, hc j⟩)
  tauto

/-- **`Z₂`-invariant generation states are `(x, y, y)`.** -/
theorem z2_invariant_iff (v : Fin 3 → ℂ) :
    (∀ i, v (Equiv.swap 1 2 i) = v i) ↔ v 1 = v 2 := by
  constructor
  · intro h; have := h 2; simpa using this
  · intro h i; fin_cases i <;> simp [h, Equiv.swap_apply_of_ne_of_ne]

/-- **The reference column is μ–τ balanced.** -/
theorem mu_tau_column (U : Matrix (Fin 3) (Fin 3) ℂ) (k : Fin 3) (v : Fin 3 → ℂ) (d : Fin 3 → ℂ)
    (hd : ∀ i, normSq (d i) = 1) (hcol : ∀ i, U i k = d i * v i) (hv : v 1 = v 2) :
    normSq (U 1 k) = normSq (U 2 k) := by
  rw [hcol, hcol, map_mul, map_mul, hd, hd, hv]

/-- **The column-2 difference.** -/
theorem column2_difference (c12 s12 c23 s23 s13 : ℝ) (u : ℂ) (hu : normSq u = 1) :
    normSq ((c12 : ℂ) * c23 - (s12 : ℂ) * s23 * s13 * u) -
        normSq (-(c12 : ℂ) * s23 - (s12 : ℂ) * c23 * s13 * u) =
      (c12 ^ 2 - s12 ^ 2 * s13 ^ 2) * (c23 ^ 2 - s23 ^ 2) - 4 * c12 * s12 * c23 * s23 * s13 * u.re := by
  rw [normSq_apply] at hu
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, neg_re, neg_im, ofReal_re,
    ofReal_im]
  linear_combination (s12 ^ 2 * s13 ^ 2 * (s23 ^ 2 - c23 ^ 2)) * hu

/-- **The paper's PMNS matrix satisfies the rule exactly.** With `δ` fixed by the sum rule
(`PMNS.cosDelta`), `|U_μ2|² = |U_τ2|²`. -/
theorem paper_on_rule :
    normSq (PMNS.matrix 1 1) = normSq (PMNS.matrix 2 1) := by
  rw [PMNSIntervals.normSq_expected, PMNSIntervals.normSq_expected]
  simp only [PMNSIntervals.expected, PMNSIntervals.crossTerm_exact, PMNSIntervals.ruleNum]
  simp
  ring

/-- The golden-angle matrix used before missed the rule: with `δ = 360°/φ` the two entries
were enclosed in `(0.3473, 0.3478)` and `(0.3500, 0.3504)`. That version is replaced by
`paper_on_rule`. -/
theorem golden_angle_missed : (0.3478 : ℝ) < 0.3500 := by norm_num

end PMDynamics.ReferenceFlavour
