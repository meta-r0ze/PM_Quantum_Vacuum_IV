# Paper IV: open work (todo)

Checked mathematics and the downstream handoff are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains. Paper IV builds clean (4315 jobs, zero warnings,
1515 strict-audited declarations). Every item below is a physical input no theorem
can supply, a data task, or a genuinely open structural question.

> **Current focus (2026-11-04).** The PM-2 Yang–Mills branch is frozen at its
> classical/finite-volume deliverable (see `PM-2-Action/lean/YANG-MILLS-STATUS.md`).
> The redirected PM-specific work is here: **item 2** (global all-nonzero mixing)
> and **item 5** (per-step maintenance contract) are the two structural targets,
> alongside the native control/admission question in PM-2 `NativePacketUpdate`.

## Open items

### 1. Numerical link weights (physics, not a proof)
`BreakingLink.brokenLink δ` and `brokenLinkB ε` are structural: the doublet splits
for any `δ ≠ 0`, the `Z₂` obstruction is removed for any `ε ≠ 0`. The **values** of
`δ, ε` are dynamical wall couplings and cannot be derived from the persistence
axioms. Do not fit them by hand (that is numerology); a substrate determination is
the only valid route.

### 2. Full all-nonzero mixing (structural, partially open)
`MixingMatrix.all_nonzero_mixing_interval` proves every entry of the mixing overlap
is nonzero on the **whole square `0 < δ, ε ≤ 4`** (via `rootP > 4`, `1 < rootM`,
`rootM < 5/2`), and `all_nonzero_mixing_witness` gives the `δ = ε = 2` point. The
global statement is false: `MixingMatrix.ip_M_M_vanishes_at` proves the term
`rootM+rootM−5` vanishes at `δ = ε = 9/2` (`rootM 9/2 = 5/2`). Remaining: a global exceptional-set argument (zeros are
measure-zero) or a proof that the physical `(δ, ε)` never leaves the nonzero
region once item 1 is fixed.

### 3. Derive φ (open, no known route)
`FlavourPulls.φ = (1+√5)/2` is a postulate; the solar angle `1/(2φ)` and its octant
(`WolfensteinOctant.solar_lt_half_iff`) reduce to `1 < φ < 2`. Either derive the
golden ratio from the substrate, or state explicitly that the solar sector is a
one-parameter postulate. No Lean path from E8/clock data to φ is known.

### 4. Physical preparation and the energy-spread bound (physics)
`ChordBranch` reduces the branch condition to `t ≤ tStar` and to the *energy*
spread `≤ π/43`; `MixingMatrix.spread_exceeds_pi_over_43` shows link eigenvalues are
the wrong scale. Remaining: a concrete preparation protocol (not just
`LightFlavourPreparation`'s existence theorem) and a proof that the physical energy
spread is within `π/43`, which needs the momentum/detuning of the physical state.

### 5. Per-step maintenance contract (structural, hard)
`LeptonAxisRestriction` proves the per-cycle (three-step) contract. A per-step
(one-step) contract needs exact within-step state restoration; the gap is documented
there. This is the hardest remaining structural proof.

### 6. Carrier-current identification (cross-paper, partly done)
`WeakCurrentBridge` proves the native current's chiral projector **is** Paper II's
weak V−A projector: `spinProjector_eq_PL` (`spinProjector = WeakVertex.PL`), with
`spinProjector_idempotent` / `_hermitian` / `_trace` transported from PM-2, plus
`vertex_eq_native` and `modelCurrent_eq_PL`. So the chirality is not a free choice.
Remaining (physical inputs): the flavour generator `G`, the carrier charge values,
and the mediator/statistics. Paper II gained the su(2) doublet algebra
(`ChargedCurrent.T3`, `commutator_T1_T2`, `commutator_T3_Tp/Tm`, `commutator_Tp_Tm`,
`anticommutator_Tp_Tm`) and `WeakVertex.PL_*` for selection-rule use.

### 7. Data module (data work, outside the axiom-checked tree)
`FalsifiablePredictions.prediction_ledger` is the auditable input. A separate module
must record measurements with provenance, uncertainties and covariance and evaluate
residuals against the ledger. Do not put measured numbers into the theorem tree.

## Suggested order

1. **Item 2** — extend the `0 < δ, ε ≤ 4` result to a global exceptional-set
   statement (zeros are measure-zero), or tie the physical range to item 1.
2. **Item 5** — deepest structural proof; needs exact within-step restoration.
3. **Item 4** — concrete preparation protocol and the physical `π/43` bound.
4. **Item 6** — chirality is now tied to `PM-2`; the remaining part is the
   physical generator/charge/mediator input.
5. **Item 3** — no derivation route exists; keep the solar sector a postulate until
   one is found.
6. **Items 1 & 7** — physical/data tasks, done last and kept out of the tree.

## Verification

**4315** build jobs, **zero** errors, **zero** warnings
**1515** strict-audited PMFlavor declarations
No Paper V–VI imports, six-module independent-algebra audit passes.
Permitted transitive axioms: only `propext`, `Classical.choice`, `Quot.sound`.

Full check log: `check.sh`.
