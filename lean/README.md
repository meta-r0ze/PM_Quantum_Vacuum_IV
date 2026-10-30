# PM-4-Dynamics: initial mixing checks

Lean 4.34.1, pinned mathlib dependencies inherited from the sibling PM-1-Arch/lean
package. Run `./check.sh` with elan available. The local cache is reused through
ignored `.lake/` links; no new installation was needed.

`PMDynamics/Mixing.lean` checks a standard first-row normalization identity,
uniform amplitude dressing, the scaling of a Jarlskog quartet, and the fact that
moduli do not determine complex phases. This is an initial set of exact checks,
not a complete formalization of the proposed CKM/PMNS geometry or full matrix
unitarity.

The calculation code multiplies all CKM amplitudes by sqrt(1-1/688). A normalized
row then has squared norm 687/688, rather than one. The corresponding quartet
scales by the fourth power of the dressing amplitude. A visible-channel loss
interpretation can reserve probability 1/688 for an extra outcome, but requires
an explicit open-system model. It cannot simultaneously be treated as an
exactly unitary closed three-channel matrix. The raw standard parameterization
and the dressed matrix must be distinguished.

Remaining work: a full complex matrix construction with row/column unitarity,
a consistent interpretation of dressing and CP invariants, and a microscopic
argument selecting the mixing angles and phase. Numerical agreement alone
does not establish that selection.

Verification: build and strict transitive axiom audit passed on 2026-10-27,
covering 14 project declarations. The audit accepts only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

## The CKM matrix: unitarity, determinant and Jarlskog invariant

`PMDynamics/CKM.lean` builds the full complex standard-parametrization matrix and proves:

- `ckm_unitary`: for `cᵢⱼ² + sᵢⱼ² = 1` and a unit phase, `Σₖ VᵢₖV̄ⱼₖ = δᵢⱼ` for all nine
  row pairs. Exact unitarity holds for any angles, so it selects none of them.
- `ckm_det`: `det V = 1`. The mixing is complex while its determinant is real, which is
  the split that Paper III's `CPPhases` needs: CP violation in mixing without feeding the
  strong-CP combination `arg det`.
- `jarlskog_ckm`: `Im(V_ud V_cs V̄_us V̄_cd) = c₁₂s₁₂c₂₃s₂₃c₁₃²s₁₃ Im u`.

With the paper's values (`s₁₂ = π/(ν−χ)`, `|V_cb| = (π+χ)/(α⁻¹ − Dπ)`, `s₂₃ = |V_cb|/c₁₃`,
`s₁₃ = 1/(χα⁻¹ + π)`, `δ = arctan(σ/χ)`, certified `α⁻¹` from Paper I),
`pm_jarlskog_matrix` shows the matrix gives exactly `pmJ`, and `pmJ_bounds` puts it in
`(3.02, 3.03)×10⁻⁵`, matching the calculator's undressed `3.02287×10⁻⁵`.

Paper III's separate formula `J = φ² T_geo η` (from PM-1's calculator, `N = 32`,
`R_M = 172`) lies in `(3.0848, 3.0850)×10⁻⁵` (`pm3J_bounds`). `papers_disagree`:
`1.016 · pmJ < pm3J`. Both sit inside the comparison value `(3.06 ± 0.20)×10⁻⁵`, but
once the angles and phase are fixed, J is determined by the matrix. The second formula
is therefore either redundant or wrong by about 2%.

## What the 1/688 dressing predicts, and what it needs

`PMDynamics/CKMDressing.lean`:

- `ckm_unitary_matrix`, `ckm_unitary_cols`: `VV† = V†V = 1` as matrix identities.
- `dressed_gram`, `dressed_gram_cols`, `first_row_sum`: the dressed matrix `A = qV`,
  `q² = 687/688`, has every row and every column summing to `687/688`.
- `first_row_deficit_test`: the measured first-row sum `0.9984 ± 0.0007` (CKM 2023
  workshop) is 0.21σ from the dressed prediction and more than 2.28σ from exact unitarity.
  The dressing amounts to a prediction of the Cabibbo-angle anomaly.
- `dilation_needs_three`: if `AA† = c·1` with `c ≠ 1` and `A` is the 3×3 block of any unitary
  of size `3 + m`, then `m ≥ 3`. The lost `1/688` cannot go to one extra outcome: Conservation
  needs at least three further output channels (and, from `A†A`, three on the input side).
  `missing_outcome_restores_total` balances the scalar total only.
- `arg_dressing_invariant`: phases and unitarity-triangle angles are unchanged.
  `jarlskog_dressed`: J becomes `(3.011, 3.022)×10⁻⁵`; `papers_disagree_dressed`: Paper III's
  `φ²T_geo η` then exceeds it by more than 2%.

## What persists decides: the observable matrix is exactly unitary

`PMDynamics/CKMClosure.lean`: `basis_change_unitary` (the CKM matrix `U_uᴴU_d` is a change
between two complete orthonormal bases of the three-generation space, so it is unitary under
Closure); `closure_excludes_dressing` (no such basis change equals the dressed `qV`); and
`global_dressing_cancels` (a factor on every propagating state also multiplies the muon-decay
normalization and cancels in each measured `|V_ij|² = Γ_q/Γ_μ`). The calculator now compares
the undressed matrix, against PDG 2024 direct determinations rather than the unitarity-imposed
global fit. The first-row deficit becomes a 2.3σ tension the theory predicts will close;
undressed `|V_ud|` is 2.6σ above the direct value.

## Mixing formulas against data, and the shared weak mixing

`PMDynamics/FlavourPulls.lean` (requires `pm_nested`), with Paper I's derived `α⁻¹`:

- CKM (PDG 2024): `|V_us| = s₁₂c₁₃` within 0.2σ (`vus_pull`); `|V_cb|` within 0.2σ (`vcb_pull`);
  `|V_ub| = s₁₃` is 1.0–1.1σ low (`vub_pull`).
- PMNS (NuFIT 6.0): `sin²θ₁₂ = 1/(2φ)` within 0.5σ (`solar_pull`), `sin²θ₂₃ = (1 + π/21)/2` within
  0.1σ (`atmos_pull`), `sin²θ₁₃ = 3/α⁻¹` within 0.7σ (`reactor_pull`).
- `weak_mixing_shared`: Paper IV's impedance-matching `sin²θ_W` with `sin θ_C = π/14` is exactly Paper
  III's `Δ/N_sys = 1849/8295`.

The two papers' Jarlskog formulas still differ by about 1.6% (`papers_disagree`); since `J` is fixed
by the angles and phase, Paper IV's matrix value is the consistent one unless Paper III's formula
is shown to be the same quantity.

## Jarlskog review

- `UnitarityTriangle`: for any matrix with two orthogonal rows the three products close a triangle,
  its cross products are equal, and its area is `|J|/2` (`area_is_half_J`, `ckm_triangle_area`). The
  `2` in `J = 2A` is a theorem of unitarity, not of the substrate (`N/ν = 2` is a coincidence).
- `JarlskogReview`: Paper III's `φ²ηT_geo` and this paper's matrix `J` differ, `pmJ/pm3J ∈ (0.9789,
  0.9823)` (`ratio_window`), and dropping `η` makes it worse (`eta_not_the_fix`). Since angles and
  phase fix `J`, the matrix value is `J`; Paper III now cites it.

## CP phases (`CPPhases`)

Alternating-series bounds on `arctan` from monotone derivatives (`arctan_lower`, `arctan_upper`)
certify `δ = arctan(5/2) ∈ (1.190284, 1.190317)` rad, `68.198°–68.201°` (`δ_degrees`). Against
LHCb's 2024 combination `γ = (64.6 ± 2.8)°` the pull is `+1.28` to `+1.29σ`; against the paper's
cited `(68 ± 5)°` it is under `0.05σ` (`δ_vs_gamma`). The leptonic phase `360°/φ = 180°(√5−1)` is
`222.492°–222.493°`, `+0.94σ` from NuFIT 6.0 `(197 ± 27)°` (`nu_phase`).

## Unitarity-triangle angle (`TriangleAngles`)

`w = −V_cd·conj V_td` has real part `s₁₂²s₂₃c₂₃ − c₁₂²c₂₃s₂₃s₁₃² + c₁₂s₁₂s₁₃ cos δ (s₂₃² − c₂₃²)` and
imaginary part `c₁₂s₁₂s₁₃ sin δ` (`w_parts`); `β = arg w`, `sin 2β = 2 Re w Im w/|w|²`
(`sin_two_beta`, `sin2β_is_angle`). For the geometric matrix, `0.7019 < sin 2β < 0.7023`
(`sin2β_bounds`), `−0.75` to `−0.69σ` from PDG's `0.710 ± 0.011` (`sin2β_pull`). The paper cites
`0.699 ± 0.017`.
