# PM-4-Dynamics: flavour matrices, wall spectra and propagation

Lean 4.34.1; pinned sibling dependencies and the existing local mathlib cache.
Run `./check.sh`, or set `PM_LAKE_BIN` to the pinned Lake executable. Paper IV
uses Papers I–III and rejects imports from Papers V–VI.

The conditional matrix/spectrum/propagation results below are checked. The
physical generation/update law and selection of the mixing and mass formulas
remain open; those are not supplied by silently adding hypotheses to a theorem.

## Matrices, currents and mass constructions

| Modules | Checked mathematics | Supplied application inputs |
| --- | --- | --- |
| `CKM`, `CKMDressing`, `CKMClosure`, `Mixing` | Complete complex CKM matrix, both unitary Gram identities, det=1 in the chosen convention, Jarlskog quartet, dressing deficit and minimum dilation dimension | Angles/phase, complete accessible bases, any uniform dressing and physical extra outcomes |
| `PMNS`, `PMNSIntervals` | Complete proposed matrix, unitarity, determinant, CP sign, all nine squared-entry intervals and a numerical quartet enclosure | Proposed angle formulas; phase from the persistence sum rule formulas; no selected neutrino masses |
| `FlavourCurrent` | Generation-universal current lifted to a supplied flavour space; charged block Uu†Ud and neutral-current basis identities; upstream vertex normalization retained | Generation space, physical mass bases and universal-current identification |
| `MassMixing` | Hermitian positive mass constructions, diagonalization, wall-parity covariance and positive mass determinants; every unitary mixing remains compatible with fixed positive spectra | Actual link/mass law, spectrum and theta; positivity does not select angles |
| `SymmetricMass` | Symmetric U diag(m) Uᵀ and Hermitian U diag(m) U† constructions can share the same squared propagation matrix | Allowed physical mass terms, statistics and other observables are not selected |

## Exact two-wall spectrum and its flavour reduction

The newly integrated Paper II `WallDispersion` result supplies the exact
one-flavour Hamiltonian spectrum, not merely a resemblance to a Dirac formula.
`WallSpectrumLink` identifies its branch energies with the relativistic energy
law and proves the light/heavy seesaw relation.

- `FlavourWallReduction` gives the complete unitary change of basis for the
  actual `WallExchange.H` operator. Every Hermitian link is diagonalized using
  the upstream spectral theorem. `hermitian_energy_iff` proves that an energy
  occurs in the full model **iff** it occurs in one scalar-link flavour block.
  `hermitian_light_state` realizes each allowed light-branch energy in the full
  state space. The flavour dimension is arbitrary; this does not derive three
  physical generations or select a link.
- `WallLatticeSpectrum.concrete_hamiltonian` proves that replacing momentum by
  sin(k) gives the actual concrete two-wall Hamiltonian at link y=1. The branch
  theorem and the controlled half-phase estimate then apply to that lattice
  model. The exact lattice expression uses sin(p), with its domain stated.
- `WallRanks.branch_ranks` turns idempotent trace-two certificates into actual
  rank-two statements for both energy signs on both regular branches. These are
  complex linear mode counts, not a particle-statistics theorem.

The four-projector branch statements require nonzero link and positive light
energy, as in the upstream theorem. They do not identify the Hamiltonian
exponential with an arbitrary finite-tick update. Mathematical diagonalization
and state existence do not choose the physically accessible branch or preparation.

## Observables and controlled phases

`UnitarityTriangle`, `TriangleAngles` and `TriangleGamma` derive area=|J|/2,
sin(2 beta), and the actual rephasing-invariant gamma from the matrix. For the
supplied CKM ansatz, **68.16° < gamma < 68.17°**, strictly below delta; the
certified difference is 0.028–0.041°. The fixed gamma benchmark gives a residual
of 1.27–1.28 quoted errors. The old delta comparison is retained as a proxy test,
not identified with gamma. `JarlskogReview` preserves the mismatch with the older
standalone geometric J formula; no value is selected by closeness to data.

`FlavourEvolution`, `OscillationAlgebra`, `OscillationObservables`, `CPAsymmetry`
and `CPObservables` prove exact finite unitary propagation, normalized transition
probabilities, expanded cosine/sine and squared-sine formulas, the fully factored
three-flavour conjugation asymmetry, rephasing/common-energy-shift cancellation,
and absence of vacuum asymmetry for a degenerate energy pair. The PMNS example
uses a supplied test spectrum/time and is not a mass prediction. Energies,
preparation, time/baseline and the conjugate-mixing vacuum prescription remain
inputs; matter effects are not claimed.

`RelativisticPhase` proves the exact gap (m_i²-m_j²)/(E_i+E_j) and

    |t*(E_i-E_j)/2 - t*(m_i²-m_j²)/(4p)|
      ≤ |t|*(m_i⁴+m_j⁴)/(16p³),  p>0.

`PropagationEnergy` consumes Paper II's first-order Clifford eigenstate theorem,
including positive-state existence, and connects the supplied eigenstates to
these phases. The new wall modules separately close the exact eight-component
Hamiltonian identification. Neither result selects physical neutrino masses or
calibrates a baseline.

`OscillationStability` now proves a separate probability-error bound from the
phase errors, independently of earlier papers. `PropagationStability` applies it
to any unitary mixing matrix, including the exact wall light-branch energies:

    |P_exact - P_mass_squared| ≤ |t|*B/(4p³),  p>0, m_i⁴ ≤ B.

The common momentum phase is removed exactly. The bound is valid at every real
time; it is useful when its right-hand side is small. The corresponding vacuum
conjugation-asymmetry error is at most |t|*B/(2p³). The wall specialization uses
the derived light mass-squared function; it does not select the link eigenvalues
or replace exponential propagation with an arbitrary microscopic update.

## Certified PMNS entries

`PMNSIntervals.squared_entry_bounds` encloses |U_ij|² without using measured
entries. Row/column labels here follow the supplied matrix convention.

| Row | Column 0 | Column 1 | Column 2 |
| --- | --- | --- | --- |
| 0 | (0.6758, 0.6759) | (0.3022, 0.3023) | (0.0218, 0.0219) |
| 1 | (0.0888, 0.0890) | (0.3488, 0.3490) | (0.5622, 0.5623) |
| 2 | (0.2352, 0.2353) | (0.3488, 0.3490) | (0.4158, 0.4160) |

`jarlskog_bounds` gives **-0.0217 < J_PMNS < -0.0215**. The phase is no longer
the golden angle: it is fixed by the persistence sum rule `|U_μ2| = |U_τ2|`
(`ReferenceFlavour`, `PMNS.cosDelta`, `sin δ < 0` branch, `δ ≈ 220.8°`). The
cross term is then exactly `(c₁₂² − s₁₂² s₁₃²)(1 − 2 s₂₃²)/2`
(`PMNSIntervals.crossTerm_exact`), and `ReferenceFlavour.paper_on_rule` proves
the matrix satisfies the rule exactly. These are certified consequences of the
angle ansatz plus the rule, not an optimization or experimental fit.
`FlavourPulls` and `CPPhases` retain the earlier fixed dated benchmark comparisons.
No new measurements or global statistical interpretation were introduced.

## Completion boundary

See [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md). The remaining central work is a
physical generation/update contract and a selection law for the link, mixing
bases, angle/phase formulas and masses. Paper II's new weak-vertex and continuum
proofs supply operator mathematics but do not select flavour eigenbases.

In particular, the existing arbitrary-mixing theorem permits every unitary
matrix with the same positive masses and wall-parity property. The compatible
symmetric/Hermitian construction also shows why propagation alone cannot prove
a Dirac-only law. Unique-optimum, exhaustive-archetype and Majorana-exclusion
claims in the manuscript are not established by these conditional results.

## Verification

`check.sh` builds the default library, strictly audits transitive axioms against
only `propext`, `Classical.choice`, `Quot.sound`, and checks the no-Papers-V–VI
boundary. `AuditIndependent.lean` separately checks five generic modules for no
earlier/later theory imports: `OscillationAlgebra`, `SymmetricMass`,
`CPAsymmetry`, `RelativisticPhase` and `OscillationStability`.

On 2026-10-30, the integrated `check.sh` passed **4154 build jobs** and the
strict audit of **436 PMDynamics declarations**, with no warnings. Both the
no-Papers-V–VI dependency audit and the five-module independent-algebra audit
passed. Log: `/tmp/pm4-stability-full-check.log`. This includes the new phase,
transition-probability and vacuum-asymmetry stability bounds. Only Paper IV's
`lean/` sources/documentation changed in this pass; no earlier source,
calculator or manuscript was edited.
