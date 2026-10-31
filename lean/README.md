# PM-4-Dynamics: flavour mixing and propagation

Lean 4 proofs for the proposed CKM/PMNS application, using the shared dynamics
and mass-link mathematics in Papers I–III. Toolchain: Lean 4.34.1, with pinned
sibling dependencies and the existing local cache. No installation is needed.

## Main results

The package checks the full complex CKM matrix, both Gram identities, its standard-
convention determinant, the matrix Jarlskog quartet, triangle area/angle identities,
and the given numerical formulas. It also checks the complete proposed PMNS matrix.
Angle and phase formulas are supplied application inputs; neither unitarity nor
these matrix constructions prove that they are uniquely selected by persistence.

The upstream work now supports four additional default modules:

- `FlavourCurrent` lifts Paper II's charged doublet generator to a supplied
  three-generation space. In complete mass bases the charged block is Uu† Ud;
  the reverse vertex is its adjoint. Generation-universal neutral coefficients
  remain flavour diagonal. The existing chiral vertex coefficient is retained.
- `MassMixing` constructs M = U diag(m) U†, proves the prescribed eigenbasis,
  Hermiticity and positivity for positive m, and uses the actual Paper II wall-
  parity criterion. Mass determinants are positive for any unitary U; Paper III's
  strong-CP combination is then θ̄ = θ. With fixed positive mass spectra,
  **every unitary mixing remains possible**. These conditions do not select angles.
- `PMNS` constructs the full matrix from the proposed squared sines
  1/(2φ), (1+π/21)/2, 3/α⁻¹ and phase 2π/φ. It proves the squared sines lie in
  (0,1), exact row/column unitarity, det = 1 in this convention, the stated phase
  conversion, and a negative nonzero Jarlskog quartet. No neutrino masses are selected.
- `FlavourEvolution` uses Paper II's basis-independent exponential to identify
  U diag(exp(−itE)) U† with the Hermitian flavour evolution. It proves unitarity,
  composition, zero-time identity, and total three-channel probability one.
  Column phases cancel in propagation, and the Jarlskog quartet is invariant
  under independent unit phases on rows and columns. Energies, physical time and
  the squared-amplitude probability rule are explicit inputs.

## Independent algebra and completed observables

This pass adds four default modules without new upstream proof obligations:

- `OscillationAlgebra` imports Mathlib only. It proves the complete three-state
  cosine/sine and squared-sine interference formulas, conjugation asymmetry,
  conjugation with phase reversal, common-phase cancellation and degenerate-phase
  behavior. Arbitrary coefficients and the squared-amplitude readout are inputs.
- `OscillationObservables` identifies those amplitudes with the already defined
  finite flavour evolution. It proves the normalized squared-sine formula from
  unitarity, invariance under a common energy offset, absence of conversion for
  degenerate energies, vacuum conjugation/time reversal and survival-channel
  conjugation symmetry. Physical eigenenergies, time/baseline and the vacuum
  conjugation prescription remain inputs; no matter-effect model is asserted.
- `TriangleGamma` extracts gamma from the actual invariant CKM quartet, proves
  invariance under row/column phases, and proves agreement with the standard
  ratio definition on the concrete matrix. The supplied ansatz gives
  **68.16° < gamma < 68.17°**, strictly below delta. The certified difference is
  between 0.028° and 0.041°. The old fixed 64.6 ± 2.8 degree benchmark gives an
  actual-gamma residual between 1.27 and 1.28 quoted errors; this is not a new fit.
- `SymmetricMass` imports Mathlib only. For arbitrary real spectral values and a
  supplied unitary basis U, it constructs U diag(m) Uᵀ and proves transpose
  symmetry, diagonal congruence and the same squared matrix as the Hermitian
  U diag(m) U† construction. This is compatibility of matrix constructions, not
  a derivation of fermion fields, statistics or a physically allowed mass term.
  Propagation depending only on this squared matrix cannot distinguish the two.

`AuditIndependent.lean` separately checks the generic algebra modules for no
earlier/later theory imports. The numerical application still uses the existing
proposed CKM inputs. The additional Paper II spectral bridge is described below.

## CP factorization and spectral phase bridge

The next pass completes two independent algebra steps and connects a new reusable
Paper II spectral theorem:

- `CPAsymmetry` factors the three-state conjugation difference as minus 16 times
  one closed-triangle quartet times the three signed half-phase sines. Nonzero
  quartet and all three nonzero sine factors give nonzero asymmetry; an equal
  phase pair removes it. This module has no earlier-paper imports.
- `CPObservables` supplies closure from unitary row orthogonality and fixes the
  physical sign for theta_i=-t E_i. It identifies the 0/1 appearance quartet with
  the matrix Jarlskog invariant, proves that any degenerate energy pair removes
  vacuum asymmetry in every channel, and gives an explicit nonzero PMNS example
  at a supplied test spectrum/time. The example is not a mass prediction.
- `RelativisticPhase` uses Mathlib only: exact E=sqrt(p²+m²), exact gap
  (m_i²-m_j²)/(E_i+E_j), and the bound
  `|t*(E_i-E_j)/2 - t*(m_i²-m_j²)/(4p)| ≤ |t|*(m_i⁴+m_j⁴)/(16p³)` for p>0.
  This controls the common-momentum approximation without equating it to the
  exact spectrum or claiming a probability-error bound.
- `PropagationEnergy` consumes Paper II's `DiracEnergy` theorem for the supplied
  first-order four-component Clifford Hamiltonian. Positive-branch states exist
  for every supplied mass at p>0, and any such eigenstate has the exact energy
  used in the finite propagator. The common momentum offset cancels exactly.
  An equal mass-squared pair then removes the vacuum conjugation asymmetry.

The physical masses, accessible states/preparation, common momentum, mixing
basis and clock/baseline readout remain inputs. The positive-state existence
proof is not a derivation of a neutrino mass spectrum or a normalized complete
spinor basis. The first-order Hamiltonian here is not silently identified with
the complete eight-component finite-tick wall dispersion.

`AuditIndependent.lean` now checks four generic modules: `OscillationAlgebra`,
`SymmetricMass`, `CPAsymmetry` and `RelativisticPhase`.

## Premises and consequences

| Supplied input | Checked consequence | What remains physical |
| --- | --- | --- |
| Complete orthonormal mass bases of one three-dimensional space | Exactly unitary Uu† Ud; generation-universal charged/neutral current identities | Generation count, completeness/accessibility, physical mass bases and universal current identification |
| Real mass spectra and unitary diagonalizing bases | Hermitian links; positivity for positive spectra; Paper II wall-parity covariance; positive mass determinants | Actual link/update law and mass scale; θ itself is not selected here |
| Proposed CKM angles and phase | Full unitary matrix, J, determinant and triangle checks | A process/cost rule selecting those values |
| Proposed PMNS angles and phase | Full unitary matrix and conditional CP quartet sign | A neutrino propagation/mass model selecting them; Dirac-only/ Majorana claims |
| Supplied real eigenenergies and unitary mixing | Exact finite flavour evolution and normalized transition probabilities | E(m,p), baseline/time calibration, physical preparation and probability readout |
| Supplied uniform dressing q² = 687/688 | Contracted row/column Gram matrices; at least three extra channels for a unitary dilation | Whether that dressing and any additional channels describe the physical system |
| Fixed benchmark numbers quoted in the source | Exact interval and standardized-residual arithmetic | Data provenance, current updates, covariance and a global statistical interpretation |

## Existing CKM and comparison checks

`CKM`, `CKMDressing` and `Mixing` distinguish the exactly unitary matrix from
uniform amplitude contraction. The latter has row/column norm 687/688 and cannot
be the same complete three-channel basis change. `dilation_needs_three` counts
the minimum additional dimensions in any unitary dilation. A scalar missing-
probability balance alone is not a one-channel unitary implementation.

`CKMClosure` gives the conditional complete-basis exclusion and the cancellation
of a common nonzero factor in a rate ratio. It does not prove three physical
states, equality of physical rate factors, or resolution of a measured anomaly.

`UnitarityTriangle` proves area = |J|/2. `JarlskogReview` retains the exact mismatch
between the matrix J and Paper III's older φ²ηT_geo estimate; the latter is not
an independent invariant once the matrix is fixed. Paper III now uses the matrix
value. `TriangleAngles` derives sin(2β) from the actual matrix. `CPPhases.δ_vs_gamma`
is an arithmetic comparison of the parametrization phase δ with a quoted γ
benchmark; the actual matrix-based γ is now extracted in `TriangleGamma`, which
checks the branch, nonzero denominator and rephasing invariance explicitly.

`FlavourPulls` and `CPPhases` use fixed PDG 2024 / NuFIT 6.0 / quoted experimental
inputs. These are dated comparison tests, not a live data update or a proof that
the formulas are unique. The shared weak-mixing identity uses Paper III's stated
clock/ledger definitions; its physical scope assumptions remain upstream.

## What is left

See [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) for the reviewed dependency order.
The full CP factorization and controlled mass-squared phase approximation are now
proved. The main gap is an actual flavour/generation update and cost rule that selects the
mixing bases, angles and phase. The positive-Hermitian arbitrary-mixing theorem
shows why mass positivity, wall parity and unitarity alone cannot close that gap.
Physical neutrino energies/mass splittings and a calibrated oscillation comparison
remain additional work. The actual triangle γ and expanded probabilities are now
proved. Column-phase cancellation and the constructive symmetric/Hermitian
compatibility result do not select the physically allowed mass terms or prove a
Dirac-only law. The manuscript's stronger
unique-optimum, exhaustive-archetype and Majorana-exclusion statements are not
established by this Lean package.

## Verification

Run `./check.sh` with elan available, or set `PM_LAKE_BIN` to the pinned lake binary.
The script builds the default library, audits every project declaration for only
`propext`, `Classical.choice`, `Quot.sound`, and rejects Paper V–VI imports.
On 2026-10-30, the integrated check passed **4145 build jobs** and the strict
audit of **359 PMDynamics declarations**, with no warnings and no Paper V–VI
imports. `AuditIndependent.lean` passed for all four generic modules.
The preceding pass had 4140 jobs and 319 declarations. Current log:
`/tmp/pm4-cp-energy-full-check.log`.

This pass also added the reusable `DiracEnergy` module and its documentation in
Paper II. No experimental table, calculator or manuscript was changed.

Paper II also passed its complete build and audits: 3764 jobs and 4002 declarations.
See its `DIRAC-ENERGY.md` and `VERIFICATION.md` for scope and provenance.
