# PM-4-Dynamics: flavour matrices, wall spectra and propagation

Lean 4.34.1; pinned sibling dependencies and the existing local mathlib cache.
Run `./check.sh`, or set `PM_LAKE_BIN` to the pinned Lake executable. Paper IV
uses Papers I–III and rejects imports from Papers V–VI.

The conditional matrix/spectrum/propagation results are checked. The physical
generation/update law and selection of the mixing and mass formulas remain open;
those are not supplied by silently adding hypotheses to a theorem.

## Matrices, currents and mass constructions

| Modules | Checked mathematics | Supplied application inputs |
| --- | --- | --- |
| `CKM`, `CKMDressing`, `CKMClosure`, `Mixing` | Complete complex CKM matrix, unitarity, det=1, Jarlskog quartet, dressing deficit | Angles/phase, complete accessible bases, any uniform dressing |
| `PMNS`, `PMNSIntervals` | Complete matrix, unitarity, determinant, CP sign, all nine squared-entry intervals, quartet enclosure | Proposed angle formulas; phase from persistence sum rule; no selected masses |
| `FlavourCurrent` | Generation-universal current, charged block Uu†Ud, neutral-current identities | Generation space, physical mass bases, universal-current identification |
| `MassMixing` | Hermitian positive mass constructions, diagonalization, wall-parity covariance | Actual link/mass law, spectrum, theta; positivity does not select angles |
| `SymmetricMass` | Symmetric U diag(m) Uᵀ and Hermitian U diag(m) U† can share squared propagation | Allowed physical mass terms, statistics, observables not selected |

## Exact wall spectrum and flavour reduction

`WallSpectrumLink` identifies branch energies with the relativistic energy law
and proves the light/heavy seesaw relation.

- `FlavourWallReduction`: complete unitary change of basis for `WallExchange.H`,
  arbitrary finite flavour dimension, not three generations or a selected link.
- `WallLatticeSpectrum.concrete_hamiltonian`: sin(k) gives concrete Hamiltonian at y=1.
- `WallRanks.branch_ranks`: trace-two idempotents → rank-two projectors.

## Observables and controlled phases

`UnitarityTriangle`, `TriangleAngles`, `TriangleGamma`: area=|J|/2, sin(2β),
gamma from the matrix. For the supplied CKM ansatz, **68.16° < γ < 68.17°**.

`OscillationAlgebra`, `OscillationObservables`, `CPAsymmetry`, `CPObservables`:
exact finite unitary propagation, normalized probabilities, expanded formulas,
factored three-flavour conjugation asymmetry, rephasing cancellation.

`RelativisticPhase`: exact gap formula and controlled half-phase estimate.
`PropagationEnergy`: connects supplied eigenstates to phases.
`OscillationStability`: probability-error bound, independent of earlier papers.
`PropagationStability`: uniform fourth-mass bound, common momentum phase removal.

## Certified PMNS entries

`PMNSIntervals.squared_entry_bounds` encloses |U_ij|² without measured entries.
`jarlskog_bounds` gives **-0.0217 < J < -0.0215**. The phase δ ≈ 220.8° from the
persistence sum rule `|U_μ2| = |U_τ2|` (`ReferenceFlavour`, `PMNS.cosDelta`).

## Native carrier and register realization

| Module | Proved result |
| --- | --- |
| `NativeFlavourWall` | Native Hamiltonian identified with wall operator, exact readout, encoded spectrum |
| `NativeFlavourCurrent` | Native chiral current, charged mass-basis block, universal neutral identity |
| `NativeMassBasis` | Mass frame diagonalizes Hermitian block; every unitary mixing with fixed spectra |
| `NativeFlavourPropagation` | Prepared eigenmodes give exact evolution, normalized probabilities, compressed ticks |
| `LightFlavourPreparation` | Orthonormal three-mode light preparation exists for every regular link |
| `NativeFlavourObservables` | Native probabilities: interference, CP asymmetry, error bounds |
| `NativeFlavourStationarity` | Configuration-space residual = flavour residual; variance/gap bounds, ray tests |

## Reference persistence and stationarity

`ReferenceSpectrum`: persistence iff single-energy eigenspace.
`sampled_aliasing`: integer-tick persistence aliases distinct energies.
`one_tick_iff_of_band`: occupied-band condition bridges sampled to continuous.

`SpectralVariance`: exact least-squares identity.
`FlavourStationarity`: residual coordinates, gap bounds, full-support PMNS obstruction.
`NativeFlavourStationarity`: native realization of same conclusions.

## Completion boundary

### Restoration (full six-root alphabet)

| Module | Proved result |
| --- | --- |
| `AllRootRestoration` | Exhaustive six-reflection alphabet, minimum two calls, price c, density c K/T |
| `ReferenceSafeRestoration` | Roots 1,2,3 preserve lepton coordinate, two-call exact repair |
| `RootRepairSelection` | Unique cheapest restoring word `[1,0]`, most persistent |
| `RestorationBudget` | Feasibility bounds, minimum density c K/T for T>0, K>0 |

The cheapest schedules are `[1,0]`, `[0,2]` and `[2,1]`; they implement the same
inverse operator. A unique cheapest word in the restricted generator alphabet
must not be reported as a unique physical schedule.

### Five selection tests narrow the remaining problem

- `ReferenceSelection`: complementary rotation preserves reference, changes link
- `NativeReferenceFreedom`: same amplitude eigenstate throughout link family
- `FlavourResponseSelection`: uniform response sees only spectrum, ties all mixing
- `SelectionSymmetry`: unique minimum inherits symmetry, not broken
- `TransitionSelection`: unconstrained minimization → zero flux; required work → lower bound

These rules out several incomplete routes to angle selection. The gap-weighted
relative-frame cost below supplies the missing weighting; an **event-level law
for required transfer between the identified generations**, together with its
actual preparation/readout and priced work, remains the open obligation.

`FlavourOrderComparison` supplies a joint readout route using Paper II's
`OrderComparison`: compare two evolution orders in opposite orders. The squared
joint response is `(AB−BA)²/12`; a phase-flip example gives `(8/3)c²s²` for a
complementary rotation.

### Relative-frame cost and required transfer work

`RelativeFrameCost` turns that readout into a price and shows it has the two
properties the earlier readouts lacked.

| Result | Content |
| --- | --- |
| `common_relabel` | a common class relabeling divides out — the value depends on the **relative** configuration |
| `frameCost_zero_iff`, `aligned_zero`, `mixes_of_positive` | an exact obstruction to simultaneous diagonalization |
| `gap_weighted`, `diagonal_free` | each frame entry is priced by its **own** eigenphase gap; only off-diagonal entries are charged |
| `plane_cost01/02/12` | closed form `gap_ij · s² / 6` for a plane rotation |
| `sum_three_pairs`, `frame_price` | any frame reduces to a linear program in three pair weights |
| `signal_range01`, `signal_max01`, `signal_attainable` | exact range `0 ≤ price ≤ gap/6`, every value attained |
| `sign_tie01`, `conjugation_tie` | even in the amplitude and CP-even — no branch selection |

`GenerationPersistence` models inter-generation transfer as a rate policy: any
nonzero net drift accumulates without bound (`starvation_grows_linearly`), so
bounded accumulation forces a balanced policy (`persistence_selects_balanced`).

`TransferWorkLaw` combines the two into the required-work law the five tests
asked for: `12 · price = Σ gap · weight` and `12 · work = period · Σ gap ·
weight`. Under a strictly ordered gap the smallest-gap pair is the **unique**
cheapest transfer route (`min_cost_is_min_gap`, `wasted_work`,
`unique_min_concentrates`), and a frame's induced policy is balanced already
(`policyOf_balanced`).

`Wolfenstein` defines the paper's four standard observables λ, A, ρ̄, η̄ on its own
matrix for the first time, with exact closed forms and the decimal-free ordering
`η̄ > ρ̄` (equivalent to `σ > 2χ`), plus the proof that the leading Wolfenstein
`V_td` is exact only at zero mixing.

`SpectralGapOrder` then removes the three gaps as inputs. Using the eigenphases
of the existing `FlavourEvolution.evolution` (`eigenphase_is_evolution_diagonal`),
the chord law `gap_of_splitting` gives `gap i j = 2 − 2 cos|t(e i − e j)|`, the
splittings telescope (`splitting_telescope`), and inside one chord branch price
order is splitting order (`gap_lt_iff_splitting_lt`). Hence:

| Result | Content |
| --- | --- |
| `extreme_is_widest`, `extreme_never_cheapest` | the extreme generation pair carries the **largest** gap |
| `route_is_tightest_adjacent` / `'` | a work-minimizing frame routes through an **adjacent** pair only |
| `route_extreme_amplitude_vanishes` | the extreme-pair amplitude is exactly zero at the bound |
| `splitting_comparison_is_spectral`, `..._scalefree` | the surviving choice is `e₁−e₀` vs `e₂−e₁`; the tick divides out |
| `degenerate_route_free`, `doublet_free`, `doublet_price_tie` | a degenerate pair has zero gap and zero price |
| `gap_budget`, `gap_not_independent`, `gap_le_four` | the three gaps are constrained, not independent |

**What is selected vs. what is not.** The gap ordering selects *which* pair
transfers, and the tighter adjacent splitting selects *which adjacent* pair. It
does not select *how much*: the total weight has zero
unconstrained minimum (`zero_weight_minimum`, mirroring
`TransitionSelection.zero_flux_minimum`) and the price is even in the amplitude
(`weight_not_selected`). Deriving the required weight, and identifying the three
pair gaps as numbers rather than inputs, remain physical obligations. No
measured angle is used in any of these modules.

### Lepton-axis restriction + Dirac survival

`LeptonAxisRestriction` derives from the reference-maintenance contract that
every admissible event root avoids the lepton axis (`cycle_root_axis_zero`),
so B−L is conserved and all Majorana pairings are unreachable. Combining with
`MassTermLaw`, `dirac_survival` proves only the Dirac neutrino mass term survives.

`MassTermLaw` supplies conditional insertion-cost and carrier-root exclusions
under an isolated-reflection and gauge-repair contract.

## Verification

`check.sh` builds the default library, strictly audits transitive axioms against
only `propext`, `Classical.choice`, `Quot.sound`, and checks the no-Papers-V–VI
boundary. `AuditIndependent.lean` separately checks six generic modules for no
earlier/later theory imports.

**4315** build jobs, **zero** errors, **zero** warnings
**1515** strict-audited PMDynamics declarations
No Paper V–VI imports, six-module independent-algebra audit passed

See [OVERVIEW.md](OVERVIEW.md) for the overview of checked results.
See [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) for the remaining open work.
