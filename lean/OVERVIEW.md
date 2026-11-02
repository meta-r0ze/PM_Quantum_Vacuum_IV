# Paper IV: overview of checked results

*Persistence Mechanics of the Quantum Vacuum IV: Information Transfer.*

This is the single overview of what Paper IV proves and how it hands off to
Papers V–VI. The actionable open work is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md);
build/layout instructions are in [`README.md`](README.md). The Lean source is the
ground truth; theorem names below are entry points, not an exhaustive list.

## Scope

Paper IV builds on the Paper I substrate (E8, clock Δ = 43, invariants
D = 4, ν = 16, σ = 5, χ = 2) and Paper II/III wall and register results. It treats
the flavour sector — CKM/PMNS mixing, wall spectra, propagation, reference
persistence, and a transfer/work cost — as a constrained-persistence application.
Nothing here compares to measurement; the falsifiable claims are collected in one
ledger. No Paper V–VI imports are allowed.

## What is checked

**Matrices and mixing.** `CKM`, `PMNS`: complete complex matrices with exact
unitarity, determinant 1, the Jarlskog quartet, and certified squared-entry /
Jarlskog intervals (`PMNSIntervals`: `−0.0217 < J < −0.0215`). The PMNS phase is
fixed by the persistence sum rule `|U_μ2| = |U_τ2|` (`ReferenceFlavour`), on the
`sin δ < 0` branch. Unitarity triangles have area `|J|/2`
(`UnitarityTriangle.area_is_half_J`), with `68.16° < γ < 68.17°`.

**Wall spectrum and native carriers.** `WallSpectrumLink` identifies branch
energies with the relativistic energy law and the light/heavy seesaw;
`FlavourWallReduction` gives the exact multi-flavour reduction; `NativeFlavour*`,
`NativeMassBasis`, `LightFlavourPreparation` realise prepared eigenmodes on the
native carrier and reproduce exact flavour evolution and probabilities.

**Reference persistence.** `ReferenceSpectrum`: persistence iff a single-energy
eigenspace. `SpectralVariance`, `FlavourStationarity`: residual coordinates and
gap bounds. `persistent_single_frequency`: a persisting state is one energy/
frequency, hence on-shell (used by Paper V).

**Selection and restoration.** `AllRootRestoration`, `RootRepairSelection`,
`RestorationBudget`: the six-reflection restoring alphabet, unique cheapest word,
minimum density. The five selection tests (`ReferenceSelection`,
`NativeReferenceFreedom`, `FlavourResponseSelection`, `SelectionSymmetry`,
`TransitionSelection`) isolate what a persistence cost can and cannot select.

**Lepton axis, Dirac survival.** `LeptonAxisRestriction` (per-cycle contract) plus
`MassTermLaw` give `dirac_survival`: only the Dirac neutrino mass term survives;
active-Majorana and sterile terms are unreachable.

**Transfer cost and generation selection.** `RelativeFrameCost` prices a frame by
`‖AB−BA‖²/12 = Σ gap·weight/12`. `TransferWorkLaw` shows the least-work route is
the smallest-gap pair; `SpectralGapOrder` derives the gap ordering from the
spectrum (`gap = 2 − 2cos|t·Δe|`); `ChordBranch` reduces the one-branch hypothesis
to `t ≤ tStar` and discharges it at `tStar`; `TransferAmount` shows any positive
transfer costs positive work.

**The link, derived.** `SubstrateLink.linkOverlap` is the glue-class overlap
matrix (`2` diagonal, `1` off), `S₃`-invariant with spectrum `{4,1,1}` — a
degenerate light doublet. `BreakingLink.brokenLink δ` (lepton-axis weight on
generation 0) splits it for any `δ ≠ 0`; `brokenLinkB ε` breaks the residual μ–τ
`Z₂` and loses the protected antisymmetric state. `MixingMatrix` computes the
protected-state overlap and shows the shared-state no-go is resolved
(`anti_overlaps_all`), all-nonzero mixing on the physical square `0 < δ, ε ≤ 4`
(`all_nonzero_mixing_interval`), and a witness point (`all_nonzero_mixing_witness`).

**Derived inputs and Wolfenstein.** `FlavourInvariants` ties the six flavour
formulas to the Paper I invariants; `CabibboDressing` proves the `687/688`
dressing is `1 − 1/(νΔ)` with `ν = 16`, `Δ = 43`. `Wolfenstein` defines
λ, A, ρ̄, η̄ on the paper's own matrix and proves `η̄ > ρ̄` (from `σ > 2χ`) and the
`O(λ³)` truncation structure. `WolfensteinOctant` proves the solar/atmospheric/
reactor octants, and that the solar octant is exactly `1 < φ < 2`.

**Current chirality tied to Paper II.** `WeakCurrentBridge.spinProjector_eq_PL`: the
native flavour current's chiral projector is Paper II's weak V−A projector `P_L`
(rank two), so `modelCurrent G = P_L ⊗ G` is inherited, not chosen.

**CP for the next papers.** `Downstream`: `pmJ > 0` (CKM CP violated, positive
Jarlskog → baryon-asymmetry sign), `cp_conserved_iff` (`pmJ = 0 ↔ sin δ = 0`), and
the leptonic side `PMNS.jarlskog_nonpos` (opposite sign to CKM).

**Falsifiable ledger.** `FalsifiablePredictions.prediction_ledger` bundles every
unconditional, measured-input-free claim in one conjunction — the auditable input
to a data fit (the fit itself is data work, outside the axiom-checked tree).

## What is *not* derived

`φ = (1+√5)/2` is a postulate (the solar sector is a one-parameter input). The
numerical breaking weights `δ, ε` are dynamical, not fixed. Link eigenvalues are
not the physical energy scale, so the `π/43` chord bound is about energies. No
measured number enters the theorem tree.

## Downstream handoff

`PM-5-Decay` and `PM-6-Cosmo` both build against this tree. Paper IV supplies
them the CP input (`Downstream`), external-state on-shellness
(`persistent_single_frequency`), unitarity/mixing (`PMNS`, `CKM`), and Jarlskog
bounds. Their remaining work is their own physical modelling (interaction,
phase-space measure, decay-law cost for V; background/perturbation/baryon dynamics
for VI) — not missing Paper IV proofs.

## Verification

**4315** build jobs, **zero** errors, **zero** warnings
**1515** strict-audited PMDynamics declarations
No Paper V–VI imports; six-module independent-algebra audit passes.
Permitted transitive axioms: only `propext`, `Classical.choice`, `Quot.sound`.

Full check log: `check.sh`.
