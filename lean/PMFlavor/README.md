# PMFlavor — Paper IV flavour library

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum IV: Information
Transfer* — CKM/PMNS matrices, wall spectra, propagation and persistence
selection in the flavour sector.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — the module map, matrices,
  wall spectrum, native carriers, selection tests and transfer/work results.
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) — open physical inputs
  and structural questions.

Build: Lean 4.34.1, with sibling dependencies pinned through Lake. Paper IV uses
Papers I–III and rejects imports from Papers V–VI.

```sh
./check.sh
```

`check.sh` builds the library, runs the strict axiom audit, the dependency audit,
and the independent-algebra audit. The physical generation/update law and the
selection of mixing and mass formulas remain open; they are not supplied by
silently adding hypotheses to a theorem.
