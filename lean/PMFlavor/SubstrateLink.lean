import PMFlavor.GenerationLink
import PMFlavor.SpectralGapOrder
import Mathlib.Tactic

/-!
# A link derived from the substrate, not postulated

`GenerationLink` proved that an `S₃`-invariant link is `α·1 + β·(J − 1)` and
that its light branch is a degenerate doublet, but it took the link `Y` as a
supplied matrix. This module **derives** the link from the substrate's own glue
structure and shows the resulting spectrum is forced.

**The link is the generation overlap.** A generation is one of the three unordered
pairs of nontrivial glue classes (`GenerationLink.pair_of_missing`). Two
generations are coupled through the classes they share. The natural substrate
linking matrix therefore counts overlaps,

    linkOverlap i j = |pair i ∩ pair j|  =  2 on the diagonal, 1 off it,

so `linkOverlap = 1 + J`. Nothing is fitted: every entry is a cardinality of an
intersection of substrate glue classes, and `share_one` already proved the
off-diagonal overlap is exactly one.

**What it forces.**
* `linkOverlap_eq_form` — it is literally the `α·1 + β·(J − 1)` form of
  `GenerationLink.invariant_form` with `α = β = 1`, so it is `S₃`-invariant.
* `linkOverlap_hermitian` — a real symmetric matrix, hence a valid wall link.
* `linkOverlap_democratic_eigen` / `linkOverlap_sumzero_eigen` — its eigenvalues
  are `4` on `(1,1,1)` and `1` on the sum-zero plane, i.e. the **light branch is
  doubly degenerate**.
* `linkOverlap_light_spectrum_degenerate` — fed through the same eigenphase map
  the work law uses, the two light generations have equal energy and the light
  pair gap is zero. This is the substrate origin of `SpectralGapOrder.doublet_free`
  and of `GenerationLink.light_mixing_free`.

**What it does not do.** It does not split the degenerate doublet. Any actual
light mass splitting, and hence the observed mixing, requires a breaking of this
`S₃` link — exactly the lepton-axis breaking that `GenerationBreaking` studies.
This module makes the "the supplied link is physical" hypothesis concrete for the
symmetric case and shows the symmetric case cannot produce mixing.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.SubstrateLink
open Matrix GenerationLink SpectralGapOrder RelativeFrameCost

/-- **The substrate generation link**: the number of glue classes two generations
share. Every entry is an intersection cardinality of substrate glue classes. -/
def linkOverlap : Matrix (Fin 3) (Fin 3) ℂ :=
  of fun i j => ((pair_of_missing i ∩ pair_of_missing j).card : ℂ)

/-- Diagonal entries are two: a generation shares both its own classes. -/
theorem linkOverlap_diag (i : Fin 3) : linkOverlap i i = 2 := by
  simp [linkOverlap, pair_of_missing]

/-- Off-diagonal entries are one: two distinct generations share exactly one class
(`GenerationLink.share_one`). -/
theorem linkOverlap_offdiag {i j : Fin 3} (h : i ≠ j) : linkOverlap i j = 1 := by
  have := share_one i j h
  simp [linkOverlap, this]

/-- **The link is the democratic form `1 + J`, entrywise.** -/
theorem linkOverlap_eq_form (i j : Fin 3) :
    linkOverlap i j = if i = j then (2 : ℂ) else 1 := by
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl]; exact linkOverlap_diag i
  · rw [ite_eq_right h]; exact linkOverlap_offdiag h

/-- **`S₃`-invariant**, because it is `α·1 + β·(J − 1)` with `α = β = 1`. -/
theorem linkOverlap_invariant (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    linkOverlap (σ i) (σ j) = linkOverlap i j := by
  rw [linkOverlap_eq_form (σ i) (σ j), linkOverlap_eq_form i j]
  by_cases h : i = j
  · subst h; simp
  · have h' : σ i ≠ σ j := fun e => h (σ.injective e)
    simp [h, h']

/-- It matches `GenerationLink.invariant_form`'s conclusion with the concrete values. -/
theorem linkOverlap_eq_invariant_form :
    ∀ i j, linkOverlap i j = if i = j then linkOverlap 0 0 else linkOverlap 0 1 :=
  invariant_form linkOverlap_invariant

/-- **Hermitian**, so it is an admissible wall link. -/
theorem linkOverlap_hermitian : linkOverlap.IsHermitian := by
  ext i j
  rw [conjTranspose_apply, linkOverlap_eq_form j i, linkOverlap_eq_form i j]
  by_cases h : i = j
  · subst h; simp
  · have h' : j ≠ i := h ∘ Eq.symm
    simp [h, h']

/-- The matrix is literally `of (fun i j => if i = j then 2 else 1)`. -/
theorem linkOverlap_as_of :
    linkOverlap = of (fun i j : Fin 3 => if i = j then (2 : ℂ) else 1) := by
  ext i j; rw [linkOverlap_eq_form i j]; rfl

/-- The democratic (all-ones) eigenvector has eigenvalue `4 = 2 + 2·1`. -/
theorem linkOverlap_democratic_eigen :
    linkOverlap *ᵥ w = (4 : ℂ) • w := by
  have h := democratic_eigen (2 : ℂ) (1 : ℂ)
  rw [show ((2 : ℂ) + 2 * 1) = 4 by norm_num] at h
  rw [linkOverlap_as_of]; exact h

/-- A sum-zero vector has eigenvalue `1`: the light branch is doubly degenerate. -/
theorem linkOverlap_sumzero_eigen (v : Fin 3 → ℂ) (hv : v 0 + v 1 + v 2 = 0) :
    linkOverlap *ᵥ v = (1 : ℂ) • v := by
  have h := sumzero_eigen (2 : ℂ) (1 : ℂ) v hv
  rw [show ((2 : ℂ) - 1) = 1 by norm_num] at h
  rw [linkOverlap_as_of]; exact h

/-! ## The light spectrum it forces is degenerate -/

/-- **The substrate link forces a degenerate light doublet in the work law.** Feed
the two equal light eigenvalues (`1, 1`) through the same eigenphase map that
`SpectralGapOrder` uses; the light pair gap is zero, hence weight on that pair is
unpriced. This is the substrate origin of `doublet_free`. -/
theorem linkOverlap_light_spectrum_degenerate (t : ℝ) :
    gap (eigenphase ![4, 1, 1] t) 1 2 = 0 :=
  degenerate_route_free _ t 1 2 (by norm_num)

/-- The light pair has zero splitting, so it is the free route: the substrate link
makes the light doublet the cheapest transfer path for any tick. -/
theorem linkOverlap_light_splitting_zero (t : ℝ) :
    splitting ![4, 1, 1] t 1 2 = 0 := by
  show |t * ((1 : ℝ) - 1)| = 0
  norm_num

end PMFlavor.SubstrateLink
