import PMFlavor.SubstrateLink
import PMFlavor.GenerationBreaking
import Mathlib.Tactic

/-!
# The `S₃`-breaking link: a lepton-axis term splits the degenerate doublet

`SubstrateLink` derived the symmetric link `linkOverlap` from the substrate glue
classes and proved its spectrum is `{4, 1, 1}`: the light branch is a **doubly
degenerate doublet**, so the symmetric link cannot produce mixing. Review item 1
names the missing object: the actual breaking link. This module constructs it and
proves it does the one thing the symmetric link provably cannot — split the light
doublet.

**The breaking term is the lepton axis.** `GenerationBreaking` showed the lepton
axis (vector class, axis `0`) leaves at most a residual `Z₂` (the swap of
generations `1, 2`) and is otherwise broken. The generation that *omits* the
vector class is generation `0` (`GenerationLink.pair_of_missing 0 = {1,2}`); the
other two generations both contain it. The lepton-axis self-coupling therefore
modifies generation `0`'s diagonal entry and nothing else, giving a `Z₂`-invariant
breaking:

    brokenLink δ = linkOverlap + δ · E₀₀,

     = !![2 + δ, 1, 1; 1, 2, 1; 1, 1, 2].

At `δ = 0` it is exactly the symmetric substrate link (`brokenLink_zero`), so
nothing is refitted: the breaking is a single diagonal lepton-axis weight.

**What it proves.**
* `brokenLink_hermitian` — a valid wall link for every `δ : ℝ`.
* `brokenLink_z2` — the residual `Z₂` (swap `1 2`) is preserved, so the breaking is
  exactly the lepton-axis one and no more.
* `brokenLink_antisym` — `(0, 1, −1)` is an eigenvector with eigenvalue `1`, the
  `antisym_eigen` state of `GenerationBreaking`.
* `brokenLink_eigenspace_one_antisym` — for `δ ≠ 0` the eigenvalue-`1` eigenspace is
  **exactly** the line `span{(0,1,−1)}`.
* `symmetric_doublet_is_two_dim` — at `δ = 0` it is the **whole sum-zero plane**.
* `light_doublet_splits` — consequently a symmetry-breaking `δ ≠ 0` collapses the
  two-dimensional light eigenspace to one dimension and the light doublet splits.
  This is precisely the nondegeneracy the symmetric link (`SubstrateLink`) rules
  out and that observed mixing needs.

**What it does not do.** It does not compute the numerical value of `δ`; that is a
dynamical quantity of the wall model. It proves that *any* nonzero lepton-axis
weight splits the doublet, so the symmetric no-mixing obstruction is removed as
soon as the breaking is present.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.BreakingLink
open Matrix GenerationBreaking SubstrateLink

/-- The lepton-axis diagonal term `E₀₀`: unit weight on the generation that omits
the vector class. -/
def leptonAxis : Matrix (Fin 3) (Fin 3) ℂ :=
  of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- **The `S₃`-breaking link**: the symmetric substrate link plus a lepton-axis
diagonal weight `δ` on generation `0`. -/
def brokenLink (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![((2 : ℂ) + (δ : ℂ)), 1, 1; 1, 2, 1; 1, 1, 2]

/-- The breaking is exactly the symmetric link plus the lepton-axis term. -/
theorem brokenLink_eq_add (δ : ℝ) :
    brokenLink δ = linkOverlap + (δ : ℂ) • leptonAxis := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, linkOverlap_eq_form i j]
  fin_cases i <;> fin_cases j <;>
    simp [brokenLink, leptonAxis, smul_eq_mul]

/-- At `δ = 0` the breaking link is the symmetric substrate link. -/
theorem brokenLink_zero : brokenLink 0 = linkOverlap := by
  rw [brokenLink_eq_add]
  simp

/-- **A valid wall link for every real `δ`.** -/
theorem brokenLink_hermitian (δ : ℝ) : (brokenLink δ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brokenLink, conjTranspose_apply, Complex.conj_ofReal]

/-- **The residual `Z₂` (swap `1 2`) is preserved.** The breaking is precisely the
lepton-axis one: it distinguishes generation `0` while leaving the μ–τ swap
intact, matching `GenerationBreaking.stabilizer_of_fixed`. -/
theorem brokenLink_z2 (δ : ℝ) (i j : Fin 3) :
    brokenLink δ (Equiv.swap 1 2 i) (Equiv.swap 1 2 j) = brokenLink δ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [brokenLink, Equiv.swap_apply_def]

/-- The antisymmetric state `(0, 1, −1)` is an eigenvector with eigenvalue `1`
(`c − d` at `c = d = 1`), as in `GenerationBreaking.antisym_eigen`. -/
theorem brokenLink_antisym (δ : ℝ) :
    brokenLink δ *ᵥ anti = (1 : ℂ) • anti := by
  have h := antisym_eigen ((2 : ℂ) + (δ : ℂ)) 1 2 1
  rw [show ((2 : ℂ) - 1) = 1 by norm_num] at h
  simpa [brokenLink] using h

/-! ## The eigenvalue-`1` eigenspace -/

/-- **Component form of the eigenvalue-`1` equation.** The matrix minus the
identity is `!![1+δ, 1, 1; 1, 1, 1; 1, 1, 1]`, so an eigenvector at `1` satisfies
two independent linear conditions. -/
theorem brokenLink_eigenspace_one (δ : ℝ) (v : Fin 3 → ℂ) :
    brokenLink δ *ᵥ v = (1 : ℂ) • v ↔
      (((1 : ℂ) + (δ : ℂ)) * v 0 + v 1 + v 2 = 0 ∧ v 0 + v 1 + v 2 = 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] at h0 h1
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  · intro ⟨e0, e1⟩
    ext i
    fin_cases i <;>
      simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    · linear_combination e0
    · linear_combination e1
    · linear_combination e1

/-- **Broken case: the eigenvalue-`1` eigenspace is exactly the antisymmetric line.**
For `δ ≠ 0`, `(brokenLink δ · v = 1 • v) ↔ v₀ = 0 ∧ v₁ + v₂ = 0`. -/
theorem brokenLink_eigenspace_one_antisym (δ : ℝ) (hδ : δ ≠ 0) (v : Fin 3 → ℂ) :
    brokenLink δ *ᵥ v = (1 : ℂ) • v ↔ v 0 = 0 ∧ v 1 + v 2 = 0 := by
  rw [brokenLink_eigenspace_one]
  constructor
  · intro ⟨e0, e1⟩
    have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
    have hzero : (δ : ℂ) * v 0 = 0 := by linear_combination e0 - e1
    have hv0 : v 0 = 0 := (mul_eq_zero.mp hzero).resolve_left hδc
    refine ⟨hv0, ?_⟩
    rw [hv0] at e1
    simpa using e1
  · intro ⟨hv0, hs⟩
    refine ⟨?_, ?_⟩
    · rw [hv0]; simpa using hs
    · rw [hv0]; simpa using hs

/-- **The two non-antisymmetric modes.** If `λ` is a root of the light quadratic
`λ² − (5 + δ)λ + (4 + 3δ)` (the characteristic polynomial of the `μ–τ` symmetric
block), then `(λ − 3, 1, 1)` is an eigenvector with eigenvalue `λ`. So the broken
link carries three explicit modes: the antisymmetric one at `1`, and two roots of
the quadratic. -/
theorem brokenLink_eigen_two_roots (δ : ℝ) (lam : ℂ)
    (hq : lam ^ 2 - ((5 : ℂ) + (δ : ℂ)) * lam + ((4 : ℂ) + 3 * (δ : ℂ)) = 0) :
    brokenLink δ *ᵥ (![lam - 3, 1, 1] : Fin 3 → ℂ) =
      lam • (![lam - 3, 1, 1] : Fin 3 → ℂ) := by
  ext i
  fin_cases i
  · simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -hq
  · simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring

/-- The light quadratic does **not** vanish at `1` when `δ ≠ 0`, so the
antisymmetric mode at eigenvalue `1` is spectrally separated from the two modes of
`brokenLink_eigen_two_roots`. -/
theorem two_roots_not_one (δ : ℝ) (hδ : δ ≠ 0) :
    (1 : ℂ) ^ 2 - ((5 : ℂ) + (δ : ℂ)) * 1 + ((4 : ℂ) + 3 * (δ : ℂ)) ≠ 0 := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  intro h
  apply hδc
  linear_combination (1 / 2 : ℂ) * h

/-- **Symmetric case: the eigenvalue-`1` eigenspace is the whole sum-zero plane.**
This is `linkOverlap_sumzero_eigen` upgraded to an iff — the two-dimensional light
doublet. -/
theorem symmetric_doublet_is_two_dim (v : Fin 3 → ℂ) :
    linkOverlap *ᵥ v = (1 : ℂ) • v ↔ v 0 + v 1 + v 2 = 0 := by
  have h := brokenLink_eigenspace_one 0 v
  rw [brokenLink_zero] at h
  rw [h]
  constructor
  · rintro ⟨-, h2⟩; exact h2
  · intro h; exact ⟨by simpa using h, h⟩

/-- **The light doublet splits.** A symmetry-breaking lepton-axis weight `δ ≠ 0`
reduces the eigenvalue-`1` eigenspace from the two-dimensional sum-zero plane to
the one-dimensional antisymmetric line: the degeneracy the symmetric link forces
is removed. -/
theorem light_doublet_splits (δ : ℝ) (hδ : δ ≠ 0) (v : Fin 3 → ℂ)
    (hv : brokenLink δ *ᵥ v = (1 : ℂ) • v) :
    v 0 = 0 ∧ v 1 + v 2 = 0 :=
  (brokenLink_eigenspace_one_antisym δ hδ v).mp hv

/-- The witness that the doublet genuinely splits: `(1, −1, 0)` lies in the
symmetric sum-zero plane but is **not** an eigenvector at `1` once `δ ≠ 0`. -/
theorem splitting_witness (δ : ℝ) (hδ : δ ≠ 0) :
    brokenLink δ *ᵥ (![1, -1, 0] : Fin 3 → ℂ) ≠ (1 : ℂ) • (![1, -1, 0] : Fin 3 → ℂ) := by
  intro h
  have h0 := ((brokenLink_eigenspace_one_antisym δ hδ _).mp h).1
  norm_num at h0

/-! ## A `Z₂`-breaking second-sector link

`brokenLink δ` keeps the residual μ–τ `Z₂` and, with it, the protected
antisymmetric state `anti = (0,1,−1)` at eigenvalue `1` (`brokenLink_antisym`).
The lecton no-go `GenerationBreaking.pmns_no_shared_state` says two sectors that
share a mass state produce a zero PMNS entry — but the supplied PMNS is all
nonzero. So the two sectors cannot *both* be Z₂-invariant. This section builds
the second-sector link that breaks the `Z₂` and shows it necessarily loses the
shared antisymmetric state. -/

/-- The `E₁₁` lepton-axis term: unit weight on generation `1` alone. -/
def leptonAxisB : Matrix (Fin 3) (Fin 3) ℂ :=
  of fun i j => if i = 1 ∧ j = 1 then 1 else 0

/-- **The `Z₂`-breaking second link**: the symmetric link plus a diagonal weight on
generation `1` alone, which breaks the μ–τ swap. -/
def brokenLinkB (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2, 1, 1; 1, ((2 : ℂ) + (ε : ℂ)), 1; 1, 1, 2]

/-- It is the symmetric link plus the `E₁₁` term. -/
theorem brokenLinkB_eq_add (ε : ℝ) :
    brokenLinkB ε = linkOverlap + (ε : ℂ) • leptonAxisB := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, linkOverlap_eq_form i j]
  fin_cases i <;> fin_cases j <;>
    simp [brokenLinkB, leptonAxisB, smul_eq_mul]

/-- At `ε = 0` it is the symmetric substrate link (no Z₂ breaking). -/
theorem brokenLinkB_zero : brokenLinkB 0 = linkOverlap := by
  rw [brokenLinkB_eq_add]; simp

/-- A valid wall link for every real `ε`. -/
theorem brokenLinkB_hermitian (ε : ℝ) : (brokenLinkB ε).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brokenLinkB, conjTranspose_apply, Complex.conj_ofReal]

/-- **It breaks the μ–τ `Z₂`** as soon as `ε ≠ 0`: the two spinor generations no
longer carry equal self-coupling. -/
theorem brokenLinkB_z2_broken (ε : ℝ) (hε : ε ≠ 0) :
    brokenLinkB ε 1 1 ≠ brokenLinkB ε 2 2 := by
  have e11 : brokenLinkB ε 1 1 = ((2 : ℂ) + (ε : ℂ)) := by simp [brokenLinkB]
  have e22 : brokenLinkB ε 2 2 = (2 : ℂ) := by simp [brokenLinkB]
  rw [e11, e22]
  intro h
  apply hε
  have : (ε : ℂ) = 0 := by linear_combination h
  exact_mod_cast this

/-- **The antisymmetric state survives only in the symmetric limit.**
`brokenLinkB ε · anti = (0, 1+ε, −1)`, which is a multiple of `anti` iff `ε = 0`.
So every genuine `Z₂`-breaking loses the protected state `brokenLink δ` retains. -/
theorem brokenLinkB_anti_eigen_iff (ε : ℝ) :
    (∃ lam : ℂ, brokenLinkB ε *ᵥ anti = lam • anti) ↔ ε = 0 := by
  constructor
  · rintro ⟨lam, h⟩
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [brokenLinkB, anti, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul] at h1 h2
    have hlam : lam = 1 := by linear_combination h2
    have : (ε : ℂ) = 0 := by
      rw [hlam] at h1
      linear_combination h1
    exact_mod_cast this
  · rintro rfl
    refine ⟨1, ?_⟩
    have hB : brokenLinkB 0 = brokenLink 0 := by rw [brokenLinkB_zero, brokenLink_zero]
    rw [hB]
    exact brokenLink_antisym 0

/-- **The two sectors cannot both keep `anti`.** `brokenLink δ` has `anti` as an
eigenvector at eigenvalue `1` for every `δ`; `brokenLinkB ε` has `anti` as an
eigenvector only at `ε = 0`. So a genuine `Z₂`-breaking second sector does not
share the protected antisymmetric mass state with the lepton-axis sector. -/
theorem brokenLinkB_no_shared_anti (δ ε : ℝ) (hε : ε ≠ 0) :
    brokenLink δ *ᵥ anti = (1 : ℂ) • anti ∧
      ¬ ∃ lam : ℂ, brokenLinkB ε *ᵥ anti = lam • anti := by
  refine ⟨brokenLink_antisym δ, ?_⟩
  rw [brokenLinkB_anti_eigen_iff]
  exact hε

end PMFlavor.BreakingLink
