import PMFlavor.BreakingLink
import Mathlib.Tactic

/-!
# The mixing overlap of the two breaking links: the shared-state obstruction is gone

`GenerationBreaking.pmns_no_shared_state` says that if two sectors share a mass
state, the mixing matrix has a zero entry — but the supplied PMNS is all nonzero.
`BreakingLink` built the two concrete links: `brokenLink δ` (lepton-axis, keeps
the residual `Z₂` and the protected state `anti = (0,1,−1)`) and `brokenLinkB ε`
(mirror, breaks the `Z₂` for `ε ≠ 0`). This module computes the overlap of the
protected state of sector 1 with the eigenbasis of sector 2 and proves it has **no
zero components** — the resolution of the no-go, in closed form.

**The spectrum.** Both links are rank-one deformations of the `S₃`-symmetric
`linkOverlap = 1 + J`, whose `μ–τ` block has quadratic
`q_x(λ) = λ² − (5 + x)λ + (4 + 3x)` and roots

    root±(x) = (5 + x ± √((x−1)² + 8)) / 2.

* `rootP_quadratic`, `rootM_quadratic` — the roots satisfy `q_x = 0`.
* `rootP_ne_four`, `rootM_ne_four` — **`4` is not a root for `x ≠ 0`**, because
  `q_x(4) = −x`. This is the whole content of the non-degeneracy.
* `brokenLinkB_eigP`, `brokenLinkB_eigM`, `brokenLinkB_eigAnti` — the eigenpairs of
  the `Z₂`-breaking link are `(1, root±(ε) − 3, 1)` at `root±(ε)` and `(1, 0, −1)`
  at `1`.

**The overlap.** The protected state `anti = (0,1,−1)` of `brokenLink δ` has inner
products with the three `brokenLinkB ε` eigenvectors

    1,   rootP(ε) − 4,   rootM(ε) − 4,

all nonzero for `ε ≠ 0` (`anti_overlaps_all`). So the antisymmetric mass state of
sector 1 is spread over *every* mass state of sector 2: no zero mixing entry is
forced by it. This is exactly the entry the `pmns_no_shared_state` no-go would
have made zero, and the `Z₂`-breaking removes it.

**Scope.** It does not prove *all* entries of `U₁ᴴU₂` are nonzero for every
`δ, ε` — the cross terms `root±(δ) + root±(ε) − 5` can vanish at special values.
It proves the specific obstruction that the no-go identified is gone, which is what
a shared-state argument can establish unconditionally.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
namespace PMFlavor.MixingMatrix
open Matrix GenerationBreaking BreakingLink

/-- The larger eigenvalue of the `μ–τ` block at deformation `x`. -/
def rootP (x : ℝ) : ℝ := (5 + x + Real.sqrt ((x - 1) ^ 2 + 8)) / 2
/-- The smaller eigenvalue of the `μ–τ` block at deformation `x`. -/
def rootM (x : ℝ) : ℝ := (5 + x - Real.sqrt ((x - 1) ^ 2 + 8)) / 2

/-- The block quadratic evaluated at `rootP x` is zero. -/
theorem rootP_quadratic (x : ℝ) :
    (rootP x) ^ 2 - (5 + x) * (rootP x) + (4 + 3 * x) = 0 := by
  have hs : Real.sqrt ((x - 1) ^ 2 + 8) ^ 2 = (x - 1) ^ 2 + 8 :=
    Real.sq_sqrt (by positivity)
  unfold rootP
  nlinarith [hs]

/-- The block quadratic evaluated at `rootM x` is zero. -/
theorem rootM_quadratic (x : ℝ) :
    (rootM x) ^ 2 - (5 + x) * (rootM x) + (4 + 3 * x) = 0 := by
  have hs : Real.sqrt ((x - 1) ^ 2 + 8) ^ 2 = (x - 1) ^ 2 + 8 :=
    Real.sq_sqrt (by positivity)
  unfold rootM
  nlinarith [hs]

/-- `q_x(4) = −x`, so `4` is a root exactly at `x = 0`. -/
theorem quadratic_at_four (x : ℝ) :
    (4 : ℝ) ^ 2 - (5 + x) * 4 + (4 + 3 * x) = -x := by ring

/-- **`4` is not an eigenvalue of the breaking for `x ≠ 0`** (via `rootP`). -/
theorem rootP_ne_four (x : ℝ) (hx : x ≠ 0) : rootP x ≠ 4 := by
  intro h
  have hq := rootP_quadratic x
  rw [h, quadratic_at_four] at hq
  exact hx (by linarith)

theorem rootM_ne_four (x : ℝ) (hx : x ≠ 0) : rootM x ≠ 4 := by
  intro h
  have hq := rootM_quadratic x
  rw [h, quadratic_at_four] at hq
  exact hx (by linarith)

/-! ## Eigenvectors of the `Z₂`-breaking link -/

/-- The block quadratic cast to `ℂ` at `rootP x`. -/
theorem rootP_quadratic_C (x : ℝ) :
    ((rootP x : ℂ)) ^ 2 - ((5 : ℂ) + (x : ℂ)) * (rootP x : ℂ)
      + ((4 : ℂ) + 3 * (x : ℂ)) = 0 := by
  have hh := rootP_quadratic x
  have : ((rootP x : ℂ)) ^ 2 - ((5 : ℂ) + (x : ℂ)) * (rootP x : ℂ)
      + ((4 : ℂ) + 3 * (x : ℂ))
      = (((rootP x) ^ 2 - (5 + x) * (rootP x) + (4 + 3 * x) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, hh]; simp

theorem rootM_quadratic_C (x : ℝ) :
    ((rootM x : ℂ)) ^ 2 - ((5 : ℂ) + (x : ℂ)) * (rootM x : ℂ)
      + ((4 : ℂ) + 3 * (x : ℂ)) = 0 := by
  have hh := rootM_quadratic x
  have : ((rootM x : ℂ)) ^ 2 - ((5 : ℂ) + (x : ℂ)) * (rootM x : ℂ)
      + ((4 : ℂ) + 3 * (x : ℂ))
      = (((rootM x) ^ 2 - (5 + x) * (rootM x) + (4 + 3 * x) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, hh]; simp

/-- The antisymmetric state of the `Z₂`-breaking link: `(1, 0, −1)`. -/
def antiB : Fin 3 → ℂ := ![1, 0, -1]

theorem brokenLinkB_eigAnti : brokenLinkB 0 *ᵥ antiB = (1 : ℂ) • antiB := by
  ext i; fin_cases i <;>
    simp [brokenLinkB, antiB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul] <;> norm_num

/-- `(1, rootP ε − 3, 1)` is an eigenvector of `brokenLinkB ε` at `rootP ε`. -/
theorem brokenLinkB_eigP (ε : ℝ) :
    brokenLinkB ε *ᵥ (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) =
      (rootP ε : ℂ) • (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) := by
  have hq := rootP_quadratic_C ε
  ext i
  fin_cases i
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -hq
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring

/-- `(1, rootM ε − 3, 1)` is an eigenvector of `brokenLinkB ε` at `rootM ε`. -/
theorem brokenLinkB_eigM (ε : ℝ) :
    brokenLinkB ε *ᵥ (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) =
      (rootM ε : ℂ) • (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) := by
  have hq := rootM_quadratic_C ε
  ext i
  fin_cases i
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linear_combination -hq
  · simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring

/-! ## The protected state overlaps every sector-2 eigenvector -/

/-- The (real-entry) pairing `∑ uᵢ wᵢ`. -/
def ip (u w : Fin 3 → ℂ) : ℂ := ∑ i, u i * w i

theorem ip_anti_antiB : ip anti antiB = 1 := by
  simp [ip, anti, antiB, Fin.sum_univ_three]

theorem ip_anti_P (ε : ℝ) :
    ip anti (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootP ε : ℂ) - 4 := by
  simp [ip, anti, Fin.sum_univ_three]; ring

theorem ip_anti_M (ε : ℝ) :
    ip anti (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootM ε : ℂ) - 4 := by
  simp [ip, anti, Fin.sum_univ_three]; ring

/-- **The shared-state obstruction is gone.** The protected state `anti` of the
lepton-axis sector has nonzero overlap with *every* eigenvector of the `Z₂`-breaking
sector, provided `ε ≠ 0`. The `pmns_no_shared_state` no-go would have forced a zero
here; the `Z₂` breaking removes it. -/
theorem anti_overlaps_all (ε : ℝ) (hε : ε ≠ 0) :
    ip anti antiB ≠ 0 ∧
      ip anti (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip anti (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 := by
  refine ⟨by rw [ip_anti_antiB]; norm_num, ?_, ?_⟩
  · rw [ip_anti_P]
    intro h
    apply rootP_ne_four ε hε
    have : (rootP ε : ℂ) = 4 := by linear_combination h
    exact_mod_cast this
  · rw [ip_anti_M]
    intro h
    apply rootM_ne_four ε hε
    have : (rootM ε : ℂ) = 4 := by linear_combination h
    exact_mod_cast this

/-! ## The mirror direction: `antiB` overlaps every sector-1 eigenvector -/

/-- `(rootP δ − 3, 1, 1)` is an eigenvector of `brokenLink δ` at `rootP δ`. -/
theorem brokenLink_eigP (δ : ℝ) :
    brokenLink δ *ᵥ (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) =
      (rootP δ : ℂ) • (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) :=
  brokenLink_eigen_two_roots δ ((rootP δ : ℂ)) (rootP_quadratic_C δ)

/-- `(rootM δ − 3, 1, 1)` is an eigenvector of `brokenLink δ` at `rootM δ`. -/
theorem brokenLink_eigM (δ : ℝ) :
    brokenLink δ *ᵥ (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) =
      (rootM δ : ℂ) • (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) :=
  brokenLink_eigen_two_roots δ ((rootM δ : ℂ)) (rootM_quadratic_C δ)

theorem ip_antiB_anti : ip antiB anti = 1 := by
  simp [ip, anti, antiB, Fin.sum_univ_three]

theorem ip_antiB_P (δ : ℝ) :
    ip antiB (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) = (rootP δ : ℂ) - 4 := by
  simp [ip, antiB, Fin.sum_univ_three]; ring

theorem ip_antiB_M (δ : ℝ) :
    ip antiB (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) = (rootM δ : ℂ) - 4 := by
  simp [ip, antiB, Fin.sum_univ_three]; ring

/-- **The mirror direction.** `antiB = (1,0,−1)`, the protected state of the
`Z₂`-breaking sector, has nonzero overlap with *every* eigenvector of the
lepton-axis sector `brokenLink δ` when `δ ≠ 0`. So the obstruction is broken in
both directions. -/
theorem antiB_overlaps_all (δ : ℝ) (hδ : δ ≠ 0) :
    ip antiB anti ≠ 0 ∧
      ip antiB (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip antiB (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) ≠ 0 := by
  refine ⟨by rw [ip_antiB_anti]; norm_num, ?_, ?_⟩
  · rw [ip_antiB_P]
    intro h
    apply rootP_ne_four δ hδ
    have : (rootP δ : ℂ) = 4 := by linear_combination h
    exact_mod_cast this
  · rw [ip_antiB_M]
    intro h
    apply rootM_ne_four δ hδ
    have : (rootM δ : ℂ) = 4 := by linear_combination h
    exact_mod_cast this

/-! ## Why the chord branch is about energies, not link eigenvalues

The `ChordBranch` window bounds the *energy* spread `e₂ − e₀ ≤ π/43`. It cannot be
applied to the raw link eigenvalues: the symmetric link's spread is `3`, far above
`π/43`. So the physical energies must enter through the wall dispersion
(`WallDispersion.massSqM`), which is what suppresses the differences. This is a
clarifying negative result: it rules out the tempting but wrong closure of the
branch bound at the link-eigenvalue scale. -/

theorem rootP_zero : rootP 0 = 4 := by
  unfold rootP
  have h : Real.sqrt (((0 : ℝ) - 1) ^ 2 + 8) = 3 := by
    rw [show ((0 : ℝ) - 1) ^ 2 + 8 = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]; norm_num

theorem rootM_zero : rootM 0 = 1 := by
  unfold rootM
  have h : Real.sqrt (((0 : ℝ) - 1) ^ 2 + 8) = 3 := by
    rw [show ((0 : ℝ) - 1) ^ 2 + 8 = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]; norm_num

/-- The symmetric link's eigenvalue spread is `3` (`4 − 1`). -/
theorem symmetric_link_spread : rootP 0 - rootM 0 = 3 := by
  rw [rootP_zero, rootM_zero]; norm_num

/-- It exceeds the chord-branch threshold `π/43` by a wide margin, so the branch
bound cannot be closed on link eigenvalues alone. -/
theorem spread_exceeds_pi_over_43 : rootP 0 - rootM 0 > Real.pi / 43 := by
  rw [symmetric_link_spread]
  nlinarith [Real.pi_lt_d20]

/-! ## Attainability of an all-nonzero mixing matrix

The shared-state obstruction is gone for every `δ ≠ 0`; the *full* all-nonzero
statement fails only at isolated `(δ, ε)`. Here is a concrete parameter point where
it holds, so all-nonzero mixing is genuinely attainable. At `δ = ε = 2` the block
roots are rational (`rootP 2 = 5`, `rootM 2 = 2`), giving explicit integer
eigenvectors whose nine pairwise overlaps are all nonzero. Normalization divides
each by a positive norm, so every entry of `U₁ᴴU₂` is nonzero there. -/

theorem rootP_two : rootP 2 = 5 := by
  unfold rootP
  have h : Real.sqrt (((2 : ℝ) - 1) ^ 2 + 8) = 3 := by
    rw [show ((2 : ℝ) - 1) ^ 2 + 8 = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]; norm_num

theorem rootM_two : rootM 2 = 2 := by
  unfold rootM
  have h : Real.sqrt (((2 : ℝ) - 1) ^ 2 + 8) = 3 := by
    rw [show ((2 : ℝ) - 1) ^ 2 + 8 = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]; norm_num

/-- `(2,1,1)` is the `rootP` eigenvector of `brokenLink 2` (eigenvalue `5`). -/
theorem brokenLink2_eigP :
    brokenLink 2 *ᵥ (![2, 1, 1] : Fin 3 → ℂ) = (5 : ℂ) • (![2, 1, 1] : Fin 3 → ℂ) := by
  ext i; fin_cases i <;>
    simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- `(−1,1,1)` is the `rootM` eigenvector of `brokenLink 2` (eigenvalue `2`). -/
theorem brokenLink2_eigM :
    brokenLink 2 *ᵥ (![-1, 1, 1] : Fin 3 → ℂ) = (2 : ℂ) • (![-1, 1, 1] : Fin 3 → ℂ) := by
  ext i; fin_cases i <;>
    simp [brokenLink, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- `(1,2,1)` is the `rootP` eigenvector of `brokenLinkB 2` (eigenvalue `5`). -/
theorem brokenLinkB2_eigP :
    brokenLinkB 2 *ᵥ (![1, 2, 1] : Fin 3 → ℂ) = (5 : ℂ) • (![1, 2, 1] : Fin 3 → ℂ) := by
  ext i; fin_cases i <;>
    simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- `(1,−1,1)` is the `rootM` eigenvector of `brokenLinkB 2` (eigenvalue `2`). -/
theorem brokenLinkB2_eigM :
    brokenLinkB 2 *ᵥ (![1, -1, 1] : Fin 3 → ℂ) = (2 : ℂ) • (![1, -1, 1] : Fin 3 → ℂ) := by
  ext i; fin_cases i <;>
    simp [brokenLinkB, mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- **All-nonzero mixing is attainable.** At `δ = ε = 2` every pairwise overlap
between the `brokenLink 2` eigenbasis `{(0,1,−1), (2,1,1), (−1,1,1)}` and the
`brokenLinkB 2` eigenbasis `{(1,0,−1), (1,2,1), (1,−1,1)}` is nonzero, so after
normalization every entry of the mixing matrix `U₁ᴴU₂` is nonzero. -/
theorem all_nonzero_mixing_witness :
    (ip anti antiB ≠ 0 ∧
      ip anti (![1, 2, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip anti (![1, -1, 1] : Fin 3 → ℂ) ≠ 0) ∧
    (ip (![2, 1, 1] : Fin 3 → ℂ) antiB ≠ 0 ∧
      ip (![-1, 1, 1] : Fin 3 → ℂ) antiB ≠ 0) ∧
    (ip (![2, 1, 1] : Fin 3 → ℂ) (![1, 2, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![2, 1, 1] : Fin 3 → ℂ) (![1, -1, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![-1, 1, 1] : Fin 3 → ℂ) (![1, 2, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![-1, 1, 1] : Fin 3 → ℂ) (![1, -1, 1] : Fin 3 → ℂ) ≠ 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [ip, anti, antiB, Fin.sum_univ_three] <;> norm_num

/-! ## Nonzero mixing across the physical range `0 < δ, ε ≤ 4`

The single witness at `δ = ε = 2` generalizes: on the whole square
`0 < δ, ε ≤ 4` every entry of the mixing overlap is nonzero. The bounds used are
`4 < rootP x` and `1 < rootM x` for `x > 0`, and `rootM x < 5/2` for `x ≤ 4`.
Between them the four cross terms are sign-definite:
`rootP+rootP−5 > 0`, `rootP+rootM−5 > 0`, `rootM+rootP−5 > 0`,
`rootM+rootM−5 < 0`; and the diagonal terms `rootP−4 > 0`, `rootM−4 < 0`. -/

theorem rootP_gt_four (x : ℝ) (hx : 0 < x) : 4 < rootP x := by
  unfold rootP
  have h : 3 - x < Real.sqrt ((x - 1) ^ 2 + 8) := by
    by_cases h3 : 3 ≤ x
    · exact lt_of_le_of_lt (by linarith) (Real.sqrt_pos.mpr (by positivity))
    · have h3' : x < 3 := not_le.mp h3
      rw [Real.lt_sqrt (by linarith : (0 : ℝ) ≤ 3 - x)]
      nlinarith [hx]
  linarith

theorem rootM_gt_one (x : ℝ) (hx : 0 < x) : 1 < rootM x := by
  unfold rootM
  have h : Real.sqrt ((x - 1) ^ 2 + 8) < x + 3 := by
    rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < x + 3)]
    nlinarith [hx]
  linarith

theorem rootM_lt_five_halves (x : ℝ) (hx : 0 < x) (hx4 : x ≤ 4) : rootM x < 5 / 2 := by
  unfold rootM
  have h : x < Real.sqrt ((x - 1) ^ 2 + 8) := by
    rw [Real.lt_sqrt (by linarith : (0 : ℝ) ≤ x)]
    nlinarith [hx4]
  linarith

/-- `(rootP δ − 3, 1, 1)` paired with `(1, rootP ε − 3, 1)`. -/
theorem ip_P_P (δ ε : ℝ) :
    ip (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
       (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootP δ : ℂ) + (rootP ε : ℂ) - 5 := by
  simp [ip, Fin.sum_univ_three]; ring

theorem ip_P_M (δ ε : ℝ) :
    ip (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
       (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootP δ : ℂ) + (rootM ε : ℂ) - 5 := by
  simp [ip, Fin.sum_univ_three]; ring

theorem ip_M_P (δ ε : ℝ) :
    ip (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
       (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootM δ : ℂ) + (rootP ε : ℂ) - 5 := by
  simp [ip, Fin.sum_univ_three]; ring

theorem ip_M_M (δ ε : ℝ) :
    ip (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
       (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) = (rootM δ : ℂ) + (rootM ε : ℂ) - 5 := by
  simp [ip, Fin.sum_univ_three]; ring

/-- The pairing is symmetric (`ip` has no conjugation). -/
theorem ip_comm (u w : Fin 3 → ℂ) : ip u w = ip w u := by
  simp [ip, Fin.sum_univ_three]; ring

/-- Real nonzero survives the cast to `ℂ`. -/
private lemma real_cast_ne {r : ℝ} (h : r ≠ 0) : ((r : ℂ)) ≠ 0 := by
  exact_mod_cast h

/-- **Nonzero mixing on the square `0 < δ ≤ 4`, `0 < ε ≤ 4`.** -/
theorem all_nonzero_mixing_interval (δ ε : ℝ) (hδ0 : 0 < δ) (hε0 : 0 < ε)
    (hδ4 : δ ≤ 4) (hε4 : ε ≤ 4) :
    (ip anti antiB ≠ 0 ∧
      ip anti (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip anti (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0) ∧
    (ip (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) antiB ≠ 0 ∧
      ip (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ) antiB ≠ 0) ∧
    (ip (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![(rootP δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (rootP ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      ip (![(rootM δ : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0) := by
  have hPδ : 4 < rootP δ := rootP_gt_four δ hδ0
  have hPε : 4 < rootP ε := rootP_gt_four ε hε0
  have hMδ : rootM δ < 5 / 2 := rootM_lt_five_halves δ hδ0 hδ4
  have hMε : rootM ε < 5 / 2 := rootM_lt_five_halves ε hε0 hε4
  have hMid : 1 < rootM δ := rootM_gt_one δ hδ0
  have hMie : 1 < rootM ε := rootM_gt_one ε hε0
  -- complex nonzeroness from real inequalities
  have ePδ : (rootP δ : ℂ) - 4 ≠ 0 := by
    have heq : (rootP δ : ℂ) - 4 = ((rootP δ - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have ePε : (rootP ε : ℂ) - 4 ≠ 0 := by
    have heq : (rootP ε : ℂ) - 4 = ((rootP ε - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have eMδ : (rootM δ : ℂ) - 4 ≠ 0 := by
    have heq : (rootM δ : ℂ) - 4 = ((rootM δ - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have eMε : (rootM ε : ℂ) - 4 ≠ 0 := by
    have heq : (rootM ε : ℂ) - 4 = ((rootM ε - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have ePP : (rootP δ : ℂ) + (rootP ε : ℂ) - 5 ≠ 0 := by
    have heq : (rootP δ : ℂ) + (rootP ε : ℂ) - 5
        = ((rootP δ + rootP ε - 5 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have ePM : (rootP δ : ℂ) + (rootM ε : ℂ) - 5 ≠ 0 := by
    have heq : (rootP δ : ℂ) + (rootM ε : ℂ) - 5
        = ((rootP δ + rootM ε - 5 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have eMP : (rootM δ : ℂ) + (rootP ε : ℂ) - 5 ≠ 0 := by
    have heq : (rootM δ : ℂ) + (rootP ε : ℂ) - 5
        = ((rootM δ + rootP ε - 5 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  have eMM : (rootM δ : ℂ) + (rootM ε : ℂ) - 5 ≠ 0 := by
    have heq : (rootM δ : ℂ) + (rootM ε : ℂ) - 5
        = ((rootM δ + rootM ε - 5 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]; exact real_cast_ne (by linarith)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [ip_anti_antiB]; norm_num
  · rw [ip_anti_P]; exact ePε
  · rw [ip_anti_M]; exact eMε
  · rw [ip_comm, ip_antiB_P]; exact ePδ
  · rw [ip_comm, ip_antiB_M]; exact eMδ
  · rw [ip_P_P]; exact ePP
  · rw [ip_P_M]; exact ePM
  · rw [ip_M_P]; exact eMP
  · rw [ip_M_M]; exact eMM

/-! ## The interval `0 < x ≤ 4` is not vacuous — the global statement genuinely fails

At `δ = ε = 9/2` the smaller block root is exactly `5/2`, so the cross term
`rootM+rootM−5` vanishes. This is the concrete isolated zero that makes "all
`δ, ε`" false and shows why the interval theorem stops at `4`. -/

theorem rootM_nine_halves : rootM (9 / 2) = 5 / 2 := by
  unfold rootM
  have h : Real.sqrt (((9 / 2 : ℝ) - 1) ^ 2 + 8) = 9 / 2 := by
    rw [show ((9 / 2 : ℝ) - 1) ^ 2 + 8 = (9 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]; norm_num

/-- The `rootM/rootM` mixing overlap vanishes at `δ = ε = 9/2`. -/
theorem ip_M_M_vanishes_at :
    ip (![(rootM (9 / 2) : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
       (![1, (rootM (9 / 2) : ℂ) - 3, 1] : Fin 3 → ℂ) = 0 := by
  rw [ip_M_M, rootM_nine_halves]; norm_num

end PMFlavor.MixingMatrix





