import PMAction.WallDispersion
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Turn the upstream idempotent trace certificates into actual eigenspace
ranks. This counts complex linear modes, not physical fermion statistics. -/
noncomputable section
namespace PMDynamics.WallRanks
open Matrix PMAction.WallDispersion

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem rank_two_of_trace (P : Matrix n n ℂ) (hP : P*P=P) (ht : P.trace=2) : P.rank=2 := by
  have hi : IsIdempotentElem P.toLin' := by
    apply LinearMap.ext
    intro v
    change P *ᵥ (P *ᵥ v)=P *ᵥ v
    rw [mulVec_mulVec,hP]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hi)
  rw [Matrix.trace_toLin'_eq,ht] at h
  have hn : Module.finrank ℂ (LinearMap.range P.toLin')=2 := by exact_mod_cast h.symm
  exact hn

/-- Both energy signs on both nondegenerate branches have rank two. -/
theorem branch_ranks (k : Fin 3 → ℝ) (δ y : ℝ) (hy : y ≠ 0)
    (hM : 0<msq3 k+massSqM δ y) (σ : ℂ) (hσ : σ*σ=1) :
    (R k δ y (rhoP δ y) (rhoM δ y) σ).rank=2 ∧
    (R k δ y (rhoM δ y) (rhoP δ y) σ).rank=2 := by
  have hP : 0<msq3 k+δ^2+rhoP δ y := by
    have hm := (branch_masses δ y hy).2.2.1
    have hk : 0 ≤ msq3 k := by unfold msq3; positivity
    change 0<δ^2+rhoP δ y at hm
    linarith
  have hM' : 0<msq3 k+δ^2+rhoM δ y := by
    change 0<msq3 k+(δ^2+rhoM δ y) at hM
    linarith
  have hp := branch_projector k δ y _ _ (roots_PM k δ y hy) hP σ hσ
  have hm := branch_projector k δ y _ _ (roots_MP k δ y hy) hM' σ hσ
  have ht := two_dirac_particles k δ y hy hM
  exact ⟨rank_two_of_trace _ hp.2.1 ((ht.1 σ hσ).2),
    rank_two_of_trace _ hm.2.1 ((ht.2 σ hσ).2)⟩

end PMDynamics.WallRanks
