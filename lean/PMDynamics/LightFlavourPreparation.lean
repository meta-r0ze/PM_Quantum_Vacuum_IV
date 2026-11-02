import PMDynamics.NativeFlavourPropagation

/-!
# An orthonormal family of the three actual light branches exists

Choose one normalized light spinor per diagonal flavour slot, then transport
the family through the Hermitian link's complete unitary basis. Distinct flavour
slots make the columns orthogonal even for degenerate energies. Thus the
preparation hypotheses in the native propagation theorems are satisfiable for
every regular supplied Hermitian three-flavour link. This is state existence,
not a physically admitted preparation protocol or a selection of the link.
-/
noncomputable section
set_option synthInstance.maxSize 512
namespace PMDynamics.LightFlavourPreparation
open Matrix PMAction FlavourWallReduction

private def normalized (v : WallDispersion.Ix → ℂ) :=
  (((Real.sqrt (CommonResponse.nsq v))⁻¹ : ℝ) : ℂ) • v

private theorem normalized_nsq (v : WallDispersion.Ix → ℂ) (hv : v ≠ 0) :
    CommonResponse.nsq (normalized v) = 1 := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hv
  have hp : 0 < CommonResponse.nsq v := by
    rw [LinkExpansion.nsq_eq]
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  have hs : Real.sqrt (CommonResponse.nsq v) ^ 2 = CommonResponse.nsq v := Real.sq_sqrt hp.le
  rw [normalized, ControllerHamiltonian.nsq_smul, Complex.normSq_ofReal]
  field_simp
  nlinarith

private theorem normalized_ne_zero (v : WallDispersion.Ix → ℂ) (hv : v ≠ 0) : normalized v ≠ 0 := by
  intro he
  have hh := normalized_nsq v hv
  simp [he, CommonResponse.nsq] at hh

private def columns (v : Fin 3 → WallDispersion.Ix → ℂ) :
    Matrix (Ix (Fin 3)) (Fin 3) ℂ := fun x j => inject j (v j) x

private theorem columns_isometry (v : Fin 3 → WallDispersion.Ix → ℂ)
    (hn : ∀ j, CommonResponse.nsq (v j) = 1) : (columns v)ᴴ * columns v = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have ht : ∑ x, star (v i x) * v i x = 1 := by
      have h := hn i
      rw [LinkExpansion.nsq_eq] at h
      simpa only [← Complex.normSq_eq_conj_mul_self, Complex.star_def,
        ← Complex.ofReal_sum, Complex.ofReal_one] using congrArg Complex.ofReal h
    simpa [columns, inject, Matrix.mul_apply, conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type] using ht
  · simp [columns, inject, Matrix.mul_apply, conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, hij, Ne.symm hij]

theorem light_frame_exists (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : Y.IsHermitian) (hy : ∀ j, hY.eigenvalues j ≠ 0)
    (hM : ∀ j, 0 < WallDispersion.msq3 k + WallDispersion.massSqM δ (hY.eigenvalues j)) :
    ∃ Ψ : Matrix (Ix (Fin 3)) (Fin 3) ℂ, Ψᴴ * Ψ = 1 ∧
      ∀ j, WallExchange.H k δ Y *ᵥ (fun x => Ψ x j) =
        (Real.sqrt (WallDispersion.msq3 k + WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) •
          (fun x => Ψ x j) := by
  have hex (j : Fin 3) : ∃ v : WallDispersion.Ix → ℂ, v ≠ 0 ∧
      WallDispersion.Hy k δ (hY.eigenvalues j) *ᵥ v =
        (Real.sqrt (WallDispersion.msq3 k + WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) • v := by
    have hh := (WallDispersion.two_dirac_particles k δ (hY.eigenvalues j) (hy j) (hM j)).2 1 (by norm_num)
    have he := hh.1
    simp only [one_mul] at he
    have ht : (WallDispersion.R k δ (hY.eigenvalues j)
        (WallDispersion.rhoM δ (hY.eigenvalues j)) (WallDispersion.rhoP δ (hY.eigenvalues j)) 1).trace ≠ 0 := by
      rw [hh.2]
      norm_num
    exact WallDispersion.eigenvector_of_projector k δ (hY.eigenvalues j) _ _ he ht
  let v : Fin 3 → WallDispersion.Ix → ℂ := fun j => Classical.choose (hex j)
  have hv (j) := (Classical.choose_spec (hex j)).1
  have he (j) := (Classical.choose_spec (hex j)).2
  let w := fun j => normalized (v j)
  have hw (j) : WallDispersion.Hy k δ (hY.eigenvalues j) *ᵥ w j =
      (Real.sqrt (WallDispersion.msq3 k + WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) • w j := by
    have he' : WallDispersion.Hy k δ (hY.eigenvalues j) *ᵥ v j =
        (Real.sqrt (WallDispersion.msq3 k + WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) • v j := he j
    simp only [w, normalized, Matrix.mulVec_smul, he', smul_smul]
    congr 1
    ring
  let U := HermitianTransport.basis hY
  have hl : Uᴴ * U = 1 := HermitianTransport.basis_left hY
  have hr : U * Uᴴ = 1 := HermitianTransport.basis_right hY
  have hd : Uᴴ * Y * U = diagonal (fun j => (hY.eigenvalues j : ℂ)) := by
    calc
      _ = Uᴴ * (U * LinkExpansion.genDiag hY.eigenvalues * Uᴴ) * U :=
        congrArg (fun A => Uᴴ * A * U) (HermitianTransport.generated hY)
      _ = _ := by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hl, one_mul, mul_one, LinkExpansion.genDiag]
  refine ⟨basis U * columns w, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (basis U)ᴴ (basis U),
      basis_left U hl, Matrix.one_mul]
    exact columns_isometry w (fun j => normalized_nsq (v j) (hv j))
  · intro j
    exact (lift_eigenstate k δ Y U hl hr hY.eigenvalues hd j (w j)
      (normalized_ne_zero (v j) (hv j)) _ (hw j)).2

/-- All preparation/eigenmode hypotheses of the native propagation bridge are
satisfied on the regular light branches of a supplied Hermitian three-flavour link. -/
theorem native_light_propagation_exists {r : Type*} [Fintype r] [DecidableEq r]
    (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ)
    (Y : Matrix (Fin 3) (Fin 3) ℂ) (hY : Y.IsHermitian)
    (hy : ∀ j, hY.eigenvalues j ≠ 0)
    (hM : ∀ j, 0 < WallDispersion.msq3 (NativeFlavourWall.momentum k) +
      WallDispersion.massSqM δ (hY.eigenvalues j)) (ρ : r → ℂ)
    (hρ : ∑ j, star (ρ j) * ρ j = 1) :
    ∃ Ψ : Matrix (Ix (Fin 3)) (Fin 3) ℂ, Ψᴴ * Ψ = 1 ∧
      ∀ (U : FlavourCurrent.M), U * Uᴴ = 1 → ∀ t : ℝ,
      (NativeFlavourPropagation.frame c Ψ ρ U)ᴴ *
        NativeFlavourPropagation.evolve (r := r) c p k δ Y t *
        NativeFlavourPropagation.frame c Ψ ρ U =
      FlavourEvolution.evolution U
        (fun j => Real.sqrt (WallDispersion.msq3 (NativeFlavourWall.momentum k) +
          WallDispersion.massSqM δ (hY.eigenvalues j))) t := by
  obtain ⟨Ψ,hΨ,he⟩ := light_frame_exists (NativeFlavourWall.momentum k) δ Y hY hy hM
  refine ⟨Ψ,hΨ,?_⟩
  intro U hU t
  exact NativeFlavourPropagation.compressed_evolution c p hp hp1 k δ Y Ψ ρ _ he hΨ hρ U hU t

end PMDynamics.LightFlavourPreparation
