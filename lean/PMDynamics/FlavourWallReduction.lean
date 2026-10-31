import PMAction.WallDispersion
import PMAction.HermitianTransport

/-! Exact reduction of the supplied Hermitian flavour-link two-wall model.
The flavour space is arbitrary finite dimension; no physical generation count,
link, accessible state or mixing angle is selected by diagonalization. -/
noncomputable section
namespace PMDynamics.FlavourWallReduction
open Matrix PMAction
open scoped Kronecker

variable {f : Type*} [Fintype f] [DecidableEq f]
abbrev Ix (f : Type*) := (Fin 4 × f) ⊕ (Fin 4 × f)

/-- The same flavour basis change on each spinor component and wall. -/
def basis (U : Matrix f f ℂ) : Matrix (Ix f) (Ix f) ℂ :=
  fromBlocks ((1 : ConcreteFermion.Spin) ⊗ₖ U) 0 0 ((1 : ConcreteFermion.Spin) ⊗ₖ U)

omit [Fintype f] [DecidableEq f] in
lemma basis_adjoint (U : Matrix f f ℂ) : (basis U)ᴴ=basis Uᴴ := by
  simp [basis,fromBlocks_conjTranspose,conjTranspose_kronecker]

lemma basis_mul (U V : Matrix f f ℂ) : basis U*basis V=basis (U*V) := by
  simp [basis,fromBlocks_multiply,← mul_kronecker_mul]

omit [Fintype f] in
lemma basis_one : basis (1 : Matrix f f ℂ)=1 := by
  simp [basis,fromBlocks_one]

lemma basis_left (U : Matrix f f ℂ) (hU : Uᴴ*U=1) : (basis U)ᴴ*basis U=1 := by
  rw [basis_adjoint,basis_mul,hU,basis_one]

lemma basis_right (U : Matrix f f ℂ) (hU : U*Uᴴ=1) : basis U*(basis U)ᴴ=1 := by
  rw [basis_adjoint,basis_mul,hU,basis_one]

/-- Conjugating the full wall Hamiltonian conjugates only its flavour link. -/
theorem conjugates (k : Fin 3 → ℝ) (δ : ℝ) (Y U : Matrix f f ℂ) (hU : Uᴴ*U=1) :
    (basis U)ᴴ*WallExchange.H k δ Y*basis U=WallExchange.H k δ (Uᴴ*Y*U) := by
  rw [basis_adjoint]
  simp only [basis,WallExchange.H,fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero]
  simp only [← mul_kronecker_mul,one_mul,mul_one,Matrix.mul_assoc,hU,
    conjTranspose_mul,conjTranspose_conjTranspose]

/-- Every Hermitian link has a complete orthonormal flavour basis in which
that exact Hamiltonian has diagonal real links. No diagonalizer is postulated. -/
theorem hermitian_reduction (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (hY : Y.IsHermitian) :
    ∃ U : Matrix f f ℂ, Uᴴ*U=1 ∧ U*Uᴴ=1 ∧
      (basis U)ᴴ*WallExchange.H k δ Y*basis U=
        WallExchange.H k δ (diagonal (fun i => (hY.eigenvalues i : ℂ))) := by
  let U := HermitianTransport.basis hY
  have hl : Uᴴ*U=1 := HermitianTransport.basis_left hY
  have hr : U*Uᴴ=1 := HermitianTransport.basis_right hY
  refine ⟨U,hl,hr,?_⟩
  rw [conjugates k δ Y U hl]
  have hd : Uᴴ*Y*U=diagonal (fun i => (hY.eigenvalues i : ℂ)) := by
    calc
      _ = Uᴴ*(U*PMAction.LinkExpansion.genDiag hY.eigenvalues*Uᴴ)*U :=
        congrArg (fun A : Matrix f f ℂ => Uᴴ*A*U) (HermitianTransport.generated hY)
      _ = _ := by
        simp only [Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U,hl,one_mul,mul_one,
          PMAction.LinkExpansion.genDiag]

  rw [hd]

/-- Embed one eight-component wall spinor into one diagonal flavour slot. -/
def inject (j : f) (v : WallDispersion.Ix → ℂ) : Ix f → ℂ :=
  Sum.elim (fun ai => if ai.2=j then v (.inl ai.1) else 0)
    (fun ai => if ai.2=j then v (.inr ai.1) else 0)

omit [Fintype f] in
lemma inject_add (j : f) (v w : WallDispersion.Ix → ℂ) :
    inject j (v+w)=inject j v+inject j w := by
  ext (⟨a,i⟩ | ⟨a,i⟩) <;> by_cases hi : i=j <;> simp [inject,hi]

omit [Fintype f] in
lemma inject_smul (j : f) (c : ℂ) (v : WallDispersion.Ix → ℂ) :
    inject j (c • v)=c • inject j v := by
  ext (⟨a,i⟩ | ⟨a,i⟩) <;> by_cases hi : i=j <;> simp [inject,hi]

omit [Fintype f] in
lemma inject_injective (j : f) : Function.Injective (inject j) := by
  intro v w h
  ext (a | a)
  · have hh := congrFun h (.inl (a,j))
    simpa [inject] using hh
  · have hh := congrFun h (.inr (a,j))
    simpa [inject] using hh

/-- Diagonal flavour slots really evolve by the upstream scalar-link model. -/
theorem diagonal_action (k : Fin 3 → ℝ) (δ : ℝ) (lam : f → ℝ) (j : f)
    (v : WallDispersion.Ix → ℂ) :
    WallExchange.H k δ (diagonal (fun i => (lam i : ℂ))) *ᵥ inject j v=
      inject j (WallDispersion.Hy k δ (lam j) *ᵥ v) := by
  ext (⟨a,i⟩ | ⟨a,i⟩) <;> by_cases hi : i=j <;>
    simp [WallExchange.H,WallDispersion.Hy,inject,mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type,diagonal_conjTranspose,
      Matrix.one_apply,Matrix.diagonal_apply,hi,mul_left_comm,mul_comm]

/-- Read one flavour slot without choosing a spinor or branch. -/
def slice (j : f) (v : Ix f → ℂ) : WallDispersion.Ix → ℂ :=
  Sum.elim (fun a => v (.inl (a,j))) (fun a => v (.inr (a,j)))

omit [Fintype f] [DecidableEq f] in
lemma slice_smul (j : f) (c : ℂ) (v : Ix f → ℂ) :
    slice j (c • v)=c • slice j v := by
  ext (a | a) <;> rfl

omit [Fintype f] [DecidableEq f] in
lemma slices_separate (v : Ix f → ℂ) (h : ∀ j, slice j v=0) : v=0 := by
  ext (⟨a,j⟩ | ⟨a,j⟩)
  · exact congrFun (h j) (.inl a)
  · exact congrFun (h j) (.inr a)

/-- The readout intertwines the diagonal-link Hamiltonian on every state. -/
theorem sliced_action (k : Fin 3 → ℝ) (δ : ℝ) (lam : f → ℝ) (j : f)
    (v : Ix f → ℂ) :
    slice j (WallExchange.H k δ (diagonal (fun i => (lam i : ℂ))) *ᵥ v)=
      WallDispersion.Hy k δ (lam j) *ᵥ slice j v := by
  ext (a | a) <;>
    simp [WallExchange.H,WallDispersion.Hy,slice,mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type,diagonal_conjTranspose,
      Matrix.one_apply,Matrix.diagonal_apply,mul_left_comm,mul_comm]

/-- Lift an eigenstate of one scalar-link model back into the original
multi-flavour Hamiltonian through the same complete basis. -/
theorem lift_eigenstate (k : Fin 3 → ℝ) (δ : ℝ) (Y U : Matrix f f ℂ)
    (hl : Uᴴ*U=1) (hr : U*Uᴴ=1) (lam : f → ℝ)
    (hd : Uᴴ*Y*U=diagonal (fun i => (lam i : ℂ))) (j : f)
    (v : WallDispersion.Ix → ℂ) (hv : v ≠ 0) (E : ℂ)
    (he : WallDispersion.Hy k δ (lam j) *ᵥ v=E • v) :
    let w := basis U *ᵥ inject j v
    w ≠ 0 ∧ WallExchange.H k δ Y *ᵥ w=E • w := by
  intro w
  have hc : (basis U)ᴴ*WallExchange.H k δ Y*basis U=
      WallExchange.H k δ (diagonal (fun i => (lam i : ℂ))) := by
    rw [conjugates k δ Y U hl,hd]
  have hi : WallExchange.H k δ Y*basis U=
      basis U*WallExchange.H k δ (diagonal (fun i => (lam i : ℂ))) := by
    have h := congrArg (fun A => basis U*A) hc
    simpa only [← Matrix.mul_assoc,basis_right U hr,one_mul] using h
  constructor
  · intro hz
    have h := congrArg (fun z => (basis U)ᴴ *ᵥ z) hz
    have hin : inject j v=0 := by
      simpa only [w,mulVec_mulVec,basis_left U hl,one_mulVec,mulVec_zero] using h
    apply hv
    have hz0 : inject j (0 : WallDispersion.Ix → ℂ)=0 := by
      ext (⟨a,i⟩ | ⟨a,i⟩) <;> simp [inject]
    exact inject_injective j (hin.trans hz0.symm)
  · change WallExchange.H k δ Y *ᵥ (basis U *ᵥ inject j v)=_
    rw [mulVec_mulVec,hi,← mulVec_mulVec,diagonal_action,he,inject_smul,mulVec_smul]

/-- Exact spectrum reduction in both directions, including all states. An
energy occurs iff it occurs in at least one scalar-link flavour block. -/
theorem energy_iff_some_flavour (k : Fin 3 → ℝ) (δ : ℝ) (Y U : Matrix f f ℂ)
    (hl : Uᴴ*U=1) (hr : U*Uᴴ=1) (lam : f → ℝ)
    (hd : Uᴴ*Y*U=diagonal (fun i => (lam i : ℂ))) (E : ℂ) :
    (∃ w : Ix f → ℂ, w ≠ 0 ∧ WallExchange.H k δ Y *ᵥ w=E • w) ↔
      ∃ j : f, ∃ v : WallDispersion.Ix → ℂ, v ≠ 0 ∧
        WallDispersion.Hy k δ (lam j) *ᵥ v=E • v := by
  constructor
  · rintro ⟨w,hw,he⟩
    let z := (basis U)ᴴ *ᵥ w
    have hz : z ≠ 0 := by
      intro h
      have hh := congrArg (fun v => basis U *ᵥ v) h
      have hz0 : w=0 := by
        simpa only [z,mulVec_mulVec,basis_right U hr,one_mulVec,mulVec_zero] using hh
      exact hw hz0
    have hj : ∃ j, slice j z ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hz (slices_separate z hn)
    obtain ⟨j,hj⟩ := hj
    refine ⟨j,slice j z,hj,?_⟩
    have hc : WallExchange.H k δ (diagonal (fun i => (lam i : ℂ)))=
        (basis U)ᴴ*WallExchange.H k δ Y*basis U := by
      rw [conjugates k δ Y U hl,hd]
    have hez : WallExchange.H k δ (diagonal (fun i => (lam i : ℂ))) *ᵥ z=E • z := by
      rw [hc]
      change _ *ᵥ ((basis U)ᴴ *ᵥ w)=_
      rw [mulVec_mulVec]
      have hm : ((basis U)ᴴ*WallExchange.H k δ Y*basis U)*(basis U)ᴴ=
          (basis U)ᴴ*WallExchange.H k δ Y := by
        simp only [Matrix.mul_assoc,basis_right U hr,mul_one]
      rw [hm,← mulVec_mulVec,he,mulVec_smul]
    rw [← sliced_action,hez,slice_smul]
  · rintro ⟨j,v,hv,he⟩
    exact ⟨basis U *ᵥ inject j v,lift_eigenstate k δ Y U hl hr lam hd j v hv E he⟩

/-- For an arbitrary Hermitian link, spectral reduction requires no supplied
eigenbasis: the upstream spectral theorem provides it internally. -/
theorem hermitian_energy_iff (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (hY : Y.IsHermitian) (E : ℂ) :
    (∃ w : Ix f → ℂ, w ≠ 0 ∧ WallExchange.H k δ Y *ᵥ w=E • w) ↔
      ∃ j : f, ∃ v : WallDispersion.Ix → ℂ, v ≠ 0 ∧
        WallDispersion.Hy k δ (hY.eigenvalues j) *ᵥ v=E • v := by
  let U:=HermitianTransport.basis hY
  have hl : Uᴴ*U=1 := HermitianTransport.basis_left hY
  have hr : U*Uᴴ=1 := HermitianTransport.basis_right hY
  have hd : Uᴴ*Y*U=diagonal (fun i => (hY.eigenvalues i : ℂ)) := by
    calc
      _ = Uᴴ*(U*PMAction.LinkExpansion.genDiag hY.eigenvalues*Uᴴ)*U :=
        congrArg (fun A : Matrix f f ℂ => Uᴴ*A*U) (HermitianTransport.generated hY)
      _ = _ := by
        simp only [Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U,hl,one_mul,mul_one,
          PMAction.LinkExpansion.genDiag]
  exact energy_iff_some_flavour k δ Y U hl hr hY.eigenvalues hd E

/-- Every allowed light-branch energy of every nonzero link eigenvalue is
realized in the full Hamiltonian; it is not merely a formal dispersion root. -/
theorem hermitian_light_state (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (hY : Y.IsHermitian) (j : f) (hj : hY.eigenvalues j ≠ 0)
    (hM : 0<WallDispersion.msq3 k+WallDispersion.massSqM δ (hY.eigenvalues j)) :
    ∃ w : Ix f → ℂ, w ≠ 0 ∧ WallExchange.H k δ Y *ᵥ w=
      (Real.sqrt (WallDispersion.msq3 k+WallDispersion.massSqM δ (hY.eigenvalues j)) : ℂ) • w := by
  apply (hermitian_energy_iff k δ Y hY _).mpr
  have h:= (WallDispersion.two_dirac_particles k δ (hY.eigenvalues j) hj hM).2 1 (by norm_num)
  have he := h.1
  simp only [one_mul] at he
  have ht : (WallDispersion.R k δ (hY.eigenvalues j)
      (WallDispersion.rhoM δ (hY.eigenvalues j)) (WallDispersion.rhoP δ (hY.eigenvalues j)) 1).trace ≠ 0 := by
    rw [h.2]
    norm_num
  obtain ⟨v,hv,heig⟩ := WallDispersion.eigenvector_of_projector k δ (hY.eigenvalues j) _ _ he ht
  exact ⟨j,v,hv,heig⟩

end PMDynamics.FlavourWallReduction
