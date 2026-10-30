import PMDynamics.CKMDressing

/-!
# What persists decides: the observable CKM matrix is exactly unitary

Two upstream constraints settle the dressing question; no fit to the first-row data is used.

* `basis_change_unitary`: the CKM matrix is `U_uᴴ U_d`, the change of basis between the up-type
  and down-type mass eigenbases. Under Closure the three generations are the whole flavour state
  space, so both are complete orthonormal bases of the same 3-dimensional space and the product
  is exactly unitary.
* `closure_excludes_dressing`: hence no such basis change equals a uniformly dressed matrix
  `qV` with `q² = 687/688`. (`CKMDressing.dilation_needs_three`: keeping the dressing would
  need at least three channels outside the three generations, which Closure does not supply.)
* `global_dressing_cancels`: if the `1/688` resolution factor multiplies every propagating
  state, as the calculator's comment says, it multiplies the muon-decay normalization as well,
  and every measured `|V_ij|² = Γ_q/Γ_μ` is unchanged. A global factor is unobservable in the
  matrix; only a quark-only factor would show, and that is the case excluded above.

Consequence: the observable matrix is the undressed `V`. The first-row deficit
`0.9984 ± 0.0007` is then a 2.3σ tension the theory predicts will close, and the undressed
`|V_ud|` sits 2.6σ above the PDG 2024 direct value.
-/

noncomputable section
namespace PMDynamics.CKMClosure
open Matrix Complex ComplexConjugate PMDynamics.CKM PMDynamics.CKMDressing

theorem basis_change_unitary (Uu Ud : Matrix (Fin 3) (Fin 3) ℂ)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) : (Uuᴴ * Ud) * (Uuᴴ * Ud)ᴴ = 1 := by
  have hu' : Uuᴴ * Uu = 1 := mul_eq_one_comm.mp hu
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Ud, hd, Matrix.one_mul, hu']

theorem closure_excludes_dressing {c12 s12 c23 s23 c13 s13 : ℝ} {u : ℂ} (q : ℝ) (hq : q^2 = q2)
    (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1)
    (hu1 : u * conj u = 1) (Uu Ud : Matrix (Fin 3) (Fin 3) ℂ)
    (hu : Uu * Uuᴴ = 1) (hd : Ud * Udᴴ = 1) :
    Uuᴴ * Ud ≠ (q:ℂ) • V c12 s12 c23 s23 c13 s13 u := by
  intro h
  have h1 := basis_change_unitary Uu Ud hu hd
  rw [h, dressed_gram q hq r12 r23 r13 hu1] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [q2] at h2
  norm_num at h2

theorem global_dressing_cancels {q Γq Γμ : ℝ} (hq : q ≠ 0) (hμ : Γμ ≠ 0) :
    (q^2 * Γq) / (q^2 * Γμ) = Γq / Γμ := by
  have : q^2 ≠ 0 := pow_ne_zero 2 hq
  field_simp

end PMDynamics.CKMClosure
