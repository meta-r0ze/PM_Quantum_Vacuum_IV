import PMDynamics.CKMDressing

/-!
# CKM closure conditional on complete three-generation mass bases

`basis_change_unitary` proves that Uu† Ud is unitary for supplied complete unitary
bases of the same three-dimensional flavour space. `closure_excludes_dressing`
then excludes the proposed uniformly contracted block as that exact basis change.
A larger unitary dilation remains possible with explicitly counted extra channels.

Neither three physical generations nor complete accessibility of this sector is
derived from Finiteness/Conservation/Causality by these theorems. The matrix
hypotheses express that model choice. `global_dressing_cancels` is the conditional
rate-ratio identity when the same nonzero factor multiplies both rates. It does
not identify the physical normalization or resolve an experimental discrepancy.
The fixed benchmark comparisons elsewhere are arithmetic tests, not selection laws.
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
