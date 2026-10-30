import PMDynamics.CKM

/-!
# Every unitarity triangle has area |J|/2

Paper IV's §5 explains the factor in `A = J/2` as "the chiral projection" (`N/ν = 2`). It is a
theorem of unitarity alone, for any matrix and any lattice.

* `triangle_closes`: orthogonality of two rows makes the three products `aₖ = V₀ₖ V̄₁ₖ` sum to zero:
  they are the sides of a closed triangle.
* `cross_equal`: for a closed triangle the three cross products `Im(āᵢ aⱼ)` (twice the signed area)
  are all equal.
* `cross_is_jarlskog`: that cross product is `−J`, with `J = Im(V_ud V_cs V̄_us V̄_cd)`.
* `area_is_half_J`: hence the triangle's area is `|J|/2`.
* `ckm_triangle_area`: in particular for Paper IV's unitary CKM matrix.

The `2` is the `1/2` in the area of a triangle spanned by two sides. No property of the substrate
enters, so `N/ν = 2` should not be cited as its origin.
-/

noncomputable section
namespace PMDynamics.UnitarityTriangle
open Complex ComplexConjugate PMDynamics.CKM

variable (V : Fin 3 → Fin 3 → ℂ)

def side (k : Fin 3) : ℂ := V 0 k * conj (V 1 k)

theorem triangle_closes (h : ∑ k, V 0 k * conj (V 1 k) = 0) :
    side V 0 + side V 1 + side V 2 = 0 := by
  simpa [side, Fin.sum_univ_three] using h

theorem cross_equal (h : side V 0 + side V 1 + side V 2 = 0) :
    (conj (side V 0) * side V 1).im = (conj (side V 1) * side V 2).im ∧
      (conj (side V 1) * side V 2).im = (conj (side V 2) * side V 0).im := by
  have h2 : side V 2 = -(side V 0) - side V 1 := by linear_combination h
  rw [h2]
  constructor <;> simp [Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem cross_is_jarlskog : (conj (side V 0) * side V 1).im = -jarlskog V := by
  simp only [side, jarlskog, map_mul, Complex.conj_conj]
  have : conj (V 0 0) * V 1 0 * (V 0 1 * conj (V 1 1)) =
      conj (V 0 0 * V 1 1 * conj (V 0 1) * conj (V 1 0)) := by
    simp only [map_mul, Complex.conj_conj]; ring
  rw [this, Complex.conj_im]

/-- The area of the triangle with sides `a₀, a₁` (and `a₂ = −a₀ − a₁`). -/
def area : ℝ := |(conj (side V 0) * side V 1).im| / 2

theorem area_is_half_J : area V = |jarlskog V| / 2 := by
  rw [area, cross_is_jarlskog, abs_neg]

theorem ckm_triangle_area {c12 s12 c23 s23 c13 s13 : ℝ} {u : ℂ}
    (r12 : c12^2 + s12^2 = 1) (r23 : c23^2 + s23^2 = 1) (r13 : c13^2 + s13^2 = 1)
    (hu : u * conj u = 1) :
    side (ckm c12 s12 c23 s23 c13 s13 u) 0 + side (ckm c12 s12 c23 s23 c13 s13 u) 1 +
        side (ckm c12 s12 c23 s23 c13 s13 u) 2 = 0 ∧
      area (ckm c12 s12 c23 s23 c13 s13 u) = |jarlskog (ckm c12 s12 c23 s23 c13 s13 u)| / 2 := by
  refine ⟨triangle_closes _ ?_, area_is_half_J _⟩
  have := ckm_unitary r12 r23 r13 hu 0 1
  simpa using this

end PMDynamics.UnitarityTriangle
