import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Normalization checks for the proposed mixing construction and uniform
amplitude dressing. Geometric angle choices remain model inputs. -/
noncomputable section
namespace PMDynamics
open Finset

theorem first_row_normalized (c12 s12 c13 s13 : ℝ)
    (h12 : c12^2+s12^2=1) (h13 : c13^2+s13^2=1) :
    (c12*c13)^2+(s12*c13)^2+s13^2=1  := by
  calc
    (c12*c13)^2+(s12*c13)^2+s13^2 = (c12^2+s12^2)*c13^2+s13^2 := by ring
    _ = 1 := by rw [h12, one_mul, h13]

def dressing : ℝ := Real.sqrt (1-1/688)

theorem dressing_squared : dressing^2 = 687/688 := by
  rw [dressing, Real.sq_sqrt (by norm_num)]
  norm_num

def rowMass {ι : Type*} [Fintype ι] (row : ι → ℂ) : ℝ := ∑ i, Complex.normSq (row i)

theorem dressed_row_mass {ι : Type*} [Fintype ι] (q : ℝ) (row : ι → ℂ) :
    rowMass (fun i => (q : ℂ)*row i) = q^2*rowMass row := by
  simp only [rowMass, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← mul_sum]
  ring

/-- Uniform dressing is a visible-channel probability loss, not a unitary 3×3 change. -/
theorem dressed_normalization_deficit {ι : Type*} [Fintype ι] (row : ι → ℂ)
    (h : rowMass row = 1) :
    rowMass (fun i => (dressing : ℂ)*row i) = 687/688 ∧
    rowMass (fun i => (dressing : ℂ)*row i) ≠ 1 := by
  rw [dressed_row_mass, h, mul_one, dressing_squared]
  norm_num

theorem missing_outcome_restores_total : (687 : ℝ)/688 + 1/688 = 1 := by norm_num

def quartet (a b c d : ℂ) : ℝ := (a*b*star c*star d).im

theorem quartet_dressing (q : ℝ) (a b c d : ℂ) :
    quartet ((q:ℂ)*a) ((q:ℂ)*b) ((q:ℂ)*c) ((q:ℂ)*d) = q^4*quartet a b c d := by
  simp [quartet, Complex.mul_re, Complex.mul_im]
  ring

/-- A modulus table alone does not specify CP-violating phases. -/
theorem equal_modulus_opposite_imaginary :
    Complex.normSq Complex.I = Complex.normSq (-Complex.I) ∧
      Complex.I.im ≠ (-Complex.I).im := by norm_num

end PMDynamics
