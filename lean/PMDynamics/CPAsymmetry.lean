import PMDynamics.OscillationAlgebra

/-! Fully factored three-state conjugation asymmetry. Independent of all
earlier papers. Closure is supplied by row orthogonality in the application;
real phases and the squared-amplitude readout remain model inputs. -/
noncomputable section
namespace PMDynamics.CPAsymmetry
open OscillationAlgebra

/-- Orthogonal distinct rows give a closed complex coefficient triangle. -/
theorem closed_quartets (z : Fin 3 → ℂ) (hz : z 0+z 1+z 2=0) :
    (quartet z 0 2).im=-(quartet z 0 1).im ∧
    (quartet z 1 2).im=(quartet z 0 1).im := by
  have h2 : z 2= -z 0-z 1 := by linear_combination hz
  rw [show quartet z 0 2=z 0*star (-z 0-z 1) by rw [← h2]; rfl,
      show quartet z 1 2=z 1*star (-z 0-z 1) by rw [← h2]; rfl]
  simp [quartet,Complex.mul_im]
  constructor <;> ring

/-- The scalar trigonometric factor; no matrix assumptions enter. -/
theorem sine_factor (a b : ℝ) :
    Real.sin a+Real.sin b-Real.sin (a+b)=
      4*Real.sin (a/2)*Real.sin (b/2)*Real.sin ((a+b)/2) := by
  have hs : Real.sin (a+b)=2*Real.sin ((a+b)/2)*Real.cos ((a+b)/2) := by
    simpa only [show 2*((a+b)/2)=a+b by ring] using Real.sin_two_mul ((a+b)/2)
  have hc : Real.cos ((a-b)/2)-Real.cos ((a+b)/2)=
      2*Real.sin (a/2)*Real.sin (b/2) := by
    rw [show (a-b)/2=a/2-b/2 by ring,show (a+b)/2=a/2+b/2 by ring,
      Real.cos_sub,Real.cos_add]
    ring
  rw [Real.sin_add_sin,hs]
  linear_combination (2*Real.sin ((a+b)/2))*hc

/-- Exact factorization, with the sign fixed by `exp(+i theta)` in the
independent amplitude definition. Physical phases are theta_i=-t E_i. -/
theorem factored (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) (hz : z 0+z 1+z 2=0) :
    probability z θ-probability (fun i => star (z i)) θ =
      -16*(quartet z 0 1).im * Real.sin ((θ 0-θ 1)/2)*
        Real.sin ((θ 1-θ 2)/2)*Real.sin ((θ 0-θ 2)/2) := by
  rw [conjugate_difference,(closed_quartets z hz).1,(closed_quartets z hz).2]
  have hs := sine_factor (θ 0-θ 1) (θ 1-θ 2)
  rw [show θ 0-θ 1+(θ 1-θ 2)=θ 0-θ 2 by ring] at hs
  linear_combination (-4*(quartet z 0 1).im)*hs

/-- A nonzero CP quartet alone is insufficient: equal eigenphases kill the
three-state asymmetry even when that quartet is nonzero. -/
theorem equal_pair_no_asymmetry (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ)
    (hz : z 0+z 1+z 2=0)
    (hθ : θ 0=θ 1 ∨ θ 1=θ 2 ∨ θ 0=θ 2) :
    probability z θ=probability (fun i => star (z i)) θ := by
  have h := factored z θ hz
  rcases hθ with hθ | hθ | hθ <;> rw [hθ] at h <;>
    simp only [sub_self,zero_div,Real.sin_zero,mul_zero,zero_mul] at h <;>
    exact sub_eq_zero.mp h

/-- Conversely, all four nonzero factors give a nonzero asymmetry. -/
theorem nonzero_factors (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) (hz : z 0+z 1+z 2=0)
    (hJ : (quartet z 0 1).im ≠ 0)
    (h01 : Real.sin ((θ 0-θ 1)/2) ≠ 0)
    (h12 : Real.sin ((θ 1-θ 2)/2) ≠ 0)
    (h02 : Real.sin ((θ 0-θ 2)/2) ≠ 0) :
    probability z θ ≠ probability (fun i => star (z i)) θ := by
  apply sub_ne_zero.mp
  rw [factored z θ hz]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hJ) h01) h12) h02

/-- A concrete phase choice gives a direct nonzero witness whenever the
closed triangle has a nonzero quartet. It selects no physical energy spectrum. -/
theorem quarter_cycle (z : Fin 3 → ℂ) (hz : z 0+z 1+z 2=0) :
    probability z ![0,-Real.pi/2,-Real.pi]-
      probability (fun i => star (z i)) ![0,-Real.pi/2,-Real.pi] =
        -8*(quartet z 0 1).im := by
  rw [conjugate_difference,(closed_quartets z hz).1,(closed_quartets z hz).2]
  have h01 : (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 0-
      (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 1=Real.pi/2 := by simp; ring
  have h02 : (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 0-
      (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 2=Real.pi := by simp
  have h12 : (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 1-
      (![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) 2=Real.pi/2 := by simp; ring
  rw [h01,h02,h12,Real.sin_pi_div_two,Real.sin_pi]
  ring

end PMDynamics.CPAsymmetry
