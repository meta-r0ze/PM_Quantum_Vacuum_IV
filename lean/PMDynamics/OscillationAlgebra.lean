import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! Three-component interference algebra, independent of every earlier paper.
Coefficients, phases and a squared-amplitude readout are supplied. No physical
mass spectrum, preparation, baseline or interaction is selected here. -/
noncomputable section
namespace PMDynamics.OscillationAlgebra

/-- Unit complex phase, expressed trigonometrically for exact interference. -/
def phase (x : ℝ) : ℂ := ⟨Real.cos x, Real.sin x⟩

theorem phase_exp (x : ℝ) : phase x = Complex.exp ((x : ℂ)*Complex.I) := by
  apply Complex.ext <;> simp [phase]

theorem phase_norm (x : ℝ) : Complex.normSq (phase x)=1 := by
  simpa [phase, Complex.normSq_apply, pow_two] using Real.cos_sq_add_sin_sq x

theorem phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  rw [phase_exp,phase_exp,phase_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_phase (z : ℂ) (x : ℝ) : Complex.normSq (z*phase x)=Complex.normSq z := by
  rw [Complex.normSq_mul, phase_norm, mul_one]

/-- Three outgoing amplitude coefficients with arbitrary real phases. -/
def probability (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) : ℝ :=
  Complex.normSq (∑ i, z i*phase (θ i))

def quartet (z : Fin 3 → ℂ) (i j : Fin 3) : ℂ := z i*star (z j)

theorem norm_three (a b c : ℂ) :
    Complex.normSq (a+b+c) = Complex.normSq a+Complex.normSq b+Complex.normSq c+
      2*((a*star b).re+(a*star c).re+(b*star c).re) := by
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

theorem pair_interference (a b : ℂ) (x y : ℝ) :
    (a*phase x*star (b*phase y)).re =
      (a*star b).re*Real.cos (x-y)-(a*star b).im*Real.sin (x-y) := by
  simp [phase, Complex.mul_re, Complex.mul_im, Real.cos_sub, Real.sin_sub]
  ring

def interference (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (quartet z i j).re*Real.cos (θ i-θ j) -
    (quartet z i j).im*Real.sin (θ i-θ j)

/-- The complete three-state cosine/sine formula; no unitarity is assumed. -/
theorem expanded (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) :
    probability z θ = (∑ i, Complex.normSq (z i))+
      2*(interference z θ 0 1+interference z θ 0 2+interference z θ 1 2) := by
  simp only [probability, Fin.sum_univ_three, norm_three, norm_phase,
    pair_interference, interference, quartet]

/-- The standard squared-sine pair contribution. The sign of the imaginary
term follows the signed phases supplied to `probability`. -/
def relativeInterference (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  -4*(quartet z i j).re*Real.sin ((θ i-θ j)/2)^2-
    2*(quartet z i j).im*Real.sin (θ i-θ j)

theorem squared_sine_form (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) :
    probability z θ = Complex.normSq (∑ i, z i)+
      relativeInterference z θ 0 1+relativeInterference z θ 0 2+
      relativeInterference z θ 1 2 := by
  have hc (x : ℝ) : Real.cos x=1-2*Real.sin (x/2)^2 := by
    have h := Real.cos_two_mul (x/2)
    have hs := Real.sin_sq_add_cos_sq (x/2)
    rw [show 2*(x/2)=x by ring] at h
    nlinarith
  simp only [expanded,interference,relativeInterference,Fin.sum_univ_three,norm_three,hc,
    quartet]
  ring

/-- A common phase cannot change an interference probability. -/
theorem common_phase (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) (c : ℝ) :
    probability z (fun i => θ i+c)=probability z θ := by
  have hs (i j : Fin 3) : (θ i+c)-(θ j+c)=θ i-θ j := by ring
  simp only [expanded, interference,hs]

/-- Complex conjugation changes the sign of the CP-odd interference terms. -/
theorem conjugate_difference (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) :
    probability z θ-probability (fun i => star (z i)) θ =
      -4*((quartet z 0 1).im*Real.sin (θ 0-θ 1)+
          (quartet z 0 2).im*Real.sin (θ 0-θ 2)+
          (quartet z 1 2).im*Real.sin (θ 1-θ 2)) := by
  simp only [expanded, interference, quartet, Fin.sum_univ_three]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Conjugating coefficients and reversing all phases leaves probability unchanged. -/
theorem conjugate_reverse (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ) :
    probability (fun i => star (z i)) (fun i => -θ i)=probability z θ := by
  have hp (x : ℝ) : phase (-x)=star (phase x) := by
    apply Complex.ext <;> simp [phase]
  simp only [probability, hp]
  have he : (∑ i, star (z i)*star (phase (θ i))) = star (∑ i, z i*phase (θ i)) := by
    simp only [star_sum,star_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact Complex.normSq_conj _

/-- Real pair quartets imply no conjugation asymmetry in this model. -/
theorem real_quartets_no_asymmetry (z : Fin 3 → ℂ) (θ : Fin 3 → ℝ)
    (h01 : (quartet z 0 1).im=0) (h02 : (quartet z 0 2).im=0)
    (h12 : (quartet z 1 2).im=0) :
    probability z θ=probability (fun i => star (z i)) θ := by
  have h := conjugate_difference z θ
  simp only [h01,h02,h12,zero_mul,zero_add,mul_zero] at h
  linarith

/-- Degenerate eigenphases give the initial coherent probability. -/
theorem equal_phases (z : Fin 3 → ℂ) (c : ℝ) :
    probability z (fun _ => c)=Complex.normSq (∑ i, z i) := by
  unfold probability
  rw [← Finset.sum_mul, norm_phase]

end PMDynamics.OscillationAlgebra
