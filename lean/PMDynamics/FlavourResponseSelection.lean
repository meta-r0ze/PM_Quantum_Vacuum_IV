import PMDynamics.FlavourEvolution
import PMAction.CommonResponse

/-!
# What the existing comparison readout can see of flavour mixing

Apply Paper II's actual `stateFlag` to the supplied flavour evolution. A
weighted orthonormal flavour ensemble probes overlaps between preparation and
energy eigenmodes. For uniform weights it probes only the spectrum: its mean
flag rate is independent of every mixing angle and phase. Uniform preparation
over physical generations is not derived from uniformity of the sixteen packet
channels. Neither these weights nor an event price are selected here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.FlavourResponseSelection
open Matrix PMAction
abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def response (U : M) (energy : Fin 3 → ℝ) (t : ℝ) (a : Fin 3) : ℝ :=
  CommonResponse.stateFlag (FlavourEvolution.evolution U energy t) (Pi.single a 1)

def average (w : Fin 3 → ℝ) (U : M) (energy : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ a, w a * response U energy t a

theorem diagonal_real (U : M) (energy : Fin 3 → ℝ) (t : ℝ) (a : Fin 3) :
    (FlavourEvolution.evolution U energy t a a).re =
      ∑ i, Complex.normSq (U a i) * Real.cos (t * energy i) := by
  rw [FlavourEvolution.evolution, Matrix.mul_apply]
  simp only [LinkExpansion.phaseDiag, Matrix.mul_diagonal, conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : U a i * Complex.exp (((-t * energy i:ℝ):ℂ)*Complex.I) * star (U a i) =
      (U a i * star (U a i)) * Complex.exp (((-t * energy i:ℝ):ℂ)*Complex.I) := by ring
  rw [he, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re, neg_mul, Real.cos_neg]

theorem response_formula (U : M) (hu : U * Uᴴ=1) (energy : Fin 3 → ℝ)
    (t : ℝ) (a : Fin 3) :
    response U energy t a =
      (1 - ∑ i, Complex.normSq (U a i) * Real.cos (t * energy i))/2 := by
  rw [response, CommonResponse.basis_case _ (FlavourEvolution.evolution_unitary U energy hu t),
    InterferenceReadout.flag_formula _ (FlavourEvolution.evolution_unitary U energy hu t),
    diagonal_real]

theorem weighted_formula (w : Fin 3 → ℝ) (U : M) (hu : U * Uᴴ=1)
    (energy : Fin 3 → ℝ) (t : ℝ) :
    average w U energy t =
      ((∑ a, w a) - ∑ i, (∑ a, w a * Complex.normSq (U a i)) * Real.cos (t * energy i))/2 := by
  have hs : (∑ a, w a * ∑ i, Complex.normSq (U a i) * Real.cos (t * energy i)) =
      ∑ i, (∑ a, w a * Complex.normSq (U a i)) * Real.cos (t * energy i) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  calc
    _ = ((∑ a, w a) - ∑ a, w a * ∑ i, Complex.normSq (U a i) * Real.cos (t * energy i))/2 := by
      simp only [average, response_formula U hu, mul_div, mul_sub, mul_one]
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
    _ = _ := by rw [hs]

theorem column_norm (U : M) (hu : U * Uᴴ=1) (i : Fin 3) :
    ∑ a, Complex.normSq (U a i) = 1 := by
  have hu' : Uᴴ * U = 1 := mul_eq_one_comm.mp hu
  have hh := congrArg Complex.re (congrFun (congrFun hu' i) i)
  simpa [Matrix.mul_apply, conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self] using hh

theorem uniform_formula (U : M) (hu : U * Uᴴ=1) (energy : Fin 3 → ℝ) (t : ℝ) :
    average (fun _ => 1/3) U energy t = (∑ i : Fin 3, (1 - Real.cos (t * energy i)))/6 := by
  rw [weighted_formula _ U hu]
  simp only [← Finset.mul_sum, column_norm U hu, mul_one]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-- Uniform response costs tie at every tick, including for different mixing bases. -/
theorem uniform_tie (U V : M) (hu : U * Uᴴ=1) (hv : V * Vᴴ=1)
    (energy : Fin 3 → ℝ) (t : ℝ) :
    average (fun _ => 1/3) U energy t = average (fun _ => 1/3) V energy t := by
  rw [uniform_formula U hu, uniform_formula V hv]

end PMDynamics.FlavourResponseSelection
