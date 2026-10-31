import PMDynamics.CPAsymmetry
import PMDynamics.OscillationObservables
import PMDynamics.PMNSIntervals

/-! Exact vacuum three-flavour conjugation asymmetry for the existing finite
propagator. Orthogonality supplies coefficient closure; energies, time and the
conjugate-mixing antineutrino rule are inputs. Matter effects are not included. -/
noncomputable section
namespace PMDynamics.CPObservables
open Matrix
open OscillationAlgebra OscillationObservables

lemma coefficients_closed (U : M) (hU : U*Uᴴ=1) (a b : Fin 3) (hab : a ≠ b) :
    coefficients U a b 0+coefficients U a b 1+coefficients U a b 2=0 := by
  have h := congrArg (fun A : M => A a b) hU
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,hab,
    coefficients,Fin.sum_univ_three] using h

lemma coefficients_conjugated (U : M) (a b : Fin 3) :
    coefficients (conjugated U) a b=fun i => star (coefficients U a b i) := by
  funext i
  simp [coefficients,conjugated]

/-- All three half-energy gaps, including the orientation/sign convention. -/
theorem factored_asymmetry (U : M) (hU : U*Uᴴ=1) (E : Fin 3 → ℝ)
    (t : ℝ) (a b : Fin 3) (hab : a ≠ b) :
    FlavourEvolution.probability U E t a b-
      FlavourEvolution.probability (conjugated U) E t a b =
        16*(OscillationAlgebra.quartet (coefficients U a b) 0 1).im *
          Real.sin (t*(E 0-E 1)/2)*Real.sin (t*(E 1-E 2)/2)*Real.sin (t*(E 0-E 2)/2) := by
  rw [probability_bridge,probability_bridge,coefficients_conjugated,
    CPAsymmetry.factored _ _ (coefficients_closed U hU a b hab)]
  have hp (i j : Fin 3) : (phases E t i-phases E t j)/2= -(t*(E i-E j)/2) := by
    unfold phases
    ring
  simp only [hp,Real.sin_neg]
  ring

/-- The 0→1 appearance quartet is exactly the matrix Jarlskog convention. -/
theorem quartet_jarlskog (U : M) : (OscillationAlgebra.quartet (coefficients U 0 1) 0 1).im=CKM.jarlskog U := by
  have h : OscillationAlgebra.quartet (coefficients U 0 1) 0 1=
      U 0 0*U 1 1*star (U 0 1)*star (U 1 0) := by
    simp only [OscillationAlgebra.quartet,coefficients,star_mul,star_star]
    ring
  rw [h]
  rfl

/-- A degenerate pair kills the asymmetry in every channel of this vacuum
three-state model, even when the matrix Jarlskog invariant is nonzero. -/
theorem degenerate_pair_no_asymmetry (U : M) (hU : U*Uᴴ=1) (E : Fin 3 → ℝ)
    (t : ℝ) (a b : Fin 3) (hE : E 0=E 1 ∨ E 1=E 2 ∨ E 0=E 2) :
    FlavourEvolution.probability U E t a b=
      FlavourEvolution.probability (conjugated U) E t a b := by
  by_cases hab : a=b
  · subst b
    exact survival_no_asymmetry U E t a
  · apply sub_eq_zero.mp
    rw [factored_asymmetry U hU E t a b hab]
    rcases hE with hE | hE | hE <;> simp [hE]

/-- Nonzero PMNS J admits a nonzero vacuum asymmetry for an explicit supplied
spectrum and time. The spectrum is a mathematical witness, not a mass prediction. -/
theorem pmns_example :
    FlavourEvolution.probability PMNS.matrix ![0,1,2] (Real.pi/2) 0 1-
      FlavourEvolution.probability (conjugated PMNS.matrix) ![0,1,2] (Real.pi/2) 0 1 =
        -8*CKM.jarlskog PMNS.matrix := by
  rw [probability_bridge,probability_bridge,coefficients_conjugated]
  have hp : phases ![0,1,2] (Real.pi/2)=(![0,-Real.pi/2,-Real.pi] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> simp [phases]
    all_goals ring
  rw [hp,CPAsymmetry.quarter_cycle _ (coefficients_closed _ PMNS.rows 0 1 (by decide)),
    quartet_jarlskog]

theorem pmns_example_positive :
    0 < FlavourEvolution.probability PMNS.matrix ![0,1,2] (Real.pi/2) 0 1-
      FlavourEvolution.probability (conjugated PMNS.matrix) ![0,1,2] (Real.pi/2) 0 1 := by
  rw [pmns_example]
  nlinarith [PMNSIntervals.jarlskog_negative]

end PMDynamics.CPObservables
