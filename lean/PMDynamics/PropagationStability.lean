import PMDynamics.OscillationStability
import PMDynamics.PropagationEnergy
import PMDynamics.WallSpectrumLink

/-! Observable error control for the supplied relativistic flavour model.
Unitarity supplies normalization; no measured masses, baseline, or fitted angle
enters these results. The approximation concerns exponential vacuum evolution,
not an arbitrary microscopic finite-tick update. -/
noncomputable section
namespace PMDynamics.PropagationStability
open Matrix OscillationObservables

/-- Cauchy-Schwarz supplies the coefficient normalization from row unitarity. -/
theorem coefficients_normalized (U : M) (hU : U*Uᴴ=1) (a b : Fin 3) :
    ∑ i, ‖coefficients U a b i‖ ≤ 1 := by
  have hr (r : Fin 3) : ∑ i, ‖U r i‖^2 = 1 := by
    have h := congrArg (fun A : M => (A r r).re) hU
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,← Complex.ofReal_pow] using h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖U a i‖) (fun i => ‖U b i‖)
  simp only [hr,mul_one] at hc
  have hs : (∑ i, ‖coefficients U a b i‖)^2 ≤ 1 := by
    simpa only [coefficients,norm_mul,norm_star] using hc
  have hn : 0 ≤ ∑ i, ‖coefficients U a b i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith

/-- Common energy offsets are removed exactly. A uniform remaining energy
error ε changes each transition probability by at most 2|t|ε. -/
theorem energy_error (U : M) (hU : U*Uᴴ=1) (E F : Fin 3 → ℝ)
    (c t ε : ℝ) (hε : 0 ≤ ε) (h : ∀ i, |(E i-c)-F i| ≤ ε) (a b : Fin 3) :
    |FlavourEvolution.probability U E t a b-FlavourEvolution.probability U F t a b| ≤
      2*|t| *ε := by
  have hoff : FlavourEvolution.probability U E t a b=
      FlavourEvolution.probability U (fun i => E i-c) t a b := by
    have hh := OscillationObservables.energy_shift U (fun i => E i-c) c t a b
    simpa only [sub_add_cancel] using hh
  rw [hoff,probability_bridge,probability_bridge]
  rw [show 2*|t| *ε=2*(|t| *ε) by ring]
  apply OscillationStability.probability_error_uniform _ (coefficients_normalized U hU a b)
    _ _ (|t| *ε) (mul_nonneg (abs_nonneg _) hε)
  intro i
  change |(-t*(E i-c))-(-t*F i)| ≤ |t| *ε
  rw [show (-t*(E i-c))-(-t*F i)=(-t)*((E i-c)-F i) by ring,abs_mul,abs_neg]
  exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

/-- Quantitative error in replacing √(p²+mᵢ²) by mᵢ²/(2p), after removing the
unobservable common p. B is any uniform bound on mᵢ⁴; the inequality holds for
all positive p and all real times, whether or not the bound is small. -/
theorem relativistic_probability_error (U : M) (hU : U*Uᴴ=1)
    (p t B : ℝ) (hp : 0<p) (hB : 0 ≤ B) (m : Fin 3 → ℝ)
    (hm : ∀ i, m i^4 ≤ B) (a b : Fin 3) :
    |FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b-
      FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b| ≤
      |t| *B/(4*p^3) := by
  have he (i : Fin 3) :
      |(RelativisticPhase.energy p (m i)-p)-m i^2/(2*p)| ≤ B/(8*p^3) := by
    have hr := RelativisticPhase.remainder_bounds p (m i) hp
    rw [abs_of_nonpos (by linarith :
      (RelativisticPhase.energy p (m i)-p)-m i^2/(2*p) ≤ 0)]
    have hb := (div_le_div_iff_of_pos_right (by positivity : 0<8*p^3)).mpr (hm i)
    linarith
  have h := energy_error U hU (fun i => RelativisticPhase.energy p (m i))
    (fun i => m i^2/(2*p)) p t (B/(8*p^3)) (by positivity) he a b
  convert h using 1
  ring

/-- The corresponding error in the vacuum conjugation asymmetry is at most
twice the transition-probability error. Conjugation is the model's supplied
antineutrino prescription, not a derivation of the physical interaction. -/
theorem relativistic_asymmetry_error (U : M) (hU : U*Uᴴ=1)
    (p t B : ℝ) (hp : 0<p) (hB : 0 ≤ B) (m : Fin 3 → ℝ)
    (hm : ∀ i, m i^4 ≤ B) (a b : Fin 3) :
    |(FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b-
        FlavourEvolution.probability (conjugated U) (fun i => RelativisticPhase.energy p (m i)) t a b)-
      (FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b-
        FlavourEvolution.probability (conjugated U) (fun i => m i^2/(2*p)) t a b)| ≤
      |t| *B/(2*p^3) := by
  rw [conjugation_time,conjugation_time]
  have hpos := relativistic_probability_error U hU p t B hp hB m hm a b
  have hneg := relativistic_probability_error U hU p (-t) B hp hB m hm a b
  simp only [abs_neg] at hneg
  have ht := abs_sub
    (FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b-
      FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b)
    (FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) (-t) a b-
      FlavourEvolution.probability U (fun i => m i^2/(2*p)) (-t) a b)
  rw [show (FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b-
        FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) (-t) a b)-
      (FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b-
        FlavourEvolution.probability U (fun i => m i^2/(2*p)) (-t) a b)=
      (FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) t a b-
        FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b)-
      (FlavourEvolution.probability U (fun i => RelativisticPhase.energy p (m i)) (-t) a b-
        FlavourEvolution.probability U (fun i => m i^2/(2*p)) (-t) a b) by ring]
  calc
    _ ≤ 2*(|t| *B/(4*p^3)) := by linarith
    _ = _ := by ring

/-- The same probability bound for supplied on-shell eigenstates of Paper II's
concrete Clifford Hamiltonian. No extra assumption about their energies is used. -/
theorem eigenstate_probability_error (U : M) (hU : U*Uᴴ=1)
    (p t B : ℝ) (hp : 0<p) (hB : 0 ≤ B) (m E : Fin 3 → ℝ)
    (hm : ∀ i, m i^4 ≤ B) (v : Fin 3 → Fin 4 → ℂ) (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, PMAction.Dirac.H PMAction.ConcreteFermion.alpha PMAction.ConcreteFermion.beta
      ![p,0,0] (m i) *ᵥ v i=E i • v i) (hE : ∀ i, 0 ≤ E i) (a b : Fin 3) :
    |FlavourEvolution.probability U E t a b-
      FlavourEvolution.probability U (fun i => m i^2/(2*p)) t a b| ≤
      |t| *B/(4*p^3) := by
  rw [PropagationEnergy.eigenstate_energies p m E v hv he hE]
  exact relativistic_probability_error U hU p t B hp hB m hm a b

/-- Apply the bound to the exact light-branch energies of the supplied wall
links. The approximating phases use the derived seesaw masses, not a separately
inserted tower. Selecting links, occupied states and readout is still required. -/
theorem wall_light_probability_error (U : M) (hU : U*Uᴴ=1)
    (p t δ B : ℝ) (hp : 0<p) (hB : 0 ≤ B) (y : Fin 3 → ℝ)
    (hy : ∀ i, y i ≠ 0) (hm : ∀ i, (PMAction.WallDispersion.massSqM δ (y i))^2 ≤ B)
    (a b : Fin 3) :
    |FlavourEvolution.probability U
        (fun i => PMAction.WallDispersion.Eb ![p,0,0] δ (PMAction.WallDispersion.rhoM δ (y i))) t a b-
      FlavourEvolution.probability U
        (fun i => PMAction.WallDispersion.massSqM δ (y i)/(2*p)) t a b| ≤
      |t| *B/(4*p^3) := by
  have hs (i : Fin 3) : (Real.sqrt (PMAction.WallDispersion.massSqM δ (y i)))^2=
      PMAction.WallDispersion.massSqM δ (y i) :=
    Real.sq_sqrt (PMAction.WallDispersion.branch_masses δ (y i) (hy i)).2.2.2
  have hfour (i : Fin 3) : (Real.sqrt (PMAction.WallDispersion.massSqM δ (y i)))^4 ≤ B := by
    calc
      _ = ((Real.sqrt (PMAction.WallDispersion.massSqM δ (y i)))^2)^2 := by ring
      _ ≤ B := by rw [hs]; exact hm i
  simpa only [hs,← fun i => (WallSpectrumLink.wall_energies p δ (y i) (hy i)).2] using
    relativistic_probability_error U hU p t B hp hB
      (fun i => Real.sqrt (PMAction.WallDispersion.massSqM δ (y i))) hfour a b

end PMDynamics.PropagationStability
