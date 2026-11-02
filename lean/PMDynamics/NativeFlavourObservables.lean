import PMDynamics.NativeFlavourPropagation
import PMDynamics.PropagationStability
import PMDynamics.CPObservables

/-! Interference, conjugation asymmetry and error bounds for the prepared native
wall modes. Preparation, the complete flavour basis, eigenenergy identification
and the conjugate-mixing vacuum prescription remain explicit. No matter effect,
measured mass or dynamical angle-selection law is added. -/
noncomputable section
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
namespace PMDynamics.NativeFlavourObservables
open Matrix PMAction NativeFlavourWall NativeFlavourPropagation OscillationObservables
variable (c : Fin 3) {f r : Type*} [Fintype f] [DecidableEq f] [Fintype r] [DecidableEq r]

def probability (p : ℝ) (k : Fin 3 → ℝ) (δ : ℝ) (Y : Matrix f f ℂ)
    (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ) (U : FlavourCurrent.M)
    (t : ℝ) (a b : Fin 3) : ℝ :=
  Complex.normSq (((frame c Ψ ρ U)ᴴ * evolve (r := r) c p k δ Y t * frame c Ψ ρ U) a b)

variable (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (k : Fin 3 → ℝ) (δ : ℝ)
  (Y : Matrix f f ℂ) (Ψ : Matrix (Modes (f := f)) (Fin 3) ℂ) (ρ : r → ℂ)
  (E : Fin 3 → ℝ)
  (he : ∀ j, WallExchange.H (momentum k) δ Y *ᵥ (fun x => Ψ x j) = (E j : ℂ) • (fun x => Ψ x j))
  (hΨ : Ψᴴ * Ψ = 1) (hρ : ∑ j, star (ρ j) * ρ j = 1)
include hp hp1 he hΨ hρ

theorem probability_eq (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) (a b : Fin 3) :
    probability c p k δ Y Ψ ρ U t a b = FlavourEvolution.probability U E t a b :=
  NativeFlavourPropagation.probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU t a b

theorem squared_sine (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (t : ℝ) (a b : Fin 3) :
    probability c p k δ Y Ψ ρ U t a b = (if a=b then 1 else 0) +
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 0 1 +
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 0 2 +
      OscillationAlgebra.relativeInterference (coefficients U a b) (phases E t) 1 2 := by
  rw [probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU]
  exact OscillationObservables.unitary_squared_sine U hU E t a b

theorem conjugation_asymmetry (U : FlavourCurrent.M) (hU : U * Uᴴ = 1)
    (t : ℝ) (a b : Fin 3) (hab : a ≠ b) :
    probability c p k δ Y Ψ ρ U t a b - probability c p k δ Y Ψ ρ (conjugated U) t a b =
      16 * (OscillationAlgebra.quartet (coefficients U a b) 0 1).im *
        Real.sin (t*(E 0-E 1)/2) * Real.sin (t*(E 1-E 2)/2) * Real.sin (t*(E 0-E 2)/2) := by
  have hu : conjugated U * (conjugated U)ᴴ = 1 := by
    ext i j
    have hh := congrArg star (congrFun (congrFun hU i) j)
    simpa [conjugated, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using hh
  rw [probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU,
    probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ (conjugated U) hu]
  exact CPObservables.factored_asymmetry U hU E t a b hab

theorem energy_error (U : FlavourCurrent.M) (hU : U * Uᴴ = 1) (F : Fin 3 → ℝ)
    (offset t ε : ℝ) (hε : 0 ≤ ε) (hF : ∀ i, |(E i-offset)-F i| ≤ ε) (a b : Fin 3) :
    |probability c p k δ Y Ψ ρ U t a b - FlavourEvolution.probability U F t a b| ≤
      2 * |t| * ε := by
  rw [probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU]
  exact PropagationStability.energy_error U hU E F offset t ε hε hF a b

theorem wall_light_error (U : FlavourCurrent.M) (hU : U * Uᴴ = 1)
    (q t B : ℝ) (hq : 0 < q) (hB : 0 ≤ B) (hY : Y.IsHermitian)
    (index : Fin 3 → f) (hlink : ∀ i, hY.eigenvalues (index i) ≠ 0)
    (hE : E = fun i => WallDispersion.Eb ![q,0,0] δ
      (WallDispersion.rhoM δ (hY.eigenvalues (index i))))
    (hm : ∀ i, (WallDispersion.massSqM δ (hY.eigenvalues (index i)))^2 ≤ B) (a b : Fin 3) :
    |probability c p k δ Y Ψ ρ U t a b -
      FlavourEvolution.probability U (fun i => WallDispersion.massSqM δ (hY.eigenvalues (index i))/(2*q)) t a b| ≤
        |t| * B/(4*q^3) := by
  rw [probability_eq c p hp hp1 k δ Y Ψ ρ E he hΨ hρ U hU, hE]
  exact PropagationStability.wall_light_probability_error U hU q t δ B hq hB (fun i => hY.eigenvalues (index i)) hlink hm a b

end PMDynamics.NativeFlavourObservables
