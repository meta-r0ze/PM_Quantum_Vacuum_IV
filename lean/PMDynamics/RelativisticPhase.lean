import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Exact relativistic kinematics and controlled large-momentum phases.
Mathlib only: the energy law, common momentum and masses are supplied, not
identified with physical substrate eigenstates by this module. Units have c=1. -/
noncomputable section
namespace PMDynamics.RelativisticPhase

def energy (p m : ℝ) : ℝ := Real.sqrt (p^2+m^2)

theorem energy_square (p m : ℝ) : energy p m^2=p^2+m^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg p) (sq_nonneg m))

theorem energy_nonnegative (p m : ℝ) : 0 ≤ energy p m := Real.sqrt_nonneg _

theorem energy_ge_momentum (p m : ℝ) (hp : 0<p) : p ≤ energy p m := by
  have h := energy_square p m
  have hn := energy_nonnegative p m
  nlinarith [sq_nonneg m]

/-- Exact rationalization of the kinetic correction. -/
theorem excess_exact (p m : ℝ) (hp : 0<p) :
    energy p m-p=m^2/(energy p m+p) := by
  have hd : energy p m+p ≠ 0 := by have := energy_ge_momentum p m hp; linarith
  apply (eq_div_iff hd).mpr
  nlinarith [energy_square p m]

/-- Exact energy splitting, with no relativistic expansion. -/
theorem gap_exact (p a b : ℝ) (hp : 0<p) :
    energy p a-energy p b=(a^2-b^2)/(energy p a+energy p b) := by
  have hd : energy p a+energy p b ≠ 0 := by
    have := energy_ge_momentum p a hp
    have := energy_ge_momentum p b hp
    linarith
  apply (eq_div_iff hd).mpr
  nlinarith [energy_square p a,energy_square p b]

lemma excess_bounds (p m : ℝ) (hp : 0<p) :
    0 ≤ energy p m-p ∧ energy p m-p ≤ m^2/(2*p) := by
  have hE := energy_ge_momentum p m hp
  constructor
  · linarith
  · rw [excess_exact p m hp]
    apply (div_le_div_iff₀ (by linarith : 0<energy p m+p) (by linarith : 0<2*p)).mpr
    nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hE)]

/-- The Taylor remainder is an exact nonnegative square. -/
theorem remainder_exact (p m : ℝ) (hp : 0<p) :
    p+m^2/(2*p)-energy p m=(energy p m-p)^2/(2*p) := by
  have hn : p ≠ 0 := hp.ne'
  field_simp
  nlinarith [energy_square p m]

/-- Explicit fourth-order energy error, valid for every positive p; the
approximation is useful when |m|/p is small, but no such extra premise is needed. -/
theorem remainder_bounds (p m : ℝ) (hp : 0<p) :
    0 ≤ p+m^2/(2*p)-energy p m ∧
    p+m^2/(2*p)-energy p m ≤ m^4/(8*p^3) := by
  rw [remainder_exact p m hp]
  have h := excess_bounds p m hp
  constructor
  · positivity
  · have hs : (energy p m-p)^2 ≤ (m^2/(2*p))^2 :=
      pow_le_pow_left₀ h.1 h.2 2
    calc
      _ ≤ (m^2/(2*p))^2/(2*p) := (div_le_div_iff_of_pos_right (by positivity)).mpr hs
      _ = _ := by field_simp; ring

/-- Error in the splitting approximation ΔE ≈ Δm²/(2p). -/
theorem gap_error (p a b : ℝ) (hp : 0<p) :
    |(energy p a-energy p b)-(a^2-b^2)/(2*p)| ≤ (a^4+b^4)/(8*p^3) := by
  have ha := remainder_bounds p a hp
  have hb := remainder_bounds p b hp
  have h1 : 0 ≤ a^4/(8*p^3) := by positivity
  have h2 : 0 ≤ b^4/(8*p^3) := by positivity
  rw [add_div,sub_div]
  apply abs_le.mpr
  constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]

/-- Controlled half-phase used in the factored oscillation formula.
No identification of t with an experimental baseline is asserted. -/
theorem half_phase_error (p a b t : ℝ) (hp : 0<p) :
    |t*(energy p a-energy p b)/2-t*(a^2-b^2)/(4*p)| ≤
      |t| *(a^4+b^4)/(16*p^3) := by
  have h := mul_le_mul_of_nonneg_left (gap_error p a b hp) (abs_nonneg (t/2))
  have he : t*(energy p a-energy p b)/2-t*(a^2-b^2)/(4*p)=
      (t/2)*((energy p a-energy p b)-(a^2-b^2)/(2*p)) := by ring
  rw [he,abs_mul]
  calc
    _ ≤ |t/2| *((a^4+b^4)/(8*p^3)) := h
    _ = _ := by rw [abs_div]; norm_num; ring

end PMDynamics.RelativisticPhase
