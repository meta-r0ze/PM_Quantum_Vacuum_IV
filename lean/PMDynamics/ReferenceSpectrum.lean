import PMDynamics.ReferenceFlavour

/-!
# Exact ray persistence and the degeneracy boundary

Persistence here means staying on one complex ray at **every real time** under
the supplied diagonal phase evolution. It is stronger than recurrence at clock
samples, and weaker than selecting a unique vector in a degenerate eigenspace.
Neither the energy spectrum nor the physical reference is selected here.
-/

noncomputable section
namespace PMDynamics.ReferenceSpectrum
open Complex

def Persists {n : Type*} (energy : n → ℝ) (v : n → ℂ) : Prop :=
  ∀ t : ℝ, ∃ c : ℂ, ∀ i,
    v i * exp (-((energy i * t : ℝ) : ℂ) * I) = c * v i

/-- A nonzero state persists exactly iff its support lies in one energy eigenspace.
In particular, degeneracy permits superpositions; it does not select a basis vector. -/
theorem persists_iff_single_energy {n : Type*} (energy : n → ℝ) (v : n → ℂ)
    (hv : v ≠ 0) :
    Persists energy v ↔ ∃ E : ℝ, ∀ i, v i ≠ 0 → energy i = E := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    exact ⟨energy j, fun i hi => ReferenceFlavour.persistent_single_frequency energy v h i j hi hj⟩
  · rintro ⟨E, hE⟩ t
    refine ⟨exp (-((E * t : ℝ) : ℂ) * I), fun i => ?_⟩
    by_cases hi : v i = 0
    · simp [hi]
    · rw [hE i hi, mul_comm]

/-- For a simple spectrum a persisting nonzero state occupies exactly one slot. -/
theorem simple_spectrum_single_slot {n : Type*} [DecidableEq n]
    (energy : n → ℝ) (hs : Function.Injective energy) (v : n → ℂ)
    (hv : v ≠ 0) (h : Persists energy v) :
    ∃ j, v j ≠ 0 ∧ v = v j • Pi.single j 1 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  refine ⟨j, hj, ?_⟩
  ext i
  by_cases hij : i = j
  · subst i; simp
  · have hi : v i = 0 := by
      by_contra hi
      exact hij (hs (ReferenceFlavour.persistent_single_frequency energy v h i j hi hj))
    simp [hij, hi]

/-- A fully populated state persists iff all energies coincide. -/
theorem full_support_iff_constant {n : Type*} [Nonempty n]
    (energy : n → ℝ) (v : n → ℂ) (hv : ∀ i, v i ≠ 0) :
    Persists energy v ↔ ∃ E, ∀ i, energy i = E := by
  have hn : v ≠ 0 := by
    intro h
    exact hv (Classical.arbitrary n) (congrFun h _)
  rw [persists_iff_single_energy energy v hn]
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E, fun i => hE i (hv i)⟩
  · rintro ⟨E, hE⟩
    exact ⟨E, fun i _ => hE i⟩

/-- A sufficient no-aliasing condition closes the sampled-to-continuous bridge.
The occupied tick phases must lie in one principal energy band. This band is
an explicit hypothesis, not a consequence of finiteness or unitarity. -/
theorem one_tick_iff_of_band {n : Type*} (energy : n → ℝ) (v : n → ℂ)
    (hv : v ≠ 0) (tick : ℝ) (ht : tick ≠ 0)
    (hband : ∀ i, v i ≠ 0 → -Real.pi ≤ energy i * tick ∧ energy i * tick < Real.pi) :
    (∃ c : ℂ, ∀ i, v i * exp (-((energy i * tick : ℝ) : ℂ) * I) = c * v i) ↔
      Persists energy v := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    apply (persists_iff_single_energy energy v hv).mpr
    refine ⟨energy j, fun i hi => ?_⟩
    have ei : exp (-((energy i * tick : ℝ) : ℂ) * I) = c :=
      mul_left_cancel₀ hi (by rw [hc i, mul_comm])
    have ej : exp (-((energy j * tick : ℝ) : ℂ) * I) = c :=
      mul_left_cancel₀ hj (by rw [hc j, mul_comm])
    have bi := hband i hi
    have bj := hband j hj
    have hz := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (x := -((energy i * tick : ℝ) : ℂ) * I)
      (y := -((energy j * tick : ℝ) : ℂ) * I)
      (by simpa using (neg_lt_neg bi.2)) (by simpa using (neg_le_neg bi.1))
      (by simpa using (neg_lt_neg bj.2)) (by simpa using (neg_le_neg bj.1))
      (ei.trans ej.symm)
    have hm := congrArg Complex.im hz
    have he : energy i * tick = energy j * tick := by simpa using congrArg Neg.neg hm
    exact mul_right_cancel₀ ht he
  · intro h
    exact h tick

/-- Every charged-flavour row of the supplied PMNS matrix has full support.
It therefore cannot be a stationary reference unless the supplied energies are all equal. -/
theorem pmns_flavour_persists_iff (energy : Fin 3 → ℝ) (a : Fin 3) :
    Persists energy (fun i => star (PMNS.matrix a i)) ↔ ∃ E, ∀ i, energy i = E := by
  apply full_support_iff_constant
  intro i
  simpa using GenerationBreaking.pmns_all_nonzero a i

/-- Tick samples alone do not justify single-frequency selection: energies 0 and
`2π` agree in phase at every integer tick, although their superposition beats
between ticks. The unit tick here is just a choice of time units. -/
theorem sampled_aliasing :
    (∀ t : ℤ, ∃ c : ℂ, ∀ i : Fin 2,
      exp (-(((![0, 2 * Real.pi] : Fin 2 → ℝ) i * (t : ℝ) : ℝ) : ℂ) * I) = c) ∧
    ¬ Persists (![0, 2 * Real.pi] : Fin 2 → ℝ) (fun _ => (1 : ℂ)) := by
  constructor
  · intro t
    refine ⟨1, fun i => ?_⟩
    fin_cases i
    · simp
    · change exp (-(((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * I) = 1
      have he : -(((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * I =
          ((-t : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
      rw [he, exp_int_mul, exp_two_pi_mul_I, one_zpow]
  · intro h
    have he := ReferenceFlavour.persistent_single_frequency
      (![0, 2 * Real.pi] : Fin 2 → ℝ) (fun _ => (1 : ℂ)) h 0 1 one_ne_zero one_ne_zero
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
    linarith [Real.pi_pos]

end PMDynamics.ReferenceSpectrum
