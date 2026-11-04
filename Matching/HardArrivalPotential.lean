import Matching.HardUpperOneStep
import Matching.HardPoissonInstance
import Matching.PoissonArrivalIntegral
import Matching.EmpiricalTailBound

/-! The upper potential under the actual next-arrival distribution of the
hard Poisson instance. The payoff allows a match whenever the arriving
neighborhood intersects the current unmatched set. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

noncomputable def hardUnmatchedFraction (A : Finset ι) : ℝ := (A.card : ℝ) / Fintype.card ι

theorem hardUnmatchedFraction_bounds (A : Finset ι) :
    hardUnmatchedFraction A ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
      (Nat.cast_le.mpr (Finset.card_le_univ A))

theorem hardUnmatchedFraction_jump (A : Finset ι) (hA : A.Nonempty) :
    1 / (Fintype.card ι : ℝ) ≤ hardUnmatchedFraction A := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hA.card_pos

noncomputable def hardAfterFraction (A S : Finset ι) : ℝ :=
  if (S ∩ A).Nonempty then hardUnmatchedFraction A - 1 / Fintype.card ι
  else hardUnmatchedFraction A

theorem hardAfterFraction_bounds (A S : Finset ι) : hardAfterFraction A S ∈ Icc (0 : ℝ) 1 := by
  unfold hardAfterFraction
  split_ifs with hh
  · have hA : A.Nonempty := ⟨hh.choose, (Finset.mem_inter.mp hh.choose_spec).2⟩
    exact ⟨sub_nonneg.mpr (hardUnmatchedFraction_jump A hA),
      (sub_le_self _ (by positivity)).trans (hardUnmatchedFraction_bounds A).2⟩
  · exact hardUnmatchedFraction_bounds A

noncomputable def hardArrivalUpperPayoff (T : ℝ) (A : Finset ι) : Unit ⊕ (ℝ × Finset ι) → ℝ :=
  Sum.elim (fun _ => 1 - hardUnmatchedFraction A)
    (fun e => hardUpperPotential (max 0 (T - e.1)) (hardAfterFraction A e.2))

theorem hardArrivalUpperPayoff_measurable (T : ℝ) (A : Finset ι) :
    Measurable (hardArrivalUpperPayoff T A) := by
  apply measurable_const.sumElim
  apply measurable_from_prod_countable
  intro S
  exact ((continuous_hardUpperPotential_time (hardAfterFraction_bounds A S).1).comp
    (continuous_const.max (continuous_const.sub continuous_id))).measurable

theorem hardArrivalUpperPayoff_bounds (T : ℝ) (A : Finset ι) (e : Unit ⊕ (ℝ × Finset ι)) :
    0 ≤ hardArrivalUpperPayoff T A e ∧ hardArrivalUpperPayoff T A e ≤ 1 := by
  cases e with
  | inl _ => exact ⟨sub_nonneg.mpr (hardUnmatchedFraction_bounds A).2,
      sub_le_self _ (hardUnmatchedFraction_bounds A).1⟩
  | inr e => exact hardUpperPotential_bounds (le_max_left _ _) (hardAfterFraction_bounds A e.2)

theorem hardPoissonIntensity_hit_rate (A : Finset ι) :
    (∑ S : Finset ι, if (S ∩ A).Nonempty then (hardPoissonIntensity S : ℝ) else 0) =
      (Fintype.card ι : ℝ) * hardSuccessProbability (hardUnmatchedFraction A) := by
  change supplyCoverage id (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) A = _
  rw [hardPoissonIntensity_coverage, hardSuccessProbability, hardUnmatchedFraction]
  field_simp

theorem hardPoissonIntensity_payoff_sum (T : ℝ) (A : Finset ι) :
    (∑ S : Finset ι, (hardPoissonIntensity S : ℝ) * hardUpperPotential T (hardAfterFraction A S)) =
      (Fintype.card ι : ℝ) *
        ((1 - hardSuccessProbability (hardUnmatchedFraction A)) *
            hardUpperPotential T (hardUnmatchedFraction A) +
          hardSuccessProbability (hardUnmatchedFraction A) *
            hardUpperPotential T (hardUnmatchedFraction A - 1 / Fintype.card ι)) := by
  have he (S : Finset ι) :
      (hardPoissonIntensity S : ℝ) * hardUpperPotential T (hardAfterFraction A S) =
        (hardPoissonIntensity S : ℝ) * hardUpperPotential T (hardUnmatchedFraction A) +
          (if (S ∩ A).Nonempty then (hardPoissonIntensity S : ℝ) else 0) *
            (hardUpperPotential T (hardUnmatchedFraction A - 1 / Fintype.card ι) -
              hardUpperPotential T (hardUnmatchedFraction A)) := by
    unfold hardAfterFraction
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    hardPoissonIntensity_total, hardPoissonIntensity_hit_rate]
  ring

theorem hardPoisson_first_arrival_upper_bound {T : ℝ} (hT : 0 < T) (A : Finset ι) :
    (∫ e, hardArrivalUpperPayoff T A e
      ∂poissonNextArrival (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) T) ≤
        hardUpperPotential T (hardUnmatchedFraction A) := by
  let capacity := fun S : Finset ι => (hardPoissonIntensity S : ℝ)
  letI := poissonNextArrival_probability capacity (fun S => (hardPoissonIntensity S).coe_nonneg) T hT
  have hi : Integrable (hardArrivalUpperPayoff T A) (poissonNextArrival capacity T) :=
    integrable_of_abs_bounded _ (hardArrivalUpperPayoff_measurable T A) 1 (fun e => by
      rw [abs_of_nonneg (hardArrivalUpperPayoff_bounds T A e).1]
      exact (hardArrivalUpperPayoff_bounds T A e).2)
  by_cases hA : A.Nonempty
  · rw [poissonNextArrival_integral capacity (fun S => (hardPoissonIntensity S).coe_nonneg)
      hT.le _ (hardArrivalUpperPayoff_measurable T A) hi]
    change Real.exp (-((∑ S : Finset ι, (hardPoissonIntensity S : ℝ)) * T)) *
        (1 - hardUnmatchedFraction A) +
      (∑ S : Finset ι, ∫ t in (0 : ℝ)..T, (hardPoissonIntensity S : ℝ) *
        Real.exp (-(∑ U : Finset ι, (hardPoissonIntensity U : ℝ)) * t) *
          hardUpperPotential (max 0 (T - t)) (hardAfterFraction A S)) ≤ _
    simp only [hardPoissonIntensity_total]
    rw [← intervalIntegral.integral_finset_sum]
    · have he :
          (∫ t in (0 : ℝ)..T, ∑ S : Finset ι, (hardPoissonIntensity S : ℝ) *
            Real.exp (-(Fintype.card ι : ℝ) * t) *
              hardUpperPotential (max 0 (T - t)) (hardAfterFraction A S)) =
          ∫ t in (0 : ℝ)..T, Real.exp (-(Fintype.card ι : ℝ) * t) * (Fintype.card ι : ℝ) *
            ((1 - hardSuccessProbability (hardUnmatchedFraction A)) *
                hardUpperPotential (T - t) (hardUnmatchedFraction A) +
              hardSuccessProbability (hardUnmatchedFraction A) *
                hardUpperPotential (T - t) (hardUnmatchedFraction A - 1 / Fintype.card ι)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT.le] at ht
        dsimp only
        rw [max_eq_right (sub_nonneg.mpr ht.2)]
        have he (S : Finset ι) : (hardPoissonIntensity S : ℝ) * Real.exp (-(Fintype.card ι : ℝ) * t) *
            hardUpperPotential (T - t) (hardAfterFraction A S) =
            Real.exp (-(Fintype.card ι : ℝ) * t) *
              ((hardPoissonIntensity S : ℝ) * hardUpperPotential (T - t) (hardAfterFraction A S)) := by ring
        simp_rw [he]
        rw [← Finset.mul_sum, hardPoissonIntensity_payoff_sum]
        ring
      rw [he]
      simpa only [neg_mul] using hardUpper_one_step hT.le
        (Nat.cast_pos.mpr Fintype.card_pos) (hardUnmatchedFraction_bounds A)
        (hardUnmatchedFraction_jump A hA)
    · intro S _
      apply Continuous.intervalIntegrable
      have hc : Continuous (fun t : ℝ => hardUpperPotential (max 0 (T - t)) (hardAfterFraction A S)) :=
        (continuous_hardUpperPotential_time (hardAfterFraction_bounds A S).1).comp
        (continuous_const.max (continuous_const.sub continuous_id))
      exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hc
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    have hf (e : Unit ⊕ (ℝ × Finset ι)) : hardArrivalUpperPayoff T ∅ e = 1 := by
      cases e <;> simp [hardArrivalUpperPayoff, hardAfterFraction, hardUnmatchedFraction, hardUpperPotential_zero]
    simp_rw [hf]
    simp [hardUnmatchedFraction, hardUpperPotential_zero]

end StochasticMatching
