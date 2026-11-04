import Matching.HardControllerPotential

/-! Global upper bound for all admissible controllers on the hard Poisson
instance, for every finite truncation and the supremum of their rewards. -/
open MeasureTheory ProbabilityTheory Set
namespace StochasticMatching.PoissonOnlineController
variable {H ι : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
variable (P : PoissonOnlineController (H := H) (id : Finset ι → Finset ι) hardPoissonIntensity)

theorem hard_reward_measurable : Measurable P.reward :=
  measurable_const.sub ((measurable_of_countable (fun A : Finset ι => (A.card : ℝ))).comp P.remaining_measurable)

theorem hard_reward_bounds (x : ControllerState H ι) : 0 ≤ P.reward x ∧ P.reward x ≤ Fintype.card ι := by
  constructor
  · exact sub_nonneg.mpr (Nat.cast_le.mpr (Finset.card_le_univ _))
  · exact sub_le_self _ (Nat.cast_nonneg _)

theorem hard_reward_le_potential (x : ControllerState H ι) :
    P.reward x ≤ (Fintype.card ι : ℝ) * P.hardPotential x := by
  have hm : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he (A : Finset ι) : (Fintype.card ι : ℝ) - A.card =
      (Fintype.card ι : ℝ) * (1 - hardUnmatchedFraction A) := by
    unfold hardUnmatchedFraction
    field_simp
  cases x with
  | inl A => exact le_of_eq (he A)
  | inr h =>
      change (Fintype.card ι : ℝ) - (P.available h).card ≤ _
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (hardUpperPotential_ge_matched (P.horizon_pos h).le (hardUnmatchedFraction_bounds _))
        (Nat.cast_nonneg _)

theorem hard_scaled_potential_step (x : ControllerState H ι) :
    (∫ x', (Fintype.card ι : ℝ) * P.hardPotential x' ∂P.step x) ≤
      (Fintype.card ι : ℝ) * P.hardPotential x := by
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (P.hardPotential_step x) (Nat.cast_nonneg _)

theorem hard_expected_reward_le (h : H) :
    P.expectedReward h ≤ (Fintype.card ι : ℝ) * P.hardPotential (.inr h) := by
  apply kernelExpectedReward_le P.step
    (fun x => (Fintype.card ι : ℝ) * P.hardPotential x) P.reward
    (measurable_const.mul P.hardPotential_measurable) P.hard_reward_measurable
    (Fintype.card ι : ℝ) (Fintype.card ι : ℝ) _ _ P.hard_reward_le_potential P.hard_scaled_potential_step
  · intro x
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (P.hardPotential_bounds x).1)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (P.hardPotential_bounds x).2
  · intro x
    rw [abs_of_nonneg (P.hard_reward_bounds x).1]
    exact (P.hard_reward_bounds x).2

theorem hard_expected_reward_upper_bound (h : H)
    (horizon_one : P.horizon h = 1) (available_all : P.available h = Finset.univ) :
    P.expectedReward h ≤ (Fintype.card ι : ℝ) * Comparison.ratio := by
  have he : hardUnmatchedFraction (Finset.univ : Finset ι) = 1 := by
    simp [hardUnmatchedFraction, Fintype.card_ne_zero]
  have hb := P.hard_expected_reward_le h
  change P.expectedReward h ≤ (Fintype.card ι : ℝ) *
    hardUpperPotential (P.horizon h) (hardUnmatchedFraction (P.available h)) at hb
  rwa [horizon_one, available_all, he, hardUpperPotential_initial] at hb

end StochasticMatching.PoissonOnlineController
