import Matching.PoissonOnlineController
import Matching.MonotoneKernelReward

/-! The controller reward is the expectation of its limiting accepted count,
not merely a formal bound on one finite truncation. The count is monotone
because every accepted vertex is removed from the available set. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSpace (Option ι)] [MeasurableSpace (Finset ι)]
  [MeasurableSingletonClass (Finset ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ]

theorem unmatchedAfterMark_subset (A : Finset ι) (j : Option ι) : unmatchedAfterMark A j ⊆ A := by
  cases j with
  | none => exact Finset.Subset.refl _
  | some i => exact Finset.erase_subset _ _

namespace PoissonOnlineController
variable {N : σ → Finset ι} {intensity : σ → ℝ≥0}
variable (P : PoissonOnlineController (H := H) N intensity)

theorem reward_measurable : Measurable P.reward :=
  measurable_const.sub ((measurable_of_countable (fun A : Finset ι => (A.card : ℝ))).comp P.remaining_measurable)

theorem reward_bounds (x : ControllerState H ι) : 0 ≤ P.reward x ∧ P.reward x ≤ Fintype.card ι := by
  constructor
  · exact sub_nonneg.mpr (Nat.cast_le.mpr (Finset.card_le_univ _))
  · exact sub_le_self _ (Nat.cast_nonneg _)

theorem reward_step_pointwise (h : H) (y : ControllerEvent σ ι × ControllerState H ι)
    (hy : ControllerStepValid N P.horizon P.available h y) : P.reward (.inr h) ≤ P.reward y.2 := by
  have hsub : P.remaining y.2 ⊆ P.available h := by
    rcases y with ⟨e, x⟩
    cases e with
    | inl _ =>
        change x = .inl (P.available h) at hy
        rw [hy]
        exact Finset.Subset.refl _
    | inr p =>
        cases x with
        | inl A =>
            change _ ∧ A = unmatchedAfterMark (P.available h) p.2.2 at hy
            change A ⊆ P.available h
            rw [hy.2]
            exact unmatchedAfterMark_subset _ _
        | inr h' =>
            change _ ∧ P.available h' = unmatchedAfterMark (P.available h) p.2.2 ∧ _ at hy
            change P.available h' ⊆ P.available h
            rw [hy.2.1]
            exact unmatchedAfterMark_subset _ _
  exact sub_le_sub_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) _

theorem reward_step (x : ControllerState H ι) : ∀ᵐ x' ∂P.step x, P.reward x ≤ P.reward x' := by
  have hS : MeasurableSet {x' | P.reward x ≤ P.reward x'} :=
    measurableSet_le measurable_const P.reward_measurable
  cases x with
  | inl A =>
      change ∀ᵐ x' ∂Measure.dirac (.inl A : ControllerState H ι), P.reward (.inl A) ≤ P.reward x'
      exact (ae_dirac_iff hS).mpr le_rfl
  | inr h =>
      change ∀ᵐ x' ∂Measure.map Prod.snd (P.next h), P.reward (.inr h) ≤ P.reward x'
      apply (ae_map_iff measurable_snd.aemeasurable hS).mpr
      exact (P.valid h).mono (fun y hy => P.reward_step_pointwise h y hy)

theorem expectedReward_eq_trajectory (h : H) :
    P.expectedReward h =
      ∫ z, (⨆ n : ℕ, P.reward (z n)) ∂markovTrajectory P.step (.inr h) := by
  apply kernelExpectedReward_eq_trajectory P.step P.reward P.reward_measurable (Fintype.card ι : ℝ)
  · intro x
    rw [abs_of_nonneg (P.reward_bounds x).1]
    exact (P.reward_bounds x).2
  · exact P.reward_step

theorem expectedReward_le_card (h : H) : P.expectedReward h ≤ Fintype.card ι := by
  apply kernelExpectedReward_le P.step (fun _ => (Fintype.card ι : ℝ)) P.reward
    measurable_const P.reward_measurable (Fintype.card ι : ℝ) (Fintype.card ι : ℝ)
    (fun _ => by simp) _ (fun x => (P.reward_bounds x).2) _
  · intro x
    rw [abs_of_nonneg (P.reward_bounds x).1]
    exact (P.reward_bounds x).2
  · intro x
    simp

end PoissonOnlineController
end StochasticMatching
