import Matching.PosteriorExecution
import Matching.HistoryReconstruction
import Matching.TerminalConditional

/-! Expected completion counts of the constructed adaptive execution. The
recursion follows from the actual event partition and marked pushforward law.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching.PosteriorStage
universe u v
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem countPlan_offset (n : ℕ) (s : PosteriorStage H ι) (k : ℕ)
    (x : H × (ι → ℝ)) :
    AdaptivePlan.run (E := ℕ) (countPlan n s k) x = k + AdaptivePlan.run (E := ℕ) (countPlan n s 0) x := by
  induction n generalizing H ι k with
  | zero => simp [countPlan, AdaptivePlan.run]
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (countPlan (n + 1) s k) hj,
        AdaptivePlan.run_of_winner (countPlan (n + 1) s 0) hj]
      change AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) (s.service.observation j x) =
        k + AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) 1) (s.service.observation j x)
      rw [ih (s.next j) (k + 1), ih (s.next j) 1]
      omega
    · change branchSelect s.service.winner _ _ x = k + branchSelect s.service.winner _ _ x
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw),
        branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      exact (Nat.add_zero k).symm

theorem integrable_countPlan (n : ℕ) (s : PosteriorStage H ι) (k : ℕ)
    (μ : Measure (H × (ι → ℝ))) [IsFiniteMeasure μ] :
    Integrable (fun x => (AdaptivePlan.run (E := ℕ) (countPlan n s k) x : ℝ)) μ := by
  have hm : Measurable (fun x => (AdaptivePlan.run (E := ℕ) (countPlan n s k) x : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (AdaptivePlan.measurable_run _)
  apply (integrable_const ((k + n : ℕ) : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (countPlan_bounds n s k x).2

theorem countPlan_winner_integral (n : ℕ) (s : PosteriorStage H ι) (k : ℕ)
    (ν : Measure H) (j : ι) :
    (∫ x in s.service.winner j, (AdaptivePlan.run (E := ℕ) (countPlan (n + 1) s k) x : ℝ)
      ∂ν.prod independentExponentials) =
    ∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) x : ℝ)
      ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have hm : Measurable (fun x => (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) x : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (AdaptivePlan.measurable_run _)
  calc
    _ = ∫ x in s.service.winner j,
        (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) (s.service.observation j x) : ℝ)
          ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact congrArg (fun m : ℕ => (m : ℝ))
        (AdaptivePlan.run_of_winner (countPlan (n + 1) s k) hx)
    _ = ∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) x : ℝ)
        ∂Measure.map (s.service.observation j)
          ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j) hm.stronglyMeasurable).symm
    _ = _ := by rw [s.service.first_completion_factorization]

theorem countPlan_expected_step (n : ℕ) (s : PosteriorStage H ι) (k : ℕ)
    (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, (AdaptivePlan.run (E := ℕ) (countPlan (n + 1) s k) x : ℝ) ∂ν.prod independentExponentials) =
      (∫ _ in s.service.terminalEvent, (k : ℝ) ∂ν.prod (independentExponentials (ι := ι))) +
      ∑ j, ∫ x, (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) (k + 1)) x : ℝ)
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  have hi := integrable_countPlan (n + 1) s k (ν.prod independentExponentials)
  have hit := hi
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hit
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hit.1 hit.2, integral_sum_measure hit.2, tsum_fintype]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    exact congrArg (fun m : ℕ => (m : ℝ))
      (AdaptivePlan.run_of_terminal (countPlan (n + 1) s k) hx)
  · exact Finset.sum_congr rfl (fun j _ => countPlan_winner_integral n s k ν j)

theorem countPlan_expected_completions (n : ℕ) (s : PosteriorStage H ι)
    (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, (AdaptivePlan.run (E := ℕ) (countPlan (n + 1) s 0) x : ℝ) ∂ν.prod independentExponentials) =
      ∑ j, ∫ x, (1 + (AdaptivePlan.run (E := ℕ) (countPlan n (s.next j) 0) x : ℝ))
        ∂(s.service.markedHistoryMeasure ν j).prod independentExponentials := by
  rw [countPlan_expected_step]
  simp only [Nat.cast_zero, integral_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [countPlan_offset n (s.next j) 1, Nat.cast_add, Nat.cast_one]

end StochasticMatching.PosteriorStage
