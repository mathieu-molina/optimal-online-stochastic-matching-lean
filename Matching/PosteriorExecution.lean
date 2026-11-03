import Matching.AdaptiveBudget
import Matching.PosteriorStage

/-! A complete, measurable finite posterior-policy execution on the original
incoming history/residual sample. Its observable output is the completion
count. The exact law includes every terminal and completion branch.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StochasticMatching.PosteriorStage

universe u v

noncomputable def countPlan : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    PosteriorStage H ι → ℕ → AdaptivePlan ℕ n H ι
  | 0, _, _, _, _, _, _, k => ⟨{value := fun _ => k, measurable_value := measurable_const}⟩
  | n + 1, _, _, _, _, _, s, k =>
      (s.service, {value := fun _ => k, measurable_value := measurable_const},
        fun j => countPlan n (s.next j) (k + 1))

variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem countPlan_bounds (n : ℕ) (s : PosteriorStage H ι) (k : ℕ)
    (x : H × (ι → ℝ)) :
    k ≤ AdaptivePlan.run (countPlan n s k) x ∧
      AdaptivePlan.run (countPlan n s k) x ≤ k + n := by
  induction n generalizing H ι k with
  | zero => simp [countPlan, AdaptivePlan.run]
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (countPlan (n + 1) s k) hj]
      have hb := ih (s.next j) (k + 1) (s.service.observation j x)
      change k ≤ AdaptivePlan.run (countPlan n (s.next j) (k + 1)) (s.service.observation j x) ∧
        AdaptivePlan.run (countPlan n (s.next j) (k + 1)) (s.service.observation j x) ≤ k + (n + 1)
      omega
    · change k ≤ branchSelect s.service.winner _ _ x ∧
        branchSelect s.service.winner _ _ x ≤ k + (n + 1)
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      change k ≤ k ∧ k ≤ k + (n + 1)
      omega

noncomputable def completionCount (s : PosteriorStage H ι) : H × (ι → ℝ) → ℕ :=
  AdaptivePlan.run (countPlan (Fintype.card ι) s 0)

theorem measurable_completionCount (s : PosteriorStage H ι) : Measurable s.completionCount :=
  AdaptivePlan.measurable_run _

theorem completionCount_le (s : PosteriorStage H ι) (x : H × (ι → ℝ)) :
    s.completionCount x ≤ Fintype.card ι := by
  simpa only [Nat.zero_add] using (countPlan_bounds (Fintype.card ι) s 0 x).2

theorem countPlan_exhaustive (s : PosteriorStage H ι) (k : ℕ) :
    AdaptivePlan.Exhaustive (countPlan (Fintype.card ι) s k) :=
  AdaptivePlan.exhaustive_of_card_le _ (le_refl _)

theorem completionCount_law (s : PosteriorStage H ι) (ν : Measure H) :
    Measure.map s.completionCount (ν.prod independentExponentials) =
      AdaptivePlan.law (countPlan (Fintype.card ι) s 0) ν :=
  AdaptivePlan.run_law _ ν

end StochasticMatching.PosteriorStage
