import Matching.PosteriorTrace

/-! The concrete completion count is exactly the length of the concrete log.
This holds on every sample, including the total exceptional fallback branches.
-/

open MeasureTheory Set
namespace StochasticMatching

def LogLength {J : Type*} (k : ℕ) (L : CompletionLog J) : Prop :=
  ∀ r, L r = Sum.inl () ↔ k ≤ r

namespace PosteriorStage
universe u v w
variable {J : Type w} [MeasurableSpace J]
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem appendLog_length (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) (j : ι) (h : H × ℝ)
    (hL : LogLength k (L h.1)) :
    LogLength (k + 1) (s.appendLog label L elapsed k j h) := by
  intro r
  by_cases hr : r = k
  · subst r
    simp [appendLog]
  · simp only [appendLog, if_neg hr, hL r]
    omega

theorem tracePlan_length (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (hlen : LogLength k (L x.1)) :
    LogLength (AdaptivePlan.run (countPlan n s k) x)
      (AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x) := by
  induction n generalizing H ι k with
  | zero => exact hlen
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (countPlan (n + 1) s k) hj,
        AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      exact ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x)
        (s.appendLog_length label L elapsed k j (s.service.observation j x).1 hlen)
    · change LogLength (branchSelect (E := ℕ) s.service.winner _ _ x)
        (branchSelect (E := CompletionLog J) s.service.winner _ _ x)
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw),
        branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      exact hlen

theorem completionLog_length (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) :
    LogLength (s.completionCount x) (s.completionLog label x) := by
  apply tracePlan_length (Fintype.card ι) s label (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0 x
  intro r
  simp [emptyCompletionLog]

theorem completionLog_filled_iff (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) (r : ℕ) :
    (∃ j t d, s.completionLog label x r = Sum.inr (j, t, d)) ↔ r < s.completionCount x := by
  have h := s.completionLog_length label x r
  cases he : s.completionLog label x r with
  | inl a =>
    cases a
    simp only [he, true_iff] at h
    simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, exists_false, false_iff]
    omega
  | inr q =>
    rcases q with ⟨j, t, d⟩
    simp only [he, Sum.inr_ne_inl, false_iff, not_le] at h
    exact ⟨fun _ => h, fun _ => ⟨j, t, d, rfl⟩⟩

end PosteriorStage
end StochasticMatching
