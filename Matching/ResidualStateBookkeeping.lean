import Matching.TerminalSegment

/-! Reconstruct original job demands from accumulated service and current
residuals. Recycling an inactive coordinate cannot change these demands.
-/
namespace StochasticMatching.CompletionState
variable {ι : Type*} [DecidableEq ι]

def originalDemands (s : CompletionState ι) (r : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s.completed then s.served i else s.served i + r i

@[simp] theorem originalDemands_initial (r : ι → ℝ) : initial.originalDemands r = r := by
  funext i
  simp [originalDemands, initial]

theorem valid_originalDemands (s : CompletionState ι) (r : ι → ℝ)
    (hs : ∀ i, 0 ≤ s.served i) (hr : ∀ i ∉ s.completed, 0 < r i) :
    Valid (s.originalDemands r) s := by
  refine ⟨hs, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s.completed
    · simp [originalDemands, hi]
    · simp only [originalDemands, if_neg hi]
      linarith [hr i hi]
  · intro i
    by_cases hi : i ∈ s.completed
    · simp [originalDemands, hi]
    · simp only [originalDemands, hi, if_false, false_iff]
      linarith [hr i hi]

theorem originalDemands_of_valid {z : ι → ℝ} {s : CompletionState ι} (hs : Valid z s)
    (r : ι → ℝ) (hr : ∀ i ∉ s.completed, r i = z i - s.served i) :
    s.originalDemands r = z := by
  funext i
  by_cases hi : i ∈ s.completed
  · simp [originalDemands, hi, valid_completed_eq hs hi]
  · simp [originalDemands, hi, hr i hi]

theorem afterService_originalDemands (s : CompletionState ι) (u r r' : ι → ℝ)
    (hfrozen : ∀ i ∈ s.completed, u i = 0)
    (hr : ∀ i ∉ s.completed, r' i = r i - u i) :
    (s.afterService u).originalDemands r' = s.originalDemands r := by
  funext i
  by_cases hi : i ∈ s.completed
  · simp [originalDemands, afterService, hi, hfrozen i hi]
  · simp [originalDemands, afterService, hi, hr i hi]

theorem afterCompletion_originalDemands (s : CompletionState ι) (u r r' : ι → ℝ) (j : ι)
    (hj : j ∉ s.completed) (hfrozen : ∀ i ∈ s.completed, u i = 0) (hw : u j = r j)
    (hr : ∀ i ∉ insert j s.completed, r' i = r i - u i) :
    (s.afterCompletion u j).originalDemands r' = s.originalDemands r := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [originalDemands, afterCompletion, hj, hw]
  · by_cases hi : i ∈ s.completed
    · simp [originalDemands, afterCompletion, hi, hfrozen i hi]
    · have hi' : i ∉ insert j s.completed := by simp [hij, hi]
      simp [originalDemands, afterCompletion, hij, hi, hr i hi']

end StochasticMatching.CompletionState
