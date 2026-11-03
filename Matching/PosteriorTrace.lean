import Matching.PosteriorExecution

/-! The posterior execution's complete finite observation log on fixed original
job labels. Each completion records its label, absolute time, and revealed
demand. Unused entries are empty; the policy never reads them to choose rates.
-/

open MeasureTheory Set

namespace StochasticMatching

abbrev CompletionLog (J : Type*) := ℕ → Unit ⊕ (J × ℝ × ℝ)

def emptyCompletionLog {J : Type*} : CompletionLog J := fun _ => Sum.inl ()

namespace PosteriorStage

universe u v w

variable {J : Type w} [MeasurableSpace J]

noncomputable def appendLog {H : Type u} {ι : Type v} [MeasurableSpace H]
    [Fintype ι] [DecidableEq ι] (s : PosteriorStage H ι)
    (label : ι → J) (L : H → CompletionLog J) (elapsed : H → ℝ)
    (k : ℕ) (j : ι) (h : H × ℝ) : CompletionLog J := fun r =>
  if r = k then Sum.inr (label j, elapsed h.1 + h.2,
    s.initial h.1 j + (s.service.curves h.1).service j h.2) else L h.1 r

theorem measurable_appendLog {H : Type u} {ι : Type v} [MeasurableSpace H]
    [Fintype ι] [DecidableEq ι] (s : PosteriorStage H ι)
    (label : ι → J) {L : H → CompletionLog J} (hL : Measurable L)
    {elapsed : H → ℝ} (he : Measurable elapsed) (k : ℕ) (j : ι) :
    Measurable (s.appendLog label L elapsed k j) := by
  apply measurable_pi_lambda
  intro r
  by_cases hr : r = k
  · simp only [appendLog, if_pos hr]
    exact measurable_inr.comp (measurable_const.prodMk
      (((he.comp measurable_fst).add measurable_snd).prodMk
        ((((measurable_pi_apply j).comp s.measurable_initial).comp measurable_fst).add
          (s.service.measurable_service j))))
  · simp only [appendLog, if_neg hr]
    exact ((measurable_pi_apply r).comp hL).comp measurable_fst

noncomputable def tracePlan : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    (s : PosteriorStage H ι) → (label : ι → J) →
    (L : H → CompletionLog J) → Measurable L →
    (elapsed : H → ℝ) → Measurable elapsed → (k : ℕ) →
    AdaptivePlan (CompletionLog J) n H ι
  | 0, _, _, _, _, _, _, _, L, hL, _, _, _ => ⟨⟨L, hL⟩⟩
  | n + 1, _, _, _, _, _, s, label, L, hL, elapsed, he, k =>
      (s.service, ⟨L, hL⟩, fun j =>
        tracePlan n (s.next j) (fun i => label i.1)
          (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1))

variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem tracePlan_preserves_prefix (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) {r : ℕ} (hr : r < k) :
    AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x r = L x.1 r := by
  induction n generalizing H ι k with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      have h := ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x) (by omega)
      simpa only [appendLog, if_neg (Nat.ne_of_lt hr), HistoryServiceFamily.observation] using h
    · change branchSelect (E := CompletionLog J) s.service.winner _ _ x r = L x.1 r
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      rfl

theorem tracePlan_preserves_tail (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) {r : ℕ} (hr : k + n ≤ r) :
    AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x r = L x.1 r := by
  induction n generalizing H ι k with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      have hrk : r ≠ k := by omega
      have h := ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x) (by omega)
      simpa only [appendLog, if_neg hrk, HistoryServiceFamily.observation] using h
    · change branchSelect (E := CompletionLog J) s.service.winner _ _ x r = L x.1 r
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      rfl

noncomputable def completionLog (s : PosteriorStage H ι) (label : ι → J) :
    H × (ι → ℝ) → CompletionLog J :=
  AdaptivePlan.run (tracePlan (Fintype.card ι) s label (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0)

theorem measurable_completionLog (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.completionLog label) := AdaptivePlan.measurable_run _

theorem completionLog_empty_after_card (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) {r : ℕ} (hr : Fintype.card ι ≤ r) :
    s.completionLog label x r = Sum.inl () := by
  exact tracePlan_preserves_tail (Fintype.card ι) s label (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0 x (by simpa using hr)

theorem completionLog_law (s : PosteriorStage H ι) (label : ι → J) (ν : Measure H) :
    Measure.map (s.completionLog label) (ν.prod independentExponentials) =
      AdaptivePlan.law (tracePlan (Fintype.card ι) s label (fun _ => emptyCompletionLog)
        measurable_const (fun _ => 0) measurable_const 0) ν :=
  AdaptivePlan.run_law _ ν

end PosteriorStage
end StochasticMatching
