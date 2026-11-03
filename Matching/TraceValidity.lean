import Matching.GoodExecution

/-! The constructed log records actual original demands. On good executions
all recorded times are nonnegative and precede the original deadline.
-/

open MeasureTheory Set

namespace StochasticMatching

def LogDemandsCorrect {J : Type*} (z : J → ℝ) (L : CompletionLog J) : Prop :=
  ∀ r j t d, L r = Sum.inr (j, t, d) → d = z j

def LogTimesBefore {J : Type*} (T : ℝ) (L : CompletionLog J) : Prop :=
  ∀ r j t d, L r = Sum.inr (j, t, d) → 0 ≤ t ∧ t ≤ T

namespace PosteriorStage

universe u v w

variable {J : Type w} [MeasurableSpace J]
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem tracePlan_demands_correct (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (z : J → ℝ) (hg : GoodExecution n s x)
    (hprefix : LogDemandsCorrect z (L x.1))
    (hz : ∀ i, s.initial x.1 i + x.2 i = z (label i)) :
    LogDemandsCorrect z (AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x) := by
  induction n generalizing H ι k with
  | zero => exact hprefix
  | succ n ih =>
    rcases hg with ⟨hpos, ht | ⟨j, hj, hchild⟩⟩
    · rw [AdaptivePlan.run_of_terminal (tracePlan (n + 1) s label L hL elapsed he k) ht]
      exact hprefix
    · rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      apply ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x) hchild
      · intro r a t d hentry
        by_cases hr : r = k
        · simp only [appendLog, if_pos hr, HistoryServiceFamily.observation] at hentry
          have hpair := Sum.inr.inj hentry
          have ha := congrArg Prod.fst hpair
          have hd := congrArg (fun q : J × ℝ × ℝ => q.2.2) hpair
          calc
            d = s.initial x.1 j + (s.service.curves x.1).service j (s.service.clock j x) := hd.symm
            _ = s.initial x.1 j + x.2 j := s.winner_revealed_demand x j (hpos j) hj
            _ = z (label j) := hz j
            _ = z a := congrArg z ha
        · apply hprefix r a t d
          simpa only [appendLog, if_neg hr, HistoryServiceFamily.observation] using hentry
      · intro i
        rw [s.next_original_demand]
        exact hz i.1

theorem tracePlan_times_before (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (hg : GoodExecution n s x) (he0 : 0 ≤ elapsed x.1)
    (hprefix : LogTimesBefore (elapsed x.1) (L x.1)) :
    ∀ r a t d, AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x r = Sum.inr (a, t, d) →
      0 ≤ t ∧ t < elapsed x.1 + s.deadline x.1 := by
  induction n generalizing H ι k with
  | zero =>
    intro r a t d hentry
    have h := hprefix r a t d hentry
    exact ⟨h.1, lt_of_le_of_lt h.2 (lt_add_of_pos_right _ (s.deadline_pos x.1))⟩
  | succ n ih =>
    rcases hg with ⟨hpos, ht | ⟨j, hj, hchild⟩⟩
    · rw [AdaptivePlan.run_of_terminal (tracePlan (n + 1) s label L hL elapsed he k) ht]
      intro r a t d hentry
      have h := hprefix r a t d hentry
      exact ⟨h.1, lt_of_le_of_lt h.2 (lt_add_of_pos_right _ (s.deadline_pos x.1))⟩
    · rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      have ht0 := s.winner_clock_pos x j (hpos j)
      have hprefix' : LogTimesBefore (elapsed x.1 + s.service.clock j x)
          (s.appendLog label L elapsed k j (s.service.observation j x).1) := by
        intro r a t d hentry
        by_cases hr : r = k
        · simp only [appendLog, if_pos hr, HistoryServiceFamily.observation] at hentry
          have ht := congrArg (fun q : J × ℝ × ℝ => q.2.1) (Sum.inr.inj hentry)
          change elapsed x.1 + s.service.clock j x = t at ht
          rw [← ht]
          exact ⟨add_nonneg he0 ht0.le, le_refl _⟩
        · have hold : L x.1 r = Sum.inr (a, t, d) := by
            simpa only [appendLog, if_neg hr, HistoryServiceFamily.observation] using hentry
          have h := hprefix r a t d hold
          exact ⟨h.1, h.2.trans (le_add_of_nonneg_right ht0.le)⟩
      have h := ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x) hchild (add_nonneg he0 ht0.le) hprefix'
      intro r a t d hentry
      have hout := h r a t d hentry
      refine ⟨hout.1, ?_⟩
      have heq := s.next_total_deadline elapsed x j hj
      exact lt_of_lt_of_eq hout.2 heq

theorem completionLog_demands_correct_ae [MeasurableSpace ι]
    (s : PosteriorStage H ι) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials,
      LogDemandsCorrect (s.initial x.1 + x.2) (s.completionLog id x) := by
  filter_upwards [goodExecution_ae (Fintype.card ι) s ν] with x hx
  apply tracePlan_demands_correct (Fintype.card ι) s id (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0 x (s.initial x.1 + x.2) hx
  · intro r j t d h
    cases h
  · intro i
    rfl

theorem completionLog_times_before_ae (s : PosteriorStage H ι) (label : ι → J) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials,
      ∀ r a t d, s.completionLog label x r = Sum.inr (a, t, d) → 0 ≤ t ∧ t < s.deadline x.1 := by
  filter_upwards [goodExecution_ae (Fintype.card ι) s ν] with x hx
  have hp : LogTimesBefore 0 (emptyCompletionLog (J := J)) := by
    intro r a t d h
    cases h
  simpa only [zero_add] using tracePlan_times_before (Fintype.card ι) s label
    (fun _ => emptyCompletionLog) measurable_const (fun _ => 0) measurable_const 0 x hx (le_refl _) hp

end PosteriorStage
end StochasticMatching
