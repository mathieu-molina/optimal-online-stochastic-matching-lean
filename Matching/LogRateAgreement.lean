import Matching.LogRateReader
import Matching.PathBounds
import Matching.TraceLength

/-! The log-based evaluator agrees with the actual sample-space rate path
on every good execution. In particular the actual rate has a version measurable
with respect to the completion-observation filtration at each fixed time.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace J] [Fintype J] [DecidableEq J] [MeasurableSingletonClass J]

theorem readRate_empty (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (k : ℕ) (q : RateQuery H J) (ht : 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1)
    (he : q.2.2.2 k = Sum.inl ()) : readRate (n + 1) s label k q = s.readerCurrent label q := by
  change (if 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1 then
    branchSelect (E := J → ℝ) (readerWinner label k) _ _ q else 0) = _
  rw [if_pos ht]
  apply branchSelect_of_not_mem
  intro j hj
  change completionEntryLabel (q.2.2.2 k) = Sum.inr (label j) at hj
  rw [he] at hj
  cases hj

theorem readRate_entry (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (k : ℕ) (q : RateQuery H J)
    (ht : 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1)
    {j : ι} {τ d : ℝ} (he : q.2.2.2 k = Sum.inr (label j, τ, d)) :
    readRate (n + 1) s label k q =
      readRate n (s.next j) (fun i => label i.1) (k + 1) (readerNextQuery k q) := by
  change (if 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1 then
    branchSelect (E := J → ℝ) (readerWinner label k) _ _ q else 0) = _
  rw [if_pos ht]
  apply branchSelect_of_mem (readerWinner_disjoint label hinj k)
  change completionEntryLabel (q.2.2.2 k) = Sum.inr (label j)
  rw [he]
  rfl

theorem observedRate_eq_ratePath (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (hx : GoodExecution n s x) (hlen : LogLength k (L x.1))
    (t : ℝ) :
    observedRate n s label k (elapsed x.1 + t, (x.1, (elapsed x.1,
      AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x))) = ratePath n s label (t, x) := by
  induction n generalizing H ι k t with
  | zero => rfl
  | succ n ih =>
    classical
    by_cases ht : 0 ≤ t ∧ t < s.deadline x.1
    · have hqt : 0 ≤ (elapsed x.1 + t) - elapsed x.1 ∧
          (elapsed x.1 + t) - elapsed x.1 < s.deadline x.1 := by
        simpa only [add_sub_cancel_left] using ht
      rcases hx with ⟨hp, hterm | ⟨j, hj, hchild⟩⟩
      · rw [AdaptivePlan.run_of_terminal (tracePlan (n + 1) s label L hL elapsed he k) hterm]
        change observedRate (n + 1) s label k
          (elapsed x.1 + t, (x.1, (elapsed x.1, L x.1))) = _
        have hempty : censorLog (elapsed x.1 + t) (L x.1) k = Sum.inl () := by
          rw [censorLog, (hlen k).mpr (le_refl k)]
          split_ifs <;> rfl
        unfold observedRate
        rw [readRate_empty n s label k _ hqt hempty]
        rw [ratePath_before_stop n s label x ht.1 (by rw [s.stopClock_terminal x hterm]; exact ht.2)]
        simp only [readerCurrent, currentRate, add_sub_cancel_left]
      · rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
        let Lout := AdaptivePlan.run (tracePlan n (s.next j) (fun i => label i.1)
          (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1))
          (s.service.observation j x)
        let τ := s.service.clock j x
        let d := s.initial x.1 j + (s.service.curves x.1).service j τ
        change observedRate (n + 1) s label k
          (elapsed x.1 + t, (x.1, (elapsed x.1, Lout))) = _
        have hentry : Lout k = Sum.inr (label j, elapsed x.1 + τ, d) := by
          have h := tracePlan_preserves_prefix n (s.next j) (fun i => label i.1)
            (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
            (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
            (k + 1) (s.service.observation j x) (r := k) (by omega)
          simpa only [appendLog, if_pos rfl, HistoryServiceFamily.observation] using h
        by_cases htτ : t < τ
        · have hc : censorLog (elapsed x.1 + t) Lout k = Sum.inl () := by
            rw [censorLog, hentry]
            change (if elapsed x.1 + τ ≤ elapsed x.1 + t then _ else _) = _
            rw [if_neg (by linarith)]
          unfold observedRate
          rw [readRate_empty n s label k _ hqt hc]
          rw [ratePath_before_stop n s label x ht.1
            (by rw [s.service.stopClock_winner hj]; exact htτ)]
          simp only [readerCurrent, currentRate, add_sub_cancel_left]
        · have hτt : τ ≤ t := le_of_not_gt htτ
          have hc : censorLog (elapsed x.1 + t) Lout k =
              Sum.inr (label j, elapsed x.1 + τ, d) := by
            rw [censorLog, hentry]
            change (if elapsed x.1 + τ ≤ elapsed x.1 + t then _ else _) = _
            rw [if_pos (add_le_add_left hτt _)]
          unfold observedRate
          rw [readRate_entry n s label hinj k _ hqt hc]
          have hquery : readerNextQuery k
              (elapsed x.1 + t, (x.1, (elapsed x.1, censorLog (elapsed x.1 + t) Lout))) =
              (elapsed x.1 + t, ((x.1, τ), (elapsed x.1 + τ,
                censorLog (elapsed x.1 + t) Lout))) := by
            simp only [readerNextQuery, hc, completionEntryTime, Sum.elim_inr, add_sub_cancel_left]
          rw [hquery]
          have hI := ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective)
            (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
            (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
            (k + 1) (s.service.observation j x) hchild
            (s.appendLog_length label L elapsed k j (s.service.observation j x).1 hlen) (t - τ)
          change readRate n (s.next j) (fun i => label i.1) (k + 1)
            ((elapsed x.1 + τ) + (t - τ), ((x.1, τ), (elapsed x.1 + τ,
              censorLog ((elapsed x.1 + τ) + (t - τ)) Lout))) =
            ratePath n (s.next j) (fun i => label i.1) (t - τ, s.service.observation j x) at hI
          have hnum : (elapsed x.1 + τ) + (t - τ) = elapsed x.1 + t := by ring
          rw [hnum] at hI
          exact hI.trans (ratePath_restart n s label x hj hτt).symm
    · simp only [observedRate, readRate, ratePath, add_sub_cancel_left, if_neg ht]

theorem observedRate_eq_ratePath_ae (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t,
      observedRate (Fintype.card ι) s label 0 (t, (x.1, (0, s.completionLog label x))) =
        ratePath (Fintype.card ι) s label (t, x) := by
  filter_upwards [goodExecution_ae (Fintype.card ι) s ν] with x hx
  intro t
  have hlen : LogLength 0 (emptyCompletionLog (J := J)) := by
    intro r
    simp [emptyCompletionLog]
  simpa only [zero_add] using observedRate_eq_ratePath (Fintype.card ι) s label hinj
    (fun _ => emptyCompletionLog) measurable_const (fun _ => 0) measurable_const 0 x hx hlen t

end StochasticMatching.PosteriorStage
