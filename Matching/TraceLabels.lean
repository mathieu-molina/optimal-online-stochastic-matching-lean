import Matching.PosteriorTrace

/-! Original labels cannot complete twice in the constructed execution.
The proof follows the changing survivor types, not a numerical count bound.
-/

open MeasureTheory Set
namespace StochasticMatching

def LogLabelsDistinct {J : Type*} (L : CompletionLog J) : Prop :=
  ∀ r q a t d u e, L r = Sum.inr (a, t, d) → L q = Sum.inr (a, u, e) → r = q

def LogAvoids {J ι : Type*} (label : ι → J) (L : CompletionLog J) : Prop :=
  ∀ r i t d, L r ≠ Sum.inr (label i, t, d)

namespace PosteriorStage
universe u v w
variable {J : Type w} [MeasurableSpace J]
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem appendLog_avoids_survivors (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) (j : ι) (h : H × ℝ)
    (hinj : Function.Injective label) (hfresh : LogAvoids label (L h.1)) :
    LogAvoids (fun i : {i : ι // i ≠ j} => label i.1) (s.appendLog label L elapsed k j h) := by
  intro r i t d hentry
  by_cases hr : r = k
  · simp only [appendLog, if_pos hr] at hentry
    have hl := congrArg Prod.fst (Sum.inr.inj hentry)
    exact i.2 (hinj hl).symm
  · apply hfresh r i.1 t d
    simpa only [appendLog, if_neg hr] using hentry

theorem appendLog_labels_distinct (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) (j : ι) (h : H × ℝ)
    (hdist : LogLabelsDistinct (L h.1)) (hfresh : LogAvoids label (L h.1)) :
    LogLabelsDistinct (s.appendLog label L elapsed k j h) := by
  intro r q a t d u e hr hq
  by_cases hrk : r = k
  · by_cases hqk : q = k
    · exact hrk.trans hqk.symm
    · simp only [appendLog, if_pos hrk] at hr
      simp only [appendLog, if_neg hqk] at hq
      have hl : label j = a := congrArg Prod.fst (Sum.inr.inj hr)
      exact False.elim (hfresh q j u e (by simpa only [hl] using hq))
  · by_cases hqk : q = k
    · simp only [appendLog, if_neg hrk] at hr
      simp only [appendLog, if_pos hqk] at hq
      have hl : label j = a := congrArg Prod.fst (Sum.inr.inj hq)
      exact False.elim (hfresh r j t d (by simpa only [hl] using hr))
    · apply hdist r q a t d u e
      · simpa only [appendLog, if_neg hrk] using hr
      · simpa only [appendLog, if_neg hqk] using hq

theorem tracePlan_labels_distinct (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (hinj : Function.Injective label)
    (hdist : LogLabelsDistinct (L x.1)) (hfresh : LogAvoids label (L x.1)) :
    LogLabelsDistinct (AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x) := by
  induction n generalizing H ι k with
  | zero => exact hdist
  | succ n ih =>
    classical
    by_cases hw : ∃ j, x ∈ s.service.winner j
    · obtain ⟨j, hj⟩ := hw
      rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj]
      apply ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
        (k + 1) (s.service.observation j x)
      · exact hinj.comp Subtype.val_injective
      · exact s.appendLog_labels_distinct label L elapsed k j
          (s.service.observation j x).1 hdist hfresh
      · exact s.appendLog_avoids_survivors label L elapsed k j
          (s.service.observation j x).1 hinj hfresh
    · change LogLabelsDistinct (branchSelect (E := CompletionLog J) s.service.winner _ _ x)
      rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
      exact hdist

theorem completionLog_labels_distinct (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × (ι → ℝ)) :
    LogLabelsDistinct (s.completionLog label x) := by
  apply tracePlan_labels_distinct (Fintype.card ι) s label (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0 x hinj
  · intro r q a t d u e h
    cases h
  · intro r i t d h
    cases h

end PosteriorStage
end StochasticMatching
