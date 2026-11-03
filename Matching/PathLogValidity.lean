import Matching.PathCount
import Matching.TraceLength

/-! Every newly recorded completion is realized by the integrated service
path, and the completed coordinate remains frozen at its recorded demand.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace J] [Fintype J] [DecidableEq J]

theorem tracePlan_service_frozen (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : H × (ι → ℝ)) (hx : GoodExecution n s x) (hlen : LogLength k (L x.1)) :
    ∀ r, k ≤ r → ∀ a u d,
      AdaptivePlan.run (tracePlan n s label L hL elapsed he k) x r = Sum.inr (a, u, d) →
      ∃ i, label i = a ∧ elapsed x.1 ≤ u ∧ ∀ t, u - elapsed x.1 ≤ t →
        s.initial x.1 i + cumulativePath n s label x t a = d := by
  induction n generalizing H ι k with
  | zero =>
    intro r hr a u d hentry
    change L x.1 r = Sum.inr (a, u, d) at hentry
    rw [(hlen r).mpr hr] at hentry
    cases hentry
  | succ n ih =>
    intro r hr a u d hentry
    rcases hx with ⟨hp, hterm | ⟨j, hj, hchild⟩⟩
    · rw [AdaptivePlan.run_of_terminal (tracePlan (n + 1) s label L hL elapsed he k) hterm] at hentry
      change L x.1 r = Sum.inr (a, u, d) at hentry
      rw [(hlen r).mpr hr] at hentry
      cases hentry
    · rw [AdaptivePlan.run_of_winner (tracePlan (n + 1) s label L hL elapsed he k) hj] at hentry
      change AdaptivePlan.run (tracePlan n (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1))
        (s.service.observation j x) r = Sum.inr (a, u, d) at hentry
      have hτ : 0 ≤ s.service.clock j x := (s.winner_clock_pos x j (hp j)).le
      by_cases hrk : r = k
      · subst r
        have hfirst := tracePlan_preserves_prefix n (s.next j) (fun i => label i.1)
          (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
          (k + 1) (s.service.observation j x) (r := k) (by omega)
        rw [hfirst] at hentry
        simp only [appendLog, if_pos rfl, HistoryServiceFamily.observation] at hentry
        have ha := congrArg Prod.fst (Sum.inr.inj hentry)
        have hu := congrArg (fun q : J × ℝ × ℝ => q.2.1) (Sum.inr.inj hentry)
        have hd := congrArg (fun q : J × ℝ × ℝ => q.2.2) (Sum.inr.inj hentry)
        change label j = a at ha
        change elapsed x.1 + s.service.clock j x = u at hu
        change s.initial x.1 j + (s.service.curves x.1).service j (s.service.clock j x) = d at hd
        refine ⟨j, ha, by linarith, ?_⟩
        intro t ht
        have hct : s.service.clock j x ≤ t := by linarith
        rw [← ha, cumulativePath_at_completed_winner n s label hinj hP0 hPc hPcompact hPdown
          hmem x hj (hp j) hct, ← hd]
        congr 1
        exact ((s.service.curves x.1).winner_service_eq (hp j) hj).symm
      · have hnext := ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective)
          (s.next_feasibleAllocation label hPdown hmem j)
          (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd)
          (k + 1) (s.service.observation j x) hchild
          (s.appendLog_length label L elapsed k j (s.service.observation j x).1 hlen)
          r (by omega) a u d hentry
        obtain ⟨i, ha, hu, hf⟩ := hnext
        change elapsed x.1 + s.service.clock j x ≤ u at hu
        refine ⟨i.1, ha, by linarith, ?_⟩
        intro t ht
        have hct : s.service.clock j x ≤ t := by linarith
        have hc := hf (t - s.service.clock j x) (by
          change u - (elapsed x.1 + s.service.clock j x) ≤ t - s.service.clock j x
          linarith)
        rw [← ha] at hc ⊢
        rw [cumulativePath_restart n s label hP0 hPc hPcompact hPdown hmem x hj hct]
        simp only [Pi.add_apply, labelLift_at_label label hinj]
        change (s.initial x.1 i.1 + (s.service.curves x.1).service i.1 (s.service.clock j x)) +
          cumulativePath n (s.next j) (fun i => label i.1) (s.service.observation j x)
            (t - s.service.clock j x) (label i.1) = d at hc
        linarith

theorem completionLog_service_frozen_ae [MeasurableSpace ι]
    (s : PosteriorStage H ι)
    {P : Set (ι → ℝ)} (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation id P) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ r a u d,
      s.completionLog id x r = Sum.inr (a, u, d) → ∀ t, u ≤ t →
        s.initial x.1 a + cumulativePath (Fintype.card ι) s id x t a = d := by
  filter_upwards [goodExecution_ae (Fintype.card ι) s ν] with x hx
  intro r a u d hentry
  have hlen : LogLength 0 (emptyCompletionLog (J := ι)) := by
    intro r
    simp [emptyCompletionLog]
  obtain ⟨i, ha, _, hf⟩ := tracePlan_service_frozen (Fintype.card ι) s id Function.injective_id
    hP0 hPc hPcompact hPdown hmem (fun _ => emptyCompletionLog) measurable_const
    (fun _ => 0) measurable_const 0 x hx hlen r (Nat.zero_le r) a u d hentry
  change i = a at ha
  subst i
  simpa only [sub_zero] using hf

end StochasticMatching.PosteriorStage
