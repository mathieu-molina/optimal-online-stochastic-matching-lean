import Matching.CursorCompletionLog
import Matching.CursorStageDemand

/-! The full scheduling completion log predicted from a current routing
cursor and its still-unseen residual demands. This links cursor execution to
the already verified recursive scheduling trace.
-/
open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]

noncomputable def cursorContinuation : (n : ℕ) → {H ι : Type} → [MeasurableSpace H] →
    [Fintype ι] → [DecidableEq ι] → (s : PosteriorStage H ι) → (ι → J) →
    (L : H → CompletionLog J) → Measurable L → (elapsed : H → ℝ) → Measurable elapsed →
    ℕ → RoutingCursor n H ι × (J → ℝ) → CompletionLog J
  | 0, _, _, _, _, _, _, _, L, _, _, _, _, x => L x.1.1
  | n + 1, _, _, _, _, _, s, label, L, hL, elapsed, he, k, x =>
      Sum.elim
        (fun y => AdaptivePlan.run (tracePlan (n + 1) s label L hL elapsed he k)
          (y.1, s.stageDemand label y x.2))
        (fun y => cursorContinuation n (s.next y.1) (fun i => label i.1)
          (s.appendLog label L elapsed k y.1) (s.measurable_appendLog label hL he k y.1)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1) (y.2, x.2)) x.1

variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem measurable_cursorContinuation (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.cursorContinuation n label L hL elapsed he k) := by
  induction n generalizing H ι k with
  | zero => exact hL.comp (measurable_fst.comp measurable_fst)
  | succ n ih =>
    refine measurable_sum_prod_elim
      (fun x : (H × ℝ) × (J → ℝ) => AdaptivePlan.run (tracePlan (n + 1) s label L hL elapsed he k)
        (x.1.1, s.stageDemand label x.1 x.2))
      (fun x : ((j : ι) × RoutingCursor n (H × ℝ) {i : ι // i ≠ j}) × (J → ℝ) =>
        (s.next x.1.1).cursorContinuation n (fun i => label i.1)
          (s.appendLog label L elapsed k x.1.1) (s.measurable_appendLog label hL he k x.1.1)
          (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1) (x.1.2, x.2)) ?_ ?_
    · exact (AdaptivePlan.measurable_run _).comp
        ((measurable_fst.comp measurable_fst).prodMk (s.measurable_stageDemand label))
    · exact measurable_sigma_prod_elim _ (fun j => ih (s.next j) (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1))

theorem cursorContinuation_initial (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (h : H) (r : J → ℝ) :
    s.cursorContinuation n label L hL elapsed he k (initialRoutingCursor n h, r) =
      AdaptivePlan.run (tracePlan n s label L hL elapsed he k) (h, fun i => r (label i)) := by
  cases n with
  | zero => rfl
  | succ n =>
    change AdaptivePlan.run _ (h, s.stageDemand label (h, 0) r) = _
    rw [s.stageDemand_initial]

theorem cursorContinuation_rejected (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : H × ℝ) (r : J → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < ((s.routingService label).curves x).deadline) :
    s.cursorContinuation (n + 1) label L hL elapsed he k
      (.inl (s.advanceRoutingTime label (x, t)),
        fun j => r j - ((s.routingService label).curves x).service j t) =
      s.cursorContinuation (n + 1) label L hL elapsed he k (.inl x, r) := by
  change AdaptivePlan.run _ (x.1, s.stageDemand label (s.advanceRoutingTime label (x, t)) _) = _
  rw [s.stageDemand_after_service label hinj x r t ht0 htT]
  rfl

theorem cursorContinuation_terminal (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : H × ℝ) (r : J → ℝ)
    (hr : ∀ j, ((s.routingService label).curves x).service j
      ((s.routingService label).curves x).deadline < r j) :
    s.cursorContinuation (n + 1) label L hL elapsed he k (.inl x, r) = L x.1 :=
  AdaptivePlan.run_of_terminal (tracePlan (n + 1) s label L hL elapsed he k)
    (s.stageDemand_terminal label hinj x r hr)

end StochasticMatching.PosteriorStage
