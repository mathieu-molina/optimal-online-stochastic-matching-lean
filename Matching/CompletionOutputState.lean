import Matching.CursorRestartConservation
import Matching.PosteriorRoutingProcess
import Matching.TerminalPayload
import Matching.GuardedRestart
import Matching.HistoryRejectionClock

/-! An absorbing state that retains the completed scheduling log. Its
continuation observation is preserved by every actual residual restart.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def completionStateService (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    HistoryServiceFamily (CompletionLog J ⊕ RoutingCursor n H ι) J :=
  (HistoryServiceFamily.idle (fun _ : CompletionLog J => (1 : ℝ)) measurable_const
    (fun _ => zero_lt_one)).sum (s.cursorService n label)

noncomputable def completionStateUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) :
    (CompletionLog J ⊕ RoutingCursor n H ι) × (Unit ⊕ (ℝ × Option J)) →
      CompletionLog J ⊕ RoutingCursor n H ι :=
  freezeTerminalUpdate (fun x => fillTerminal
    (s.cursorLog n label L elapsed k x.1, s.guardedCursorUpdate n label x))

theorem measurable_completionStateUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.completionStateUpdate n label L elapsed k) :=
  measurable_freezeTerminalUpdate _ (measurable_fillTerminal.comp
    (((s.measurable_cursorLog n label L hL elapsed he k).comp measurable_fst).prodMk
      (s.measurable_guardedCursorUpdate n label)))

noncomputable def completionStateObservation (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    (CompletionLog J ⊕ RoutingCursor n H ι) × (J → ℝ) → CompletionLog J :=
  terminalObservation (s.cursorContinuation n label L hL elapsed he k)

theorem measurable_completionStateObservation (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.completionStateObservation n label L hL elapsed he k) :=
  measurable_terminalObservation _ (s.measurable_cursorContinuation n label L hL elapsed he k)

theorem completionStateObservation_preserved_ae (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (Λ : ℝ) (hΛ : ∀ b t, t ∈ Icc 0 ((s.completionStateService n label).curves b).deadline →
      ∑ a, ((s.completionStateService n label).curves b).rate a t ≤ Λ)
    (b : CompletionLog J ⊕ RoutingCursor n H ι) :
    let q := (s.completionStateService n label).withRejectionClock Λ hΛ
    ∀ᵐ z ∂(independentExponentials (ι := Option J)),
      s.completionStateObservation n label L hL elapsed he k
        (s.completionStateUpdate n label L elapsed k (b, (historyRestart q (b, z)).1),
          (historyRestart q (b, z)).2) =
      s.completionStateObservation n label L hL elapsed he k (b, fun a => z (some a)) := by
  intro q
  cases b with
  | inl log => exact Filter.Eventually.of_forall (fun _ => rfl)
  | inr x =>
    filter_upwards [s.cursorRestartValue_preserved_ae n label hinj L hL elapsed he k x Λ
      (hΛ (.inr x))] with z hz
    let p := ((s.cursorService n label).curves x).withRejectionClock Λ (hΛ (.inr x))
    change terminalObservation (s.cursorContinuation n label L hL elapsed he k)
      (fillTerminal (s.cursorLog n label L elapsed k x,
        s.guardedCursorUpdate n label (x, (firstEventRestart p z).1)), (firstEventRestart p z).2) = _
    rw [terminalObservation_filled]
    have hg := guardedEventUpdate_restart (fun y => ((s.cursorService n label).curves y).deadline)
      (s.cursorUpdate n label) x (s.cursorUpdate_terminal n label x) p rfl z
    change Sum.elim _ _ (guardedEventUpdate _ _ (x, (firstEventRestart p z).1)) = _
    rw [hg]
    exact hz

end StochasticMatching.PosteriorStage
