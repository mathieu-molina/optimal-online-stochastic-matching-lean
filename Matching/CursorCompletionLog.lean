import Matching.PosteriorCursorUpdate
import Matching.PosteriorTrace

/-! Read the actual completion prefix stored in a posterior routing cursor.
The record is the same label/time/revealed-demand record as tracePlan uses.
-/
open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]

noncomputable def cursorLog : (n : ℕ) → {H ι : Type} → [MeasurableSpace H] →
    [Fintype ι] → [DecidableEq ι] → PosteriorStage H ι → (ι → J) →
    (H → CompletionLog J) → (H → ℝ) → ℕ → RoutingCursor n H ι → CompletionLog J
  | 0, _, _, _, _, _, _, _, L, _, _, x => L x.1
  | n + 1, _, _, _, _, _, s, label, L, elapsed, k, x =>
      Sum.elim (fun y => L y.1)
        (fun y => cursorLog n (s.next y.1) (fun i => label i.1)
          (s.appendLog label L elapsed k y.1) (fun h => elapsed h.1 + h.2) (k + 1) y.2) x

variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem measurable_cursorLog (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.cursorLog n label L elapsed k) := by
  induction n generalizing H ι k with
  | zero => exact hL.comp measurable_fst
  | succ n ih =>
    apply Measurable.sumElim (hL.comp measurable_fst)
    exact measurable_sigma_elim _ (fun j => ih (s.next j) (fun i => label i.1)
      (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
      (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1))

theorem cursorLog_initial (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) (h : H) :
    s.cursorLog n label L elapsed k (initialRoutingCursor n h) = L h := by cases n <;> rfl

theorem cursorLog_accepted (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (elapsed : H → ℝ)
    (k : ℕ) (j : ι) (x : H × ℝ) :
    s.cursorLog (n + 1) label L elapsed k (acceptedRoutingCursor n label (label j) x) =
      s.appendLog label L elapsed k j x := by
  rw [acceptedRoutingCursor_at_label n label hinj j x]
  exact cursorLog_initial n (s.next j) (fun i => label i.1)
    (s.appendLog label L elapsed k j) (fun h => elapsed h.1 + h.2) (k + 1) x

theorem cursorLog_current (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) (x : H × ℝ) :
    s.cursorLog (n + 1) label L elapsed k (.inl x) = L x.1 := rfl

end StochasticMatching.PosteriorStage
