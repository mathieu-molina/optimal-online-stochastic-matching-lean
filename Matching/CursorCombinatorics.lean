import Matching.CursorCompletionLog
import Matching.LogReward
import Matching.RoutingSupport

/-! Combinatorial state read from the actual posterior routing cursor:
currently available labels and the number of accepted arrivals. -/
open MeasureTheory Set
namespace StochasticMatching
variable {J : Type} [Fintype J] [DecidableEq J]

def cursorDepth : (n : ℕ) → {H ι : Type} → RoutingCursor n H ι → ℕ
  | 0, _, _, _ => 0
  | n + 1, _, _, x => Sum.elim (fun _ => 0) (fun y => cursorDepth n y.2 + 1) x

noncomputable def cursorAvailable : (n : ℕ) → {H ι : Type} → [Fintype ι] → [DecidableEq ι] →
    (ι → J) → RoutingCursor n H ι → Finset J
  | 0, _, _, _, _, _, _ => ∅
  | n + 1, _, _, _, _, label, x => Sum.elim (fun _ => Finset.univ.image label)
      (fun y => cursorAvailable n (fun i => label i.1) y.2) x

variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem measurable_cursorDepth (n : ℕ) : Measurable (cursorDepth (H := H) (ι := ι) n) := by
  induction n generalizing H ι with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_const.sumElim (measurable_sigma_elim _ (fun j => (ih (H := H × ℝ) (ι := {i : ι // i ≠ j})).add_const 1))

theorem cursorDepth_initial (n : ℕ) (h : H) : cursorDepth (ι := ι) n (initialRoutingCursor n h) = 0 := by
  cases n <;> rfl

theorem cursorDepth_le (n : ℕ) (x : RoutingCursor n H ι) : cursorDepth n x ≤ n := by
  induction n generalizing H ι with
  | zero => exact le_rfl
  | succ n ih =>
    cases x with
    | inl x => exact Nat.zero_le _
    | inr x => exact Nat.add_le_add_right (ih x.2) 1

theorem cursorAvailable_subset_labels (n : ℕ) (label : ι → J) (x : RoutingCursor n H ι) :
    cursorAvailable n label x ⊆ Finset.univ.image label := by
  induction n generalizing H ι with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    cases x with
    | inl x => exact Finset.Subset.refl _
    | inr x =>
      intro a ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ih (fun i => label i.1) x.2 ha)
      exact Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, hi⟩

theorem measurable_cursorAvailable [MeasurableSpace (Finset J)] (n : ℕ) (label : ι → J) :
    Measurable (cursorAvailable (H := H) n label) := by
  induction n generalizing H ι with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_const.sumElim (measurable_sigma_elim _ (fun j =>
      ih (H := H × ℝ) (fun i : {i : ι // i ≠ j} => label i.1)))

namespace PosteriorStage
variable [MeasurableSpace J]

theorem cursorLog_length_from_prefix (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ)
    (hL : ∀ h, LogLength k (L h)) (x : RoutingCursor n H ι) :
    LogLength (k + cursorDepth n x) (s.cursorLog n label L elapsed k x) := by
  induction n generalizing H ι k with
  | zero => exact hL x.1
  | succ n ih =>
    cases x with
    | inl x => exact hL x.1
    | inr x =>
      have h := ih (s.next x.1) (fun i => label i.1) (s.appendLog label L elapsed k x.1)
        (fun h => elapsed h.1 + h.2) (k + 1)
        (fun h => s.appendLog_length label L elapsed k x.1 h (hL h.1)) x.2
      convert h using 1 <;> simp only [cursorDepth, Sum.elim_inr] <;> omega

theorem cursorLogReward_eq_depth (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) :
    completionLogReward n (s.cursorLog n label (fun _ => emptyCompletionLog) (fun _ => 0) 0 x) =
      cursorDepth n x := by
  apply completionLogReward_of_length _ _ (cursorDepth_le n x)
  simpa only [zero_add] using s.cursorLog_length_from_prefix n label
    (fun _ => emptyCompletionLog) (fun _ => 0) 0 (fun _ r => by simp [emptyCompletionLog]) x

theorem cursorService_frozen_outside (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) (a : J) (ha : a ∉ cursorAvailable n label x) (t : ℝ) :
    ((s.cursorService n label).curves x).rate a t = 0 := by
  induction n generalizing H ι with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x =>
      apply s.routingService_rate_frozen label a
      intro i hi
      exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    | inr x => exact ih (s.next x.1) (fun i => label i.1) x.2 ha

end PosteriorStage
end StochasticMatching
