import Matching.LabelledHistoryService
import Matching.HistoryServiceAssembly

/-! A concrete, fixed-label state space for executing the posterior policy
at arrival times. Its finite tree stores which jobs completed; each leaf
stores the posterior history and elapsed time within its current segment.
-/
open MeasureTheory Set
namespace StochasticMatching

def RoutingCursor : ℕ → Type → Type → Type
  | 0, H, _ => H × ℝ
  | n + 1, H, ι => (H × ℝ) ⊕ ((j : ι) × RoutingCursor n (H × ℝ) {i : ι // i ≠ j})

instance routingCursorMeasurable : (n : ℕ) → (H ι : Type) → [MeasurableSpace H] →
    MeasurableSpace (RoutingCursor n H ι)
  | 0, H, _, _ => inferInstanceAs (MeasurableSpace (H × ℝ))
  | n + 1, H, ι, _ => by
      letI := fun j : ι => routingCursorMeasurable n (H × ℝ) {i : ι // i ≠ j}
      exact inferInstanceAs (MeasurableSpace ((H × ℝ) ⊕ ((j : ι) × RoutingCursor n (H × ℝ) {i : ι // i ≠ j})))

def initialRoutingCursor (n : ℕ) {H ι : Type} (h : H) : RoutingCursor n H ι :=
  match n with
  | 0 => (h, 0)
  | _ + 1 => Sum.inl (h, 0)

theorem measurable_initialRoutingCursor (n : ℕ) {H ι : Type} [MeasurableSpace H] :
    Measurable (initialRoutingCursor (H := H) (ι := ι) n) := by
  cases n with
  | zero => exact measurable_id.prodMk measurable_const
  | succ n => exact measurable_inl.comp (measurable_id.prodMk measurable_const)

namespace PosteriorStage
variable {J : Type} [Fintype J] [DecidableEq J]

noncomputable def cursorService : (n : ℕ) → {H ι : Type} → [MeasurableSpace H] →
    [Fintype ι] → [DecidableEq ι] → PosteriorStage H ι → (ι → J) →
    HistoryServiceFamily (RoutingCursor n H ι) J
  | 0, _, _, _, _, _, s, label =>
      HistoryServiceFamily.idle (fun x => ((s.routingService label).curves x).deadline)
        (s.routingService label).deadline_measurable (fun x => ((s.routingService label).curves x).deadline_pos)
  | n + 1, _, _, _, _, _, s, label =>
      (s.routingService label).sum
        (HistoryServiceFamily.sigma (fun j => cursorService n (s.next j) (fun i => label i.1)))

variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem cursorService_rate_mem (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P) (hPclosed : IsClosed P)
    (hPdown : NonnegDownwardClosed P) (hmem : s.data.FeasibleAllocation label P)
    (x : RoutingCursor n H ι) (u : ℝ) (hu : u ∈ Icc 0 ((s.cursorService n label).curves x).deadline) :
    (fun j => ((s.cursorService n label).curves x).rate j u) ∈ P := by
  induction n generalizing H ι with
  | zero => exact hP0
  | succ n ih =>
    cases x with
    | inl x => exact s.routingService_rate_mem label hPc hPclosed hmem x u hu
    | inr x =>
      obtain ⟨j, x⟩ := x
      exact ih (s.next j) (fun i => label i.1) (s.next_feasibleAllocation label hPdown hmem j) x hu

theorem cursorService_deadline_le (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) : ((s.cursorService n label).curves x).deadline ≤ s.horizon := by
  induction n generalizing H ι with
  | zero =>
      exact (sub_le_self _ ((s.service.labelled label).shiftOffset_nonneg x)).trans (s.deadline_le x.1)
  | succ n ih =>
      cases x with
      | inl x =>
        exact (sub_le_self _ ((s.service.labelled label).shiftOffset_nonneg x)).trans (s.deadline_le x.1)
      | inr x => exact ih (s.next x.1) (fun i => label i.1) x.2

end PosteriorStage
end StochasticMatching
