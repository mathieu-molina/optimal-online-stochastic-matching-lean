import Matching.PosteriorCursorUpdate

/-! Every genuine arrival advances the concrete posterior cursor by exactly
its waiting time, whether the job is accepted or the arrival is rejected.
-/
open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J]

theorem cursorService_initial_deadline (n : ℕ) (s : PosteriorStage H ι)
    (label : ι → J) (h : H) :
    ((s.cursorService n label).curves (initialRoutingCursor n h)).deadline = s.deadline h := by
  cases n <;>
    change s.deadline h - (s.service.labelled label).shiftOffset (h, 0) = s.deadline h
  all_goals rw [(s.service.labelled label).shiftOffset_eq h 0 le_rfl (s.deadline_pos h), sub_zero]

theorem advanceRoutingTime_bounds (s : PosteriorStage H ι) (label : ι → J)
    (x : H × ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (htT : t < ((s.routingService label).curves x).deadline) :
    0 ≤ (s.advanceRoutingTime label (x, t)).2 ∧
      (s.advanceRoutingTime label (x, t)).2 < s.deadline x.1 := by
  have h0 := (s.service.labelled label).shiftOffset_nonneg x
  change t < s.deadline x.1 - (s.service.labelled label).shiftOffset x at htT
  change 0 ≤ (s.service.labelled label).shiftOffset x + t ∧
    (s.service.labelled label).shiftOffset x + t < s.deadline x.1
  constructor <;> linarith

theorem routingService_advance_deadline (s : PosteriorStage H ι) (label : ι → J)
    (x : H × ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (htT : t < ((s.routingService label).curves x).deadline) :
    ((s.routingService label).curves (s.advanceRoutingTime label (x, t))).deadline =
      ((s.routingService label).curves x).deadline - t := by
  have hb := s.advanceRoutingTime_bounds label x t ht0 htT
  change s.deadline x.1 - (s.service.labelled label).shiftOffset
      (x.1, (s.advanceRoutingTime label (x, t)).2) =
    (s.deadline x.1 - (s.service.labelled label).shiftOffset x) - t
  rw [(s.service.labelled label).shiftOffset_eq _ _ hb.1 hb.2]
  simp only [advanceRoutingTime]
  ring

theorem cursorService_next_initial_deadline (n : ℕ) (s : PosteriorStage H ι)
    (label : ι → J) (j : ι) (x : H × ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (htT : t < ((s.routingService label).curves x).deadline) :
    (((s.next j).cursorService n (fun i => label i.1)).curves
      (initialRoutingCursor n (s.advanceRoutingTime label (x, t)))).deadline =
        ((s.routingService label).curves x).deadline - t := by
  rw [cursorService_initial_deadline]
  have hb := s.advanceRoutingTime_bounds label x t ht0 htT
  change remainingDeadline s.horizon s.deadline (s.advanceRoutingTime label (x, t)) = _
  rw [remainingDeadline_eq s.horizon s.deadline _ hb.1 hb.2 (s.deadline_le x.1)]
  change s.deadline x.1 - ((s.service.labelled label).shiftOffset x + t) =
    (s.deadline x.1 - (s.service.labelled label).shiftOffset x) - t
  ring

theorem currentRoutingStep_deadline (n : ℕ) (s : PosteriorStage H ι)
    (label : ι → J) (x : H × ℝ) (t : ℝ) (a : Option J) (ht0 : 0 ≤ t)
    (htT : t < ((s.routingService label).curves x).deadline) :
    ∃ y, s.currentRoutingStep n label (x, .inr (t, a)) = .inr y ∧
      ((s.cursorService (n + 1) label).curves y).deadline =
        ((s.routingService label).curves x).deadline - t := by
  classical
  cases a with
  | none =>
    exact ⟨.inl (s.advanceRoutingTime label (x, t)), rfl,
      s.routingService_advance_deadline label x t ht0 htT⟩
  | some a =>
    unfold currentRoutingStep
    dsimp only [Sum.elim_inr, Option.elim_some]
    unfold acceptedRoutingCursor
    split_ifs with ha
    · exact ⟨_, rfl, s.cursorService_next_initial_deadline n label ha.choose x t ht0 htT⟩
    · exact ⟨_, rfl, s.routingService_advance_deadline label x t ht0 htT⟩

theorem cursorUpdate_deadline (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) (t : ℝ) (a : Option J) (ht0 : 0 ≤ t)
    (htT : t < ((s.cursorService n label).curves x).deadline) :
    ∃ y, s.cursorUpdate n label (x, .inr (t, a)) = .inr y ∧
      ((s.cursorService n label).curves y).deadline =
        ((s.cursorService n label).curves x).deadline - t := by
  induction n generalizing H ι with
  | zero => exact ⟨_, rfl, s.routingService_advance_deadline label x t ht0 htT⟩
  | succ n ih =>
    cases x with
    | inl x => exact s.currentRoutingStep_deadline n label x t a ht0 htT
    | inr x =>
      obtain ⟨j, x⟩ := x
      obtain ⟨y, hy, hD⟩ := ih (s.next j) (fun i => label i.1) x htT
      refine ⟨.inr ⟨j, y⟩, ?_, hD⟩
      change Sum.map id _ ((s.next j).cursorUpdate n (fun i => label i.1) (x, .inr (t, a))) = _
      rw [hy]
      rfl

end StochasticMatching.PosteriorStage
