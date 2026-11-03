import Matching.IntegratedSegment

/-!
A final service segment may reach the deadline without a completion.
The full finite execution therefore consists of a completion run followed by
one such segment, including the possibility of zero completions.
-/

namespace StochasticMatching
namespace CompletionState

variable {ι : Type*} [DecidableEq ι]

def afterService (s : CompletionState ι) (u : ι → ℝ) : CompletionState ι :=
  ⟨fun i => s.served i + u i, s.completed⟩

theorem afterService_valid {z : ι → ℝ} {s : CompletionState ι} (hs : Valid z s)
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hfrozen : ∀ i ∈ s.completed, u i = 0)
    (hrest : ∀ i, i ∉ s.completed → s.served i + u i < z i) :
    Valid z (afterService s u) := by
  refine ⟨fun i => add_nonneg (hs.1 i) (hu i), ?_, ?_⟩
  · intro i
    change s.served i + u i ≤ z i
    by_cases hi : i ∈ s.completed
    · rw [hfrozen i hi, add_zero, valid_completed_eq hs hi]
    · exact (hrest i hi).le
  · intro i
    change i ∈ s.completed ↔ s.served i + u i = z i
    constructor
    · intro hi
      rw [hfrozen i hi, add_zero, valid_completed_eq hs hi]
    · intro heq
      by_contra hi
      exact (ne_of_lt (hrest i hi)) heq

structure TerminalSegment (M dt : ℝ) (s t : CompletionState ι) : Prop where
  duration_nonneg : 0 ≤ dt
  completed_eq : t.completed = s.completed
  monotone_service : ∀ i, s.served i ≤ t.served i
  frozen_service : ∀ i ∈ s.completed, t.served i = s.served i
  increment_le : ∀ i, t.served i - s.served i ≤ M * dt

omit [DecidableEq ι] in
theorem terminalSegment_zero (M : ℝ) (s : CompletionState ι) :
    TerminalSegment M 0 s s := by
  refine ⟨le_refl _, rfl, fun _ => le_refl _, fun _ _ => rfl, ?_⟩
  intro i
  simp

theorem integrated_terminal_segment {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) (r : ℝ → ι → ℝ) (a b M : ℝ) (hab : a ≤ b)
    (hI : ∀ i, IntervalIntegrable (fun t => r t i) MeasureTheory.volume a b)
    (hlo : ∀ i, ∀ t ∈ Set.Icc a b, 0 ≤ r t i)
    (hhi : ∀ i, ∀ t ∈ Set.Icc a b, r t i ≤ M)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Set.Icc a b, r t i = 0)
    (hrest : ∀ i, i ∉ s.completed → s.served i + segmentWork r a b i < z i) :
    Valid z (afterService s (segmentWork r a b)) ∧
      TerminalSegment M (b - a) s (afterService s (segmentWork r a b)) := by
  have hnonneg := segmentWork_nonneg hab hlo
  have hzero : ∀ i ∈ s.completed, segmentWork r a b i = 0 := by
    intro i hi
    exact segmentWork_zero_of_rate_zero hab i (hfrozen i hi)
  refine ⟨afterService_valid hs _ hnonneg hzero hrest, ?_⟩
  refine ⟨sub_nonneg.mpr hab, rfl, ?_, ?_, ?_⟩
  · intro i
    exact le_add_of_nonneg_right (hnonneg i)
  · intro i hi
    simp [afterService, hzero i hi]
  · intro i
    change s.served i + segmentWork r a b i - s.served i ≤ M * (b - a)
    simpa using segmentWork_le hab hI hhi i

def FiniteExecution (M deadline : ℝ) (n : ℕ) (s t : CompletionState ι) : Prop :=
  ∃ T dt u, TimedCompletionRun M n T s u ∧ TerminalSegment M dt u t ∧ T + dt = deadline

theorem TimedCompletionRun.toExecution {M T : ℝ} {n : ℕ} {s t : CompletionState ι}
    (h : TimedCompletionRun M n T s t) : FiniteExecution M T n s t :=
  ⟨T, 0, t, h, terminalSegment_zero M t, add_zero T⟩

theorem TerminalSegment.toExecution {M dt : ℝ} {s t : CompletionState ι}
    (h : TerminalSegment M dt s t) : FiniteExecution M dt 0 s t :=
  ⟨0, dt, s, TimedCompletionRun.zero s, h, zero_add dt⟩

theorem FiniteExecution.deadline_nonneg {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t) : 0 ≤ deadline := by
  obtain ⟨T, dt, u, run, tail, rfl⟩ := h
  exact add_nonneg run.time_nonneg tail.duration_nonneg

theorem FiniteExecution.card {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t) :
    t.completed.card = s.completed.card + n := by
  obtain ⟨T, dt, u, run, tail, _⟩ := h
  rw [tail.completed_eq, run.toCompletionRun.card]

theorem FiniteExecution.length_le [Fintype ι] {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t) :
    n ≤ Fintype.card ι - s.completed.card := by
  obtain ⟨T, dt, u, run, _, _⟩ := h
  exact run.length_le

theorem FiniteExecution.served_mono {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t) (i : ι) :
    s.served i ≤ t.served i := by
  obtain ⟨T, dt, u, run, tail, _⟩ := h
  exact (run.toCompletionRun.served_mono i).trans (tail.monotone_service i)

theorem FiniteExecution.served_le {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t) (i : ι) :
    t.served i ≤ s.served i + M * deadline := by
  obtain ⟨T, dt, u, run, tail, rfl⟩ := h
  have hrun := run.served_le i
  have htail := tail.increment_le i
  linarith

theorem FiniteExecution.frozen {M deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : FiniteExecution M deadline n s t)
    {i : ι} (hi : i ∈ s.completed) : t.served i = s.served i := by
  obtain ⟨T, dt, u, run, tail, _⟩ := h
  exact (tail.frozen_service i (run.toCompletionRun.completed_subset hi)).trans (run.frozen hi)

end CompletionState
end StochasticMatching
