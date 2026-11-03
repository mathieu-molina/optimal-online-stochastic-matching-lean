import Matching.CompletionState

/-!
Finite completion runs with elapsed time and a uniform bound on service.
The increment bound is a hypothesis on each segment; proving it from a bounded
measurable service rate is an analytic obligation outside this module.
-/

namespace StochasticMatching
namespace CompletionState

variable {ι : Type*} [DecidableEq ι]

structure BoundedCompletionStep (M dt : ℝ) (s t : CompletionState ι) : Prop
    extends CompletionStep s t where
  duration_nonneg : 0 ≤ dt
  increment_le : ∀ i, t.served i - s.served i ≤ M * dt

inductive TimedCompletionRun (M : ℝ) :
    ℕ → ℝ → CompletionState ι → CompletionState ι → Prop
  | zero (s) : TimedCompletionRun M 0 0 s s
  | snoc {n T dt s t v} : TimedCompletionRun M n T s t →
      BoundedCompletionStep M dt t v → TimedCompletionRun M (n + 1) (T + dt) s v

theorem TimedCompletionRun.toCompletionRun {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) :
    CompletionRun n s t := by
  induction h with
  | zero => exact CompletionRun.zero _
  | snoc _ step ih => exact CompletionRun.snoc ih step.toCompletionStep

theorem TimedCompletionRun.time_nonneg {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) : 0 ≤ T := by
  induction h with
  | zero => exact le_refl _
  | snoc _ step ih => exact add_nonneg ih step.duration_nonneg

theorem TimedCompletionRun.served_le {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) (i : ι) :
    t.served i ≤ s.served i + M * T := by
  induction h with
  | zero => simp
  | snoc _ step ih =>
      have hstep := step.increment_le i
      linarith

theorem TimedCompletionRun.increment_le {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) (i : ι) :
    t.served i - s.served i ≤ M * T := by
  have hb := h.served_le i
  linarith

theorem TimedCompletionRun.increment_nonneg {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) (i : ι) :
    0 ≤ t.served i - s.served i :=
  sub_nonneg.mpr (h.toCompletionRun.served_mono i)

theorem TimedCompletionRun.length_le [Fintype ι] {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t) :
    n ≤ Fintype.card ι - s.completed.card :=
  h.toCompletionRun.length_le

theorem TimedCompletionRun.frozen {M T : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t)
    {i : ι} (hi : i ∈ s.completed) : t.served i = s.served i :=
  h.toCompletionRun.frozen hi

theorem TimedCompletionRun.trans {M T U : ℝ} {n m : ℕ}
    {s t v : CompletionState ι} (h : TimedCompletionRun M n T s t)
    (h' : TimedCompletionRun M m U t v) :
    TimedCompletionRun M (n + m) (T + U) s v := by
  induction h' with
  | zero => simpa using h
  | snoc _ step ih =>
      simpa [Nat.add_assoc, add_assoc] using TimedCompletionRun.snoc (ih h) step

theorem TimedCompletionRun.served_eq_of_time_zero {M : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n 0 s t) (i : ι) :
    t.served i = s.served i := by
  apply le_antisymm
  · simpa using h.served_le i
  · exact h.toCompletionRun.served_mono i

theorem TimedCompletionRun.served_le_deadline {M T deadline : ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : TimedCompletionRun M n T s t)
    (hM : 0 ≤ M) (hT : T ≤ deadline) (i : ι) :
    t.served i ≤ s.served i + M * deadline :=
  (h.served_le i).trans (add_le_add_left (mul_le_mul_of_nonneg_left hT hM) _)

/-- Completion endpoints yield a valid state whenever each individual segment
was checked with `afterCompletion_valid`; this theorem packages the global
nonnegativity and demand cap at the terminal endpoint. -/
theorem TimedCompletionRun.served_mem_interval {M T : ℝ} {n : ℕ}
    {z : ι → ℝ} {s t : CompletionState ι} (h : TimedCompletionRun M n T s t)
    (hs : Valid z s) (ht : Valid z t) (i : ι) :
    0 ≤ t.served i ∧ t.served i ≤ min (z i) (s.served i + M * T) := by
  refine ⟨le_trans (hs.1 i) (h.toCompletionRun.served_mono i), ?_⟩
  exact le_min (ht.2.1 i) (h.served_le i)

theorem TimedCompletionRun.time_pos_of_completion {M T : ℝ} {n : ℕ}
    {z : ι → ℝ} {s t : CompletionState ι} (h : TimedCompletionRun M n T s t)
    (hs : Valid z s) (ht : Valid z t) (hn : 0 < n) : 0 < T := by
  apply lt_of_le_of_ne h.time_nonneg
  intro hzero
  subst T
  obtain ⟨j, hj⟩ := h.toCompletionRun.some_service_strict hs ht hn
  rw [h.served_eq_of_time_zero j] at hj
  exact (lt_irrefl _) hj

end CompletionState
end StochasticMatching
