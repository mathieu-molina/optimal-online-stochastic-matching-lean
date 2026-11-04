import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
Deterministic bookkeeping for a finite sequence of single-job completions.
The type of job labels stays fixed throughout. This module does not construct
the stochastic policy or establish the law of its completion times.
-/

namespace StochasticMatching

variable {ι : Type*}

structure CompletionState (ι : Type*) where
  served : ι → ℝ
  completed : Finset ι

namespace CompletionState

def initial : CompletionState ι := ⟨fun _ => 0, ∅⟩

def Valid (z : ι → ℝ) (s : CompletionState ι) : Prop :=
  (∀ i, 0 ≤ s.served i) ∧
  (∀ i, s.served i ≤ z i) ∧
  (∀ i, i ∈ s.completed ↔ s.served i = z i)

theorem valid_served_nonneg {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) (i : ι) : 0 ≤ s.served i := hs.1 i

theorem valid_served_le {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) (i : ι) : s.served i ≤ z i := hs.2.1 i

theorem valid_completed_eq {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) {i : ι} (hi : i ∈ s.completed) :
    s.served i = z i := (hs.2.2 i).mp hi

theorem valid_unfinished_lt {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) {i : ι} (hi : i ∉ s.completed) :
    s.served i < z i := by
  apply lt_of_le_of_ne (hs.2.1 i)
  intro heq
  exact hi ((hs.2.2 i).mpr heq)

theorem initial_valid {z : ι → ℝ} (hz : ∀ i, 0 < z i) :
    Valid z initial := by
  refine ⟨fun _ => le_refl _, fun i => le_of_lt (hz i), ?_⟩
  intro i
  simp only [initial, Finset.not_mem_empty, false_iff]
  exact ne_of_lt (hz i)

theorem completed_eq_of_served_eq {z : ι → ℝ} {s t : CompletionState ι}
    (hs : Valid z s) (ht : Valid z t) (h : s.served = t.served) :
    s.completed = t.completed := by
  ext i
  rw [hs.2.2 i, ht.2.2 i, h]

variable [DecidableEq ι]

def afterCompletion (s : CompletionState ι) (u : ι → ℝ) (j : ι) :
    CompletionState ι :=
  ⟨fun i => s.served i + u i, insert j s.completed⟩

theorem afterCompletion_valid {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) (u : ι → ℝ) (j : ι)
    (hu : ∀ i, 0 ≤ u i)
    (hfrozen : ∀ i ∈ s.completed, u i = 0)
    (hj : s.served j + u j = z j)
    (hrest : ∀ i, i ∉ insert j s.completed → s.served i + u i < z i) :
    Valid z (afterCompletion s u j) := by
  refine ⟨fun i => add_nonneg (hs.1 i) (hu i), ?_, ?_⟩
  · intro i
    change s.served i + u i ≤ z i
    by_cases hi : i ∈ insert j s.completed
    · rcases Finset.mem_insert.mp hi with hij | hi
      · subst i
        exact le_of_eq hj
      · rw [hfrozen i hi, add_zero, valid_completed_eq hs hi]
    · exact le_of_lt (hrest i hi)
  · intro i
    change i ∈ insert j s.completed ↔ s.served i + u i = z i
    constructor
    · intro hi
      rcases Finset.mem_insert.mp hi with hij | hi
      · subst i
        exact hj
      · rw [hfrozen i hi, add_zero, valid_completed_eq hs hi]
    · intro heq
      by_contra hi
      exact (ne_of_lt (hrest i hi)) heq

theorem afterCompletion_served_mono (s : CompletionState ι) (u : ι → ℝ)
    (j i : ι) (hu : 0 ≤ u i) :
    s.served i ≤ (afterCompletion s u j).served i := by
  exact le_add_of_nonneg_right hu

theorem afterCompletion_frozen (s : CompletionState ι) (u : ι → ℝ)
    (j i : ι) (hu : u i = 0) :
    (afterCompletion s u j).served i = s.served i := by
  simp [afterCompletion, hu]

theorem afterCompletion_card (s : CompletionState ι) (u : ι → ℝ)
    (j : ι) (hj : j ∉ s.completed) :
    (afterCompletion s u j).completed.card = s.completed.card + 1 := by
  exact Finset.card_insert_of_not_mem hj

/-- Every transition identifies its unique new completion using the original
job type. Validity is a separate invariant, propagated from concrete increments
by `afterCompletion_valid`. -/
structure CompletionStep (s t : CompletionState ι) : Prop where
  event : ∃ j, j ∉ s.completed ∧ t.completed = insert j s.completed
  monotone_service : ∀ i, s.served i ≤ t.served i
  frozen_service : ∀ i ∈ s.completed, t.served i = s.served i

theorem afterCompletion_step (s : CompletionState ι) (u : ι → ℝ) (j : ι)
    (hj : j ∉ s.completed) (hu : ∀ i, 0 ≤ u i)
    (hfrozen : ∀ i ∈ s.completed, u i = 0) :
    CompletionStep s (afterCompletion s u j) := by
  refine ⟨⟨j, hj, rfl⟩, ?_, ?_⟩
  · intro i
    exact afterCompletion_served_mono s u j i (hu i)
  · intro i hi
    exact afterCompletion_frozen s u j i (hfrozen i hi)

theorem CompletionStep.completed_subset {s t : CompletionState ι}
    (h : CompletionStep s t) : s.completed ⊆ t.completed := by
  obtain ⟨j, _, ht⟩ := h.event
  rw [ht]
  exact Finset.subset_insert j s.completed

theorem CompletionStep.card {s t : CompletionState ι}
    (h : CompletionStep s t) : t.completed.card = s.completed.card + 1 := by
  obtain ⟨j, hj, ht⟩ := h.event
  rw [ht, Finset.card_insert_of_not_mem hj]

/-- Exactly `n` successful single-completion transitions. -/
inductive CompletionRun : ℕ → CompletionState ι → CompletionState ι → Prop
  | zero (s) : CompletionRun 0 s s
  | snoc {n s t v} : CompletionRun n s t → CompletionStep t v →
      CompletionRun (n + 1) s v

theorem CompletionRun.completed_subset {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) : s.completed ⊆ t.completed := by
  induction h with
  | zero => exact Finset.Subset.refl _
  | snoc _ step ih => exact Finset.Subset.trans ih step.completed_subset

theorem CompletionRun.served_mono {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) (i : ι) : s.served i ≤ t.served i := by
  induction h with
  | zero => exact le_refl _
  | snoc _ step ih => exact le_trans ih (step.monotone_service i)

theorem CompletionRun.frozen {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) {i : ι} (hi : i ∈ s.completed) :
    t.served i = s.served i := by
  induction h with
  | zero => rfl
  | snoc run step ih =>
      exact (step.frozen_service i (run.completed_subset hi)).trans (ih hi)

theorem CompletionRun.card {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) : t.completed.card = s.completed.card + n := by
  induction h with
  | zero => simp
  | snoc _ step ih => rw [step.card, ih, Nat.add_assoc]

theorem CompletionRun.length_le [Fintype ι] {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) : n ≤ Fintype.card ι - s.completed.card := by
  have hcard := Finset.card_le_univ t.completed
  rw [h.card] at hcard
  omega

theorem CompletionRun.served_eq_of_completed {z : ι → ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : CompletionRun n s t) (hs : Valid z s)
    {i : ι} (hi : i ∈ s.completed) : t.served i = z i := by
  exact (h.frozen hi).trans (valid_completed_eq hs hi)

theorem CompletionRun.exists_new_completion {n : ℕ} {s t : CompletionState ι}
    (h : CompletionRun n s t) (hn : 0 < n) :
    ∃ j, j ∉ s.completed ∧ j ∈ t.completed := by
  cases h with
  | zero => omega
  | snoc run step =>
      obtain ⟨j, hj, ht⟩ := step.event
      refine ⟨j, fun hi => hj (run.completed_subset hi), ?_⟩
      rw [ht]
      exact Finset.mem_insert_self _ _

theorem CompletionRun.some_service_strict {z : ι → ℝ} {n : ℕ}
    {s t : CompletionState ι} (h : CompletionRun n s t)
    (hs : Valid z s) (ht : Valid z t) (hn : 0 < n) :
    ∃ j, s.served j < t.served j := by
  obtain ⟨j, hj, hj'⟩ := h.exists_new_completion hn
  refine ⟨j, ?_⟩
  rw [valid_completed_eq ht hj']
  exact valid_unfinished_lt hs hj

end CompletionState
end StochasticMatching
