import Matching.MeasurableBranching

/-! Finite adaptive decision trees. Each node selects service curves from
the observed history, and each completion adds its time to that history and
removes the winning label. Outputs at terminal or cutoff nodes use history
only, without reading the unobserved residual demands.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StochasticMatching

universe u v w

structure HistoryOutput (H : Type u) (E : Type w)
    [MeasurableSpace H] [MeasurableSpace E] where
  value : H → E
  measurable_value : Measurable value

def AdaptivePlan (E : Type w) [MeasurableSpace E] :
    (n : ℕ) → (H : Type u) → (ι : Type v) →
      [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] → Type (max u v w)
  | 0, H, _, _, _, _ => ULift.{v} (HistoryOutput H E)
  | n + 1, H, ι, _, _, _ => HistoryServiceFamily H ι × HistoryOutput H E ×
      ((j : ι) → AdaptivePlan E n (H × ℝ) {i : ι // i ≠ j})

namespace AdaptivePlan

variable {E : Type w} [MeasurableSpace E]

noncomputable def run : {n : ℕ} → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    AdaptivePlan E n H ι → H × (ι → ℝ) → E
  | 0, _, _, _, _, _, p, x => p.down.value x.1
  | n + 1, _, _, _, _, _, p, x =>
      branchSelect p.1.winner (fun j y => run (p.2.2 j) (p.1.observation j y))
        (fun y => p.2.1.value y.1) x

theorem measurable_run {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι] (p : AdaptivePlan E n H ι) :
    Measurable (run p) := by
  induction n generalizing H ι with
  | zero => exact p.down.measurable_value.comp measurable_fst
  | succ n ih =>
    exact measurable_branchSelect p.1.winner_disjoint p.1.measurable_winner
      (fun j => (ih (p.2.2 j)).comp (p.1.measurable_observation j))
      (p.2.1.measurable_value.comp measurable_fst)

theorem run_of_winner {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι] (p : AdaptivePlan E (n + 1) H ι)
    {j : ι} {x : H × (ι → ℝ)} (hx : x ∈ p.1.winner j) :
    run p x = run (p.2.2 j) (p.1.observation j x) :=
  branchSelect_of_mem p.1.winner_disjoint _ _ hx

theorem run_of_terminal {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι] (p : AdaptivePlan E (n + 1) H ι)
    {x : H × (ι → ℝ)} (hx : x ∈ p.1.terminalEvent) :
    run p x = p.2.1.value x.1 := by
  apply branchSelect_of_not_mem
  intro j hj
  exact Set.disjoint_left.mp (p.1.winner_disjoint_terminal j) hx hj

end AdaptivePlan
end StochasticMatching
