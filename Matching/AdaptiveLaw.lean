import Matching.AdaptivePlan

/-! The exact law of a finite adaptive execution. This constructs one
measurable function on the incoming sample space and proves its distribution
by induction over the complete tree, including all terminal branches.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StochasticMatching.AdaptivePlan

universe u v w

variable {E : Type w} [MeasurableSpace E]

noncomputable def law : {n : ℕ} → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    AdaptivePlan E n H ι → Measure H → Measure E
  | 0, _, _, _, _, _, p, ν => Measure.map p.down.value ν
  | n + 1, _, _, _, _, _, p, ν =>
      Measure.map p.2.1.value (p.1.terminalHistoryMeasure ν) +
        Measure.sum (fun j => law (p.2.2 j) (p.1.markedHistoryMeasure ν j))

theorem run_terminal_law {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (p : AdaptivePlan E (n + 1) H ι) (ν : Measure H) :
    Measure.map (run p) ((ν.prod independentExponentials).restrict p.1.terminalEvent) =
      Measure.map p.2.1.value (p.1.terminalHistoryMeasure ν) := by
  have hfst : Measure.map (Prod.fst : H × (ι → ℝ) → H)
      ((ν.prod independentExponentials).restrict p.1.terminalEvent) =
      p.1.terminalHistoryMeasure ν := by
    have h := congrArg (Measure.map (Prod.fst : H × (ι → ℝ) → H))
      (p.1.terminal_factorization ν)
    rw [Measure.map_map measurable_fst
      (measurable_residualObservation p.1.measurable_terminalThreshold)] at h
    simpa only [Function.comp_def, residualObservation, Measure.map_fst_prod,
      measure_univ, one_smul] using h
  calc
    _ = Measure.map (p.2.1.value ∘ Prod.fst)
        ((ν.prod independentExponentials).restrict p.1.terminalEvent) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem p.1.measurable_terminalEvent] with x hx
      exact run_of_terminal p hx
    _ = Measure.map p.2.1.value (Measure.map Prod.fst
        ((ν.prod independentExponentials).restrict p.1.terminalEvent)) :=
      (Measure.map_map p.2.1.measurable_value measurable_fst).symm
    _ = _ := by rw [hfst]

theorem run_winner_law {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (p : AdaptivePlan E (n + 1) H ι) (ν : Measure H) (j : ι) :
    Measure.map (run p) ((ν.prod independentExponentials).restrict (p.1.winner j)) =
      Measure.map (run (p.2.2 j)) ((p.1.markedHistoryMeasure ν j).prod independentExponentials) := by
  calc
    _ = Measure.map (run (p.2.2 j) ∘ p.1.observation j)
        ((ν.prod independentExponentials).restrict (p.1.winner j)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (p.1.measurable_winner j)] with x hx
      exact run_of_winner p hx
    _ = Measure.map (run (p.2.2 j)) (Measure.map (p.1.observation j)
        ((ν.prod independentExponentials).restrict (p.1.winner j))) :=
      (Measure.map_map (measurable_run _) (p.1.measurable_observation j)).symm
    _ = _ := by rw [p.1.first_completion_factorization]

theorem run_law {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (p : AdaptivePlan E n H ι) (ν : Measure H) :
    Measure.map (run p) (ν.prod independentExponentials) = law p ν := by
  induction n generalizing H ι with
  | zero =>
    change Measure.map (p.down.value ∘ Prod.fst) (ν.prod independentExponentials) =
      Measure.map p.down.value ν
    rw [← Measure.map_map p.down.measurable_value measurable_fst]
    simp
  | succ n ih =>
    calc
      _ = Measure.map (run p)
          ((ν.prod independentExponentials).restrict p.1.terminalEvent +
            Measure.sum (fun j => (ν.prod independentExponentials).restrict (p.1.winner j))) :=
        congrArg (Measure.map (run p)) (p.1.segment_measure_decomposition ν)
      _ = Measure.map (run p) ((ν.prod independentExponentials).restrict p.1.terminalEvent) +
          Measure.sum (fun j => Measure.map (run p)
            ((ν.prod independentExponentials).restrict (p.1.winner j))) := by
        rw [Measure.map_add _ _ (measurable_run p), Measure.map_sum (measurable_run p).aemeasurable]
      _ = law p ν := by
        change _ = Measure.map p.2.1.value (p.1.terminalHistoryMeasure ν) +
          Measure.sum (fun j => law (p.2.2 j) (p.1.markedHistoryMeasure ν j))
        rw [run_terminal_law]
        congr 1
        congr 1
        funext j
        rw [run_winner_law, ih]

theorem law_isProbability {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (p : AdaptivePlan E n H ι) (ν : Measure H) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (law p ν) := by
  rw [← run_law]
  exact isProbabilityMeasure_map (measurable_run p).aemeasurable

end StochasticMatching.AdaptivePlan
