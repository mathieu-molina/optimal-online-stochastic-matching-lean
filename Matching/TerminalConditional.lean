import Matching.HistoryReconstruction

/-! Conditional expectations of the original sample on the terminal-survival
branch, with finite unnormalized history measures.
-/

open MeasureTheory Set

namespace StochasticMatching.HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

theorem finite_terminalHistoryMeasure (ν : Measure H) [IsFiniteMeasure ν] :
    IsFiniteMeasure (p.terminalHistoryMeasure ν) := by
  have hfst : Measure.map (Prod.fst : H × (ι → ℝ) → H)
      (Measure.map (residualObservation p.terminalThreshold)
        ((ν.prod independentExponentials).restrict p.terminalEvent)) =
      p.terminalHistoryMeasure ν := by
    rw [p.terminal_factorization]
    simp
  rw [← hfst]
  infer_instance

theorem terminal_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    (f : H × (ι → ℝ) → ℝ) (hf : Measurable f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (fun x : H × (ι → ℝ) => ∫ z,
      f (reconstructDemands p.terminalThreshold (x.1, z)) ∂independentExponentials)
      =ᵐ[(ν.prod independentExponentials).restrict p.terminalEvent]
    ((ν.prod independentExponentials).restrict p.terminalEvent)[
      f | (‹MeasurableSpace H›).comap Prod.fst] := by
  letI := p.finite_terminalHistoryMeasure ν
  have hf' : Measurable (fun x => f (reconstructDemands p.terminalThreshold x)) :=
    hf.comp (measurable_reconstructDemands p.measurable_terminalThreshold)
  have hfi : Integrable (fun x => f (reconstructDemands p.terminalThreshold x))
      ((p.terminalHistoryMeasure ν).prod independentExponentials) := by
    apply (integrable_const B).mono' hf'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => hB _)
  have hid := conditionalExpectation_history_transport (p.terminalHistoryMeasure ν)
    ((ν.prod independentExponentials).restrict p.terminalEvent)
    (residualObservation p.terminalThreshold)
    (measurable_residualObservation p.measurable_terminalThreshold)
    (p.terminal_factorization ν) (fun x => f (reconstructDemands p.terminalThreshold x)) hf' hfi
  simpa only [reconstruct_after_observation] using hid

end StochasticMatching.HistoryServiceFamily
