import Matching.OneStepLaw
import Matching.MeasurableBranching

/-! The full probability distribution of the next event, including an
explicit terminal outcome when no event occurs before the deadline.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def firstEvent (p : ServiceCurveFamily ι) (z : ι → ℝ) : Unit ⊕ (ℝ × ι) :=
  branchSelect (fun j => variableWinner p.service p.deadline j)
    (fun j z => Sum.inr (cappedHit (p.service j) p.deadline (z j), j)) (fun _ => (Sum.inl ())) z

theorem measurable_firstEvent (p : ServiceCurveFamily ι) : Measurable p.firstEvent := by
  apply measurable_branchSelect p.winner_disjoint p.measurable_winner
  · intro j
    exact measurable_inr.comp ((p.measurable_clock j).prodMk measurable_const)
  · exact measurable_const

theorem firstEvent_of_winner (p : ServiceCurveFamily ι) (j : ι) {z : ι → ℝ}
    (hz : z ∈ variableWinner p.service p.deadline j) :
    p.firstEvent z = Sum.inr (cappedHit (p.service j) p.deadline (z j), j) :=
  branchSelect_of_mem p.winner_disjoint _ _ hz

theorem firstEvent_of_terminal (p : ServiceCurveFamily ι) {z : ι → ℝ}
    (hz : z ∈ p.terminalSurvival) : p.firstEvent z = (Sum.inl ()) := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hz

theorem first_event_time_law (p : ServiceCurveFamily ι) (j : ι) :
    Measure.map (fun z : ι → ℝ => cappedHit (p.service j) p.deadline (z j))
      (independentExponentials.restrict (variableWinner p.service p.deadline j)) =
      variableMarkedTimeMeasure p.service p.rate p.deadline j := by
  have h := congrArg (Measure.map (Prod.fst : ℝ × ({i : ι // i ≠ j} → ℝ) → ℝ))
    (variable_first_completion_marked_law p.service_continuous p.rate_continuous p.deadline_pos
      p.service_monotone p.service_zero p.rate_nonneg p.service_deriv j)
  rw [Measure.map_map measurable_fst (p.measurable_observation j), Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

theorem firstEvent_distribution (p : ServiceCurveFamily ι) :
    Measure.map p.firstEvent independentExponentials =
      ENNReal.ofReal (Real.exp (-(∑ i, p.service i p.deadline))) • Measure.dirac (Sum.inl ()) +
        Measure.sum (fun j => Measure.map (fun t => Sum.inr (t, j))
          (variableMarkedTimeMeasure p.service p.rate p.deadline j)) := by
  have hterm : Measure.map p.firstEvent (independentExponentials.restrict p.terminalSurvival) =
      ENNReal.ofReal (Real.exp (-(∑ i, p.service i p.deadline))) • Measure.dirac (Sum.inl ()) := by
    have he : p.firstEvent =ᵐ[independentExponentials.restrict p.terminalSurvival] (fun _ => (Sum.inl ())) := by
      filter_upwards [ae_restrict_mem (measurableSet_survivalBox _)] with z hz
      exact p.firstEvent_of_terminal hz
    rw [Measure.map_congr he, Measure.map_const, Measure.restrict_apply_univ, p.terminal_survival_probability]
  have hbranch : ∀ j, Measure.map p.firstEvent
      (independentExponentials.restrict (variableWinner p.service p.deadline j)) =
      Measure.map (fun t => Sum.inr (t, j)) (variableMarkedTimeMeasure p.service p.rate p.deadline j) := by
    intro j
    have he : p.firstEvent =ᵐ[independentExponentials.restrict (variableWinner p.service p.deadline j)]
        (fun z => Sum.inr (cappedHit (p.service j) p.deadline (z j), j)) := by
      filter_upwards [ae_restrict_mem (p.measurable_winner j)] with z hz
      exact p.firstEvent_of_winner j hz
    have hf : Measurable (fun t : ℝ => (Sum.inr (t, j) : Unit ⊕ (ℝ × ι))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    rw [Measure.map_congr he, ← p.first_event_time_law j,
      Measure.map_map hf (p.measurable_clock j)]
    rfl
  rw [p.segment_measure_decomposition, Measure.map_add _ _ p.measurable_firstEvent,
    Measure.map_sum p.measurable_firstEvent.aemeasurable, hterm]
  simp only [hbranch]

end StochasticMatching.ServiceCurveFamily
