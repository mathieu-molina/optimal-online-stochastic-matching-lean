import Matching.RenewalStreamReplenish
import Matching.PoissonFirstArrival
import Matching.FirstEventRestart

/-! Joint next-event and full-future-stream law. This retains the actual
surviving waiting amounts and consumes only the winning type's head. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

namespace ServiceCurveFamily

noncomputable def renewalBranch (p : ServiceCurveFamily σ) (j : σ)
    (x : (σ → ℝ) × (σ → ℕ → ℝ)) : ℝ × (σ → ℕ → ℝ) :=
  let o := variableObservation p.service p.deadline j x.1
  (o.1, replenishRenewalStreams j (o.2, x.2))

theorem measurable_renewalBranch (p : ServiceCurveFamily σ) (j : σ) :
    Measurable (p.renewalBranch j) :=
  ((p.measurable_observation j).fst.comp measurable_fst).prodMk
    ((measurable_replenishRenewalStreams j).comp
      (((p.measurable_observation j).snd.comp measurable_fst).prodMk measurable_snd))

theorem renewalBranch_law (p : ServiceCurveFamily σ) (j : σ) :
    Measure.map (p.renewalBranch j)
      ((independentExponentials.restrict (variableWinner p.service p.deadline j)).prod
        independentRenewalStreams) =
      (variableMarkedTimeMeasure p.service p.rate p.deadline j).prod independentRenewalStreams := by
  let μ := variableMarkedTimeMeasure p.service p.rate p.deadline j
  letI : SigmaFinite μ := by unfold μ variableMarkedTimeMeasure; infer_instance
  have ho : MeasurePreserving (variableObservation p.service p.deadline j)
      (independentExponentials.restrict (variableWinner p.service p.deadline j))
      (μ.prod (independentExponentials (ι := {i : σ // i ≠ j}))) :=
    ⟨p.measurable_observation j, variable_first_completion_marked_law
      p.service_continuous p.rate_continuous p.deadline_pos p.service_monotone
      p.service_zero p.rate_nonneg p.service_deriv j⟩
  have hp := ho.prod (MeasurePreserving.id (independentRenewalStreams (σ := σ)))
  have ha := measurePreserving_prodAssoc μ
    (independentExponentials (ι := {i : σ // i ≠ j})) (independentRenewalStreams (σ := σ))
  have hr := (MeasurePreserving.id μ).prod
    (show MeasurePreserving (replenishRenewalStreams j)
      (independentExponentials.prod independentRenewalStreams) independentRenewalStreams from
      ⟨measurable_replenishRenewalStreams j, independentRenewalStreams_replenish_law j⟩)
  exact (hr.comp (ha.comp hp)).map_eq

noncomputable def renewalTerminal (p : ServiceCurveFamily σ)
    (x : (σ → ℝ) × (σ → ℕ → ℝ)) : σ → ℕ → ℝ :=
  prependRenewalStreams ((fun i => x.1 i - p.service i p.deadline), x.2)

theorem measurable_renewalTerminal (p : ServiceCurveFamily σ) :
    Measurable p.renewalTerminal :=
  measurable_prependRenewalStreams.comp
    (((measurable_subtract_threshold _).comp measurable_fst).prodMk measurable_snd)

theorem renewalTerminal_law (p : ServiceCurveFamily σ) :
    Measure.map p.renewalTerminal
      ((independentExponentials.restrict p.terminalSurvival).prod independentRenewalStreams) =
      independentExponentials p.terminalSurvival • (independentRenewalStreams (σ := σ)) := by
  have hv : Measure.map (fun z i => z i - p.service i p.deadline)
      (independentExponentials.restrict p.terminalSurvival) =
      independentExponentials p.terminalSurvival • (independentExponentials (ι := σ)) := by
    change vectorResidualLaw (fun i => p.service i p.deadline) =
      independentExponentials (survivalBox (fun i => p.service i p.deadline)) • _
    rw [vectorResidualLaw_eq_smul (p.service_nonneg ⟨p.deadline_pos.le, le_rfl⟩),
      survivalBox_measure (p.service_nonneg ⟨p.deadline_pos.le, le_rfl⟩)]
  have hm := Measure.map_prod_map (independentExponentials.restrict p.terminalSurvival)
    (independentRenewalStreams (σ := σ))
    (measurable_subtract_threshold (fun i => p.service i p.deadline)) measurable_id
  rw [Measure.map_id, hv] at hm
  have h := congrArg (Measure.map (prependRenewalStreams (σ := σ))) hm
  rw [finite_smul_measure_prod _ _ _ (measure_ne_top _ _), Measure.map_smul,
    independentRenewalStreams_prepend_law,
    Measure.map_map measurable_prependRenewalStreams
      ((measurable_subtract_threshold (fun i => p.service i p.deadline)).prodMap measurable_id)] at h
  exact h.symm

noncomputable def renewalRestart (p : ServiceCurveFamily σ)
    (x : (σ → ℝ) × (σ → ℕ → ℝ)) : (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ) :=
  branchSelect (fun j => Prod.fst ⁻¹' variableWinner p.service p.deadline j)
    (fun j x => (Sum.inr ((p.renewalBranch j x).1, j), (p.renewalBranch j x).2))
    (fun x => (Sum.inl (), p.renewalTerminal x)) x

theorem renewalWinner_disjoint (p : ServiceCurveFamily σ) :
    Pairwise (fun i j => Disjoint
      (Prod.fst ⁻¹' variableWinner p.service p.deadline i : Set ((σ → ℝ) × (σ → ℕ → ℝ)))
      (Prod.fst ⁻¹' variableWinner p.service p.deadline j)) := by
  intro i j hij
  exact (p.winner_disjoint hij).preimage Prod.fst

theorem measurable_renewalRestart (p : ServiceCurveFamily σ) : Measurable p.renewalRestart := by
  apply measurable_branchSelect p.renewalWinner_disjoint
    (fun j => measurable_fst (p.measurable_winner j))
  · intro j
    exact (measurable_inr.comp ((p.measurable_renewalBranch j).fst.prodMk measurable_const)).prodMk
      (p.measurable_renewalBranch j).snd
  · exact measurable_const.prodMk p.measurable_renewalTerminal

theorem renewalRestart_of_winner (p : ServiceCurveFamily σ) (j : σ)
    {x : (σ → ℝ) × (σ → ℕ → ℝ)} (hx : x.1 ∈ variableWinner p.service p.deadline j) :
    p.renewalRestart x = (Sum.inr ((p.renewalBranch j x).1, j), (p.renewalBranch j x).2) :=
  branchSelect_of_mem p.renewalWinner_disjoint _ _ hx

theorem renewalRestart_of_terminal (p : ServiceCurveFamily σ)
    {x : (σ → ℝ) × (σ → ℕ → ℝ)} (hx : x.1 ∈ p.terminalSurvival) :
    p.renewalRestart x = (Sum.inl (), p.renewalTerminal x) := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hx

theorem renewalRestart_branch_law (p : ServiceCurveFamily σ) (j : σ) :
    Measure.map p.renewalRestart
      ((independentExponentials.restrict (variableWinner p.service p.deadline j)).prod
        independentRenewalStreams) =
      (Measure.map (fun t => (Sum.inr (t, j) : Unit ⊕ (ℝ × σ)))
        (variableMarkedTimeMeasure p.service p.rate p.deadline j)).prod
        (independentRenewalStreams (σ := σ)) := by
  letI : SigmaFinite (variableMarkedTimeMeasure p.service p.rate p.deadline j) := by
    unfold variableMarkedTimeMeasure; infer_instance
  have he : p.renewalRestart =ᵐ[
      (independentExponentials.restrict (variableWinner p.service p.deadline j)).prod
        (independentRenewalStreams (σ := σ))]
      (fun x => (Sum.inr ((p.renewalBranch j x).1, j), (p.renewalBranch j x).2)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem ((p.measurable_winner j).prod MeasurableSet.univ)] with x hx
    exact p.renewalRestart_of_winner j hx.1
  have hf : Measurable (fun t : ℝ => (Sum.inr (t, j) : Unit ⊕ (ℝ × σ))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  have h := Measure.map_prod_map (variableMarkedTimeMeasure p.service p.rate p.deadline j)
    (independentRenewalStreams (σ := σ)) hf measurable_id
  rw [Measure.map_id, ← p.renewalBranch_law j,
    Measure.map_map (hf.prodMap measurable_id) (p.measurable_renewalBranch j)] at h
  rw [Measure.map_congr he]
  exact h.symm

theorem renewalRestart_terminal_law (p : ServiceCurveFamily σ) :
    Measure.map p.renewalRestart
      ((independentExponentials.restrict p.terminalSurvival).prod independentRenewalStreams) =
      (independentExponentials p.terminalSurvival •
        Measure.dirac (Sum.inl () : Unit ⊕ (ℝ × σ))).prod
        (independentRenewalStreams (σ := σ)) := by
  have he : p.renewalRestart =ᵐ[
      (independentExponentials.restrict p.terminalSurvival).prod (independentRenewalStreams (σ := σ))]
      (fun x => (Sum.inl (), p.renewalTerminal x)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem ((measurableSet_survivalBox _).prod MeasurableSet.univ)] with x hx
    exact p.renewalRestart_of_terminal hx.1
  have hf : Measurable (Prod.mk (Sum.inl () : Unit ⊕ (ℝ × σ)) :
      (σ → ℕ → ℝ) → (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ)) := measurable_prodMk_left
  rw [Measure.map_congr he]
  change Measure.map (Prod.mk (Sum.inl () : Unit ⊕ (ℝ × σ)) ∘ p.renewalTerminal) _ = _
  rw [← Measure.map_map hf p.measurable_renewalTerminal, p.renewalTerminal_law,
    Measure.map_smul, ← Measure.dirac_prod,
    finite_smul_measure_prod _ _ _ (measure_ne_top _ _)]

theorem renewalRestart_law (p : ServiceCurveFamily σ) :
    Measure.map p.renewalRestart
      ((independentExponentials (ι := σ)).prod independentRenewalStreams) =
      (Measure.map p.firstEvent independentExponentials).prod
        (independentRenewalStreams (σ := σ)) := by
  letI : ∀ j, SigmaFinite (variableMarkedTimeMeasure p.service p.rate p.deadline j) := fun j => by
    unfold variableMarkedTimeMeasure; infer_instance
  rw [p.segment_measure_decomposition, Measure.add_prod, Measure.prod_sum_left,
    Measure.map_add _ _ p.measurable_renewalRestart,
    Measure.map_sum p.measurable_renewalRestart.aemeasurable]
  simp_rw [p.renewalRestart_terminal_law, p.renewalRestart_branch_law]
  rw [← p.segment_measure_decomposition, p.firstEvent_distribution,
    Measure.add_prod, Measure.prod_sum_left, p.terminal_survival_probability]

noncomputable def streamNextEvent (p : ServiceCurveFamily σ)
    (z : σ → ℕ → ℝ) : (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ) :=
  p.renewalRestart (splitRenewalStreams z)

theorem measurable_streamNextEvent (p : ServiceCurveFamily σ) :
    Measurable p.streamNextEvent := p.measurable_renewalRestart.comp measurable_splitRenewalStreams

theorem streamNextEvent_law (p : ServiceCurveFamily σ) :
    Measure.map p.streamNextEvent independentRenewalStreams =
      (Measure.map p.firstEvent independentExponentials).prod
        (independentRenewalStreams (σ := σ)) := by
  change Measure.map (p.renewalRestart ∘ splitRenewalStreams) independentRenewalStreams = _
  rw [← Measure.map_map p.measurable_renewalRestart measurable_splitRenewalStreams,
    independentRenewalStreams_split_law, p.renewalRestart_law]

end ServiceCurveFamily

theorem poisson_stream_next_event_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (T : ℝ) (hT : 0 < T) :
    Measure.map (constantRateCurve capacity hc T hT).streamNextEvent independentRenewalStreams =
      (poissonNextArrival capacity T).prod (independentRenewalStreams (σ := σ)) := by
  rw [ServiceCurveFamily.streamNextEvent_law, poisson_first_arrival_law]

end StochasticMatching
