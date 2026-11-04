import Matching.RecycledResidualSlots
import Matching.FirstEventDistribution

/-! Joint law of the next event and a fixed-size fresh residual vector.
Only the newly inactive coordinate may be recycled; every surviving job
keeps its actual residual demand.
-/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching

theorem finite_smul_measure_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure B) [SigmaFinite ν]
    (c : ℝ≥0∞) (hc : c ≠ ∞) : (c • μ).prod ν = c • μ.prod ν := by
  letI : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (measure_lt_top _ _)⟩
  apply Measure.prod_eq
  intro E F hE hF
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, mul_assoc]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

def terminalResidual (p : ServiceCurveFamily (Option ι)) (z : Option ι → ℝ) (i : ι) : ℝ :=
  z (some i) - p.service (some i) p.deadline

theorem measurable_terminalResidual (p : ServiceCurveFamily (Option ι)) : Measurable (terminalResidual p) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply (some i)).sub_const _)

theorem terminalResidual_law (p : ServiceCurveFamily (Option ι)) :
    Measure.map (terminalResidual p) (independentExponentials.restrict p.terminalSurvival) =
      independentExponentials p.terminalSurvival • (independentExponentials (ι := ι)) := by
  have hn := p.service_nonneg ⟨p.deadline_pos.le, le_rfl⟩
  have hv : vectorResidualLaw (fun j => p.service j p.deadline) =
      independentExponentials p.terminalSurvival • (independentExponentials (ι := Option ι)) := by
    rw [vectorResidualLaw_eq_smul hn, ← survivalBox_measure hn]
    rfl
  let f : (Option ι → ℝ) → (ι → ℝ) := fun z i => z (some i)
  have hf : Measurable f := measurable_pi_lambda _ (fun i => measurable_pi_apply (some i))
  have h := congrArg (Measure.map f) hv
  rw [vectorResidualLaw, Measure.map_map hf (measurable_subtract_threshold _), Measure.map_smul,
    independentExponentials_injective_coordinates Option.some (Option.some_injective ι)] at h
  exact h

noncomputable def firstEventRestart (p : ServiceCurveFamily (Option ι)) (z : Option ι → ℝ) :
    (Unit ⊕ (ℝ × Option ι)) × (ι → ℝ) :=
  branchSelect (fun j => variableWinner p.service p.deadline j)
    (fun j z => (Sum.inr ((recycledObservation p j z).1, j), (recycledObservation p j z).2))
    (fun z => (Sum.inl (), terminalResidual p z)) z

theorem measurable_firstEventRestart (p : ServiceCurveFamily (Option ι)) :
    Measurable (firstEventRestart p) := by
  apply measurable_branchSelect p.winner_disjoint p.measurable_winner
  · intro j
    exact (measurable_inr.comp ((measurable_recycledObservation p j).fst.prodMk measurable_const)).prodMk
      (measurable_recycledObservation p j).snd
  · exact measurable_const.prodMk (measurable_terminalResidual p)

theorem firstEventRestart_of_winner (p : ServiceCurveFamily (Option ι)) (j : Option ι)
    {z : Option ι → ℝ} (hz : z ∈ variableWinner p.service p.deadline j) :
    firstEventRestart p z = (Sum.inr ((recycledObservation p j z).1, j), (recycledObservation p j z).2) :=
  branchSelect_of_mem p.winner_disjoint _ _ hz

theorem firstEventRestart_of_terminal (p : ServiceCurveFamily (Option ι))
    {z : Option ι → ℝ} (hz : z ∈ p.terminalSurvival) :
    firstEventRestart p z = (Sum.inl (), terminalResidual p z) := by
  apply branchSelect_of_not_mem
  intro j hj
  exact p.winner_subset_completion j hj hz

theorem firstEventRestart_terminal_law (p : ServiceCurveFamily (Option ι)) :
    Measure.map (firstEventRestart p) (independentExponentials.restrict p.terminalSurvival) =
      (independentExponentials p.terminalSurvival • Measure.dirac (Sum.inl ())).prod
        (independentExponentials (ι := ι)) := by
  have he : firstEventRestart p =ᵐ[independentExponentials.restrict p.terminalSurvival]
      (fun z => (Sum.inl (), terminalResidual p z)) := by
    filter_upwards [ae_restrict_mem (measurableSet_survivalBox _)] with z hz
    exact firstEventRestart_of_terminal p hz
  have hf : Measurable (Prod.mk (Sum.inl () : Unit ⊕ (ℝ × Option ι)) :
      (ι → ℝ) → (Unit ⊕ (ℝ × Option ι)) × (ι → ℝ)) := measurable_prodMk_left
  rw [Measure.map_congr he]
  change Measure.map (Prod.mk (Sum.inl () : Unit ⊕ (ℝ × Option ι)) ∘ terminalResidual p)
    (independentExponentials.restrict p.terminalSurvival) = _
  rw [← Measure.map_map hf (measurable_terminalResidual p),
    terminalResidual_law, Measure.map_smul, ← Measure.dirac_prod,
    finite_smul_measure_prod _ _ _ (measure_ne_top _ _)]

theorem firstEventRestart_branch_law (p : ServiceCurveFamily (Option ι)) (j : Option ι) :
    Measure.map (firstEventRestart p)
      (independentExponentials.restrict (variableWinner p.service p.deadline j)) =
      (Measure.map (fun t => (Sum.inr (t, j) : Unit ⊕ (ℝ × Option ι)))
        (variableMarkedTimeMeasure p.service p.rate p.deadline j)).prod
        (independentExponentials (ι := ι)) := by
  letI : SigmaFinite (variableMarkedTimeMeasure p.service p.rate p.deadline j) := by
    unfold variableMarkedTimeMeasure
    infer_instance
  have he : firstEventRestart p =ᵐ[independentExponentials.restrict (variableWinner p.service p.deadline j)]
      (fun z => (Sum.inr ((recycledObservation p j z).1, j), (recycledObservation p j z).2)) := by
    filter_upwards [ae_restrict_mem (p.measurable_winner j)] with z hz
    exact firstEventRestart_of_winner p j hz
  have hf : Measurable (fun t : ℝ => (Sum.inr (t, j) : Unit ⊕ (ℝ × Option ι))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  have h := Measure.map_prod_map (variableMarkedTimeMeasure p.service p.rate p.deadline j)
    (independentExponentials (ι := ι)) hf measurable_id
  rw [Measure.map_id, ← recycledObservation_law p j,
    Measure.map_map (hf.prodMap measurable_id) (measurable_recycledObservation p j)] at h
  rw [Measure.map_congr he]
  exact h.symm

theorem firstEventRestart_law (p : ServiceCurveFamily (Option ι)) :
    Measure.map (firstEventRestart p) independentExponentials =
      (Measure.map p.firstEvent independentExponentials).prod (independentExponentials (ι := ι)) := by
  letI : ∀ j, SigmaFinite (variableMarkedTimeMeasure p.service p.rate p.deadline j) := fun j => by
    unfold variableMarkedTimeMeasure
    infer_instance
  rw [p.segment_measure_decomposition, Measure.map_add _ _ (measurable_firstEventRestart p),
    Measure.map_sum (measurable_firstEventRestart p).aemeasurable]
  simp_rw [firstEventRestart_terminal_law, firstEventRestart_branch_law]
  rw [← p.segment_measure_decomposition, p.firstEvent_distribution, Measure.add_prod, Measure.prod_sum_left,
    p.terminal_survival_probability]

end StochasticMatching
