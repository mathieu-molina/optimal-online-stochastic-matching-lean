import Matching.HistoryRenewalStreams

/-! Positivity, nonexplosion, and valid next-event branches hold on the
single original stream sample, simultaneously at every iteration. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {σ H : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ] [MeasurableSpace H]

theorem independentRenewalStreams_head_law :
    Measure.map (fun z : σ → ℕ → ℝ => fun s => z s 0) independentRenewalStreams =
      independentExponentials := by
  have h := congrArg (Measure.map (Prod.fst : (σ → ℝ) × (σ → ℕ → ℝ) → _))
    (independentRenewalStreams_split_law (σ := σ))
  rw [Measure.map_map measurable_fst measurable_splitRenewalStreams,
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem independentRenewalStreams_all_pos :
    ∀ᵐ z : σ → ℕ → ℝ ∂independentRenewalStreams, ∀ s n, 0 < z s n := by
  apply ae_all_iff.mpr
  intro s
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : σ => infiniteExponentials) (i := s) infiniteExponentials_all_pos

theorem independentRenewalStreams_unbounded :
    ∀ᵐ z : σ → ℕ → ℝ ∂independentRenewalStreams,
      ∀ s T, ∃ n, T < renewalPartialSum (z s) n := by
  apply ae_all_iff.mpr
  intro s
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : σ => infiniteExponentials) (i := s) infiniteExponentials_unbounded

def RenewalStreamGood (p : HistoryServiceFamily H σ) (x : H × (σ → ℕ → ℝ)) : Prop :=
  (∀ s, 0 < x.2 s 0) ∧
    ((fun s => x.2 s 0) ∈ (p.curves x.1).terminalSurvival ∨
      ∃ j, (fun s => x.2 s 0) ∈ variableWinner (p.curves x.1).service (p.curves x.1).deadline j)

theorem measurableSet_renewalStreamGood (p : HistoryServiceFamily H σ) :
    MeasurableSet {x | RenewalStreamGood p x} := by
  have hm : Measurable (fun x : H × (σ → ℕ → ℝ) => (x.1, fun s => x.2 s 0)) :=
    measurable_fst.prodMk (measurable_splitRenewalStreams.fst.comp measurable_snd)
  have hpos : MeasurableSet {x : H × (σ → ℕ → ℝ) | ∀ s, 0 < x.2 s 0} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun s => measurableSet_lt measurable_const
      ((measurable_pi_apply s).comp hm.snd))
  have he : {x | RenewalStreamGood p x} = {x | ∀ s, 0 < x.2 s 0} ∩
      (fun x : H × (σ → ℕ → ℝ) => (x.1, fun s => x.2 s 0)) ⁻¹'
        (p.terminalEvent ∪ ⋃ j, p.winner j) := by
    ext x
    simp [RenewalStreamGood, HistoryServiceFamily.terminalEvent, historySurvival,
      ServiceCurveFamily.terminalSurvival, survivalBox, HistoryServiceFamily.terminalThreshold,
      HistoryServiceFamily.winner]
  rw [he]
  exact hpos.inter (hm (p.measurable_terminalEvent.union (MeasurableSet.iUnion p.measurable_winner)))

theorem renewalStreamGood_ae (p : HistoryServiceFamily H σ) (μ : Measure H) :
    ∀ᵐ x ∂μ.prod independentRenewalStreams, RenewalStreamGood p x := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_renewalStreamGood p)).mpr
  apply Filter.Eventually.of_forall
  intro h
  have hhead := (measurable_splitRenewalStreams (σ := σ)).fst
  have hg : ∀ᵐ v ∂Measure.map (fun z : σ → ℕ → ℝ => fun s => z s 0) independentRenewalStreams,
      (∀ s, 0 < v s) ∧ (v ∈ (p.curves h).terminalSurvival ∨
        ∃ j, v ∈ variableWinner (p.curves h).service (p.curves h).deadline j) := by
    rw [independentRenewalStreams_head_law]
    filter_upwards [independentExponentials_ae_pos, (p.curves h).no_completion_or_unique_ae] with z hp he
    exact ⟨hp, he.imp_right (fun ⟨j, hj, _⟩ => ⟨j, hj⟩)⟩
  exact ae_of_ae_map hhead.aemeasurable hg

theorem poissonStreamUpdate_all_good (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) (h : H) :
    ∀ᵐ z ∂independentRenewalStreams, ∀ n,
      RenewalStreamGood (constantRateHistory c hc D hD hpos)
        ((poissonStreamUpdate c hc D hD hpos U)^[n] (h, z)) := by
  apply ae_all_iff.mpr
  intro n
  have hm : Measurable (fun z => (poissonStreamUpdate c hc D hD hpos U)^[n] (h, z)) :=
    ((measurable_poissonStreamUpdate c hc D hD hpos U hU).iterate n).comp measurable_prodMk_left
  apply ae_of_ae_map hm.aemeasurable
  rw [poissonStreamUpdate_iterate_law c hc D hD hpos U hU n h]
  exact renewalStreamGood_ae _ _

end StochasticMatching
