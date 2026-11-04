import Matching.NextArrivalDistribution
import Matching.HistoryService
import Mathlib.Probability.Kernel.Basic

/-! Measurable routing kernels for history-dependent service curves.
The probability normalization is proved from the exponential race law.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem measurable_history_routingArrivalMeasure (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : HistoryServiceFamily H ι) (s : σ) (j : Option ι) :
    Measurable (fun h => routingArrivalMeasure N capacity (p.curves h) s j) := by
  let f : H × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (arrivalRoutingRate N capacity (fun i => (p.curves x.1).rate i x.2) s j *
      Real.exp (-(∑ s, capacity s) * x.2))
  have hf : Measurable f := by
    have hr : Measurable (fun x : H × ℝ => fun i => (p.curves x.1).rate i x.2) :=
      measurable_pi_lambda _ p.measurable_rate
    exact (((continuous_arrivalRoutingRate N capacity s j).measurable.comp hr).mul
      ((measurable_const.mul measurable_snd).exp)).ennreal_ofReal
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hm := (hf.indicator p.measurable_timeWindow).lintegral_prod_right' (ν := volume.restrict E)
  convert hm using 1
  funext h
  unfold routingArrivalMeasure
  rw [← withDensity_indicator measurableSet_Icc, withDensity_apply _ hE]
  rfl

theorem measurable_history_routingNextArrival (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : HistoryServiceFamily H ι) :
    Measurable (fun h => routingNextArrival N capacity (p.curves h)) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [routingNextArrival, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ hE]
  apply Measurable.add
  · exact (((measurable_const.mul p.deadline_measurable).neg.exp).ennreal_ofReal).mul_const _
  · apply Measurable.ennreal_tsum
    intro s
    apply Measurable.ennreal_tsum
    intro j
    have hf : Measurable (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    exact (Measure.measurable_coe hE).comp ((Measure.measurable_map _ hf).comp
      (measurable_history_routingArrivalMeasure N capacity p s j))

noncomputable def historyRoutingKernel (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : HistoryServiceFamily H ι) : Kernel H (Unit ⊕ (ℝ × (σ × Option ι))) where
  toFun h := routingNextArrival N capacity (p.curves h)
  measurable' := measurable_history_routingNextArrival N capacity p

theorem historyRoutingKernel_markov (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity) :
    IsMarkovKernel (historyRoutingKernel N capacity p) :=
  ⟨fun h => routingNextArrival_probability N capacity hc (p.curves h) (hp h)⟩

theorem historyRoutingKernel_type_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity) (h : H) :
    Measure.map arrivalTypeProjection (historyRoutingKernel N capacity p h) =
      poissonNextArrival capacity (p.curves h).deadline :=
  routingNextArrival_type_law N capacity hc (p.curves h) (hp h)

end StochasticMatching
