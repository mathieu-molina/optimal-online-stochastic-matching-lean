import Matching.RejectionClockService
import Matching.RoutingHazards

/-! A one-step coupling measure for arrival types, routing decisions and
surviving exponential demands. Summing out types gives the scheduling race;
summing out decisions gives the original constant-rate arrival law.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching

theorem finite_withDensity_ofReal_sum {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (f : κ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    (h0 : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ f k ω) :
    Measure.sum (fun k => μ.withDensity (fun ω => ENNReal.ofReal (f k ω))) =
      μ.withDensity (fun ω => ENNReal.ofReal (∑ k, f k ω)) := by
  rw [← withDensity_tsum (fun k => (hf k).ennreal_ofReal)]
  apply withDensity_congr_ae
  filter_upwards [h0] with ω hω
  simp only [tsum_fintype, Finset.sum_apply]
  exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => hω k)).symm

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def routingArrivalMeasure (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) (s : σ) (j : Option ι) : Measure ℝ :=
  (volume.restrict (Icc 0 p.deadline)).withDensity (fun t =>
    ENNReal.ofReal (arrivalRoutingRate N capacity (fun i => p.rate i t) s j *
      Real.exp (-(∑ s, capacity s) * t)))

instance routingArrivalMeasure_sigmaFinite (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) (s : σ) (j : Option ι) :
    SigmaFinite (routingArrivalMeasure N capacity p s j) := by
  unfold routingArrivalMeasure
  infer_instance

theorem measurable_routingArrivalDensity (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) (s : σ) (j : Option ι) :
    Measurable (fun t => arrivalRoutingRate N capacity (fun i => p.rate i t) s j *
      Real.exp (-(∑ s, capacity s) * t)) := by
  have hr : Continuous (fun t => fun i => p.rate i t) := continuous_pi p.rate_continuous
  exact (((continuous_arrivalRoutingRate N capacity s j).comp hr).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).measurable

theorem routingArrivalMeasure_type_marginal (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) (s : σ) :
    Measure.sum (fun j => routingArrivalMeasure N capacity p s j) =
      (volume.restrict (Icc 0 p.deadline)).withDensity
        (fun t => ENNReal.ofReal (capacity s * Real.exp (-(∑ u, capacity u) * t))) := by
  unfold routingArrivalMeasure
  rw [finite_withDensity_ofReal_sum _ _ (fun j => measurable_routingArrivalDensity N capacity p s j)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact fun j => mul_nonneg (arrivalRoutingRate_nonneg N capacity hc (hp t ht) s j) (Real.exp_pos _).le)]
  congr 1
  funext t
  rw [← Finset.sum_mul, arrivalRoutingRate_type_sum]

theorem routingArrivalMeasure_job_marginal (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (j : Option ι) :
    Measure.sum (fun s => routingArrivalMeasure N capacity p s j) =
      variableMarkedTimeMeasure
        (p.withRejectionClock (∑ s, capacity s) (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))).service
        (p.withRejectionClock (∑ s, capacity s) (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))).rate
        p.deadline j := by
  rw [p.withRejectionClock_marked_density]
  unfold routingArrivalMeasure
  rw [finite_withDensity_ofReal_sum _ _ (fun s => measurable_routingArrivalDensity N capacity p s j)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact fun s => mul_nonneg (arrivalRoutingRate_nonneg N capacity hc (hp t ht) s j) (Real.exp_pos _).le)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [← Finset.sum_mul]
  cases j with
  | none => rw [arrivalRoutingRate_reject_sum N capacity hc (hp t ht)]; rfl
  | some i => rw [arrivalRoutingRate_job_sum N capacity hc (hp t ht)]; rfl

theorem routing_first_event_residual_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (j : Option ι) :
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))
    Measure.map (variableObservation q.service q.deadline j)
      (independentExponentials.restrict (variableWinner q.service q.deadline j)) =
      Measure.sum (fun s => (routingArrivalMeasure N capacity p s j).prod
        (independentExponentials (ι := {i : Option ι // i ≠ j}))) := by
  intro q
  have h := variable_first_completion_marked_law q.service_continuous q.rate_continuous q.deadline_pos
    q.service_monotone q.service_zero q.rate_nonneg q.service_deriv j
  rw [← Measure.prod_sum_left]
  rw [routingArrivalMeasure_job_marginal N capacity hc p hp j]
  exact h

end StochasticMatching
