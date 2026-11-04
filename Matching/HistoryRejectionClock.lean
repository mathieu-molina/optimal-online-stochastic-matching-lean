import Matching.HistoryFirstEventRestart
import Matching.HistoryRoutingKernel

/-! Add a rejection clock measurably to every history-dependent service
segment, and identify its event kernel with the routed job projection.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

namespace HistoryServiceFamily

noncomputable def withRejectionClock (p : HistoryServiceFamily H ι) (Λ : ℝ)
    (hΛ : ∀ h t, t ∈ Icc 0 (p.curves h).deadline → ∑ i, (p.curves h).rate i t ≤ Λ) :
    HistoryServiceFamily H (Option ι) where
  curves h := (p.curves h).withRejectionClock Λ (hΛ h)
  deadline_measurable := p.deadline_measurable
  service_at_measurable := by
    intro j t
    cases j with
    | none => exact measurable_const.sub (Finset.measurable_sum _ (fun i _ => p.service_at_measurable i t))
    | some i => exact p.service_at_measurable i t
  rate_at_measurable := by
    intro j t
    cases j with
    | none => exact measurable_const.sub (Finset.measurable_sum _ (fun i _ => p.rate_at_measurable i t))
    | some i => exact p.rate_at_measurable i t

end HistoryServiceFamily

variable [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem history_routing_job_kernel_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity) :
    (historyRoutingKernel N capacity p).map arrivalJobProjection =
      historyEventKernel (p.withRejectionClock (∑ s, capacity s)
        (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))) := by
  ext h : 1
  rw [Kernel.map_apply _ measurable_arrivalJobProjection, historyEventKernel_apply]
  exact routingNextArrival_job_law N capacity hc (p.curves h) (hp h)

end StochasticMatching
