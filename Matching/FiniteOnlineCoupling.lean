import Matching.LatentExponentialCoupling
import Matching.HistoryRejectionClock

/-! Finite arrival-history coupling. Routing and a concrete residual-demand
simulation have exactly the same law after every number of arrivals. The
simulation samples a fresh auxiliary clock, carries surviving job demands
forward, and recycles only the newly inactive coordinate.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ProbabilityTheory
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def routingJobUpdate (V : H × (Unit ⊕ (ℝ × Option ι)) → H) :
    H × (Unit ⊕ (ℝ × (σ × Option ι))) → H :=
  fun x => V (x.1, arrivalJobProjection x.2)

theorem measurable_routingJobUpdate (V : H × (Unit ⊕ (ℝ × Option ι)) → H) (hV : Measurable V) :
    Measurable (routingJobUpdate (σ := σ) V) :=
  hV.comp (measurable_fst.prodMk (measurable_arrivalJobProjection.comp measurable_snd))

theorem routing_job_update_kernel_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (V : H × (Unit ⊕ (ℝ × Option ι)) → H) (hV : Measurable V) :
    letI := historyRoutingKernel_markov N capacity hc p hp
    eventUpdateKernel (historyRoutingKernel N capacity p) (routingJobUpdate V) =
      eventUpdateKernel (historyEventKernel (p.withRejectionClock (∑ s, capacity s)
        (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht)))) V := by
  try dsimp only
  letI := historyRoutingKernel_markov N capacity hc p hp
  let q := p.withRejectionClock (∑ s, capacity s)
    (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))
  ext h : 1
  rw [eventUpdateKernel_apply _ _ (measurable_routingJobUpdate V hV), eventUpdateKernel_apply _ V hV,
    ← history_routing_job_kernel_law N capacity hc p hp,
    Kernel.map_apply _ measurable_arrivalJobProjection]
  have hv : Measurable (fun e => V (h, e)) := hV.comp measurable_prodMk_left
  rw [Measure.map_map hv measurable_arrivalJobProjection]
  rfl

theorem finite_online_residual_coupling (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (V : H × (Unit ⊕ (ℝ × Option ι)) → H) (hV : Measurable V) (n : ℕ) (h : H) :
    letI := historyRoutingKernel_markov N capacity hc p hp
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))
    (iterateKernel (latentExponentialKernel q V) n ∘ₖ
      freshResidualKernel (independentExponentials (ι := ι))) h =
      (iterateKernel (eventUpdateKernel (historyRoutingKernel N capacity p) (routingJobUpdate V)) n h).prod
        (independentExponentials (ι := ι)) := by
  try dsimp only
  letI := historyRoutingKernel_markov N capacity hc p hp
  let q := p.withRejectionClock (∑ s, capacity s)
    (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))
  rw [routing_job_update_kernel_law N capacity hc p hp V hV]
  exact latentExponential_residual_factorization q V hV n h

theorem finite_online_history_coupling (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (V : H × (Unit ⊕ (ℝ × Option ι)) → H) (hV : Measurable V) (n : ℕ) :
    letI := historyRoutingKernel_markov N capacity hc p hp
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))
    (iterateKernel (latentExponentialKernel q V) n ∘ₖ
      freshResidualKernel (independentExponentials (ι := ι))).map Prod.fst =
      iterateKernel (eventUpdateKernel (historyRoutingKernel N capacity p) (routingJobUpdate V)) n := by
  try dsimp only
  letI := historyRoutingKernel_markov N capacity hc p hp
  let q := p.withRejectionClock (∑ s, capacity s)
    (fun h t ht => supplyRegion_total_rate_le N capacity hc (hp h t ht))
  rw [routing_job_update_kernel_law N capacity hc p hp V hV]
  exact latentExponential_history_law q V hV n

end StochasticMatching
