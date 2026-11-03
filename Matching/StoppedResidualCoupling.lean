import Matching.FiniteOnlineCoupling
import Matching.HistoryServiceAssembly
import Matching.MeasurableCursorBranches

/-! Extend the actual residual simulation through absorbing termination.
This gives the coupling for stopped online algorithms, not just live stages.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def stoppedServiceFamily (p : HistoryServiceFamily H ι) : HistoryServiceFamily (Unit ⊕ H) ι :=
  (HistoryServiceFamily.idle (fun _ : Unit => (1 : ℝ)) measurable_const (fun _ => zero_lt_one)).sum p

theorem stoppedServiceFamily_feasible (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity) :
    ∀ h t, t ∈ Icc 0 ((stoppedServiceFamily p).curves h).deadline →
      (fun i => ((stoppedServiceFamily p).curves h).rate i t) ∈ supplyRegion N capacity := by
  intro h t ht
  cases h with
  | inl _ => exact zero_mem_supplyRegion N capacity hc
  | inr h => exact hp h t ht

def stoppedEventUpdate {E : Type*} (U : H × E → Unit ⊕ H) (x : (Unit ⊕ H) × E) : Unit ⊕ H :=
  Sum.elim (fun _ => .inl ()) (fun h => U (h, x.2)) x.1

theorem measurable_stoppedEventUpdate {E : Type*} [MeasurableSpace E]
    (U : H × E → Unit ⊕ H) (hU : Measurable U) : Measurable (stoppedEventUpdate U) :=
  measurable_sum_prod_elim (fun _ : Unit × E => (Sum.inl () : Unit ⊕ H)) U measurable_const hU

def typedJobEventUpdate (U : H × (Unit ⊕ (ℝ × Option ι)) → Unit ⊕ H)
    (x : H × (Unit ⊕ (ℝ × (σ × Option ι)))) : Unit ⊕ H := U (x.1, arrivalJobProjection x.2)

theorem measurable_typedJobEventUpdate (U : H × (Unit ⊕ (ℝ × Option ι)) → Unit ⊕ H)
    (hU : Measurable U) : Measurable (typedJobEventUpdate (σ := σ) U) :=
  hU.comp (measurable_fst.prodMk (measurable_arrivalJobProjection.comp measurable_snd))

theorem stopped_routing_update_kernel (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × Option ι)) → Unit ⊕ H) (hU : Measurable U) :
    letI := historyRoutingKernel_markov N capacity hc p hp
    letI := historyRoutingKernel_markov N capacity hc (stoppedServiceFamily p)
      (stoppedServiceFamily_feasible N capacity hc p hp)
    eventUpdateKernel (historyRoutingKernel N capacity (stoppedServiceFamily p))
      (routingJobUpdate (stoppedEventUpdate U)) =
      absorbingKernel (eventUpdateKernel (historyRoutingKernel N capacity p) (typedJobEventUpdate U)) := by
  try dsimp only
  letI := historyRoutingKernel_markov N capacity hc p hp
  letI := historyRoutingKernel_markov N capacity hc (stoppedServiceFamily p)
    (stoppedServiceFamily_feasible N capacity hc p hp)
  ext x : 1
  cases x with
  | inl u =>
    rw [eventUpdateKernel_apply _ _ (measurable_routingJobUpdate _ (measurable_stoppedEventUpdate U hU))]
    change Measure.map (fun _ => (Sum.inl () : Unit ⊕ H)) _ = Measure.dirac (Sum.inl ())
    rw [Measure.map_const, measure_univ, one_smul]
  | inr h =>
    change eventUpdateKernel (historyRoutingKernel N capacity (stoppedServiceFamily p))
      (routingJobUpdate (stoppedEventUpdate U)) (Sum.inr h) =
      eventUpdateKernel (historyRoutingKernel N capacity p) (typedJobEventUpdate U) h
    rw [eventUpdateKernel_apply _ _ (measurable_routingJobUpdate _ (measurable_stoppedEventUpdate U hU)),
      eventUpdateKernel_apply _ _ (measurable_typedJobEventUpdate U hU)]
    rfl

theorem stopped_online_residual_coupling (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × Option ι)) → Unit ⊕ H) (hU : Measurable U) (n : ℕ) (h : H) :
    letI := historyRoutingKernel_markov N capacity hc p hp
    let q := (stoppedServiceFamily p).withRejectionClock (∑ a, capacity a)
      (fun x t ht => supplyRegion_total_rate_le N capacity hc
        (stoppedServiceFamily_feasible N capacity hc p hp x t ht))
    (iterateKernel (latentExponentialKernel q (stoppedEventUpdate U)) n ∘ₖ
      freshResidualKernel (independentExponentials (ι := ι))) (.inr h) =
      (iterateKernel (absorbingKernel
        (eventUpdateKernel (historyRoutingKernel N capacity p) (typedJobEventUpdate U))) n (.inr h)).prod
          (independentExponentials (ι := ι)) := by
  try dsimp only
  letI := historyRoutingKernel_markov N capacity hc p hp
  have he := finite_online_residual_coupling N capacity hc (stoppedServiceFamily p)
    (stoppedServiceFamily_feasible N capacity hc p hp) (stoppedEventUpdate U)
    (measurable_stoppedEventUpdate U hU) n (.inr h)
  rw [stopped_routing_update_kernel N capacity hc p hp U hU] at he
  exact he

end StochasticMatching
