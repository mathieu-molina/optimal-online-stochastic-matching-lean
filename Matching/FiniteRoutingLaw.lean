import Matching.PoissonInputKernel
import Matching.StateUpdateKernel

/-! Finite histories retain the prescribed arrival law after erasing the
policy's routing decisions. Histories may remember all previous events.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ProbabilityTheory
namespace StochasticMatching
variable {H B ι σ : Type*} [MeasurableSpace H] [MeasurableSpace B]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def routedStateKernel (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → H) : Kernel H H :=
  letI := historyRoutingKernel_markov N capacity hc p hp
  stateUpdateKernel (historyRoutingKernel N capacity p) U

noncomputable def poissonStateKernel (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → B) : Kernel B B :=
  letI := poissonInputKernel_markov capacity hc D hD hpos
  stateUpdateKernel (poissonInputKernel capacity D hD) V

theorem routedStateKernel_markov (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → H) (hU : Measurable U) :
    IsMarkovKernel (routedStateKernel N capacity hc p hp U) := by
  letI := historyRoutingKernel_markov N capacity hc p hp
  exact stateUpdateKernel_markov _ U hU

theorem finite_routing_input_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → H) (hU : Measurable U)
    (V : B × (Unit ⊕ (ℝ × σ)) → B) (hV : Measurable V)
    (f : H → B) (hf : Measurable f)
    (hdeadline : ∀ h, (p.curves h).deadline = D (f h))
    (hupdate : ∀ h e, f (U (h, e)) = V (f h, arrivalTypeProjection e)) (n : ℕ) (h : H) :
    Measure.map f (iterateKernel (routedStateKernel N capacity hc p hp U) n h) =
      iterateKernel (poissonStateKernel capacity hc D hD hpos V) n (f h) := by
  letI := historyRoutingKernel_markov N capacity hc p hp
  letI := poissonInputKernel_markov capacity hc D hD hpos
  apply stateUpdateKernel_iterate_projection _ _ U hU V hV f hf
    arrivalTypeProjection measurable_arrivalTypeProjection _ hupdate n h
  intro h
  change Measure.map arrivalTypeProjection (historyRoutingKernel N capacity p h) =
    poissonNextArrival capacity (D (f h))
  rw [historyRoutingKernel_type_law N capacity hc p hp h, hdeadline h]

end StochasticMatching
