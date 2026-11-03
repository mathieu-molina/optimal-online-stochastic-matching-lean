import Matching.FiniteRoutingLaw
import Matching.GeometricTermination
import Matching.RoutingTerminationMass

/-! Complete stopped routing trajectories. Their input projection is the
arrival-only trajectory law; bounded horizons imply finite termination.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory
namespace StochasticMatching
variable {H B ι σ : Type*} [MeasurableSpace H] [MeasurableSpace B]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def routingTransition (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) : Kernel H (Unit ⊕ H) :=
  letI := historyRoutingKernel_markov N capacity hc p hp
  eventUpdateKernel (historyRoutingKernel N capacity p) U

theorem routingTransition_markov (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U) :
    IsMarkovKernel (routingTransition N capacity hc p hp U) := by
  letI := historyRoutingKernel_markov N capacity hc p hp
  exact eventUpdateKernel_markov _ U hU

noncomputable def onlineRoutingTrajectory (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U) (h : H) :
    Measure (ℕ → Unit ⊕ H) :=
  letI := routingTransition_markov N capacity hc p hp U hU
  markovTrajectory (absorbingKernel (routingTransition N capacity hc p hp U)) (Sum.inr h)

noncomputable def inputTransition (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) : Kernel B (Unit ⊕ B) :=
  letI := poissonInputKernel_markov capacity hc D hD hpos
  eventUpdateKernel (poissonInputKernel capacity D hD) V

theorem inputTransition_markov (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V) :
    IsMarkovKernel (inputTransition capacity hc D hD hpos V) := by
  letI := poissonInputKernel_markov capacity hc D hD hpos
  exact eventUpdateKernel_markov _ V hV

noncomputable def poissonInputTrajectory (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V) (b : B) :
    Measure (ℕ → Unit ⊕ B) :=
  letI := inputTransition_markov capacity hc D hD hpos V hV
  markovTrajectory (absorbingKernel (inputTransition capacity hc D hD hpos V)) (Sum.inr b)

theorem stopped_routing_input_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V)
    (f : H → B) (hf : Measurable f)
    (hdeadline : ∀ h, (p.curves h).deadline = D (f h))
    (hupdate : ∀ h e, Sum.map id f (U (h, e)) = V (f h, arrivalTypeProjection e)) (h : H) :
    Measure.map (fun z : ℕ → Unit ⊕ H => fun n => Sum.map id f (z n))
        (onlineRoutingTrajectory N capacity hc p hp U hU h) =
      poissonInputTrajectory capacity hc D hD hpos V hV (f h) := by
  letI := historyRoutingKernel_markov N capacity hc p hp
  letI := poissonInputKernel_markov capacity hc D hD hpos
  letI := routingTransition_markov N capacity hc p hp U hU
  letI := inputTransition_markov capacity hc D hD hpos V hV
  apply absorbingTrajectory_projection _ _ f hf _ (Sum.inr h)
  apply eventUpdateKernel_projection _ _ U hU V hV f
    arrivalTypeProjection measurable_arrivalTypeProjection (Sum.map id f) (measurable_id.sumMap hf) _ hupdate
  intro h
  change Measure.map arrivalTypeProjection (historyRoutingKernel N capacity p h) =
    poissonNextArrival capacity (D (f h))
  rw [historyRoutingKernel_type_law N capacity hc p hp h, hdeadline h]

theorem onlineRoutingTrajectory_finite_termination (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U)
    (hterm : ∀ h, U (h, Sum.inl ()) = Sum.inl ())
    (T : ℝ) (hbound : ∀ h, (p.curves h).deadline ≤ T) (h : H) :
    ∀ᵐ z ∂onlineRoutingTrajectory N capacity hc p hp U hU h, ∃ n, z n = Sum.inl () := by
  letI := historyRoutingKernel_markov N capacity hc p hp
  letI := routingTransition_markov N capacity hc p hp U hU
  apply absorbingTrajectory_finite_termination _
    (1 - ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * T))))
    (routing_continuation_bound_lt_one capacity T) _ (Sum.inr h)
  intro a
  change eventUpdateKernel (historyRoutingKernel N capacity p) U a (Set.range Sum.inr) ≤ _
  rw [eventUpdateKernel_apply _ U hU]
  have hu : Measurable (fun e => U (a, e)) := hU.comp measurable_prodMk_left
  rw [Measure.map_apply hu measurableSet_range_inr]
  apply le_trans (measure_mono ?_) (routingNextArrival_continuation_bound N capacity hc (p.curves a) (hp a) T (hbound a))
  intro e he
  cases e with
  | inl u =>
      cases u
      change U (a, Sum.inl ()) ∈ Set.range Sum.inr at he
      rw [hterm a] at he
      simpa using he
  | inr e => exact ⟨e, rfl⟩

end StochasticMatching
