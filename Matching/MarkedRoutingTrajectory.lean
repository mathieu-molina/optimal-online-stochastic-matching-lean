import Matching.RoutedMemory
import Matching.PosteriorLoggedInput

/-! Record the actual routing mark on each arrival. Erasing these marks
recovers exactly the already-verified typed-input policy trajectory. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {H ι σ : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem loggedEventUpdate_erase_marks
    (U : H × RoutedEvent σ ι → Unit ⊕ H) (x : H × RoutedMemory σ ι) (e : RoutedEvent σ ι) :
    Sum.map id (fun y : H × RoutedMemory σ ι => (y.1, routedMemoryInput y.2))
      (loggedEventUpdate U id (x, e)) =
      loggedEventUpdate U arrivalTypeProjection ((x.1, routedMemoryInput x.2), e) := by
  unfold loggedEventUpdate
  cases he : U (x.1, e) with
  | inl u => rfl
  | inr h =>
    change Sum.inr (h, routedMemoryInput (appendEvent (x.2, e))) = _
    rw [routedMemoryInput_append]
    rfl

noncomputable def markedRoutingTrajectory (N : σ → Finset ι) (c : σ → ℝ)
    (hc : ∀ a, 0 ≤ c a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline → (fun i => (p.curves h).rate i t) ∈ supplyRegion N c)
    (U : H × RoutedEvent σ ι → Unit ⊕ H) (hU : Measurable U)
    (x : H × RoutedMemory σ ι) : Measure (ℕ → Unit ⊕ (H × RoutedMemory σ ι)) :=
  onlineRoutingTrajectory N c hc (p.comap Prod.fst measurable_fst) (fun x t ht => hp x.1 t ht)
    (loggedEventUpdate U id) (measurable_loggedEventUpdate U hU id measurable_id) x

theorem markedRoutingTrajectory_erase_marks (N : σ → Finset ι) (c : σ → ℝ)
    (hc : ∀ a, 0 ≤ c a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline → (fun i => (p.curves h).rate i t) ∈ supplyRegion N c)
    (U : H × RoutedEvent σ ι → Unit ⊕ H) (hU : Measurable U) (x : H × RoutedMemory σ ι) :
    Measure.map (fun z : ℕ → Unit ⊕ (H × RoutedMemory σ ι) => fun k =>
      Sum.map id (fun y : H × RoutedMemory σ ι => (y.1, routedMemoryInput y.2)) (z k))
      (markedRoutingTrajectory N c hc p hp U hU x) =
      loggedRoutingTrajectory N c hc p hp U hU (x.1, routedMemoryInput x.2) := by
  let q := p.comap (Prod.fst : H × RoutedMemory σ ι → H) measurable_fst
  let q' := p.comap (Prod.fst : H × ArrivalMemory σ → H) measurable_fst
  let hq := fun (x : H × RoutedMemory σ ι) t ht => hp x.1 t ht
  let hq' := fun (x : H × ArrivalMemory σ) t ht => hp x.1 t ht
  let L := loggedEventUpdate U id
  let L' := loggedEventUpdate U arrivalTypeProjection
  have hL := measurable_loggedEventUpdate U hU id measurable_id
  have hL' := measurable_loggedEventUpdate U hU _ measurable_arrivalTypeProjection
  let f := fun y : H × RoutedMemory σ ι => (y.1, routedMemoryInput y.2)
  have hf : Measurable f := measurable_fst.prodMk (measurable_routedMemoryInput.comp measurable_snd)
  letI := routingTransition_markov N c hc q hq L hL
  letI := routingTransition_markov N c hc q' hq' L' hL'
  letI := historyRoutingKernel_markov N c hc q hq
  letI := historyRoutingKernel_markov N c hc q' hq'
  apply absorbingTrajectory_projection (routingTransition N c hc q hq L)
    (routingTransition N c hc q' hq' L') f hf _ (.inr x)
  apply eventUpdateKernel_projection _ _ L hL L' hL' f id measurable_id
    (Sum.map id f) (measurable_id.sumMap hf)
  · intro a
    rw [Measure.map_id]
    rfl
  · exact loggedEventUpdate_erase_marks U

end StochasticMatching

namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def markedTrajectory (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    Measure (ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J)) :=
  markedRoutingTrajectory N c hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N c hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label) x

theorem markedTrajectory_erase_marks (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) => fun k =>
      Sum.map id (fun y : RoutingCursor n H ι × RoutedMemory σ J => (y.1, routedMemoryInput y.2)) (z k))
      (s.markedTrajectory n label N c hc hmem x) =
      s.loggedTrajectory n label N c hc hmem (x.1, routedMemoryInput x.2) :=
  markedRoutingTrajectory_erase_marks N c hc (s.cursorService n label) _ _
    (s.measurable_typedCursorUpdate n label) x

end StochasticMatching.PosteriorStage
