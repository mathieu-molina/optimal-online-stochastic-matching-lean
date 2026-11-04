import Matching.ArrivalHistory
import Matching.StoppedRoutingLaw
import Matching.HistoryServiceAssembly

/-! Preserve the complete typed arrival history while running an adaptive
policy. Forgetting the log gives the original policy trajectory; forgetting
the policy state gives the complete arrival-only logged trajectory.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {H B ι σ : Type*} [MeasurableSpace H] [MeasurableSpace B]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

abbrev ArrivalMemory (σ : Type*) := EventMemory (Unit ⊕ (ℝ × σ))

def emptyArrivalMemory (σ : Type*) : ArrivalMemory σ := (0, fun _ => .inl ())

noncomputable def loggedRoutingTrajectory (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U)
    (x : H × ArrivalMemory σ) : Measure (ℕ → Unit ⊕ (H × ArrivalMemory σ)) :=
  onlineRoutingTrajectory N capacity hc (p.comap Prod.fst measurable_fst)
    (fun x t ht => hp x.1 t ht) (loggedEventUpdate U arrivalTypeProjection)
    (measurable_loggedEventUpdate U hU _ measurable_arrivalTypeProjection) x

noncomputable def loggedInputTrajectory (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V)
    (x : B × ArrivalMemory σ) : Measure (ℕ → Unit ⊕ (B × ArrivalMemory σ)) :=
  poissonInputTrajectory capacity hc (fun x : B × ArrivalMemory σ => D x.1)
    (hD.comp measurable_fst) (fun x => hpos x.1) (loggedEventUpdate V id)
    (measurable_loggedEventUpdate V hV id measurable_id) x

theorem logged_routing_input_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V)
    (f : H → B) (hf : Measurable f)
    (hdeadline : ∀ h, (p.curves h).deadline = D (f h))
    (hupdate : ∀ h e, Sum.map id f (U (h, e)) = V (f h, arrivalTypeProjection e))
    (x : H × ArrivalMemory σ) :
    Measure.map (fun z : ℕ → Unit ⊕ (H × ArrivalMemory σ) =>
        fun k => Sum.map id (fun y => (f y.1, y.2)) (z k))
      (loggedRoutingTrajectory N capacity hc p hp U hU x) =
      loggedInputTrajectory capacity hc D hD hpos V hV (f x.1, x.2) := by
  apply stopped_routing_input_law N capacity hc (p.comap Prod.fst measurable_fst)
    (fun x t ht => hp x.1 t ht)
    (fun x : B × ArrivalMemory σ => D x.1) (hD.comp measurable_fst) (fun x => hpos x.1)
    (loggedEventUpdate U arrivalTypeProjection) (measurable_loggedEventUpdate U hU _ measurable_arrivalTypeProjection)
    (loggedEventUpdate V id) (measurable_loggedEventUpdate V hV id measurable_id)
    (fun y : H × ArrivalMemory σ => (f y.1, y.2)) (hf.prodMap measurable_id)
    (fun y => hdeadline y.1) (loggedEventUpdate_projection U V f arrivalTypeProjection hupdate) x

theorem logged_routing_forget_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ a, 0 ≤ capacity a) (p : HistoryServiceFamily H ι)
    (hp : ∀ h t, t ∈ Icc 0 (p.curves h).deadline →
      (fun i => (p.curves h).rate i t) ∈ supplyRegion N capacity)
    (U : H × (Unit ⊕ (ℝ × (σ × Option ι))) → Unit ⊕ H) (hU : Measurable U)
    (x : H × ArrivalMemory σ) :
    Measure.map (fun z : ℕ → Unit ⊕ (H × ArrivalMemory σ) =>
        fun k => Sum.map id Prod.fst (z k)) (loggedRoutingTrajectory N capacity hc p hp U hU x) =
      onlineRoutingTrajectory N capacity hc p hp U hU x.1 := by
  let q := p.comap (Prod.fst : H × ArrivalMemory σ → H) measurable_fst
  let hq := fun (x : H × ArrivalMemory σ) t ht => hp x.1 t ht
  let L := loggedEventUpdate U arrivalTypeProjection
  have hL : Measurable L := measurable_loggedEventUpdate U hU _ measurable_arrivalTypeProjection
  letI := routingTransition_markov N capacity hc q hq L hL
  letI := routingTransition_markov N capacity hc p hp U hU
  letI := historyRoutingKernel_markov N capacity hc q hq
  letI := historyRoutingKernel_markov N capacity hc p hp
  apply absorbingTrajectory_projection (routingTransition N capacity hc q hq L)
    (routingTransition N capacity hc p hp U) Prod.fst measurable_fst _ (.inr x)
  apply eventUpdateKernel_projection _ _ L hL U hU Prod.fst id measurable_id
    (Sum.map id Prod.fst) (measurable_id.sumMap measurable_fst)
  · intro a
    rw [Measure.map_id]
    rfl
  · exact loggedEventUpdate_fst U arrivalTypeProjection

end StochasticMatching
