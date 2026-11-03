import Matching.MarkedArrivalCoupling
import Matching.ExponentialBlockSplit

/-! After a routed arrival, forget the auxiliary rejection clock. Rejections
retain all original jobs; accepted arrivals remove exactly the matched job.
The remaining job demands have a fresh independent exponential product law.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching

theorem independentExponentials_injective_coordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    Measure.map (fun z : ι → ℝ => fun k => z (f k)) independentExponentials =
      (independentExponentials (ι := κ)) := by
  have hi := independentExponentials_coordinates_independent.precomp hf
  have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (f k)).aemeasurable)).mp hi
  simpa only [independentExponentials_coordinate_law] using h

theorem product_exponential_coordinate_projection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : Measure ℝ) [SFinite μ] (f : κ → ι) (hf : Function.Injective f) :
    Measure.map (fun p : ℝ × (ι → ℝ) => (p.1, fun k => p.2 (f k)))
      (μ.prod independentExponentials) = μ.prod (independentExponentials (ι := κ)) := by
  have h := Measure.map_prod_map μ (independentExponentials (ι := ι)) measurable_id
    (measurable_pi_lambda _ (fun k => measurable_pi_apply (f k)))
  rw [Measure.map_id, independentExponentials_injective_coordinates f hf] at h
  exact h.symm

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem routing_rejection_restart_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) :
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))
    Measure.map (fun z : Option ι → ℝ =>
      let t := cappedHit (q.service none) q.deadline (z none)
      (t, fun i : ι => z (some i) - p.service i t))
      (independentExponentials.restrict (variableWinner q.service q.deadline none)) =
      (Measure.sum (fun s => routingArrivalMeasure N capacity p s none)).prod
        (independentExponentials (ι := ι)) := by
  intro q
  let f : ι → {i : Option ι // i ≠ none} := fun i => ⟨some i, by simp⟩
  have hf : Function.Injective f := by
    intro i k h
    exact Option.some.inj (congrArg Subtype.val h)
  let G : ℝ × ({i : Option ι // i ≠ none} → ℝ) → ℝ × (ι → ℝ) :=
    fun v => (v.1, fun i => v.2 (f i))
  have hG : Measurable G := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply (f i)).comp measurable_snd))
  have h := congrArg (Measure.map G) (routing_first_event_residual_law N capacity hc p hp none)
  rw [Measure.map_map hG (q.measurable_observation none), ← Measure.prod_sum_left,
    product_exponential_coordinate_projection _ f hf] at h
  exact h

theorem routing_acceptance_restart_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) (j : ι) :
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))
    Measure.map (fun z : Option ι → ℝ =>
      let t := cappedHit (q.service (some j)) q.deadline (z (some j))
      (t, fun i : {i : ι // i ≠ j} => z (some i.1) - p.service i.1 t))
      (independentExponentials.restrict (variableWinner q.service q.deadline (some j))) =
      (Measure.sum (fun s => routingArrivalMeasure N capacity p s (some j))).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  intro q
  let f : {i : ι // i ≠ j} → {i : Option ι // i ≠ some j} := fun i =>
    ⟨some i.1, fun h => i.2 (Option.some.inj h)⟩
  have hf : Function.Injective f := by
    intro i k h
    exact Subtype.ext (Option.some.inj (congrArg Subtype.val h))
  let G : ℝ × ({i : Option ι // i ≠ some j} → ℝ) → ℝ × ({i : ι // i ≠ j} → ℝ) :=
    fun v => (v.1, fun i => v.2 (f i))
  have hG : Measurable G := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply (f i)).comp measurable_snd))
  have h := congrArg (Measure.map G) (routing_first_event_residual_law N capacity hc p hp (some j))
  rw [Measure.map_map hG (q.measurable_observation (some j)), ← Measure.prod_sum_left,
    product_exponential_coordinate_projection _ f hf] at h
  exact h

end StochasticMatching
