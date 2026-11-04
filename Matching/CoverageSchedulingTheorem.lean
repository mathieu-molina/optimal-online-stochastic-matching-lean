import Matching.GreedyAllocation
import Matching.SchedulingTheorem

/-! The observable scheduling guarantee specialized to the matching-derived
coverage region, with the actual offline optimum as benchmark. The offline
allocation is constructed here, so neither measurable selection nor a supplied
benchmark allocation is an assumption of this theorem.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_coverage_policy_against_offline_optimum
    {σ : Type*} [Fintype σ] (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    ∃ (L : H × (ι → ℝ) → CompletionLog ι) (r : ℝ × (H × (ι → ℝ)) → (ι → ℝ)),
      Measurable L ∧ Measurable r ∧
      (∀ x, LogLabelsDistinct (L x)) ∧
      (∀ x k, Fintype.card ι ≤ k → L x k = Sum.inl ()) ∧
      (∀ t, @Measurable (H × (ι → ℝ)) (ι → ℝ)
        ((inferInstance : MeasurableSpace (H × CompletionLog ι)).comap (observedAt Prod.fst L t))
        inferInstance (fun x => r (t, x))) ∧
      (∀ q, r q ∈ supplyRegion N capacity) ∧
      (∀ x, (∫ u in (0 : ℝ)..1, r (u, x)) ∈ supplyRegion N capacity) ∧
      (∀ x, Continuous (fun t => ∫ u in (0 : ℝ)..t, r (u, x))) ∧
      (∀ x i, Monotone (fun t => (∫ u in (0 : ℝ)..t, r (u, x)) i)) ∧
      (∀ᵐ x ∂ν.prod independentExponentials, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
        0 ≤ (∫ u in (0 : ℝ)..t, r (u, x)) i ∧
          (∫ u in (0 : ℝ)..t, r (u, x)) i ≤ x.2 i) ∧
      (∀ᵐ x ∂ν.prod independentExponentials, ∀ k i τ d,
        L x k = Sum.inr (i, τ, d) → 0 ≤ τ ∧ τ < 1 ∧ d = x.2 i ∧
          ∀ t, τ ≤ t → (∫ u in (0 : ℝ)..t, r (u, x)) i = d) ∧
      Integrable (fun x => ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i)
        (ν.prod independentExponentials) ∧
      ((∫ x, ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) =
        ∫ x, (∑ i, if (∫ u in (0 : ℝ)..1, r (u, x)) i = x.2 i then (1 : ℝ) else 0)
          ∂ν.prod independentExponentials) ∧
      (∀ i, Comparison.ratio * (∫ x, greedyAllocation N capacity x.2 i ∂ν.prod independentExponentials) ≤
        ∫ x, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) ∧
      (Comparison.ratio * (∫ x, offlineValue (supplyRegion N capacity) x.2 ∂ν.prod independentExponentials) ≤
        ∫ x, ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) ∧
      Comparison.ratio * (∫ x, offlineValue (supplyRegion N capacity) x.2 ∂ν.prod independentExponentials) ≤
        ∫ x, (∑ i, if (∫ u in (0 : ℝ)..1, r (u, x)) i = x.2 i then (1 : ℝ) else 0)
          ∂ν.prod independentExponentials := by
  have h := exists_observable_service_policy
    (fun x : H × (ι → ℝ) => greedyAllocation N capacity x.2)
    ((measurable_greedyAllocation N capacity).comp measurable_snd)
    (zero_mem_supplyRegion N capacity hcapacity)
    (supplyRegion_convex N capacity) (supplyRegion_compact N capacity)
    (supplyRegion_downward N capacity) (fun _ hx => supplyRegion_nonneg N capacity hx)
    (fun _ z => (greedyAllocation_properties N capacity hcapacity z).1)
    (fun _ z hz i => greedyAllocation_cap_nonnegative N capacity hcapacity z hz i) ν
  simpa only [greedyAllocation_optimal N capacity hcapacity] using h

end StochasticMatching
