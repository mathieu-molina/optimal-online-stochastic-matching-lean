import Matching.AdaptedPolicy

/-! The explicitly observable implementation has integrable rates and
continuous monotone service on every sample, including exceptional histories.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : PosteriorData H ι)

theorem adaptedRate_intervalIntegrable {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (x : H × (ι → ℝ)) (a b : ℝ) :
    IntervalIntegrable (fun t => p.adaptedRate (t, x)) volume a b := by
  obtain ⟨C, hC⟩ := hPcompact.isBounded.exists_norm_le
  have hm : Measurable (fun t => p.adaptedRate (t, x)) :=
    p.measurable_adaptedRate.comp (measurable_id.prodMk measurable_const)
  have hi : ∀ c d : ℝ, IntegrableOn (fun t => p.adaptedRate (t, x)) (Ioc c d) := by
    intro c d
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    exact hC _ (p.adaptedRate_feasible hP0 hPc hPcompact.isClosed hPdown hmem (t, x))
  exact ⟨hi a b, hi b a⟩

theorem continuous_adaptedService {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (x : H × (ι → ℝ)) : Continuous (p.adaptedService x) :=
  intervalIntegral.continuous_primitive
    (p.adaptedRate_intervalIntegrable hP0 hPc hPcompact hPdown hmem x) 0

theorem monotone_adaptedService {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hPnonneg : ∀ v ∈ P, ∀ i, 0 ≤ v i)
    (hmem : ∀ h z, p.allocation (h, z) ∈ P) (x : H × (ι → ℝ)) (i : ι) :
    Monotone (fun t => p.adaptedService x t i) := by
  intro a b hab
  have hi := p.adaptedRate_intervalIntegrable hP0 hPc hPcompact hPdown hmem x
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  have hp := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm (hi a b)
  simp only [ContinuousLinearMap.proj_apply] at hp
  have hn : 0 ≤ (∫ t in a..b, p.adaptedRate (t, x)) i := by
    rw [← hp]
    exact intervalIntegral.integral_nonneg_of_forall hab (fun t =>
      hPnonneg _ (p.adaptedRate_feasible hP0 hPc hPcompact.isClosed hPdown hmem (t, x)) i)
  have hs' := congrArg (fun v : ι → ℝ => v i) hs
  change p.adaptedService x a i + (∫ t in a..b, p.adaptedRate (t, x)) i = p.adaptedService x b i at hs'
  linarith

theorem integrable_adaptedReward {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] : Integrable p.adaptedReward (ν.prod independentExponentials) :=
  (p.integrable_policyReward hP0 hPc hPcompact hPdown hmem ν).congr
    (p.adaptedReward_eq_policyReward_ae ν).symm

theorem adaptedService_terminal_feasible {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (x : H × (ι → ℝ)) : p.adaptedService x 1 ∈ P := by
  haveI : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  change (∫ u in (0 : ℝ)..1, p.adaptedRate (u, x)) ∈ P
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hPc.integral_mem hPcompact.isClosed
    (Filter.Eventually.of_forall (fun t => p.adaptedRate_feasible hP0 hPc hPcompact.isClosed hPdown hmem (t, x)))
    (p.adaptedRate_intervalIntegrable hP0 hPc hPcompact hPdown hmem x 0 1).1

end StochasticMatching.PosteriorData
