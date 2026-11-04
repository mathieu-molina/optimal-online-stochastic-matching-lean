import Matching.BudgetFunctions

/-! A separate unallocated-demand budget for each job. Survivor budgets are
preserved exactly on actual restart observations; the stopped occupation
identity keeps this coordinate separate throughout the calculation.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def unallocatedCoordinate (i : ι) (x : H × (ι → ℝ)) : ℝ :=
  (s.initial x.1 + x.2) i - s.data.allocation (x.1, s.initial x.1 + x.2) i

noncomputable def meanUnallocatedCoordinate (i : ι) (h : H) : ℝ :=
  s.initial h i + 1 - posteriorRate s.data.allocation h (s.initial h) i

theorem measurable_unallocatedCoordinate (i : ι) : Measurable (s.unallocatedCoordinate i) := by
  have hv := (s.measurable_initial.comp measurable_fst).add measurable_snd
  exact ((measurable_pi_apply i).comp hv).sub
    ((measurable_pi_apply i).comp (s.data.measurable_allocation.comp (measurable_fst.prodMk hv)))

theorem integrable_unallocatedCoordinate_fiber (h : H) (i : ι) :
    Integrable (fun z => s.unallocatedCoordinate i (h, z)) independentExponentials :=
  ((integrable_const (s.initial h i)).add (integrable_exponential_coordinate i)).sub
    (s.data.integrable_shifted_allocation h (s.initial h) i)

theorem meanUnallocatedCoordinate_eq_integral (h : H) (i : ι) :
    s.meanUnallocatedCoordinate i h = ∫ z, s.unallocatedCoordinate i (h, z) ∂independentExponentials :=
  s.data.posterior_gap_eq h (s.initial h) i

theorem measurable_meanUnallocatedCoordinate (i : ι) : Measurable (s.meanUnallocatedCoordinate i) := by
  have he : s.meanUnallocatedCoordinate i =
      fun h => ∫ z, s.unallocatedCoordinate i (h, z) ∂independentExponentials :=
    funext (fun h => s.meanUnallocatedCoordinate_eq_integral h i)
  rw [he]
  exact (s.measurable_unallocatedCoordinate i).stronglyMeasurable.integral_prod_right'.measurable

theorem unallocatedCoordinate_nonneg {x : H × (ι → ℝ)} (ha : s.Admissible x.1)
    (hz : ∀ j, 0 ≤ x.2 j) (i : ι) : 0 ≤ s.unallocatedCoordinate i x :=
  sub_nonneg.mpr (ha.2 (s.initial x.1 + x.2) (fun j => add_nonneg (ha.1 j) (hz j)) i)

theorem meanUnallocatedCoordinate_nonneg {h : H} (ha : s.Admissible h) (i : ι) :
    0 ≤ s.meanUnallocatedCoordinate i h :=
  s.data.posterior_gap_nonneg_at h ha.2 (s.initial h) ha.1 i

theorem next_unallocatedCoordinate_eq {x : H × (ι → ℝ)} {j : ι}
    (hz : 0 < x.2 j) (hw : x ∈ s.service.winner j) (i : {i : ι // i ≠ j}) :
    (s.next j).unallocatedCoordinate i (s.service.observation j x) =
      s.unallocatedCoordinate i.1 x := by
  unfold unallocatedCoordinate
  rw [s.next_allocation_on_winner hz hw i]
  congr 1
  exact s.next_original_demand x j i

theorem integrable_unallocatedCoordinate (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    Integrable (s.unallocatedCoordinate i) (ν.prod independentExponentials) := by
  have hm : Measurable (fun x : H × (ι → ℝ) => s.data.allocation (x.1, s.initial x.1 + x.2) i) :=
    (measurable_pi_apply i).comp (s.data.measurable_allocation.comp
      (measurable_fst.prodMk ((s.measurable_initial.comp measurable_fst).add measurable_snd)))
  have ha : Integrable (fun x : H × (ι → ℝ) => s.data.allocation (x.1, s.initial x.1 + x.2) i)
      (ν.prod independentExponentials) := by
    apply (integrable_const (s.data.bound : ℝ)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (s.data.allocation_nonneg x.1 (s.initial x.1 + x.2) i)]
    exact s.data.allocation_le x.1 (s.initial x.1 + x.2) i
  exact (integrable_history_demand ν s.initial i (s.integrable_initial_coordinate R ν hν i)).sub ha

theorem survival_unallocatedCoordinate_integral (h : H) (i : ι) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) :
    (∫ z in survivalBox (fun j => (s.service.curves h).service j t),
      s.unallocatedCoordinate i (h, z) ∂independentExponentials) =
      survivalCurve (fun u j => (s.service.curves h).service j u) t *
        (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
  rw [original_sample_survival_integral ((s.service.curves h).service_nonneg ht)
    (fun z => s.unallocatedCoordinate i (h, z))
    ((s.measurable_unallocatedCoordinate i).comp (measurable_const.prodMk measurable_id))]
  have he : (fun z => s.unallocatedCoordinate i
      (h, (fun j => (s.service.curves h).service j t) + z)) =
      fun z => ((s.initial h + (fun j => (s.service.curves h).service j t) + z) i -
        s.data.allocation (h, s.initial h + (fun j => (s.service.curves h).service j t) + z) i) := by
    funext z
    simp only [unallocatedCoordinate, add_assoc]
  rw [he, ← s.data.posterior_gap_eq, s.rate_eq_posterior]
  rfl

theorem before_stop_unallocatedCoordinate_integral (h : H) (i : ι) {t : ℝ}
    (ht : t ∈ Ico 0 (s.service.curves h).deadline) :
    (∫ z in {z | t < (s.service.curves h).stopClock z},
      s.unallocatedCoordinate i (h, z) ∂independentExponentials) =
      survivalCurve (fun u j => (s.service.curves h).service j u) t *
        (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
  have he : {z | t < (s.service.curves h).stopClock z} =ᵐ[independentExponentials]
      survivalBox (fun j => (s.service.curves h).service j t) := by
    filter_upwards [(s.service.curves h).survival_iff_before_stopClock_ae] with z hz
    exact propext (hz t ht).symm
  rw [Measure.restrict_congr_set he]
  exact s.survival_unallocatedCoordinate_integral h i ⟨ht.1, ht.2.le⟩

theorem stopped_coordinate_budget_identity (elapsed : ℝ) (h : H) (i : ι)
    (hT : elapsed + s.deadline h ≤ 1) :
    (∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u j => (s.service.curves h).service j u) t *
        Comparison.lossKernel (elapsed + t) *
          (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t)) +
    (∫ z, Comparison.continuation (elapsed + (s.service.curves h).stopClock z) 0 *
      s.unallocatedCoordinate i (h, z) ∂independentExponentials) =
      Comparison.continuation elapsed 0 * s.meanUnallocatedCoordinate i h := by
  have hi := stopped_budget_identity (independentExponentials (ι := ι))
    (s.deadline_pos h).le hT (s.service.curves h).stopClock (s.service.curves h).measurable_stopClock
    (s.service.curves h).stopClock_bounds (fun z => s.unallocatedCoordinate i (h, z))
    (s.integrable_unallocatedCoordinate_fiber h i)
  rw [← s.meanUnallocatedCoordinate_eq_integral] at hi
  have he : (∫ t in (0 : ℝ)..s.deadline h, Comparison.lossKernel (elapsed + t) *
      (∫ z in {z | t < (s.service.curves h).stopClock z}, s.unallocatedCoordinate i (h, z)
        ∂independentExponentials)) =
      ∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u j => (s.service.curves h).service j u) t *
        Comparison.lossKernel (elapsed + t) *
          (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
    rw [intervalIntegral.integral_of_le (s.deadline_pos h).le,
      intervalIntegral.integral_of_le (s.deadline_pos h).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [s.before_stop_unallocatedCoordinate_integral h i ⟨ht.1.le, ht.2⟩]
    ring
  rw [he] at hi
  exact hi

end StochasticMatching.PosteriorStage
