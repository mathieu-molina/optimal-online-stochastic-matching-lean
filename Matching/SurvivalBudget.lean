import Matching.ResidualBudget
import Matching.StoppingClock
import Matching.StoppedBudget

/-! The survival-weighted posterior deficit equals the original unallocated
budget restricted to surviving demand samples. Together with the actual
stopping clock this gives an exact first-segment budget identity.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching

theorem original_sample_survival_integral {ι : Type*} [Fintype ι]
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    (∫ z in survivalBox a, f z ∂independentExponentials) =
      Real.exp (-(∑ i, a i)) * ∫ z, f (a + z) ∂independentExponentials := by
  have hm : Measurable (fun z : ι → ℝ => f (a + z)) := hf.comp (measurable_const.add measurable_id)
  have hmap := integral_map_of_stronglyMeasurable
    (μ := independentExponentials.restrict (survivalBox a))
    (measurable_subtract_threshold a) hm.stronglyMeasurable
  change (∫ z, f (a + z) ∂vectorResidualLaw a) =
    ∫ z in survivalBox a, f (a + (fun i => z i - a i)) ∂independentExponentials at hmap
  have he : ∀ z : ι → ℝ, a + (fun i => z i - a i) = z := by
    intro z
    funext i
    dsimp only [Pi.add_apply]
    ring
  simp_rw [he] at hmap
  rw [vectorResidualLaw_eq_smul ha, ← survivalBox_measure ha,
    integral_smul_measure, survivalBox_measure_exp_sum ha,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] at hmap
  exact hmap.symm

namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

theorem shifted_unallocated_mean (h : H) (t : ℝ) :
    (∫ z, s.unallocated (h, (fun i => (s.service.curves h).service i t) + z)
      ∂independentExponentials) =
    ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
  let a : ι → ℝ := fun i => (s.service.curves h).service i t
  have he : (fun z => s.unallocated (h, a + z)) = fun z =>
      ∑ i, ((s.initial h + a + z) i - s.data.allocation (h, s.initial h + a + z) i) := by
    funext z
    simp only [unallocated, add_assoc]
  change (∫ z, s.unallocated (h, a + z) ∂independentExponentials) = _
  rw [he, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← s.data.posterior_gap_eq, s.rate_eq_posterior]
    rfl
  · intro i _
    exact ((integrable_const ((s.initial h + a) i)).add (integrable_exponential_coordinate i)).sub
      (s.data.integrable_shifted_allocation h (s.initial h + a) i)

theorem survival_unallocated_integral (h : H) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) :
    (∫ z in survivalBox (fun i => (s.service.curves h).service i t), s.unallocated (h, z)
      ∂independentExponentials) =
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
  rw [original_sample_survival_integral ((s.service.curves h).service_nonneg ht)
    (fun z => s.unallocated (h, z))
    (s.measurable_unallocated.comp (measurable_const.prodMk measurable_id)),
    s.shifted_unallocated_mean]
  rfl

theorem before_stop_unallocated_integral (h : H) {t : ℝ}
    (ht : t ∈ Ico 0 (s.service.curves h).deadline) :
    (∫ z in {z | t < (s.service.curves h).stopClock z}, s.unallocated (h, z)
      ∂independentExponentials) =
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
  have he : {z | t < (s.service.curves h).stopClock z} =ᵐ[independentExponentials]
      survivalBox (fun i => (s.service.curves h).service i t) := by
    filter_upwards [(s.service.curves h).survival_iff_before_stopClock_ae] with z hz
    exact propext (hz t ht).symm
  rw [Measure.restrict_congr_set he]
  exact s.survival_unallocated_integral h ⟨ht.1, ht.2.le⟩

theorem stopped_unallocated_identity (elapsed : ℝ) (h : H)
    (hT : elapsed + s.deadline h ≤ 1) :
    (∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        Comparison.lossKernel (elapsed + t) *
          ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t)) +
    (∫ z, Comparison.continuation (elapsed + (s.service.curves h).stopClock z) 0 *
      s.unallocated (h, z) ∂independentExponentials) =
      Comparison.continuation elapsed 0 * s.meanUnallocated h := by
  have hi := stopped_budget_identity (independentExponentials (ι := ι))
    (s.deadline_pos h).le hT (s.service.curves h).stopClock (s.service.curves h).measurable_stopClock
    (s.service.curves h).stopClock_bounds (fun z => s.unallocated (h, z))
    (s.integrable_unallocated_fiber h)
  rw [← s.meanUnallocated_eq_integral] at hi
  have he : (∫ t in (0 : ℝ)..s.deadline h, Comparison.lossKernel (elapsed + t) *
      (∫ z in {z | t < (s.service.curves h).stopClock z}, s.unallocated (h, z)
        ∂independentExponentials)) =
      ∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        Comparison.lossKernel (elapsed + t) *
          ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t) := by
    rw [intervalIntegral.integral_of_le (s.deadline_pos h).le,
      intervalIntegral.integral_of_le (s.deadline_pos h).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [s.before_stop_unallocated_integral h ⟨ht.1.le, ht.2⟩]
    ring
  rw [he] at hi
  exact hi

theorem defect_le_stopped_budget (elapsed : H → ℝ) (h : H) (ha : s.Admissible h)
    (hT : elapsed h + s.deadline h ≤ 1) :
    s.defect elapsed h +
      (∫ z, Comparison.continuation (elapsed h + (s.service.curves h).stopClock z) 0 *
        s.unallocated (h, z) ∂independentExponentials) ≤
      Comparison.continuation (elapsed h) 0 * s.meanUnallocated h := by
  have hb := (s.service.curves h).comparisonOutcome_expected_lower_bound
    (elapsed h) (s.initial h) hT ha.1 (fun t ht i => s.flow_gap_nonneg_at h ha ht i)
  have heq : (fun z => s.stepOutcome elapsed (h, z)) =
      (s.service.curves h).comparisonOutcome (elapsed h) (s.initial h) := by
    funext z
    exact s.stepOutcome_eq elapsed (h, z)
  rw [← heq, s.potential_eq_initial] at hb
  have hD : (s.service.curves h).deadline = s.deadline h := rfl
  rw [hD] at hb
  have hi := s.stopped_unallocated_identity (elapsed h) h hT
  unfold defect
  linarith

end PosteriorStage
end StochasticMatching
