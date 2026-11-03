import Matching.EmpiricalTailBound
import Matching.HardPoissonInstance
import Matching.OfflineDeficiency
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A pathwise bound of the hard instance's maximum exponential deficiency
by the integrated absolute error of its empirical survival function. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching

theorem tailIndicator_time_integrable (z : ℝ) :
    IntegrableOn (fun t => tailIndicator t z) (Ioi (0 : ℝ)) := by
  change Integrable ((Iio z).indicator (fun _ : ℝ => (1 : ℝ))) (volume.restrict (Ioi 0))
  rw [integrable_indicator_iff measurableSet_Iio, integrableOn_const]
  right
  rw [Measure.restrict_apply measurableSet_Iio]
  have he : Iio z ∩ Ioi (0 : ℝ) = Ioo 0 z := by ext t; simp [and_comm]
  rw [he, Real.volume_Ioo]
  exact ENNReal.ofReal_lt_top

theorem tailIndicator_time_integral {z : ℝ} (hz : 0 ≤ z) :
    (∫ t in Ioi (0 : ℝ), tailIndicator t z) = z := by
  change (∫ t, (Iio z).indicator (fun _ : ℝ => (1 : ℝ)) t ∂volume.restrict (Ioi 0)) = _
  rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one,
    measureReal_restrict_apply measurableSet_Iio]
  have he : Iio z ∩ Ioi (0 : ℝ) = Ioo 0 z := by ext t; simp [and_comm]
  rw [he, Real.volume_real_Ioo_of_le hz, sub_zero]

theorem integrable_ideal_capped_tail {m k : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) :
    IntegrableOn (fun t => min k (m * Real.exp (-t))) (Ioi (0 : ℝ)) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul m).mono'
    (measurable_const.min (measurable_const.mul measurable_id.neg.exp)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_of_nonneg (le_min hk (mul_nonneg hm (Real.exp_nonneg _)))]
    exact min_le_right _ _)

theorem integral_ideal_capped_tail {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (hkm : k ≤ m) :
    (∫ t in Ioi (0 : ℝ), min k (m * Real.exp (-t))) = k * (1 - Real.log (k / m)) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [zero_mul]
    have he (t : ℝ) : min 0 (m * Real.exp (-t)) = 0 := min_eq_left (by positivity)
    simp_rw [he]
    simp
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  let T := -Real.log (k / m)
  have hq : 0 < k / m := div_pos hkpos hm
  have hq1 : k / m ≤ 1 := (div_le_one hm).mpr hkm
  have hT : 0 ≤ T := neg_nonneg.mpr (Real.log_nonpos hq.le hq1)
  have he : m * Real.exp (-T) = k := by
    dsimp [T]
    rw [neg_neg, Real.exp_log hq]
    field_simp
  have hi := integrable_ideal_capped_tail hm.le hk
  have h1 : (∫ t in Ioc (0 : ℝ) T, min k (m * Real.exp (-t))) = k * T := by
    calc
      _ = ∫ _t in Ioc (0 : ℝ) T, k := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        apply min_eq_left
        rw [← he]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ht.2)) hm.le
      _ = k * T := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hT, sub_zero, mul_comm]
  have h2 : (∫ t in Ioi T, min k (m * Real.exp (-t))) = k := by
    calc
      _ = ∫ t in Ioi T, m * Real.exp (-t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        apply min_eq_right
        rw [← he]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ht.le)) hm.le
      _ = k := by rw [integral_const_mul, integral_exp_neg_Ioi, he]
  have hd : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact not_lt_of_ge ht.2 ht'
  rw [← Ioc_union_Ioi_eq_Ioi hT, setIntegral_union hd measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hT)), h1, h2]
  dsimp [T]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem empiricalTail_nonneg (z : ι → ℝ) (t : ℝ) : 0 ≤ empiricalTail z t :=
  Finset.sum_nonneg (fun i _ => (tailIndicator_bounds t (z i)).1)

theorem empiricalTail_integrable (z : ι → ℝ) : IntegrableOn (empiricalTail z) (Ioi (0 : ℝ)) :=
  integrable_finset_sum _ (fun i _ => tailIndicator_time_integrable (z i))

noncomputable def empiricalTailError (z : ι → ℝ) (t : ℝ) : ℝ :=
  |empiricalTail z t - (Fintype.card ι : ℝ) * Real.exp (-t)|

theorem empiricalTailError_integrable (z : ι → ℝ) :
    IntegrableOn (empiricalTailError z) (Ioi (0 : ℝ)) :=
  ((empiricalTail_integrable z).sub ((integrableOn_exp_neg_Ioi 0).const_mul _)).abs

theorem subset_sum_le_integral_capped_tail (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (A : Finset ι) :
    (∑ i ∈ A, z i) ≤ ∫ t in Ioi (0 : ℝ), min (A.card : ℝ) (empiricalTail z t) := by
  have hpoint (t : ℝ) : (∑ i ∈ A, tailIndicator t (z i)) ≤ min (A.card : ℝ) (empiricalTail z t) := by
    apply le_min
    · have h := Finset.sum_le_sum (fun i (_ : i ∈ A) => (tailIndicator_bounds t (z i)).2)
      simpa using h
    · exact Finset.sum_le_univ_sum_of_nonneg (fun i => (tailIndicator_bounds t (z i)).1)
  have hi : IntegrableOn (fun t => min (A.card : ℝ) (empiricalTail z t)) (Ioi (0 : ℝ)) := by
    apply (empiricalTail_integrable z).mono' (by
      apply Measurable.aestronglyMeasurable
      exact measurable_const.min (Finset.measurable_sum _ (fun i _ =>
        measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)))
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg _) (empiricalTail_nonneg z t))]
      exact min_le_right _ _)
  have h := integral_mono (integrable_finset_sum _ (fun i _ => tailIndicator_time_integrable (z i))) hi hpoint
  rw [integral_finset_sum _ (fun i _ => tailIndicator_time_integrable (z i))] at h
  simpa only [tailIndicator_time_integral (hz _)] using h

theorem min_le_min_add_abs (k a b : ℝ) : min k a ≤ min k b + |a - b| := by
  rcases le_total k b with h | h
  · rw [min_eq_left h]
    exact (min_le_left k a).trans (le_add_of_nonneg_right (abs_nonneg _))
  · rw [min_eq_right h]
    exact (min_le_right k a).trans (by linarith [le_abs_self (a - b)])

theorem subset_exponential_deficiency_le_tail_error [Nonempty ι]
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (A : Finset ι) :
    (∑ i ∈ A, z i) - (A.card : ℝ) * (1 - Real.log ((A.card : ℝ) / Fintype.card ι)) ≤
      ∫ t in Ioi (0 : ℝ), empiricalTailError z t := by
  have hm : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hk : (A.card : ℝ) ≤ Fintype.card ι := Nat.cast_le.mpr (Finset.card_le_univ A)
  have h1 := subset_sum_le_integral_capped_tail z hz A
  have hi : IntegrableOn (fun t => min (A.card : ℝ) (empiricalTail z t)) (Ioi (0 : ℝ)) := by
    apply (empiricalTail_integrable z).mono' (by
      apply Measurable.aestronglyMeasurable
      exact measurable_const.min (Finset.measurable_sum _ (fun i _ =>
        measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)))
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg _) (empiricalTail_nonneg z t))]
      exact min_le_right _ _)
  have h2 := integral_mono hi
    ((integrable_ideal_capped_tail hm.le (Nat.cast_nonneg A.card)).add (empiricalTailError_integrable z))
    (fun t => min_le_min_add_abs (A.card : ℝ) (empiricalTail z t) ((Fintype.card ι : ℝ) * Real.exp (-t)))
  simp only [Pi.add_apply] at h2
  rw [integral_add (integrable_ideal_capped_tail hm.le (Nat.cast_nonneg A.card))
    (empiricalTailError_integrable z), integral_ideal_capped_tail hm (Nat.cast_nonneg A.card) hk] at h2
  linarith

theorem hardPoisson_max_deficiency_le_tail_error [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    maxSupplyDeficiency id (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) z ≤
      ∫ t in Ioi (0 : ℝ), empiricalTailError z t := by
  apply Finset.sup'_le
  intro A _
  rw [supplyDeficiency, hardPoissonIntensity_coverage]
  exact subset_exponential_deficiency_le_tail_error z hz A

end StochasticMatching
