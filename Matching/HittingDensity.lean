import Matching.CappedHittingTime
import Matching.ExponentialWork

/-! Density of completion before a fixed deadline for continuous nonnegative
rates. Service may have flat intervals; no inverse or positive lower rate is
assumed. The deadline atom is excluded from this completion measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StochasticMatching

theorem cappedHit_lt_deadline_of_lt {a : ℝ → ℝ} (ha : Continuous a)
    {T z : ℝ} (hT : 0 < T) (hm : MonotoneOn a (Icc 0 T)) (hz : z < a T) :
    cappedHit a T z < T := by
  by_cases hz0 : z ≤ a 0
  · exact lt_of_le_of_lt (cappedHit_le_of_reached hm ⟨le_refl _, hT.le⟩ hz0) hT
  · obtain ⟨t, ht, heq⟩ := intermediate_value_Ico hT.le ha.continuousOn
      (show z ∈ Ico (a 0) (a T) from ⟨(lt_of_not_ge hz0).le, hz⟩)
    exact lt_of_le_of_lt (cappedHit_le_of_reached hm ⟨ht.1, ht.2.le⟩ heq.ge) ht.2

theorem cappedHit_before_deadline_ae {a : ℝ → ℝ} (ha : Continuous a)
    {T : ℝ} (hT : 0 < T) (hm : MonotoneOn a (Icc 0 T)) :
    (cappedHit a T ⁻¹' Iio T) =ᵐ[unitExponential] Iic (a T) := by
  have hne : ∀ᵐ z ∂unitExponential, z ≠ a T := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with z hz
  apply propext
  constructor
  · intro h
    have h0 := (cappedHit_bounds (z := z) ha hT.le).1
    have ha' := (cappedHit_le_iff ha hT.le hm h0 h).mp (le_refl _)
    exact ha'.trans (hm (cappedHit_bounds ha hT.le) ⟨hT.le, le_refl _⟩
      (cappedHit_bounds ha hT.le).2)
  · intro h
    exact cappedHit_lt_deadline_of_lt ha hT hm (lt_of_le_of_ne h hz)

noncomputable def completionTimeLaw (a : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (Measure.map (cappedHit a T) unitExponential).restrict (Iio T)

instance completionTimeLaw_finite (a : ℝ → ℝ) (T : ℝ) :
    IsFiniteMeasure (completionTimeLaw a T) := by
  unfold completionTimeLaw
  infer_instance

theorem completionTimeLaw_univ {a : ℝ → ℝ} (ha : Continuous a)
    {T : ℝ} (hT : 0 < T) (hm : MonotoneOn a (Icc 0 T)) (ha0 : a 0 = 0) :
    completionTimeLaw a T univ = ENNReal.ofReal (1 - Real.exp (-a T)) := by
  have hat : 0 ≤ a T := by
    rw [← ha0]
    exact hm ⟨le_refl _, hT.le⟩ ⟨hT.le, le_refl _⟩ hT.le
  rw [completionTimeLaw, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.map_apply (measurable_cappedHit ha hT.le hm) measurableSet_Iio,
    measure_congr (cappedHit_before_deadline_ae ha hT hm),
    ← ENNReal.ofReal_toReal (measure_ne_top unitExponential (Iic (a T)))]
  change ENNReal.ofReal (unitExponential.real (Iic (a T))) = _
  rw [unitExponential_real_Iic, if_pos hat]

theorem completionTimeLaw_Iic {a : ℝ → ℝ} (ha : Continuous a)
    {T x : ℝ} (hT : 0 < T) (hm : MonotoneOn a (Icc 0 T)) (ha0 : a 0 = 0)
    (hx : 0 ≤ x) : completionTimeLaw a T (Iic x) =
      ENNReal.ofReal (1 - Real.exp (-a (min x T))) := by
  by_cases hxT : x < T
  · rw [min_eq_left hxT.le, completionTimeLaw,
      Measure.restrict_apply measurableSet_Iic,
      inter_eq_self_of_subset_left (Iic_subset_Iio.mpr hxT),
      ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((Measure.map (cappedHit a T) unitExponential).real (Iic x)) = _
    rw [cappedHit_exponential_CDF ha hT.le hm ha0 hx hxT]
  · rw [min_eq_right (le_of_not_gt hxT)]
    have hset : Iic x ∩ Iio T = Iio T :=
      inter_eq_self_of_subset_right (Iio_subset_Iic_self.trans (Iic_subset_Iic.mpr (le_of_not_gt hxT)))
    have heq : completionTimeLaw a T (Iic x) = completionTimeLaw a T univ := by
      simp only [completionTimeLaw, Measure.restrict_apply measurableSet_Iic,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, hset]
    rw [heq, completionTimeLaw_univ ha hT hm ha0]

theorem completionTimeLaw_Iic_neg {a : ℝ → ℝ} (ha : Continuous a)
    {T x : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T)) (hx : x < 0) :
    completionTimeLaw a T (Iic x) = 0 := by
  apply le_antisymm _ (zero_le _)
  calc
    _ ≤ Measure.map (cappedHit a T) unitExponential (Iic x) := Measure.restrict_apply_le _ _
    _ = 0 := by
      rw [Measure.map_apply (measurable_cappedHit ha hT hm) measurableSet_Iic]
      have heq : cappedHit a T ⁻¹' Iic x = ∅ := by
        ext z
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact not_le.mpr (lt_of_lt_of_le hx (cappedHit_bounds ha hT).1)
      rw [heq, measure_empty]

theorem integrated_hitting_density {a r : ℝ → ℝ} (ha : Continuous a) (hr : Continuous r)
    {T x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ T) (ha0 : a 0 = 0)
    (hr0 : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt a (r t) t) :
    (∫⁻ t in Icc 0 x, ENNReal.ofReal (r t * Real.exp (-a t))) =
      ENNReal.ofReal (1 - Real.exp (-a x)) := by
  have hc : Continuous (fun t => r t * Real.exp (-a t)) := by fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 x)] (fun t => r t * Real.exp (-a t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (hr0 t ⟨ht.1, ht.2.trans hxT⟩) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx0]
  congr 1
  have hderiv : ∀ t ∈ uIcc 0 x,
      HasDerivAt (fun s => -Real.exp (-a s)) (r t * Real.exp (-a t)) t := by
    intro t ht
    rw [uIcc_of_le hx0] at ht
    convert (hd t ⟨ht.1, ht.2.trans hxT⟩).neg.exp.neg using 1 <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable 0 x)
  simpa [ha0, sub_eq_add_neg, add_comm] using h

noncomputable def serviceDensityMeasure (a r : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 T)).withDensity (fun t => ENNReal.ofReal (r t * Real.exp (-a t)))

theorem serviceDensityMeasure_Iic_eq (a r : ℝ → ℝ) (T x : ℝ) :
    serviceDensityMeasure a r T (Iic x) =
      ∫⁻ t in Icc 0 (min x T), ENNReal.ofReal (r t * Real.exp (-a t)) := by
  rw [serviceDensityMeasure, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic x ∩ Icc 0 T = Icc 0 (min x T) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [hs]

theorem serviceDensityMeasure_univ {a r : ℝ → ℝ} (ha : Continuous a) (hr : Continuous r)
    {T : ℝ} (hT : 0 ≤ T) (ha0 : a 0 = 0)
    (hr0 : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt a (r t) t) :
    serviceDensityMeasure a r T univ = ENNReal.ofReal (1 - Real.exp (-a T)) := by
  rw [serviceDensityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact integrated_hitting_density ha hr hT le_rfl ha0 hr0 hd

/-- The scalar completion clock has the expected density even when service
has flat intervals. The no-completion atom at the deadline is excluded. -/
theorem completionTimeLaw_eq_density {a r : ℝ → ℝ} (ha : Continuous a) (hr : Continuous r)
    {T : ℝ} (hT : 0 < T) (hm : MonotoneOn a (Icc 0 T)) (ha0 : a 0 = 0)
    (hr0 : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt a (r t) t) :
    completionTimeLaw a T = serviceDensityMeasure a r T := by
  letI : IsFiniteMeasure (serviceDensityMeasure a r T) :=
    ⟨by rw [serviceDensityMeasure_univ ha hr hT.le ha0 hr0 hd]; exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro x
  by_cases hx : 0 ≤ x
  · rw [completionTimeLaw_Iic ha hT hm ha0 hx, serviceDensityMeasure_Iic_eq,
      integrated_hitting_density ha hr (le_min hx hT.le) (min_le_right _ _) ha0 hr0 hd]
  · rw [completionTimeLaw_Iic_neg ha hT.le hm (lt_of_not_ge hx), serviceDensityMeasure_Iic_eq,
      Icc_eq_empty (not_le.mpr (lt_of_le_of_lt (min_le_left _ _) (lt_of_not_ge hx)))]
    simp

end StochasticMatching
