import Matching.ExponentialResidual
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.IntermediateValue

/-! A finite-horizon first-hit clock for continuous, nondecreasing service.
The value at the deadline also represents no completion; the event of actual
completion is retained separately as `z ≤ a T`. Flat service intervals are
allowed. This module does not assert a marked time-density formula.
-/

open MeasureTheory Set

namespace StochasticMatching

def demandHitSet (a : ℝ → ℝ) (T z : ℝ) : Set ℝ :=
  Icc 0 T ∩ {t | z ≤ a t}

noncomputable def cappedHit (a : ℝ → ℝ) (T z : ℝ) : ℝ := by
  classical
  exact if z ≤ a T then sInf (demandHitSet a T z) else T

theorem demandHitSet_nonempty {a : ℝ → ℝ} {T z : ℝ}
    (hT : 0 ≤ T) (hz : z ≤ a T) : (demandHitSet a T z).Nonempty :=
  ⟨T, ⟨⟨hT, le_rfl⟩, hz⟩⟩

theorem demandHitSet_bddBelow (a : ℝ → ℝ) (T z : ℝ) :
    BddBelow (demandHitSet a T z) := ⟨0, fun _ ht => ht.1.1⟩

theorem demandHitSet_closed {a : ℝ → ℝ} (ha : Continuous a) (T z : ℝ) :
    IsClosed (demandHitSet a T z) :=
  isClosed_Icc.inter (isClosed_le continuous_const ha)

theorem cappedHit_mem_hitSet {a : ℝ → ℝ} (ha : Continuous a)
    {T z : ℝ} (hT : 0 ≤ T) (hz : z ≤ a T) :
    cappedHit a T z ∈ demandHitSet a T z := by
  rw [cappedHit, if_pos hz]
  exact (demandHitSet_closed ha T z).csInf_mem (demandHitSet_nonempty hT hz)
    (demandHitSet_bddBelow a T z)

theorem cappedHit_bounds {a : ℝ → ℝ} (ha : Continuous a) {T z : ℝ} (hT : 0 ≤ T) :
    cappedHit a T z ∈ Icc 0 T := by
  by_cases hz : z ≤ a T
  · exact (cappedHit_mem_hitSet ha hT hz).1
  · simp [cappedHit, hz, hT]

theorem cappedHit_le_of_reached {a : ℝ → ℝ} {T z t : ℝ}
    (hm : MonotoneOn a (Icc 0 T)) (ht : t ∈ Icc 0 T) (hz : z ≤ a t) :
    cappedHit a T z ≤ t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hzT : z ≤ a T := hz.trans (hm ht ⟨hT, le_rfl⟩ ht.2)
  rw [cappedHit, if_pos hzT]
  exact csInf_le (demandHitSet_bddBelow a T z) ⟨ht, hz⟩

theorem cappedHit_le_iff {a : ℝ → ℝ} (ha : Continuous a)
    {T z t : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (ht0 : 0 ≤ t) (htT : t < T) :
    cappedHit a T z ≤ t ↔ z ≤ a t := by
  constructor
  · intro h
    have hzT : z ≤ a T := by
      by_contra hzT
      simp only [cappedHit, if_neg hzT] at h
      exact (not_le.mpr htT) h
    have hmem := cappedHit_mem_hitSet ha hT hzT
    exact hmem.2.trans (hm hmem.1 ⟨ht0, htT.le⟩ h)
  · exact cappedHit_le_of_reached hm ⟨ht0, htT.le⟩

theorem service_below_demand_before_hit {a : ℝ → ℝ} (ha : Continuous a)
    {T z t : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (ht0 : 0 ≤ t) (ht : t < cappedHit a T z) : a t < z := by
  have htT : t < T := lt_of_lt_of_le ht (cappedHit_bounds ha hT).2
  exact lt_of_not_ge (fun hz => (not_le.mpr ht) ((cappedHit_le_iff ha hT hm ht0 htT).mpr hz))

theorem measurable_cappedHit_family {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → ℝ → ℝ} {z : Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : ∀ ω, Continuous (a ω)) (hm : ∀ ω, MonotoneOn (a ω) (Icc 0 T))
    (ham : ∀ t, Measurable (fun ω => a ω t)) (hz : Measurable z) :
    Measurable (fun ω => cappedHit (a ω) T (z ω)) := by
  apply measurable_of_Iic
  intro t
  by_cases ht0 : 0 ≤ t
  · by_cases htT : t < T
    · have heq : (fun ω => cappedHit (a ω) T (z ω)) ⁻¹' Iic t =
          {ω | z ω ≤ a ω t} := by
        ext ω
        exact cappedHit_le_iff (ha ω) hT (hm ω) ht0 htT
      rw [heq]
      exact measurableSet_le hz (ham t)
    · have heq : (fun ω => cappedHit (a ω) T (z ω)) ⁻¹' Iic t = univ := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cappedHit_bounds (ha ω) hT).2.trans (le_of_not_gt htT)
      rw [heq]
      exact MeasurableSet.univ
  · have heq : (fun ω => cappedHit (a ω) T (z ω)) ⁻¹' Iic t = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht0) (cappedHit_bounds (ha ω) hT).1)
    rw [heq]
    exact MeasurableSet.empty

theorem measurable_cappedHit {a : ℝ → ℝ} (ha : Continuous a) {T : ℝ}
    (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T)) : Measurable (cappedHit a T) := by
  exact measurable_cappedHit_family hT (fun _ => ha) (fun _ => hm)
    (fun _ => measurable_const) measurable_id

theorem service_at_cappedHit {a : ℝ → ℝ} (ha : Continuous a)
    {T z : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (hz0 : a 0 ≤ z) (hzT : z ≤ a T) : a (cappedHit a T z) = z := by
  apply le_antisymm _ (cappedHit_mem_hitSet ha hT hzT).2
  by_contra h
  have hz : z ∈ Ico (a 0) (a (cappedHit a T z)) := ⟨hz0, lt_of_not_ge h⟩
  obtain ⟨t, ht, heq⟩ := intermediate_value_Ico (cappedHit_bounds ha hT).1
    ha.continuousOn hz
  exact (service_below_demand_before_hit ha hT hm ht.1 ht.2).ne heq

theorem cappedHit_pos {a : ℝ → ℝ} (ha : Continuous a)
    {T z : ℝ} (hT : 0 < T) (hz0 : a 0 < z) : 0 < cappedHit a T z := by
  apply lt_of_le_of_ne (cappedHit_bounds ha hT.le).1
  intro heq
  by_cases hzT : z ≤ a T
  · have hz := (cappedHit_mem_hitSet ha hT.le hzT).2
    rw [← heq] at hz
    exact (not_le.mpr hz0) hz
  · simp only [cappedHit, if_neg hzT] at heq
    exact hT.ne heq

theorem cappedHit_monotone {a : ℝ → ℝ} (ha : Continuous a)
    {T : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T)) : Monotone (cappedHit a T) := by
  intro z w hzw
  by_cases hwT : cappedHit a T w < T
  · have hw0 := (cappedHit_bounds (z := w) ha hT).1
    have hw := (cappedHit_le_iff ha hT hm hw0 hwT).mp (le_refl (cappedHit a T w))
    exact (cappedHit_le_iff ha hT hm hw0 hwT).mpr (hzw.trans hw)
  · exact (cappedHit_bounds ha hT).2.trans (le_of_not_gt hwT)

theorem cappedHit_preimage_Iic {a : ℝ → ℝ} (ha : Continuous a)
    {T t : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (ht0 : 0 ≤ t) (htT : t < T) :
    (cappedHit a T) ⁻¹' Iic t = Iic (a t) := by
  ext z
  exact cappedHit_le_iff ha hT hm ht0 htT

theorem cappedHit_exponential_CDF {a : ℝ → ℝ} (ha : Continuous a)
    {T t : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (ha0 : a 0 = 0) (ht0 : 0 ≤ t) (htT : t < T) :
    (Measure.map (cappedHit a T) unitExponential).real (Iic t) = 1 - Real.exp (-a t) := by
  have hat : 0 ≤ a t := by
    rw [← ha0]
    exact hm ⟨le_refl _, hT⟩ ⟨ht0, htT.le⟩ ht0
  rw [map_measureReal_apply (measurable_cappedHit ha hT hm) measurableSet_Iic,
    cappedHit_preimage_Iic ha hT hm ht0 htT, unitExponential_real_Iic, if_pos hat]

theorem cappedHit_exponential_survival {a : ℝ → ℝ} (ha : Continuous a)
    {T t : ℝ} (hT : 0 ≤ T) (hm : MonotoneOn a (Icc 0 T))
    (ha0 : a 0 = 0) (ht0 : 0 ≤ t) (htT : t < T) :
    (Measure.map (cappedHit a T) unitExponential).real (Ioi t) = Real.exp (-a t) := by
  have hat : 0 ≤ a t := by
    rw [← ha0]
    exact hm ⟨le_refl _, hT⟩ ⟨ht0, htT.le⟩ ht0
  have hs : (cappedHit a T) ⁻¹' Ioi t = Ioi (a t) := by
    ext z
    simpa only [mem_preimage, mem_Ioi, not_le] using
      not_congr (cappedHit_le_iff (z := z) ha hT hm ht0 htT)
  rw [map_measureReal_apply (measurable_cappedHit ha hT hm) measurableSet_Ioi,
    hs, unitExponential_real_Ioi hat]

end StochasticMatching
