import Matching.OrderedRenewalCuts
import Matching.ExponentialPoissonTail
import Matching.InitialState
import Mathlib.Order.Interval.Finset.Fin

/-! The counting variable built from finitely many exponential waiting times
has the truncated Poisson law. This is an actual path/count identification.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {n : ℕ}

theorem finiteRenewalCount_le_length (z : Fin n → ℝ) (t : ℝ) : finiteRenewalCount z t ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem finiteRenewalCount_le_iff {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) (t : ℝ) (j : Fin n) :
    finiteRenewalCount z t ≤ j.val ↔ t < arrivalTime z j := by
  constructor
  · intro hc
    by_contra hj
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => arrivalTime z i ≤ t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (arrivalTime_mono hz (Finset.mem_Iic.mp hi)).trans (le_of_not_gt hj)⟩
    have h := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at h
    change j.val + 1 ≤ finiteRenewalCount z t at h
    omega
  · intro hj
    have hsub : Finset.univ.filter (fun i => arrivalTime z i ≤ t) ⊆ Finset.Iio j := by
      intro i hi
      have hit := (Finset.mem_filter.mp hi).2
      apply Finset.mem_Iio.mpr
      by_contra hij
      have h := arrivalTime_mono hz (le_of_not_gt hij)
      linarith
    simpa only [Fin.card_Iio] using Finset.card_le_card hsub

theorem measurable_finiteRenewalCount (t : ℝ) : Measurable (fun z : Fin n → ℝ => finiteRenewalCount z t) := by
  classical
  have he : (fun z : Fin n → ℝ => finiteRenewalCount z t) =
      fun z => ∑ i : Fin n, if arrivalTime z i ≤ t then (1 : ℕ) else 0 := by
    funext z
    simp [finiteRenewalCount]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite (measurableSet_le (measurable_arrivalTime i) measurable_const) measurable_const

theorem finiteRenewalCount_poisson_law (a : ℝ≥0) :
    Measure.map (fun z : Fin n → ℝ => finiteRenewalCount z a) independentExponentials =
      Measure.map (fun k : ℕ => min n k) (poissonMeasure a) := by
  apply Measure.ext_of_Iic
  intro k
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [map_measureReal_apply (measurable_finiteRenewalCount a) measurableSet_Iic,
    map_measureReal_apply (measurable_of_countable _) measurableSet_Iic]
  by_cases hk : n ≤ k
  · have hl : (fun z : Fin n → ℝ => finiteRenewalCount z a) ⁻¹' Iic k = Set.univ := by
      ext z
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (finiteRenewalCount_le_length z a).trans hk
    have hr : (fun q : ℕ => min n q) ⁻¹' Iic k = Set.univ := by
      ext q
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (min_le_left _ _).trans hk
    rw [hl, hr, measureReal_univ_eq_one, measureReal_univ_eq_one]
  · let j : Fin n := ⟨k, lt_of_not_ge hk⟩
    have hl : ((fun z : Fin n → ℝ => finiteRenewalCount z a) ⁻¹' Iic k : Set (Fin n → ℝ)) =ᵐ[independentExponentials]
        {z | (a : ℝ) < arrivalTime z j} := by
      filter_upwards [independentExponentials_ae_pos (ι := Fin n)] with z hz
      apply propext
      exact finiteRenewalCount_le_iff (fun i => (hz i).le) a j
    have hr : (fun q : ℕ => min n q) ⁻¹' Iic k = {q : ℕ | q < k + 1} := by
      ext q
      simp only [mem_preimage, mem_Iic, mem_setOf_eq]
      omega
    rw [measureReal_congr hl, hr]
    have h := exponential_subset_sum_poisson_tail (Finset.Iic j) a
    simpa only [Fin.card_Iic, j] using h

end StochasticMatching
