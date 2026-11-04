import Matching.InfiniteRenewal

/-! The count of an actual infinite renewal process has the full Poisson
law. The count is total and measurable, with a harmless default on paths
that never cross the horizon; that exceptional event has probability zero.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

def renewalPartialSum (z : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, z i

theorem measurable_renewalPartialSum (n : ℕ) : Measurable (fun z => renewalPartialSum z n) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem renewalPartialSum_mono {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i) :
    Monotone (renewalPartialSum z) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) (fun i _ _ => hz i)

def renewalCrossingPredicate (T : ℝ) (z : ℕ → ℝ) (n : ℕ) : Prop :=
  (∃ m, T < renewalPartialSum z m) → T < renewalPartialSum z n

theorem renewalCrossing_exists (T : ℝ) (z : ℕ → ℝ) : ∃ n, renewalCrossingPredicate T z n := by
  classical
  by_cases h : ∃ m, T < renewalPartialSum z m
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, fun _ => hn⟩
  · exact ⟨0, fun hm => False.elim (h hm)⟩

noncomputable def renewalCrossing (T : ℝ) (z : ℕ → ℝ) : ℕ := by
  classical
  exact Nat.find (renewalCrossing_exists T z)

noncomputable def infiniteRenewalCount (T : ℝ) (z : ℕ → ℝ) : ℕ := renewalCrossing T z - 1

theorem measurable_renewalCrossing (T : ℝ) : Measurable (renewalCrossing T) := by
  classical
  apply measurable_find
  intro n
  have hm : ∀ k, MeasurableSet {z : ℕ → ℝ | T < renewalPartialSum z k} :=
    fun k => measurableSet_lt measurable_const (measurable_renewalPartialSum k)
  have he : {z : ℕ → ℝ | ∃ m, T < renewalPartialSum z m} =
      ⋃ m, {z | T < renewalPartialSum z m} := by ext z; simp
  have hn : {z | renewalCrossingPredicate T z n} =
      {z : ℕ → ℝ | ∃ m, T < renewalPartialSum z m}ᶜ ∪ {z | T < renewalPartialSum z n} := by
    ext z
    simp only [renewalCrossingPredicate, mem_setOf_eq, mem_union, mem_compl_iff]
    exact imp_iff_not_or
  rw [hn, he]
  exact (MeasurableSet.iUnion hm).compl.union (hm n)

theorem measurable_infiniteRenewalCount (T : ℝ) : Measurable (infiniteRenewalCount T) :=
  (measurable_of_countable (fun n : ℕ => n - 1)).comp (measurable_renewalCrossing T)

theorem renewalCrossing_spec {T : ℝ} {z : ℕ → ℝ}
    (h : ∃ n, T < renewalPartialSum z n) : T < renewalPartialSum z (renewalCrossing T z) := by
  classical
  exact Nat.find_spec (renewalCrossing_exists T z) h

theorem renewalCrossing_le {T : ℝ} {z : ℕ → ℝ} {n : ℕ}
    (h : T < renewalPartialSum z n) : renewalCrossing T z ≤ n := by
  classical
  exact Nat.find_min' (renewalCrossing_exists T z) (fun _ => h)

theorem infiniteRenewalCount_le_iff {T : ℝ} (hT : 0 ≤ T) {z : ℕ → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hunb : ∃ n, T < renewalPartialSum z n) (k : ℕ) :
    infiniteRenewalCount T z ≤ k ↔ T < renewalPartialSum z (k + 1) := by
  have hpos : 0 < renewalCrossing T z := by
    by_contra h
    have he : renewalCrossing T z = 0 := by omega
    have hs := renewalCrossing_spec hunb
    rw [he] at hs
    simp only [renewalPartialSum, Finset.range_zero, Finset.sum_empty] at hs
    exact (not_lt.mpr hT) hs
  constructor
  · intro hk
    have hn : renewalCrossing T z ≤ k + 1 := by unfold infiniteRenewalCount at hk; omega
    exact (renewalCrossing_spec hunb).trans_le (renewalPartialSum_mono hz hn)
  · intro hk
    have hn := renewalCrossing_le hk
    unfold infiniteRenewalCount
    omega

theorem infiniteRenewalCount_poisson_law (a : ℝ≥0) :
    Measure.map (infiniteRenewalCount a) infiniteExponentials = poissonMeasure a := by
  apply Measure.ext_of_Iic
  intro k
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (Measure.map (infiniteRenewalCount a) infiniteExponentials).real (Iic k) = _
  rw [map_measureReal_apply (measurable_infiniteRenewalCount a) measurableSet_Iic]
  have he : ((infiniteRenewalCount a) ⁻¹' Iic k : Set (ℕ → ℝ)) =ᵐ[infiniteExponentials]
      {z | (a : ℝ) < renewalPartialSum z (k + 1)} := by
    filter_upwards [infiniteExponentials_all_pos, infiniteExponentials_unbounded] with z hz hunb
    apply propext
    exact infiniteRenewalCount_le_iff a.coe_nonneg (fun i => (hz i).le) (hunb a) k
  rw [measureReal_congr he]
  have hl := infiniteExponentials_sum_law (Finset.range (k + 1))
  have h := congrArg (fun μ : Measure ℝ => μ.real (Ioi (a : ℝ))) hl
  change (Measure.map (fun z => renewalPartialSum z (k + 1)) infiniteExponentials).real (Ioi (a : ℝ)) =
    (exponentialSumLaw (Finset.range (k + 1)).card).real (Ioi (a : ℝ)) at h
  rw [map_measureReal_apply (measurable_renewalPartialSum (k + 1)) measurableSet_Ioi,
    Finset.card_range, exponentialSumLaw_tail_eq_poissonLowerTail _ a.coe_nonneg,
    poissonLowerTail_eq_probability] at h
  have hk : {q : ℕ | q < k + 1} = Iic k := by
    ext q
    exact Nat.lt_succ_iff
  rw [hk] at h
  exact h

end StochasticMatching
