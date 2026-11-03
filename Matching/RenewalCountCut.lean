import Matching.InfiniteRenewalCount

/-! Deterministic count bounds and exact identification at a renewal cut. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching

theorem renewalPartialSum_zero (z : ℕ → ℝ) : renewalPartialSum z 0 = 0 := by
  simp [renewalPartialSum]

theorem renewalPartialSum_succ (z : ℕ → ℝ) (n : ℕ) :
    renewalPartialSum z (n + 1) = renewalPartialSum z n + z n :=
  Finset.sum_range_succ _ _

theorem le_infiniteRenewalCount_of_sum_le {T : ℝ} (hT : 0 ≤ T)
    {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i) (hunb : ∃ n, T < renewalPartialSum z n)
    {k : ℕ} (hk : renewalPartialSum z k ≤ T) : k ≤ infiniteRenewalCount T z := by
  by_contra h
  have hle : infiniteRenewalCount T z ≤ k - 1 := by omega
  have hkpos : 0 < k := by omega
  have hc := (infiniteRenewalCount_le_iff hT hz hunb (k - 1)).mp hle
  have he : k - 1 + 1 = k := by omega
  rw [he] at hc
  exact (not_lt.mpr hk) hc

theorem infiniteRenewalCount_eq_of_cut {T : ℝ} (hT : 0 ≤ T)
    {z : ℕ → ℝ} (hz : ∀ i, 0 ≤ z i) {k : ℕ}
    (hbefore : renewalPartialSum z k ≤ T) (hafter : T < renewalPartialSum z (k + 1)) :
    infiniteRenewalCount T z = k := by
  have hunb : ∃ n, T < renewalPartialSum z n := ⟨k + 1, hafter⟩
  exact le_antisymm ((infiniteRenewalCount_le_iff hT hz hunb k).mpr hafter)
    (le_infiniteRenewalCount_of_sum_le hT hz hunb hbefore)

end StochasticMatching
