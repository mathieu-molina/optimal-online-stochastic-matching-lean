import Matching.HardPoissonOffline
import Matching.HardUpperPotential

/-! The finite offline error tends to zero relative to the instance size.
Every proposed ratio strictly above the target is separated by a finite
square-sized member of the hard family. -/
namespace StochasticMatching

theorem exists_hard_size_separating {c r : ℝ} (hc : 0 ≤ c) (hcr : c < r) :
    ∃ m : ℕ, 0 < m ∧ 0 < (m : ℝ) - 2 * Real.sqrt m ∧
      c * m < r * ((m : ℝ) - 2 * Real.sqrt m) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 : ℝ) (2 * r / (r - c)))
  have hk2 : (2 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkd : 2 * r / (r - c) < (k : ℝ) := (le_max_right _ _).trans_lt hk
  have hd : 0 < r - c := sub_pos.mpr hcr
  have hk0 : (0 : ℝ) < k := by linarith
  have hkn : 0 < k := Nat.cast_pos.mp hk0
  refine ⟨k ^ 2, pow_pos hkn _, ?_, ?_⟩
  · rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k)]
    nlinarith [mul_pos hk0 (sub_pos.mpr hk2)]
  · rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k)]
    have hmul : 2 * r < (k : ℝ) * (r - c) := (div_lt_iff₀ hd).mp hkd
    have h := mul_lt_mul_of_pos_left hmul hk0
    nlinarith

theorem exists_poisson_ratio_separating {r : ℝ} (hr : Comparison.ratio < r) :
    ∃ m : ℕ, 0 < m ∧ ∀ (alg opt : ℝ),
      (m : ℝ) - 2 * Real.sqrt m ≤ opt → alg ≤ (m : ℝ) * Comparison.ratio →
      0 < opt ∧ alg < r * opt := by
  obtain ⟨m, hm, hpos, hgap⟩ := exists_hard_size_separating Comparison.ratio_pos.le hr
  refine ⟨m, hm, ?_⟩
  intro alg opt hopt halg
  have hr0 : 0 ≤ r := Comparison.ratio_pos.le.trans hr.le
  constructor
  · exact hpos.trans_le hopt
  · have he : alg ≤ Comparison.ratio * m := by simpa only [mul_comm] using halg
    exact (he.trans_lt hgap).trans_le (mul_le_mul_of_nonneg_left hopt hr0)

end StochasticMatching
