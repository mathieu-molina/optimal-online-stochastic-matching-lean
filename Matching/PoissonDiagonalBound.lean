import Matching.PoissonTransferMoments
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! The explicit finite-size loss bound, proved from mathlib's Stirling
sequence monotonicity and limit rather than assuming a factorial estimate. -/
open Filter
open scoped Topology
namespace StochasticMatching

theorem sqrt_pi_le_stirlingSeq (n : ℕ) (hn : 0 < n) :
    Real.sqrt Real.pi ≤ Stirling.stirlingSeq n := by
  apply le_of_tendsto Stirling.tendsto_stirlingSeq_sqrt_pi
  filter_upwards [eventually_ge_atTop n] with k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hn.trans_le hk))
  exact Stirling.stirlingSeq'_antitone (Nat.succ_le_succ_iff.mp hk)

theorem poissonWeight_diagonal_stirling (n : ℕ) (hn : 0 < n) :
    poissonWeight n n * Stirling.stirlingSeq n = 1 / Real.sqrt (2 * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs : Real.sqrt (2 * (n : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul 1 n
  unfold poissonWeight Stirling.stirlingSeq
  rw [Real.exp_neg, he, div_pow]
  field_simp [hn0, hs, hf, Real.exp_ne_zero]
  <;> ring

theorem poissonWeight_diagonal_le (n : ℕ) (hn : 0 < n) :
    poissonWeight n n ≤ 1 / Real.sqrt (2 * Real.pi * (n : ℝ)) := by
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hs : 0 < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have h := mul_le_mul_of_nonneg_left (sqrt_pi_le_stirlingSeq n hn)
    (poissonWeight_nonneg (Nat.cast_nonneg n) n)
  rw [poissonWeight_diagonal_stirling n hn] at h
  have he : Real.sqrt (2 * Real.pi * (n : ℝ)) = Real.sqrt (2 * (n : ℝ)) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * (n : ℝ))]
    congr 1
    ring
  rw [he, ← div_div]
  exact (le_div_iff₀ hp).mpr h

end StochasticMatching
