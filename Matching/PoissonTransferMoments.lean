import Matching.PoissonWeights

/-! Exact Poisson shortfall and excess moments for fixed-count transfer. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem poissonWeight_sum (a : ℝ≥0) : HasSum (poissonWeight a) 1 :=
  poissonPMFRealSum a

theorem poissonWeight_succ_balance (a : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * poissonWeight a (k + 1) = a * poissonWeight a k := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem poissonWeight_first_moment (a : ℝ≥0) :
    HasSum (fun k : ℕ => (k : ℝ) * poissonWeight a k) (a : ℝ) := by
  have h := (poissonWeight_sum a).mul_left (a : ℝ)
  have hs : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * poissonWeight a (k + 1)) (a : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, poissonWeight_succ_balance, mul_one] using h
  have ht : HasSum (fun k : ℕ => (k : ℝ) * poissonWeight a k)
      ((a : ℝ) + ∑ k ∈ Finset.range 1, (k : ℝ) * poissonWeight a k) :=
    (hasSum_nat_add_iff (f := fun k : ℕ => (k : ℝ) * poissonWeight a k) 1).mp hs
  simpa using ht

theorem poissonWeight_partial_first_moment (a : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * poissonWeight a k) =
      a * ∑ k ∈ Finset.range n, poissonWeight a k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one, poissonWeight_succ_balance,
      Finset.sum_range_succ, mul_add]

theorem poissonWeight_shortfall_finite (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - k) * poissonWeight n k) =
      (n : ℝ) * poissonWeight n n := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, poissonWeight_partial_first_moment,
    Finset.sum_range_succ]
  ring

theorem poissonWeight_shortfall (n : ℕ) :
    HasSum (fun k : ℕ => ((n - k : ℕ) : ℝ) * poissonWeight n k)
      ((n : ℝ) * poissonWeight n n) := by
  have hzero : ∀ k ∉ Finset.range (n + 1), ((n - k : ℕ) : ℝ) * poissonWeight n k = 0 := by
    intro k hk
    have hnk : n ≤ k := by simp only [Finset.mem_range, not_lt] at hk; omega
    simp [Nat.sub_eq_zero_of_le hnk]
  have h := hasSum_sum_of_ne_finset_zero hzero
  have he : (∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℝ) * poissonWeight n k) =
      (n : ℝ) * poissonWeight n n := by
    rw [← poissonWeight_shortfall_finite]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  rwa [he] at h

theorem poissonWeight_excess (n : ℕ) :
    HasSum (fun k : ℕ => ((k - n : ℕ) : ℝ) * poissonWeight n k)
      ((n : ℝ) * poissonWeight n n) := by
  have h := ((poissonWeight_shortfall n).add (poissonWeight_first_moment (n : ℝ≥0))).sub
    ((poissonWeight_sum (n : ℝ≥0)).mul_left (n : ℝ))
  have he (k : ℕ) : ((n - k : ℕ) : ℝ) * poissonWeight n k +
      (k : ℝ) * poissonWeight n k - (n : ℝ) * poissonWeight n k =
        ((k - n : ℕ) : ℝ) * poissonWeight n k := by
    rcases le_total k n with hkn | hnk
    · rw [Nat.cast_sub hkn, Nat.sub_eq_zero_of_le hkn]
      ring
    · rw [Nat.cast_sub hnk, Nat.sub_eq_zero_of_le hnk]
      ring
  simpa only [NNReal.coe_natCast, Pi.add_apply, Pi.sub_apply, mul_one, he, add_sub_cancel_right] using h

end StochasticMatching
