import Matching.SubsetRenewalRecursion
import Matching.FiniteChainRecurrence

/-! Arbitrary finite chains of nested exponential waiting sums obey the
Poisson increment recurrence. The induction retains all future constraints.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem exponential_nested_chain_value {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin n → Finset ι) (hA : Monotone A) (a : Fin n → ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | ∀ k, ((cumulativeFin a k : ℝ≥0) : ℝ) < ∑ i ∈ A k, z i} =
      poissonChainValue a (fun k => (A k).card) := by
  induction n generalizing ι with
  | zero =>
      have he : {z : ι → ℝ | ∀ k : Fin 0, ((cumulativeFin a k : ℝ≥0) : ℝ) < ∑ i ∈ A k, z i} = Set.univ := by
        ext z
        simp
      rw [he, measureReal_univ_eq_one, poissonChainValue_zero]
  | succ n ih =>
      let B : Fin n → Finset ι := fun k => A k.succ
      let b : Fin n → ℝ≥0 := fun k => a k.succ
      have hAB : ∀ k, A 0 ⊆ B k := fun k => hA (Fin.zero_le _)
      have hB : Monotone B := fun k l hkl => hA (Fin.succ_le_succ_iff.mpr hkl)
      have he : {z : ι → ℝ | ∀ k : Fin (n+1), ((cumulativeFin a k : ℝ≥0) : ℝ) < ∑ i ∈ A k, z i} =
          {z | (a 0 : ℝ) < ∑ i ∈ A 0, z i ∧
            ∀ k : Fin n, (a 0 : ℝ) + ((cumulativeFin b k : ℝ≥0) : ℝ) < ∑ i ∈ B k, z i} := by
        ext z
        simp only [mem_setOf_eq, Fin.forall_fin_succ, cumulativeFin_zero, cumulativeFin_succ, NNReal.coe_add, B, b]
      rw [he, subset_waiting_joint_recursion (A 0) B hAB (a 0).coe_nonneg
        (fun k => ((cumulativeFin b k : ℝ≥0) : ℝ)), poissonChainValue_succ]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      have hjB : ∀ k, subsetBefore (A 0) j ⊆ B k := fun k =>
        (subsetBefore_subset (A 0) j).trans (hAB k)
      rw [ih (fun k => remainingSubset (subsetBefore (A 0) j) (B k))
        ((remainingSubset_mono (subsetBefore (A 0) j)).comp hB) b]
      congr 1
      funext k
      rw [remainingSubset_card _ _ (hjB k), subsetBefore_card]

end StochasticMatching
