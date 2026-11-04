import Matching.PoissonWeights
import Mathlib.Order.Interval.Finset.Fin

/-! Cumulative increments and the finite recursive probability shared by
exponential waiting inequalities and Poisson count inequalities.
-/

open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching

def cumulativeFin {M : Type*} [AddCommMonoid M] {n : ℕ} (v : Fin n → M) (k : Fin n) : M :=
  ∑ i ∈ Finset.Iic k, v i

theorem cumulativeFin_zero {M : Type*} [AddCommMonoid M] {n : ℕ} (v : Fin (n+1) → M) :
    cumulativeFin v 0 = v 0 := by
  have he : Finset.Iic (0 : Fin (n+1)) = {0} := by ext i; simp
  simp only [cumulativeFin, he, Finset.sum_singleton]

theorem cumulativeFin_succ {M : Type*} [AddCommMonoid M] {n : ℕ}
    (v : Fin (n+1) → M) (k : Fin n) :
    cumulativeFin v k.succ = v 0 + cumulativeFin (fun i => v i.succ) k := by
  have he : Finset.Iic k.succ = insert 0 ((Finset.Iic k).map (Fin.succEmb n)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_map,
        Fin.succEmb, Fin.succ_inj, Fin.succ_ne_zero, false_or]
      simp
  have h0 : (0 : Fin (n+1)) ∉ (Finset.Iic k).map (Fin.succEmb n) := by simp
  unfold cumulativeFin
  rw [he, Finset.sum_insert h0, Finset.sum_map]
  rfl

noncomputable def poissonChainValue : {n : ℕ} → (Fin n → ℝ≥0) → (Fin n → ℕ) → ℝ
  | 0, _, _ => 1
  | n+1, a, m => ∑ j : Fin (m 0), poissonWeight (a 0) j.val *
      poissonChainValue (fun k : Fin n => a k.succ) (fun k => m k.succ - j.val)

theorem poissonChainValue_zero (a : Fin 0 → ℝ≥0) (m : Fin 0 → ℕ) :
    poissonChainValue a m = 1 := rfl

theorem poissonChainValue_succ {n : ℕ} (a : Fin (n+1) → ℝ≥0) (m : Fin (n+1) → ℕ) :
    poissonChainValue a m = ∑ j : Fin (m 0), poissonWeight (a 0) j.val *
      poissonChainValue (fun k : Fin n => a k.succ) (fun k => m k.succ - j.val) := rfl

end StochasticMatching
