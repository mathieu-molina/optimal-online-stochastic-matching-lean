import Matching.SupplyFlowConverse

/-! Removing one supported edge after fixing its assigned flow. The residual
coverage formula makes the dependence on that edge amount explicit.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

def removeSupplyEdge (N : σ → Finset ι) (s : σ) (i : ι) : σ → Finset ι :=
  Function.update N s ((N s).erase i)

def reduceSupply (capacity : σ → ℝ) (s : σ) (a : ℝ) : σ → ℝ :=
  Function.update capacity s (capacity s - a)

def reduceDemand (x : ι → ℝ) (i : ι) (a : ℝ) : ι → ℝ :=
  Function.update x i (x i - a)

def removeFlowEntry (f : σ → ι → ℝ) (s : σ) (i : ι) : σ → ι → ℝ :=
  Function.update f s (Function.update (f s) i 0)

theorem supplyCoverage_capacity_mono (N : σ → Finset ι) {c d : σ → ℝ} (hcd : c ≤ d) (A : Finset ι) :
    supplyCoverage N c A ≤ supplyCoverage N d A := by
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact hcd s
  · exact le_refl _

theorem supplyCoverage_remove_edge (N : σ → Finset ι) (capacity : σ → ℝ)
    (s : σ) (i : ι) (a : ℝ) (A : Finset ι) :
    supplyCoverage (removeSupplyEdge N s i) (reduceSupply capacity s a) A =
      supplyCoverage N capacity A +
        (if ((N s).erase i ∩ A).Nonempty then capacity s - a else 0) -
        (if (N s ∩ A).Nonempty then capacity s else 0) := by
  have he : (fun t => if (removeSupplyEdge N s i t ∩ A).Nonempty then reduceSupply capacity s a t else 0) =
      Function.update (fun t => if (N t ∩ A).Nonempty then capacity t else 0) s
        (if ((N s).erase i ∩ A).Nonempty then capacity s - a else 0) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [removeSupplyEdge, reduceSupply, Function.update_self]
    · simp only [removeSupplyEdge, reduceSupply, Function.update_of_ne ht]
  unfold supplyCoverage
  rw [he, sum_update_value]
  ring

theorem sum_reduceDemand (x : ι → ℝ) (i : ι) (a : ℝ) (A : Finset ι) :
    (∑ j ∈ A, reduceDemand x i a j) = (∑ j ∈ A, x j) - if i ∈ A then a else 0 := by
  have he : x i - a = x i + (-a) := by ring
  unfold reduceDemand
  rw [he, sum_update_add]
  by_cases hi : i ∈ A <;> simp [hi] <;> ring

theorem removeFlowEntry_feasible {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (i : ι) :
    FeasibleSupplyFlow (removeSupplyEdge N s i) (reduceSupply capacity s (f s i)) (removeFlowEntry f s i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    by_cases ht : t = s
    · subst t
      by_cases hj : j = i
      · subst j
        simp only [removeFlowEntry, Function.update_self, le_refl]
      · simpa only [removeFlowEntry, Function.update_self, Function.update_of_ne hj] using hf.1 s j
    · simpa only [removeFlowEntry, Function.update_of_ne ht] using hf.1 t j
  · intro t j hj
    by_cases ht : t = s
    · subst t
      by_cases hji : j = i
      · subst j
        simp only [removeFlowEntry, Function.update_self]
      · have hjN : j ∉ N s := by
          intro h
          apply hj
          simpa only [removeSupplyEdge, Function.update_self] using Finset.mem_erase.mpr ⟨hji, h⟩
        simpa only [removeFlowEntry, Function.update_self, Function.update_of_ne hji] using hf.2.1 s j hjN
    · have hjN : j ∉ N t := by simpa only [removeSupplyEdge, Function.update_of_ne ht] using hj
      simpa only [removeFlowEntry, Function.update_of_ne ht] using hf.2.1 t j hjN
  · intro t
    by_cases ht : t = s
    · subst t
      simp only [removeFlowEntry, reduceSupply, Function.update_self]
      rw [sum_update_value]
      have h := hf.2.2 s
      linarith
    · simpa only [removeFlowEntry, reduceSupply, Function.update_of_ne ht] using hf.2.2 t

theorem aggregate_removeFlowEntry (f : σ → ι → ℝ) (s : σ) (i : ι) :
    aggregateSupplyFlow (removeFlowEntry f s i) = reduceDemand (aggregateSupplyFlow f) i (f s i) := by
  funext j
  unfold removeFlowEntry
  rw [aggregate_update_row]
  by_cases hj : j = i
  · subst j
    simp only [reduceDemand, Function.update_self]
    ring
  · simp only [reduceDemand, Function.update_of_ne hj, sub_self, add_zero]

theorem reduceSupply_antitone_amount (capacity : σ → ℝ) (s : σ) {a b : ℝ} (hab : a ≤ b) :
    reduceSupply capacity s b ≤ reduceSupply capacity s a := by
  intro t
  by_cases ht : t = s
  · subst t
    simp only [reduceSupply, Function.update_self]
    linarith
  · simp only [reduceSupply, Function.update_of_ne ht, le_refl]

theorem erase_inter_nonempty_implies (N : Finset ι) (i : ι) (A : Finset ι)
    (h : (N.erase i ∩ A).Nonempty) : (N ∩ A).Nonempty := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hj).1,
    (Finset.mem_inter.mp hj).2⟩⟩

end StochasticMatching
