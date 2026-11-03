import Matching.FlowEdgeAmount

/-! Restoring an assigned edge after solving the residual supply instance,
and continuity of the elementary operations used by the finite construction.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

def insertFlowEntry (g : σ → ι → ℝ) (s : σ) (i : ι) (a : ℝ) : σ → ι → ℝ :=
  Function.update g s (Function.update (g s) i a)

theorem restore_supply_edge (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (s : σ) (i : ι) (hi : i ∈ N s) (a : ℝ) (ha : 0 ≤ a) (g : σ → ι → ℝ)
    (hg : FeasibleSupplyFlow (removeSupplyEdge N s i) (reduceSupply capacity s a) g)
    (hagg : aggregateSupplyFlow g = reduceDemand x i a) :
    FeasibleSupplyFlow N capacity (insertFlowEntry g s i a) ∧
      aggregateSupplyFlow (insertFlowEntry g s i a) = x := by
  have hzero : g s i = 0 := hg.2.1 s i (by simp [removeSupplyEdge])
  have hf : FeasibleSupplyFlow N capacity (insertFlowEntry g s i a) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t j
      by_cases ht : t = s
      · subst t
        by_cases hj : j = i
        · subst j
          simpa only [insertFlowEntry, Function.update_self] using ha
        · simpa only [insertFlowEntry, Function.update_self, Function.update_of_ne hj] using hg.1 s j
      · simpa only [insertFlowEntry, Function.update_of_ne ht] using hg.1 t j
    · intro t j hj
      by_cases ht : t = s
      · subst t
        have hji : j ≠ i := fun he => hj (he.symm ▸ hi)
        have hjs : j ∉ removeSupplyEdge N s i s := by
          simpa only [removeSupplyEdge, Function.update_self, Finset.mem_erase, not_and] using
            (fun _ : j ≠ i => hj)
        simpa only [insertFlowEntry, Function.update_self, Function.update_of_ne hji] using hg.2.1 s j hjs
      · have hjs : j ∉ removeSupplyEdge N s i t := by
          simpa only [removeSupplyEdge, Function.update_of_ne ht] using hj
        simpa only [insertFlowEntry, Function.update_of_ne ht] using hg.2.1 t j hjs
    · intro t
      by_cases ht : t = s
      · subst t
        simp only [insertFlowEntry, Function.update_self]
        rw [sum_update_value, hzero]
        have h := hg.2.2 s
        simp only [reduceSupply, Function.update_self] at h
        linarith
      · simpa only [insertFlowEntry, reduceSupply, Function.update_of_ne ht] using hg.2.2 t
  refine ⟨hf, ?_⟩
  funext j
  unfold insertFlowEntry
  rw [aggregate_update_row, hagg]
  by_cases hj : j = i
  · subst j
    simp only [reduceDemand, Function.update_self, hzero]
    ring
  · simp only [reduceDemand, Function.update_of_ne hj, sub_self, add_zero]

theorem continuous_reduceSupply (s : σ) :
    Continuous (fun p : (σ → ℝ) × ℝ => reduceSupply p.1 s p.2) := by
  apply continuous_pi
  intro t
  by_cases ht : t = s
  · subst t
    simp only [reduceSupply, Function.update_self]
    exact ((continuous_apply s).comp continuous_fst).sub continuous_snd
  · simp only [reduceSupply, Function.update_of_ne ht]
    exact (continuous_apply t).comp continuous_fst

theorem continuous_reduceDemand (i : ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => reduceDemand p.1 i p.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simp only [reduceDemand, Function.update_self]
    exact ((continuous_apply i).comp continuous_fst).sub continuous_snd
  · simp only [reduceDemand, Function.update_of_ne hj]
    exact (continuous_apply j).comp continuous_fst

theorem continuous_insertFlowEntry (s : σ) (i : ι) :
    Continuous (fun p : (σ → ι → ℝ) × ℝ => insertFlowEntry p.1 s i p.2) := by
  apply continuous_pi
  intro t
  apply continuous_pi
  intro j
  by_cases ht : t = s
  · subst t
    by_cases hj : j = i
    · subst j
      simp only [insertFlowEntry, Function.update_self]
      exact continuous_snd
    · simp only [insertFlowEntry, Function.update_self, Function.update_of_ne hj]
      exact (continuous_apply j).comp ((continuous_apply s).comp continuous_fst)
  · simp only [insertFlowEntry, Function.update_of_ne ht]
    exact (continuous_apply j).comp ((continuous_apply t).comp continuous_fst)

end StochasticMatching
