import Matching.FlowEdgeRemoval
import Mathlib.Data.Fintype.Powerset

/-! A continuous choice of the least amount that must use a given supply edge.
Finite coverage cuts supply its explicit formula; removing that amount and the
edge preserves feasibility of the residual instance.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def edgeLowerBound (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (s : σ) (i : ι) (A : Finset ι) : ℝ :=
  if i ∈ A ∧ ¬ ((N s).erase i ∩ A).Nonempty
    then (∑ j ∈ A, x j) - supplyCoverage N capacity A + capacity s else 0

noncomputable def edgeAmount (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (s : σ) (i : ι) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty (edgeLowerBound N capacity x s i))

theorem edgeAmount_nonneg (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ) (s : σ) (i : ι) :
    0 ≤ edgeAmount N capacity x s i := le_max_left _ _

theorem edgeLowerBound_le_amount (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (s : σ) (i : ι) (A : Finset ι) : edgeLowerBound N capacity x s i A ≤ edgeAmount N capacity x s i :=
  (Finset.le_sup' _ (Finset.mem_univ A)).trans (le_max_right _ _)

theorem edgeAmount_le_flow_entry {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f)
    (hagg : aggregateSupplyFlow f = x) (s : σ) (i : ι) (hi : i ∈ N s) :
    edgeAmount N capacity x s i ≤ f s i := by
  apply max_le (hf.1 s i)
  apply Finset.sup'_le
  intro A _
  unfold edgeLowerBound
  split_ifs with hA
  · have hg := aggregateSupplyFlow_mem_region (removeFlowEntry_feasible hf s i)
    rw [aggregate_removeFlowEntry, hagg] at hg
    have h := hg.2 A
    have hold : (N s ∩ A).Nonempty := ⟨i, Finset.mem_inter.mpr ⟨hi, hA.1⟩⟩
    rw [sum_reduceDemand, if_pos hA.1, supplyCoverage_remove_edge,
      if_neg hA.2, if_pos hold] at h
    linarith
  · exact hf.1 s i

theorem edgeAmount_bounds (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∈ N s) :
    edgeAmount N capacity x s i ≤ x i ∧ edgeAmount N capacity x s i ≤ capacity s := by
  obtain ⟨f, hf, he⟩ := exists_supply_flow_of_mem_region N capacity hcapacity hx
  have ha := edgeAmount_le_flow_entry hf he s i hi
  refine ⟨ha.trans ?_, ha.trans (feasibleSupplyFlow_coordinate_le hf s i)⟩
  rw [← he]
  exact Finset.single_le_sum (fun t _ => hf.1 t i) (Finset.mem_univ s)

theorem edgeAmount_residual_feasible (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∈ N s) :
    reduceDemand x i (edgeAmount N capacity x s i) ∈
      supplyRegion (removeSupplyEdge N s i) (reduceSupply capacity s (edgeAmount N capacity x s i)) := by
  let a := edgeAmount N capacity x s i
  obtain ⟨f, hf, he⟩ := exists_supply_flow_of_mem_region N capacity hcapacity hx
  have ha : a ≤ f s i := edgeAmount_le_flow_entry hf he s i hi
  have hab := edgeAmount_bounds N capacity hcapacity hx s i hi
  have hg := aggregateSupplyFlow_mem_region (removeFlowEntry_feasible hf s i)
  rw [aggregate_removeFlowEntry, he] at hg
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [reduceDemand, Function.update_self]
      exact sub_nonneg.mpr hab.1
    · simpa only [reduceDemand, Function.update_of_ne hj] using hx.1 j
  · intro A
    rw [sum_reduceDemand]
    by_cases hiA : i ∈ A
    · rw [if_pos hiA]
      have hold : (N s ∩ A).Nonempty := ⟨i, Finset.mem_inter.mpr ⟨hi, hiA⟩⟩
      rw [supplyCoverage_remove_edge, if_pos hold]
      by_cases hnew : ((N s).erase i ∩ A).Nonempty
      · rw [if_pos hnew]
        have h := hx.2 A
        linarith
      · rw [if_neg hnew]
        have h := edgeLowerBound_le_amount N capacity x s i A
        have hcond : i ∈ A ∧ ¬ ((N s).erase i ∩ A).Nonempty := ⟨hiA, hnew⟩
        unfold edgeLowerBound at h
        rw [if_pos hcond] at h
        change _ ≤ a at h
        linarith
    · rw [if_neg hiA, sub_zero]
      have h := hg.2 A
      rw [sum_reduceDemand, if_neg hiA, sub_zero] at h
      exact h.trans (supplyCoverage_capacity_mono (removeSupplyEdge N s i)
        (reduceSupply_antitone_amount capacity s ha) A)

theorem edgeAmount_residual_capacity (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∈ N s) :
    ∀ t, 0 ≤ reduceSupply capacity s (edgeAmount N capacity x s i) t := by
  intro t
  by_cases ht : t = s
  · subst t
    simp only [reduceSupply, Function.update_self]
    exact sub_nonneg.mpr (edgeAmount_bounds N capacity hcapacity hx s i hi).2
  · simpa only [reduceSupply, Function.update_of_ne ht] using hcapacity t

theorem continuous_supplyCoverage_capacity (N : σ → Finset ι) (A : Finset ι) :
    Continuous (fun capacity : σ → ℝ => supplyCoverage N capacity A) := by
  apply continuous_finset_sum
  intro s _
  by_cases hs : (N s ∩ A).Nonempty
  · simpa only [if_pos hs] using continuous_apply s
  · simpa only [if_neg hs] using (continuous_const : Continuous (fun _ : σ → ℝ => (0 : ℝ)))

theorem continuous_edgeAmount (N : σ → Finset ι) (s : σ) (i : ι) :
    Continuous (fun p : (σ → ℝ) × (ι → ℝ) => edgeAmount N p.1 p.2 s i) := by
  apply continuous_const.max
  apply Continuous.finset_sup'_apply
  intro A _
  unfold edgeLowerBound
  split_ifs
  · exact ((continuous_finset_sum A (fun j _ => (continuous_apply j).comp continuous_snd)).sub
      ((continuous_supplyCoverage_capacity N A).comp continuous_fst)).add
        ((continuous_apply s).comp continuous_fst)
  · exact continuous_const

end StochasticMatching
