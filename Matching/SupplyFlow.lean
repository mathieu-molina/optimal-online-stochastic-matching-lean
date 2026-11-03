import Matching.SupplyRegion

/-! Supported fractional supply flows satisfy every coverage constraint.
Normalizing a feasible flow by the type supplies gives valid arrival-assignment
probabilities and recovers the aggregate rates, including zero-supply types.
The converse flow-existence implication is a separate, unfinished obligation.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

def FeasibleSupplyFlow (N : σ → Finset ι) (capacity : σ → ℝ) (f : σ → ι → ℝ) : Prop :=
  (∀ s i, 0 ≤ f s i) ∧ (∀ s i, i ∉ N s → f s i = 0) ∧
    ∀ s, ∑ i, f s i ≤ capacity s

noncomputable def aggregateSupplyFlow (f : σ → ι → ℝ) (i : ι) : ℝ := ∑ s, f s i

theorem feasibleSupplyFlow_coordinate_le {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (i : ι) : f s i ≤ capacity s :=
  (Finset.single_le_sum (fun j _ => hf.1 s j) (Finset.mem_univ i)).trans (hf.2.2 s)

theorem feasibleSupplyFlow_capacity_nonneg {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) : 0 ≤ capacity s :=
  (Finset.sum_nonneg (fun i _ => hf.1 s i)).trans (hf.2.2 s)

theorem aggregateSupplyFlow_mem_region {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) : aggregateSupplyFlow f ∈ supplyRegion N capacity := by
  refine ⟨fun i => Finset.sum_nonneg (fun s _ => hf.1 s i), ?_⟩
  intro A
  unfold aggregateSupplyFlow supplyCoverage
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  by_cases hA : (N s ∩ A).Nonempty
  · rw [if_pos hA]
    apply le_trans _ (hf.2.2 s)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hf.1 s i)
  · rw [if_neg hA]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    exact hf.2.1 s i (fun hiN => hA ⟨i, Finset.mem_inter.mpr ⟨hiN, hi⟩⟩)

noncomputable def flowAssignmentProbability (capacity : σ → ℝ) (f : σ → ι → ℝ)
    (s : σ) (i : ι) : ℝ := f s i / capacity s

theorem flowAssignmentProbability_nonneg {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (i : ι) :
    0 ≤ flowAssignmentProbability capacity f s i :=
  div_nonneg (hf.1 s i) (feasibleSupplyFlow_capacity_nonneg hf s)

theorem flowAssignmentProbability_supported {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (i : ι) (hi : i ∉ N s) :
    flowAssignmentProbability capacity f s i = 0 := by
  simp only [flowAssignmentProbability, hf.2.1 s i hi, zero_div]

theorem flowAssignmentProbability_sum_le_one {N : σ → Finset ι} {capacity : σ → ℝ}
    {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f) (s : σ) :
    (∑ i, flowAssignmentProbability capacity f s i) ≤ 1 := by
  by_cases hc : capacity s = 0
  · simp [flowAssignmentProbability, hc]
  · have hp : 0 < capacity s := lt_of_le_of_ne (feasibleSupplyFlow_capacity_nonneg hf s) (Ne.symm hc)
    unfold flowAssignmentProbability
    rw [← Finset.sum_div]
    exact (div_le_one hp).mpr (hf.2.2 s)

theorem capacity_mul_assignmentProbability {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (i : ι) :
    capacity s * flowAssignmentProbability capacity f s i = f s i := by
  by_cases hc : capacity s = 0
  · have hz : f s i = 0 := le_antisymm (by simpa only [hc] using feasibleSupplyFlow_coordinate_le hf s i)
      (hf.1 s i)
    simp only [hc, hz, zero_mul]
  · unfold flowAssignmentProbability
    field_simp

theorem assignment_probabilities_recover_rates {N : σ → Finset ι} {capacity : σ → ℝ}
    {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f) (i : ι) :
    (∑ s, capacity s * flowAssignmentProbability capacity f s i) = aggregateSupplyFlow f i := by
  exact Finset.sum_congr rfl (fun s _ => capacity_mul_assignmentProbability hf s i)

end StochasticMatching
