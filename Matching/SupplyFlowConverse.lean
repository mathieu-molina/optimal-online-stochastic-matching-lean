import Matching.SupplyFlowVariations

/-! Every vector in the coverage region has a feasible supply-flow
representation. A supporting projection flow cannot leave positive residual
demand: its positive-residual vertices would form a violated coverage cut.
Column scaling then recovers the requested rates exactly.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

theorem supporting_flow_dominates {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (hf : FeasibleSupplyFlow N capacity f) (hs : FlowSupports N capacity x f) :
    x ≤ aggregateSupplyFlow f := by
  classical
  let A : Finset ι := Finset.univ.filter (fun i => 0 < x i - aggregateSupplyFlow f i)
  have hpos : ∀ i ∈ A, 0 < x i - aggregateSupplyFlow f i :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hnonpos : ∀ i, i ∉ A → x i - aggregateSupplyFlow f i ≤ 0 := by
    intro i hi
    apply le_of_not_gt
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hrow : ∀ s, (∑ i ∈ A, f s i) = if (N s ∩ A).Nonempty then capacity s else 0 := by
    intro s
    by_cases ht : (N s ∩ A).Nonempty
    · rw [if_pos ht]
      obtain ⟨i, hi⟩ := ht
      obtain ⟨hiN, hiA⟩ := Finset.mem_inter.mp hi
      have he : (∑ j ∈ A, f s j) = ∑ j, f s j := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro j _ hj
        exact supporting_row_zero_nonpositive hf hs s i j hiN (hpos i hiA) (hnonpos j hj)
      rw [he, supporting_row_full hf hs s i hiN (hpos i hiA)]
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro i hi
      exact hf.2.1 s i (fun hiN => ht ⟨i, Finset.mem_inter.mpr ⟨hiN, hi⟩⟩)
  have hcut : (∑ i ∈ A, aggregateSupplyFlow f i) = supplyCoverage N capacity A := by
    unfold aggregateSupplyFlow supplyCoverage
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => hrow s)
  have hA : A = ∅ := by
    by_contra hne
    have hlt : (∑ i ∈ A, aggregateSupplyFlow f i) < ∑ i ∈ A, x i :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
        (fun i hi => sub_pos.mp (hpos i hi))
    rw [hcut] at hlt
    exact (not_lt_of_ge (hx.2 A)) hlt
  intro i
  have h := hnonpos i (by rw [hA]; exact Finset.not_mem_empty _)
  linarith

theorem scale_flow_to_dominated_rates {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f)
    (hx : ∀ i, 0 ≤ x i) (hle : x ≤ aggregateSupplyFlow f) :
    ∃ g, FeasibleSupplyFlow N capacity g ∧ aggregateSupplyFlow g = x := by
  let q : ι → ℝ := fun i => x i / aggregateSupplyFlow f i
  have hw : ∀ i, 0 ≤ aggregateSupplyFlow f i := fun i => Finset.sum_nonneg (fun s _ => hf.1 s i)
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (hx i) (hw i)
  have hq1 : ∀ i, q i ≤ 1 := by
    intro i
    by_cases hi : aggregateSupplyFlow f i = 0
    · simp only [q, hi, div_zero, zero_le_one]
    · exact (div_le_one (lt_of_le_of_ne (hw i) (Ne.symm hi))).mpr (hle i)
  let g : σ → ι → ℝ := fun s i => f s i * q i
  have hg : FeasibleSupplyFlow N capacity g := by
    refine ⟨fun s i => mul_nonneg (hf.1 s i) (hq0 i), ?_, ?_⟩
    · intro s i hi
      dsimp only [g]
      rw [hf.2.1 s i hi, zero_mul]
    · intro s
      apply le_trans _ (hf.2.2 s)
      exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hf.1 s i) (hq1 i))
  refine ⟨g, hg, ?_⟩
  funext i
  change (∑ s, f s i * q i) = x i
  rw [← Finset.sum_mul]
  change aggregateSupplyFlow f i * (x i / aggregateSupplyFlow f i) = x i
  by_cases hi : aggregateSupplyFlow f i = 0
  · have hxi : x i = 0 := le_antisymm (by simpa only [hi] using hle i) (hx i)
    simp only [hi, hxi, zero_mul]
  · field_simp

theorem exists_supply_flow_of_mem_region (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) :
    ∃ f, FeasibleSupplyFlow N capacity f ∧ aggregateSupplyFlow f = x := by
  obtain ⟨f, hf, hs⟩ := exists_supporting_supply_flow N capacity hcapacity x
  exact scale_flow_to_dominated_rates hf hx.1 (supporting_flow_dominates hx hf hs)

theorem mem_supplyRegion_iff_flow (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (x : ι → ℝ) :
    x ∈ supplyRegion N capacity ↔
      ∃ f, FeasibleSupplyFlow N capacity f ∧ aggregateSupplyFlow f = x := by
  constructor
  · exact exists_supply_flow_of_mem_region N capacity hcapacity
  · rintro ⟨f, hf, rfl⟩
    exact aggregateSupplyFlow_mem_region hf

end StochasticMatching
