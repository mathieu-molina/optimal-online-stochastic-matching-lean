import Matching.FlowEdgeRestore

/-! An explicit continuous supply-flow selector. Enumerate all type/job edges,
fix the least required amount on the first edge, remove it, and recurse. The
finite construction is continuous jointly in supplies and requested rates.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

noncomputable def decomposeEdges (L : List (σ × ι)) (N : σ → Finset ι)
    (capacity : σ → ℝ) (x : ι → ℝ) : σ → ι → ℝ :=
  match L with
  | [] => 0
  | (s, i) :: rest =>
    if i ∈ N s then
      let a := edgeAmount N capacity x s i
      insertFlowEntry
        (decomposeEdges rest (removeSupplyEdge N s i) (reduceSupply capacity s a) (reduceDemand x i a)) s i a
    else decomposeEdges rest N capacity x

theorem remaining_edge_covered (N : σ → Finset ι) (L : List (σ × ι)) (s : σ) (i : ι)
    (hcover : ∀ t j, j ∈ N t → (t, j) ∈ (s, i) :: L) :
    ∀ t j, j ∈ removeSupplyEdge N s i t → (t, j) ∈ L := by
  intro t j hj
  have hjN : j ∈ N t := by
    by_cases ht : t = s
    · subst t
      simp only [removeSupplyEdge, Function.update_self] at hj
      exact Finset.mem_of_mem_erase hj
    · simpa only [removeSupplyEdge, Function.update_of_ne ht] using hj
  rcases List.mem_cons.mp (hcover t j hjN) with he | hL
  · obtain ⟨ht, hji⟩ := Prod.mk.inj_iff.mp he
    subst t
    subst j
    simp [removeSupplyEdge] at hj
  · exact hL

theorem skipped_edge_covered (N : σ → Finset ι) (L : List (σ × ι)) (s : σ) (i : ι)
    (hi : i ∉ N s) (hcover : ∀ t j, j ∈ N t → (t, j) ∈ (s, i) :: L) :
    ∀ t j, j ∈ N t → (t, j) ∈ L := by
  intro t j hj
  rcases List.mem_cons.mp (hcover t j hj) with he | hL
  · obtain ⟨ht, hji⟩ := Prod.mk.inj_iff.mp he
    subst t
    subst j
    exact False.elim (hi hj)
  · exact hL

theorem decomposeEdges_correct (L : List (σ × ι)) (N : σ → Finset ι)
    (capacity : σ → ℝ) (x : ι → ℝ) (hcapacity : ∀ s, 0 ≤ capacity s)
    (hx : x ∈ supplyRegion N capacity) (hcover : ∀ s i, i ∈ N s → (s, i) ∈ L) :
    FeasibleSupplyFlow N capacity (decomposeEdges L N capacity x) ∧
      aggregateSupplyFlow (decomposeEdges L N capacity x) = x := by
  induction L generalizing N capacity x with
  | nil =>
    have hN : ∀ s, N s = ∅ := by
      intro s
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      exact List.not_mem_nil (hcover s i hi)
    have hzero : x = 0 := by
      funext i
      apply le_antisymm
      · have h := hx.2 {i}
        simpa [supplyCoverage, hN] using h
      · exact hx.1 i
    refine ⟨zero_mem_supplyFlowSet N capacity hcapacity, ?_⟩
    rw [hzero]
    ext i
    simp [decomposeEdges, aggregateSupplyFlow]
  | cons p L ih =>
    rcases p with ⟨s, i⟩
    by_cases hi : i ∈ N s
    · simp only [decomposeEdges, if_pos hi]
      apply restore_supply_edge N capacity x s i hi _ (edgeAmount_nonneg N capacity x s i)
      · exact (ih (removeSupplyEdge N s i) _ _
          (edgeAmount_residual_capacity N capacity hcapacity hx s i hi)
          (edgeAmount_residual_feasible N capacity hcapacity hx s i hi)
          (remaining_edge_covered N L s i hcover)).1
      · exact (ih (removeSupplyEdge N s i) _ _
          (edgeAmount_residual_capacity N capacity hcapacity hx s i hi)
          (edgeAmount_residual_feasible N capacity hcapacity hx s i hi)
          (remaining_edge_covered N L s i hcover)).2
    · simp only [decomposeEdges, if_neg hi]
      exact ih N capacity x hcapacity hx (skipped_edge_covered N L s i hi hcover)

theorem continuous_decomposeEdges (L : List (σ × ι)) (N : σ → Finset ι) :
    Continuous (fun p : (σ → ℝ) × (ι → ℝ) => decomposeEdges L N p.1 p.2) := by
  induction L generalizing N with
  | nil => exact continuous_const
  | cons p L ih =>
    rcases p with ⟨s, i⟩
    by_cases hi : i ∈ N s
    · simp only [decomposeEdges, if_pos hi]
      have ha := continuous_edgeAmount N s i
      have hc := (continuous_reduceSupply s).comp (continuous_fst.prodMk ha)
      have hx := (continuous_reduceDemand i).comp (continuous_snd.prodMk ha)
      have hg := (ih (removeSupplyEdge N s i)).comp (hc.prodMk hx)
      exact (continuous_insertFlowEntry s i).comp (hg.prodMk ha)
    · simpa only [decomposeEdges, if_neg hi] using ih N

noncomputable def selectedSupplyFlow (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ) : σ → ι → ℝ :=
  decomposeEdges Finset.univ.toList N capacity x

theorem selectedSupplyFlow_correct (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) :
    FeasibleSupplyFlow N capacity (selectedSupplyFlow N capacity x) ∧
      aggregateSupplyFlow (selectedSupplyFlow N capacity x) = x :=
  decomposeEdges_correct _ N capacity x hcapacity hx (by intros; simp)

theorem continuous_selectedSupplyFlow (N : σ → Finset ι) :
    Continuous (fun p : (σ → ℝ) × (ι → ℝ) => selectedSupplyFlow N p.1 p.2) :=
  continuous_decomposeEdges _ N

theorem measurable_selectedSupplyFlow (N : σ → Finset ι) :
    Measurable (fun p : (σ → ℝ) × (ι → ℝ) => selectedSupplyFlow N p.1 p.2) :=
  (continuous_selectedSupplyFlow N).measurable

theorem continuous_selectedSupplyFlow_rates (N : σ → Finset ι) (capacity : σ → ℝ) :
    Continuous (selectedSupplyFlow N capacity) :=
  (continuous_selectedSupplyFlow N).comp (continuous_const.prodMk continuous_id)

end StochasticMatching
