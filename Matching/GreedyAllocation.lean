import Matching.GreedyGrowth
import Matching.OfflineDeficiency

/-! A continuous exact offline optimizer for coverage regions, constructed by
one finite greedy pass. This supplies measurable optimizer selection directly,
including boundary demands and zero capacities.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

noncomputable def greedyPass (N : σ → Finset ι) (capacity : σ → ℝ)
    (L : List ι) (z x : ι → ℝ) : ι → ℝ :=
  match L with
  | [] => x
  | i :: rest => greedyPass N capacity rest z (greedyGrow N capacity z x i)

theorem greedyPass_properties (N : σ → Finset ι) (capacity : σ → ℝ)
    (L : List ι) (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity)
    (hxz : x ≤ fun i => max (z i) 0) :
    greedyPass N capacity L z x ∈ supplyRegion N capacity ∧
    greedyPass N capacity L z x ≤ (fun i => max (z i) 0) ∧
    x ≤ greedyPass N capacity L z x ∧
    ∀ i ∈ L, CoordinateSettled N capacity z (greedyPass N capacity L z x) i := by
  induction L generalizing x with
  | nil => exact ⟨hx, hxz, le_refl _, by simp⟩
  | cons i L ih =>
    obtain ⟨hfeas, hcap, hge, hsettled⟩ := ih (greedyGrow N capacity z x i)
      (greedyGrow_feasible N capacity z x hx hxz i) (greedyGrow_cap N capacity z x hxz i)
    refine ⟨hfeas, hcap, (greedyGrow_ge N capacity z x hx hxz i).trans hge, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact coordinateSettled_mono N capacity z _ _ hge hfeas hcap i
        (greedyGrow_settled N capacity z x i)
    · exact hsettled j hj

theorem continuous_greedyPass (N : σ → Finset ι) (capacity : σ → ℝ) (L : List ι) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => greedyPass N capacity L p.1 p.2) := by
  induction L with
  | nil => exact continuous_snd
  | cons i L ih =>
    exact ih.comp (continuous_fst.prodMk (continuous_greedyGrow N capacity i))

noncomputable def greedyAllocation (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) : ι → ℝ :=
  greedyPass N capacity Finset.univ.toList z 0

theorem continuous_greedyAllocation (N : σ → Finset ι) (capacity : σ → ℝ) :
    Continuous (greedyAllocation N capacity) :=
  (continuous_greedyPass N capacity _).comp (continuous_id.prodMk continuous_const)

theorem measurable_greedyAllocation (N : σ → Finset ι) (capacity : σ → ℝ) :
    Measurable (greedyAllocation N capacity) := (continuous_greedyAllocation N capacity).measurable

theorem greedyAllocation_properties (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z : ι → ℝ) :
    greedyAllocation N capacity z ∈ supplyRegion N capacity ∧
    greedyAllocation N capacity z ≤ (fun i => max (z i) 0) ∧
    ∀ i, CoordinateSettled N capacity z (greedyAllocation N capacity z) i := by
  obtain ⟨hf, hc, _, hs⟩ := greedyPass_properties N capacity Finset.univ.toList z 0
    (zero_mem_supplyRegion N capacity hcapacity) (fun i => le_max_right (z i) 0)
  exact ⟨hf, hc, fun i => hs i (by simp)⟩

theorem settled_tight_certificate (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z x : ι → ℝ)
    (hx : x ∈ supplyRegion N capacity) (hs : ∀ i, CoordinateSettled N capacity z x i) :
    ∃ A : Finset ι, (∑ i ∈ A, x i) = supplyCoverage N capacity A ∧
      ∀ i, i ∉ A → x i = max (z i) 0 := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter
    (fun A => (∑ i ∈ A, x i) = supplyCoverage N capacity A)
  refine ⟨F.biUnion id, tight_set_biUnion N capacity hcapacity hx F
    (fun A hA => (Finset.mem_filter.mp hA).2), ?_⟩
  intro i hi
  rcases hs i with hcap | ⟨A, hiA, hA⟩
  · exact hcap
  · exact False.elim (hi (Finset.mem_biUnion.mpr
      ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩, hiA⟩))

theorem settled_allocation_maximal (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z x : ι → ℝ)
    (hx : x ∈ supplyRegion N capacity) (hs : ∀ i, CoordinateSettled N capacity z x i)
    (y : ι → ℝ) (hy : y ∈ offlineFeasible (supplyRegion N capacity) z) :
    (∑ i, y i) ≤ ∑ i, x i := by
  obtain ⟨A, hA, hAc⟩ := settled_tight_certificate N capacity hcapacity z x hx hs
  have hcomp : (∑ i ∈ Aᶜ, y i) ≤ ∑ i ∈ Aᶜ, x i := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hAc i (Finset.mem_compl.mp hi)]
    exact hy.2 i
  have hyA := hy.1.2 A
  have hsx := Finset.sum_add_sum_compl A x
  have hsy := Finset.sum_add_sum_compl A y
  linarith

theorem greedyAllocation_optimal (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z : ι → ℝ) :
    (∑ i, greedyAllocation N capacity z i) = offlineValue (supplyRegion N capacity) z := by
  obtain ⟨hf, hc, hs⟩ := greedyAllocation_properties N capacity hcapacity z
  apply le_antisymm
  · exact offline_allocation_le_value (supplyRegion_compact N capacity)
      (zero_mem_supplyRegion N capacity hcapacity) z ⟨hf, hc⟩
  · obtain ⟨y, hy, hv, _⟩ := exists_offline_optimizer (supplyRegion_compact N capacity)
      (zero_mem_supplyRegion N capacity hcapacity) z
    rw [hv]
    exact settled_allocation_maximal N capacity hcapacity z _ hf hs y hy

theorem greedyAllocation_cap_nonnegative (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (i : ι) :
    greedyAllocation N capacity z i ≤ z i := by
  simpa only [max_eq_left (hz i)] using (greedyAllocation_properties N capacity hcapacity z).2.1 i

theorem exists_continuous_offline_optimizer (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) :
    ∃ Y : (ι → ℝ) → (ι → ℝ), Continuous Y ∧
      (∀ z, Y z ∈ offlineFeasible (supplyRegion N capacity) z) ∧
      ∀ z, (∑ i, Y z i) = offlineValue (supplyRegion N capacity) z := by
  refine ⟨greedyAllocation N capacity, continuous_greedyAllocation N capacity, ?_,
    greedyAllocation_optimal N capacity hcapacity⟩
  intro z
  exact ⟨(greedyAllocation_properties N capacity hcapacity z).1,
    (greedyAllocation_properties N capacity hcapacity z).2.1⟩

end StochasticMatching
