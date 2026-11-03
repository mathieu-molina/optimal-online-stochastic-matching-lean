import Matching.IndependentBlocks
import Matching.ArrivalInstance
import Mathlib.Order.Disjointed

/-! The joint count law on nested subsets, expressed as cumulative sums of
independent Poisson increments. This is the count-side input to chain duality.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype κ] [LinearOrder κ] [LocallyFiniteOrderBot κ]

theorem nested_disjoint_blocks_union (F : κ → Finset σ) (hF : Monotone F) (j : κ) :
    (Finset.Iic j).biUnion (disjointed F) = F j := by
  have h := congrArg (fun g : κ →o Finset σ => g j) (partialSups_disjointed F)
  change partialSups (disjointed F) j = partialSups F j at h
  rw [hF.partialSups_eq] at h
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_eq_biUnion] using h

theorem nested_sum_eq_block_sums {M : Type*} [AddCommMonoid M]
    (F : κ → Finset σ) (hF : Monotone F) (w : σ → M) (j : κ) :
    (∑ s ∈ F j, w s) = ∑ k ∈ Finset.Iic j, ∑ s ∈ disjointed F k, w s := by
  rw [← nested_disjoint_blocks_union F hF j]
  apply Finset.sum_biUnion
  intro k hk l hl hkl
  exact disjoint_disjointed F hkl

theorem nested_poisson_counts_law (a : σ → ℝ≥0) (F : κ → Finset σ) (hF : Monotone F) :
    Measure.map (fun n : σ → ℕ => fun j => ∑ s ∈ F j, n s) (independentPoissons a) =
      Measure.map (fun increments : κ → ℕ => fun j => ∑ k ∈ Finset.Iic j, increments k)
        (independentPoissons (fun k => ∑ s ∈ disjointed F k, a s)) := by
  have hlaw := independentPoissons_block_sum_law a (disjointed F) (disjoint_disjointed F)
  rw [← hlaw, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext n j
  exact nested_sum_eq_block_sums F hF n j

variable {ι : Type*} [DecidableEq ι]

noncomputable def touchingTypes (N : σ → Finset ι) (A : Finset ι) : Finset σ :=
  Finset.univ.filter (fun s => (N s ∩ A).Nonempty)

theorem touchingTypes_mono (N : σ → Finset ι) : Monotone (touchingTypes N) := by
  intro A B hAB s hs
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i,
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hAB (Finset.mem_inter.mp hi).2⟩⟩⟩

theorem arrivalCoverageCount_eq_touching_sum [DecidableEq σ]
    (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) :
    arrivalCoverageCount N counts A = ∑ s ∈ touchingTypes N A, counts s := by
  classical
  simp only [touchingTypes, Finset.sum_filter, arrivalCoverageCount]

theorem supplyCoverage_eq_touching_sum [Fintype ι]
    (N : σ → Finset ι) (capacity : σ → ℝ) (A : Finset ι) :
    supplyCoverage N capacity A = ∑ s ∈ touchingTypes N A, capacity s := by
  classical
  simp only [touchingTypes, Finset.sum_filter, supplyCoverage]

theorem nested_arrival_counts_law [Fintype ι]
    (N : σ → Finset ι) (a : σ → ℝ≥0) (A : κ → Finset ι) (hA : Monotone A) :
    Measure.map (fun counts : σ → ℕ => fun j => arrivalCoverageCount N counts (A j))
      (independentPoissons a) =
      Measure.map (fun increments : κ → ℕ => fun j => ∑ k ∈ Finset.Iic j, increments k)
        (independentPoissons (fun k => ∑ s ∈ disjointed (fun j => touchingTypes N (A j)) k, a s)) := by
  simp_rw [arrivalCoverageCount_eq_touching_sum]
  exact nested_poisson_counts_law a (fun j => touchingTypes N (A j)) ((touchingTypes_mono N).comp hA)

end StochasticMatching
