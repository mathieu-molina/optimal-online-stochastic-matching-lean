import Matching.OfflineTightSets
import Matching.SupermodularTail

/-! The exact offline scheduling deficiency formula for coverage regions.
The tight-set certificate proves strong duality directly, without taking
linear-programming duality or flow decomposition as an assumption.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

noncomputable def maxSupplyDeficiency (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (supplyDeficiency N capacity z)

theorem supplyDeficiency_le_max (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) (A : Finset ι) :
    supplyDeficiency N capacity z A ≤ maxSupplyDeficiency N capacity z :=
  Finset.le_sup' _ (Finset.mem_univ A)

theorem maxSupplyDeficiency_nonneg (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) :
    0 ≤ maxSupplyDeficiency N capacity z := by
  simpa only [supplyDeficiency_empty] using supplyDeficiency_le_max N capacity z ∅

theorem feasible_work_add_deficiency_le (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ z) (A : Finset ι) :
    (∑ i, x i) + supplyDeficiency N capacity z A ≤ ∑ i, z i := by
  have hsx := Finset.sum_add_sum_compl A x
  have hsz := Finset.sum_add_sum_compl A z
  have hA := hx.2 A
  have hc : (∑ i ∈ Aᶜ, x i) ≤ ∑ i ∈ Aᶜ, z i := Finset.sum_le_sum (fun i _ => hxz i)
  unfold supplyDeficiency
  linarith

theorem feasible_work_add_max_deficiency_le (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ z) :
    (∑ i, x i) + maxSupplyDeficiency N capacity z ≤ ∑ i, z i := by
  have h : maxSupplyDeficiency N capacity z ≤ (∑ i, z i) - ∑ i, x i := by
    apply Finset.sup'_le
    intro A _
    have ha := feasible_work_add_deficiency_le N capacity z x hx hxz A
    linarith
  linarith

theorem offlineValue_eq_total_sub_deficiency (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    offlineValue (supplyRegion N capacity) z = (∑ i, z i) - maxSupplyDeficiency N capacity z := by
  obtain ⟨x, hx, hv, hm⟩ := exists_offline_optimizer (supplyRegion_compact N capacity)
    (zero_mem_supplyRegion N capacity hcapacity) z
  rw [offlineFeasible_nonnegative_demand _ z hz] at hx
  have hm' : ∀ y ∈ supplyRegion N capacity, y ≤ z → (∑ i, y i) ≤ ∑ i, x i := by
    intro y hy hyz
    apply hm y
    rw [offlineFeasible_nonnegative_demand _ z hz]
    exact ⟨hy, hyz⟩
  obtain ⟨A, hA, hAc⟩ := optimizer_tight_certificate N capacity hcapacity z x hx.1 hx.2 hm'
  have hc : (∑ i ∈ Aᶜ, x i) = ∑ i ∈ Aᶜ, z i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hAc i (Finset.mem_compl.mp hi)
  have hsx := Finset.sum_add_sum_compl A x
  have hsz := Finset.sum_add_sum_compl A z
  have hdef := supplyDeficiency_le_max N capacity z A
  have hupper := feasible_work_add_max_deficiency_le N capacity z x hx.1 hx.2
  unfold supplyDeficiency at hdef
  rw [hv]
  linarith

theorem continuous_maxSupplyDeficiency (N : σ → Finset ι) (capacity : σ → ℝ) :
    Continuous (maxSupplyDeficiency N capacity) := by
  apply Continuous.finset_sup'_apply
  intro A _
  exact (continuous_finset_sum A (fun i _ => continuous_apply i)).sub continuous_const

theorem measurable_maxSupplyDeficiency (N : σ → Finset ι) (capacity : σ → ℝ) :
    Measurable (maxSupplyDeficiency N capacity) := (continuous_maxSupplyDeficiency N capacity).measurable

theorem maxSupplyDeficiency_gt_iff (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) (a : ℝ) :
    a < maxSupplyDeficiency N capacity z ↔ ∃ A, a < supplyDeficiency N capacity z A := by
  classical
  constructor
  · intro h
    obtain ⟨A, _, he⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Finset ι)).Nonempty) (supplyDeficiency N capacity z)
    exact ⟨A, by simpa only [maxSupplyDeficiency, he] using h⟩
  · rintro ⟨A, hA⟩
    exact hA.trans_le (supplyDeficiency_le_max N capacity z A)

theorem supply_max_tail_chain_formula (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (N : σ → Finset ι) (capacity : σ → ℝ) (hcapacity : ∀ s, 0 ≤ capacity s) (a : ℝ) :
    μ.real {z | a < maxSupplyDeficiency N capacity z} =
      ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        (-chainWeight C) * μ.real (chainExceedance (supplyDeficiency N capacity) a C) := by
  have he : {z | a < maxSupplyDeficiency N capacity z} = maximumExceedance (supplyDeficiency N capacity) a := by
    ext z
    exact maxSupplyDeficiency_gt_iff N capacity z a
  rw [he]
  apply supermodular_max_tail_chain_formula
  · intro A
    exact ((continuous_finset_sum A (fun i _ => continuous_apply i)).sub continuous_const).measurable
  · exact Filter.Eventually.of_forall (fun z A B => supplyDeficiency_supermodular N capacity hcapacity z A B)

end StochasticMatching
