import Matching.BlockRenewalRestart
import Matching.OrderedRenewalCuts
import Mathlib.Data.Fintype.EquivFin

/-! Partition a subset waiting-time event by the unique renewal cut inside
an enumeration of that subset. No ordering assumption on the original jobs
or on later supersets is needed.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def subsetEnumeration (A : Finset ι) : Fin A.card ≃ A :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm

noncomputable def subsetEmbedding (A : Finset ι) : Fin A.card ↪ ι :=
  (subsetEnumeration A).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

noncomputable def subsetBefore (A : Finset ι) (j : Fin A.card) : Finset ι :=
  (Finset.Iio j).map (subsetEmbedding A)

theorem subsetBefore_card (A : Finset ι) (j : Fin A.card) :
    (subsetBefore A j).card = j.val := by
  simp only [subsetBefore, Finset.card_map, Fin.card_Iio]

theorem subsetBefore_subset (A : Finset ι) (j : Fin A.card) : subsetBefore A j ⊆ A := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
  exact (subsetEnumeration A k).2

theorem subsetEmbedding_not_mem_before (A : Finset ι) (j : Fin A.card) :
    subsetEmbedding A j ∉ subsetBefore A j := by
  intro h
  obtain ⟨k, hk, hkj⟩ := Finset.mem_map.mp h
  have he := (subsetEmbedding A).injective hkj
  subst k
  exact (lt_irrefl j) (Finset.mem_Iio.mp hk)

noncomputable def subsetNext (A : Finset ι) (j : Fin A.card) : ↥((subsetBefore A j)ᶜ) :=
  ⟨subsetEmbedding A j, Finset.mem_compl.mpr (subsetEmbedding_not_mem_before A j)⟩

theorem subsetBefore_sum (A : Finset ι) (j : Fin A.card) (z : ι → ℝ) :
    (∑ i ∈ subsetBefore A j, z i) = beforeArrival (fun k => z (subsetEmbedding A k)) j := by
  simp only [subsetBefore, Finset.sum_map, beforeArrival]

theorem subsetEnumeration_sum (A : Finset ι) (z : ι → ℝ) :
    (∑ j, z (subsetEmbedding A j)) = ∑ i ∈ A, z i := by
  have h := (subsetEnumeration A).sum_comp (fun i : A => z i)
  simpa only [Finset.sum_coe_sort] using h

theorem subset_renewal_cut_iff (A : Finset ι) (j : Fin A.card) (z : ι → ℝ) (t : ℝ) :
    z ∈ vectorRenewalCut (subsetBefore A j) (subsetNext A j) t ↔
      beforeArrival (fun k => z (subsetEmbedding A k)) j ≤ t ∧
      t < arrivalTime (fun k => z (subsetEmbedding A k)) j := by
  rw [arrivalTime_eq_before_add]
  simp only [vectorRenewalCut, mem_setOf_eq, subsetBefore_sum, subsetNext]

theorem subset_renewal_cut_unique (A : Finset ι) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    {t : ℝ} {j k : Fin A.card}
    (hj : z ∈ vectorRenewalCut (subsetBefore A j) (subsetNext A j) t)
    (hk : z ∈ vectorRenewalCut (subsetBefore A k) (subsetNext A k) t) : j = k := by
  exact ordered_renewal_cut_unique (fun i => hz _) ((subset_renewal_cut_iff A j z t).mp hj)
    ((subset_renewal_cut_iff A k z t).mp hk)

theorem subset_renewal_cut_exists_iff (A : Finset ι) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    {t : ℝ} (ht : 0 ≤ t) :
    t < ∑ i ∈ A, z i ↔
      ∃ j : Fin A.card, z ∈ vectorRenewalCut (subsetBefore A j) (subsetNext A j) t := by
  rw [← subsetEnumeration_sum A z]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_ordered_renewal_cut ht h
    exact ⟨j, (subset_renewal_cut_iff A j z t).mpr hj⟩
  · rintro ⟨j, hj⟩
    apply ((subset_renewal_cut_iff A j z t).mp hj).2.trans_le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hz _)

end StochasticMatching
