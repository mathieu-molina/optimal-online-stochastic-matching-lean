import Matching.NestedExponentialSums

/-! Finite renewal paths and the unique active waiting interval at a fixed
time. These deterministic partition lemmas support induction over several
observation times without assuming a Poisson-process library.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]

noncomputable def beforeArrival (z : ι → ℝ) (j : ι) : ℝ := ∑ i ∈ Finset.Iio j, z i
noncomputable def arrivalTime (z : ι → ℝ) (j : ι) : ℝ := ∑ i ∈ Finset.Iic j, z i

theorem arrivalTime_eq_before_add (z : ι → ℝ) (j : ι) : arrivalTime z j = beforeArrival z j + z j := by
  simp only [arrivalTime, beforeArrival, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  exact add_comm _ _

theorem arrivalTime_le_beforeArrival {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) {i j : ι} (hij : i < j) :
    arrivalTime z i ≤ beforeArrival z j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hk).trans_lt hij)
  · intro k _ _; exact hz k

theorem arrivalTime_mono {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) : Monotone (arrivalTime z) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans hij)
  · intro k _ _; exact hz k

theorem ordered_renewal_cut_unique {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) {t : ℝ} {i j : ι}
    (hi : beforeArrival z i ≤ t ∧ t < arrivalTime z i)
    (hj : beforeArrival z j ≤ t ∧ t < arrivalTime z j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have h := arrivalTime_le_beforeArrival hz hij
    linarith [hi.2, hj.1]
  · exact hij
  · have h := arrivalTime_le_beforeArrival hz hij
    linarith [hj.2, hi.1]

theorem exists_ordered_renewal_cut {z : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (htotal : t < ∑ i, z i) : ∃ j, beforeArrival z j ≤ t ∧ t < arrivalTime z j := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at htotal
    linarith
  let last := (Finset.univ : Finset ι).max' hne
  have hlast : Finset.Iic last = (Finset.univ : Finset ι) := by
    apply Finset.eq_univ_of_forall
    intro k
    exact Finset.mem_Iic.mpr (Finset.le_max' _ k (Finset.mem_univ k))
  let S := Finset.univ.filter (fun j => t < arrivalTime z j)
  have hS : S.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [arrivalTime, hlast] using htotal
  let j := S.min' hS
  have hj : t < arrivalTime z j := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨j, ?_, hj⟩
  by_cases hp : (Finset.Iio j).Nonempty
  · let p := (Finset.Iio j).max' hp
    have hpj : p < j := Finset.mem_Iio.mp (Finset.max'_mem _ hp)
    have he : Finset.Iic p = Finset.Iio j := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_Iio]
      constructor
      · intro h; exact h.trans_lt hpj
      · intro h; exact Finset.le_max' _ k (Finset.mem_Iio.mpr h)
    have hpt : arrivalTime z p ≤ t := by
      by_contra h
      have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
      have hjp : j ≤ p := Finset.min'_le S p hpS
      exact (not_lt_of_ge hjp) hpj
    simpa only [arrivalTime, beforeArrival, he] using hpt
  · rw [beforeArrival, Finset.not_nonempty_iff_eq_empty.mp hp, Finset.sum_empty]
    exact ht

theorem exists_unique_ordered_renewal_cut {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) {t : ℝ}
    (ht : 0 ≤ t) (htotal : t < ∑ i, z i) :
    ∃! j, beforeArrival z j ≤ t ∧ t < arrivalTime z j := by
  obtain ⟨j, hj⟩ := exists_ordered_renewal_cut ht htotal
  exact ⟨j, hj, fun i hi => ordered_renewal_cut_unique hz hi hj⟩

noncomputable def finiteRenewalCount (z : ι → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => arrivalTime z i ≤ t)).card

theorem finiteRenewalCount_at_cut {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) {t : ℝ} {j : ι}
    (hj : beforeArrival z j ≤ t ∧ t < arrivalTime z j) :
    finiteRenewalCount z t = (Finset.Iio j).card := by
  have he : Finset.univ.filter (fun i => arrivalTime z i ≤ t) = Finset.Iio j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · intro hi
      by_contra hij
      have h := arrivalTime_mono hz (le_of_not_gt hij)
      linarith [hj.2]
    · intro hij
      exact (arrivalTime_le_beforeArrival hz hij).trans hj.1
  exact congrArg Finset.card he

theorem measurable_beforeArrival (j : ι) : Measurable (fun z : ι → ℝ => beforeArrival z j) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem measurable_arrivalTime (j : ι) : Measurable (fun z : ι → ℝ => arrivalTime z j) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

end StochasticMatching
