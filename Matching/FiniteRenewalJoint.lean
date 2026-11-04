import Matching.FiniteRenewalPoisson
import Matching.VectorRenewalTotal

/-! A joint law for the count at one observation time and the final arrival
at a later time, on the original finite exponential path.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {n : ℕ}

theorem finiteRenewalCount_lt_iff_total {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) (t : ℝ) (ht0 : 0 ≤ t) :
    finiteRenewalCount z t < n ↔ t < ∑ i, z i := by
  constructor
  · intro hc
    have he : ∃ i : Fin n, t < arrivalTime z i := by
      by_contra h
      push_neg at h
      have hfilter : Finset.univ.filter (fun i => arrivalTime z i ≤ t) = Finset.univ := by
        ext i; simp [h i]
      simp only [finiteRenewalCount, hfilter, Finset.card_univ, Fintype.card_fin] at hc
      omega
    obtain ⟨i, hi⟩ := he
    apply hi.trans_le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hz i)
  · intro ht
    by_cases hn : n = 0
    · subst n
      have hsum : (∑ i : Fin 0, z i) = 0 := by simp
      rw [hsum] at ht
      exact False.elim ((not_lt_of_ge ht0) ht)
    · let j : Fin n := ⟨n - 1, by omega⟩
      have htop : Finset.Iic j = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        apply Finset.mem_Iic.mpr
        change i.val ≤ n - 1
        omega
      have hj : t < arrivalTime z j := by simpa only [arrivalTime, htop] using ht
      have h := (finiteRenewalCount_le_iff hz t j).mpr hj
      change finiteRenewalCount z t ≤ n - 1 at h
      omega

theorem finiteRenewalCount_eq_iff_cut {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin n) :
    finiteRenewalCount z t = j.val ↔ beforeArrival z j ≤ t ∧ t < arrivalTime z j := by
  constructor
  · intro hc
    have hlt : finiteRenewalCount z t < n := by rw [hc]; exact j.isLt
    obtain ⟨i, hi⟩ := exists_ordered_renewal_cut ht ((finiteRenewalCount_lt_iff_total hz t ht).mp hlt)
    have hcount := finiteRenewalCount_at_cut hz hi
    simp only [Fin.card_Iio] at hcount
    have hij : i = j := Fin.ext (hcount.symm.trans hc)
    simpa only [hij] using hi
  · intro hj
    simpa only [Fin.card_Iio] using finiteRenewalCount_at_cut hz hj

theorem finite_count_cut_later_tail (j : Fin n) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    (independentExponentials (ι := Fin n)).real
      {z | finiteRenewalCount z t = j.val ∧ u < ∑ i, z i} =
      poissonWeight t j.val * poissonLowerTail (u - t) (n - j.val) := by
  let A : Finset (Fin n) := Finset.Iio j
  let j' : ↥(Aᶜ) := ⟨j, by simp [A]⟩
  have he : ({z : Fin n → ℝ | finiteRenewalCount z t = j.val ∧ u < ∑ i, z i} : Set (Fin n → ℝ)) =ᵐ[independentExponentials]
      {z | z ∈ vectorRenewalCut A j' t ∧ u < ∑ i, z i} := by
    filter_upwards [independentExponentials_ae_pos (ι := Fin n)] with z hz
    apply propext
    have hc := finiteRenewalCount_eq_iff_cut (fun i => (hz i).le) ht j
    rw [arrivalTime_eq_before_add] at hc
    exact and_congr_left (fun _ => hc)
  rw [measureReal_congr he, vector_renewal_cut_later_tail_by_card A j' ht htu]
  simp only [A, Fin.card_Iio, Fintype.card_fin]

theorem finite_count_two_time_atom_tail (j : Fin n) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    (independentExponentials (ι := Fin n)).real
      {z | finiteRenewalCount z t = j.val ∧ finiteRenewalCount z u < n} =
      poissonWeight t j.val * poissonLowerTail (u - t) (n - j.val) := by
  have he : ({z : Fin n → ℝ | finiteRenewalCount z t = j.val ∧ finiteRenewalCount z u < n} : Set (Fin n → ℝ)) =ᵐ[independentExponentials]
      {z | finiteRenewalCount z t = j.val ∧ u < ∑ i, z i} := by
    filter_upwards [independentExponentials_ae_pos (ι := Fin n)] with z hz
    apply propext
    exact and_congr_right (fun _ => finiteRenewalCount_lt_iff_total (fun i => (hz i).le) u (ht.trans htu))
  rw [measureReal_congr he]
  exact finite_count_cut_later_tail j ht htu

end StochasticMatching
