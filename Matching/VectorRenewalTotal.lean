import Matching.VectorRenewalCut

/-! The joint renewal-count / later completion-time law on the original
exponential vector. The residual completion time has the correct Erlang law.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem remaining_waiting_count (A : Finset ι) (j : ↥(Aᶜ)) :
    Fintype.card {i : ↥(Aᶜ) // i ≠ j} + 1 = Fintype.card ι - A.card := by
  have h := Fintype.card_subtype_compl (fun i : ↥(Aᶜ) => i = j)
  simp only [Fintype.card_unique, Fintype.card_coe] at h
  have hp : 0 < (Aᶜ).card := Finset.card_pos.mpr ⟨j, j.2⟩
  rw [h]
  have hc := Finset.card_compl A
  omega

theorem sum_block_next_future (A : Finset ι) (j : ↥(Aᶜ)) (z : ι → ℝ) :
    ((∑ i ∈ A, z i) + z j) + (∑ i : {i : ↥(Aᶜ) // i ≠ j}, z i.1) = ∑ i, z i := by
  have h := Finset.sum_add_sum_compl A z
  have hc : (∑ i ∈ Aᶜ, z i) = z j + ∑ i : {i : ↥(Aᶜ) // i ≠ j}, z i.1 := by
    rw [← Finset.sum_coe_sort, Fintype.sum_eq_add_sum_subtype_ne _ j]
  rw [hc] at h
  linarith

theorem unitExponential_product_total_law {H : Type*} [Fintype H] :
    Measure.map (fun p : ℝ × (H → ℝ) => p.1 + ∑ i, p.2 i)
      (unitExponential.prod independentExponentials) = exponentialSumLaw (Fintype.card H + 1) := by
  have hs : Measurable (fun z : H → ℝ => ∑ i, z i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hp := Measure.map_prod_map unitExponential (independentExponentials (ι := H)) measurable_id hs
  rw [Measure.map_id, independentExponentials_subset_sum_law, Finset.card_univ] at hp
  have he : (fun p : ℝ × (H → ℝ) => p.1 + ∑ i, p.2 i) =
      (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map id (fun z : H → ℝ => ∑ i, z i) := rfl
  rw [he, ← Measure.map_map (measurable_fst.add measurable_snd) (measurable_id.prodMap hs), ← hp]
  rfl

theorem vector_renewal_total_residual_law (A : Finset ι) (j : ↥(Aᶜ)) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (fun z : ι → ℝ => (∑ i, z i) - t)
      (independentExponentials.restrict (vectorRenewalCut A j t)) =
      ENNReal.ofReal (poissonWeight t A.card) •
        exponentialSumLaw (Fintype.card {i : ↥(Aᶜ) // i ≠ j} + 1) := by
  let H := {i : ↥(Aᶜ) // i ≠ j}
  have hm : Measurable (fun z : ι → ℝ => ((∑ i ∈ A, z i) + z j - t, fun i : H => z i.1)) := by fun_prop
  have hg : Measurable (fun p : ℝ × (H → ℝ) => p.1 + ∑ i, p.2 i) := by fun_prop
  have h := congrArg (Measure.map (fun p : ℝ × (H → ℝ) => p.1 + ∑ i, p.2 i))
    (vector_renewal_residual_future_law A j ht)
  rw [Measure.map_map hg hm, Measure.map_smul, unitExponential_product_total_law] at h
  convert h using 1
  congr 1
  funext z
  have he := sum_block_next_future A j z
  dsimp only [Function.comp_def]
  linarith

theorem vector_renewal_cut_later_tail (A : Finset ι) (j : ↥(Aᶜ)) {t u : ℝ}
    (ht : 0 ≤ t) (htu : t ≤ u) :
    (independentExponentials (ι := ι)).real
      {z | z ∈ vectorRenewalCut A j t ∧ u < ∑ i, z i} =
      poissonWeight t A.card * poissonLowerTail (u - t)
        (Fintype.card {i : ↥(Aᶜ) // i ≠ j} + 1) := by
  have hm : Measurable (fun z : ι → ℝ => (∑ i, z i) - t) := by fun_prop
  have h := congrArg (fun μ : Measure ℝ => μ.real (Ioi (u - t)))
    (vector_renewal_total_residual_law A j ht)
  dsimp only at h
  rw [map_measureReal_apply hm measurableSet_Ioi, measureReal_restrict_apply (hm measurableSet_Ioi),
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (poissonWeight_nonneg ht A.card),
    exponentialSumLaw_tail_eq_poissonLowerTail _ (sub_nonneg.mpr htu)] at h
  convert h using 1
  congr 1
  ext z
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, sub_lt_sub_iff_right]
  exact and_comm

theorem vector_renewal_cut_later_tail_by_card (A : Finset ι) (j : ↥(Aᶜ)) {t u : ℝ}
    (ht : 0 ≤ t) (htu : t ≤ u) :
    (independentExponentials (ι := ι)).real
      {z | z ∈ vectorRenewalCut A j t ∧ u < ∑ i, z i} =
      poissonWeight t A.card * poissonLowerTail (u - t) (Fintype.card ι - A.card) := by
  rw [vector_renewal_cut_later_tail A j ht htu, remaining_waiting_count]

end StochasticMatching
