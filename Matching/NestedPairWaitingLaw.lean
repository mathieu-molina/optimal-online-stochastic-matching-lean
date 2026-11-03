import Matching.TwoTimeWaitingLaw

/-! Transfer the two-time waiting/count identity from an indexed renewal path
to arbitrary nested subsets of the original jobs.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exponential_nested_pair_law (A B : Finset ι) (hAB : A ⊆ B) :
    Measure.map (fun z : ι → ℝ => ((∑ i ∈ A, z i), ∑ i ∈ B, z i)) independentExponentials =
      Measure.map (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
        ((exponentialSumLaw A.card).prod (exponentialSumLaw (B.card - A.card))) := by
  have hd : Disjoint A (B \ A) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_sdiff.mp hi').2 hi
  have hi := independentExponentials_coordinates_independent.indepFun_finset A (B \ A) hd measurable_pi_apply
  have hs : Measurable (fun z : A → ℝ => ∑ i, z i) := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have ht : Measurable (fun z : ↥(B \ A) → ℝ => ∑ i, z i) := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hi' := hi.comp hs ht
  simp only [Function.comp_def, Finset.sum_coe_sort] at hi'
  have hAm := Finset.measurable_sum A (fun i _ => (measurable_pi_apply i : Measurable (fun z : ι → ℝ => z i)))
  have hBm := Finset.measurable_sum (B \ A) (fun i _ => (measurable_pi_apply i : Measurable (fun z : ι → ℝ => z i)))
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable hBm.aemeasurable).mp hi'
  rw [independentExponentials_subset_sum_law, independentExponentials_subset_sum_law,
    Finset.card_sdiff hAB] at hp
  rw [← hp, Measure.map_map (measurable_fst.prodMk (measurable_fst.add measurable_snd)) (hAm.prodMk hBm)]
  congr 1
  funext z
  apply Prod.ext
  · rfl
  · have h := Finset.sum_sdiff (f := z) hAB
    dsimp only [Function.comp_def]
    linarith

theorem prefix_set_card (m n : ℕ) (hmn : m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < m)).card = m := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_fin_lt_of_le hmn

theorem nested_pair_waiting_poisson_law (A B : Finset ι) (hAB : A ⊆ B) (a b : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | (a : ℝ) < ∑ i ∈ A, z i ∧ (a : ℝ) + b < ∑ i ∈ B, z i} =
    ((poissonMeasure a).prod (poissonMeasure b)).real
      {p : ℕ × ℕ | p.1 < A.card ∧ p.1 + p.2 < B.card} := by
  let C : Finset (Fin B.card) := Finset.univ.filter (fun i => i.val < A.card)
  have hc : C.card = A.card := prefix_set_card _ _ (Finset.card_le_card hAB)
  have h1 := exponential_nested_pair_law A B hAB
  have h2 := exponential_nested_pair_law C Finset.univ (Finset.subset_univ C)
  simp only [hc, Finset.card_univ, Fintype.card_fin] at h2
  have he := h1.trans h2.symm
  have hp := congrArg (fun μ : Measure (ℝ × ℝ) => μ.real {p | (a : ℝ) < p.1 ∧ (a : ℝ) + b < p.2}) he
  dsimp only at hp
  have hm1 : Measurable (fun z : ι → ℝ => ((∑ i ∈ A, z i), ∑ i ∈ B, z i)) := by fun_prop
  have hm2 : Measurable (fun z : Fin B.card → ℝ => ((∑ i ∈ C, z i), ∑ i, z i)) := by fun_prop
  have hE : MeasurableSet {p : ℝ × ℝ | (a : ℝ) < p.1 ∧ (a : ℝ) + b < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter (measurableSet_lt measurable_const measurable_snd)
  rw [map_measureReal_apply hm1 hE, map_measureReal_apply hm2 hE] at hp
  exact hp.trans (exponential_poisson_two_time_waiting_law A.card B.card (Finset.card_le_card hAB) a b)

end StochasticMatching
