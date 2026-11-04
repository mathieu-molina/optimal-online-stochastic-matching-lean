import Matching.NestedExponentialSums

/-! Split an actual demand vector into a completed block, the next waiting
time, and all untouched future coordinates. This connects renewal identities
for Erlang/product measures to the original exponential sample space.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentExponentials_restriction_law (S : Finset ι) :
    Measure.map (fun z : ι → ℝ => fun i : S => z i) independentExponentials =
      (independentExponentials (ι := S)) := by
  have hi := independentExponentials_coordinates_independent.precomp
    (show Function.Injective (fun i : S => (i : ι)) from Subtype.val_injective)
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i : S =>
    (measurable_pi_apply (i : ι)).aemeasurable)).mp hi
  simpa only [independentExponentials_coordinate_law] using h

theorem exponential_block_future_law (A : Finset ι) :
    Measure.map (fun z : ι → ℝ => ((∑ i ∈ A, z i), fun i : ↥(Aᶜ) => z i)) independentExponentials =
      (exponentialSumLaw A.card).prod (independentExponentials (ι := ↥(Aᶜ))) := by
  have hi := independentExponentials_coordinates_independent.indepFun_finset A Aᶜ
    disjoint_compl_right measurable_pi_apply
  have hs : Measurable (fun z : A → ℝ => ∑ i, z i) := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hi' := hi.comp hs measurable_id
  simp only [Function.comp_def, Finset.sum_coe_sort, id_eq] at hi'
  have h := (indepFun_iff_map_prod_eq_prod_map_map
    (Finset.measurable_sum A (fun i _ => measurable_pi_apply i)).aemeasurable
    (measurable_pi_lambda _ (fun i : ↥(Aᶜ) => measurable_pi_apply (i : ι))).aemeasurable).mp hi'
  rw [independentExponentials_subset_sum_law, independentExponentials_restriction_law] at h
  exact h

theorem exponential_block_next_future_law (A : Finset ι) (j : ↥(Aᶜ)) :
    Measure.map (fun z : ι → ℝ =>
      (((∑ i ∈ A, z i), z j), fun i : {i : ↥(Aᶜ) // i ≠ j} => z i.1)) independentExponentials =
      ((exponentialSumLaw A.card).prod unitExponential).prod
        (independentExponentials (ι := {i : ↥(Aᶜ) // i ≠ j})) := by
  let H := {i : ↥(Aᶜ) // i ≠ j} → ℝ
  let F : (ι → ℝ) → ℝ × (↥(Aᶜ) → ℝ) :=
    fun z => ((∑ i ∈ A, z i), fun i => z i)
  have hF : Measurable F := (Finset.measurable_sum A (fun i _ => measurable_pi_apply i)).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι)))
  let G : ℝ × (↥(Aᶜ) → ℝ) → ℝ × (ℝ × H) := Prod.map id (splitDemand j)
  have hG : Measurable G := measurable_id.prodMap (splitDemand j).measurable
  have h1 := congrArg (Measure.map G) (exponential_block_future_law A)
  rw [Measure.map_map hG hF] at h1
  have hprod := Measure.map_prod_map (exponentialSumLaw A.card)
    (independentExponentials (ι := ↥(Aᶜ))) measurable_id (splitDemand j).measurable
  rw [Measure.map_id, (splitDemand_preserves_measure j).map_eq] at hprod
  rw [← hprod] at h1
  have h2 := congrArg (Measure.map (fun p : ℝ × (ℝ × H) => ((p.1, p.2.1), p.2.2))) h1
  have hassoc : Measurable (fun p : ℝ × (ℝ × H) => ((p.1, p.2.1), p.2.2)) := by fun_prop
  rw [Measure.map_map hassoc (hG.comp hF)] at h2
  have hp := (measurePreserving_prodAssoc (exponentialSumLaw A.card) unitExponential
    (independentExponentials (ι := {i : ↥(Aᶜ) // i ≠ j}))).symm
  exact h2.trans hp.map_eq

end StochasticMatching
