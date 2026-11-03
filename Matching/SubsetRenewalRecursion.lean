import Matching.SubsetRenewalPartition
import Matching.BlockRenewalEvents
import Matching.FiniteRenewalJoint

/-! A first-observation recurrence retaining any finite family of later
superset observations. This is the induction step for arbitrary chains.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem subset_waiting_joint_recursion (A : Finset ι) (B : κ → Finset ι)
    (hAB : ∀ k, A ⊆ B k) {t : ℝ} (ht : 0 ≤ t) (u : κ → ℝ) :
    (independentExponentials (ι := ι)).real
      {z | t < ∑ i ∈ A, z i ∧ ∀ k, t + u k < ∑ i ∈ B k, z i} =
      ∑ j : Fin A.card, poissonWeight t j.val *
        (independentExponentials (ι := ↥((subsetBefore A j)ᶜ))).real
          {w | ∀ k, u k < ∑ i ∈ remainingSubset (subsetBefore A j) (B k), w i} := by
  let W : (ι → ℝ) → (Fin A.card → ℝ) := fun z k => z (subsetEmbedding A k)
  let E : Fin A.card → Set (ι → ℝ) := fun j =>
    {z | finiteRenewalCount (W z) t = j.val ∧ ∀ k, t + u k < ∑ i ∈ B k, z i}
  have hW : Measurable W := measurable_pi_lambda _ (fun k => measurable_pi_apply _)
  have hfuture : MeasurableSet {z : ι → ℝ | ∀ k, t + u k < ∑ i ∈ B k, z i} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_lt measurable_const
      (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin A.card)), MeasurableSet (E j) := by
    intro j _
    exact ((measurableSet_singleton j.val).preimage ((measurable_finiteRenewalCount t).comp hW)).inter hfuture
  have hd : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin A.card)) : Set (Fin A.card)) E := by
    intro j _ k _ hjk
    change Disjoint (E j) (E k)
    rw [Set.disjoint_left]
    intro z hj hk
    exact hjk (Fin.ext (hj.1.symm.trans hk.1))
  have he : ({z : ι → ℝ | t < ∑ i ∈ A, z i ∧ ∀ k, t + u k < ∑ i ∈ B k, z i} : Set (ι → ℝ)) =ᵐ[independentExponentials]
      ⋃ j ∈ (Finset.univ : Finset (Fin A.card)), E j := by
    filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
    apply propext
    change (t < ∑ i ∈ A, z i ∧ ∀ k, t + u k < ∑ i ∈ B k, z i) ↔
      z ∈ ⋃ j ∈ (Finset.univ : Finset (Fin A.card)), E j
    have hc := finiteRenewalCount_lt_iff_total (fun k => (hz (subsetEmbedding A k)).le) t ht
    rw [subsetEnumeration_sum] at hc
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_univ, exists_prop, true_and, E]
    constructor
    · rintro ⟨hA, hB⟩
      exact ⟨⟨finiteRenewalCount (W z) t, hc.mpr hA⟩, rfl, hB⟩
    · rintro ⟨j, hj, hB⟩
      exact ⟨hc.mp (hj.symm ▸ j.isLt), hB⟩
  rw [measureReal_congr he, measureReal_biUnion_finset hd hm]
  apply Finset.sum_congr rfl
  intro j _
  have hcut : E j =ᵐ[independentExponentials]
      {z | z ∈ vectorRenewalCut (subsetBefore A j) (subsetNext A j) t ∧
        ∀ k, t + u k < ∑ i ∈ B k, z i} := by
    filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
    apply propext
    have hc := finiteRenewalCount_eq_iff_cut (fun k => (hz (subsetEmbedding A k)).le) ht j
    exact and_congr_left (fun _ => hc.trans (subset_renewal_cut_iff A j z t).symm)
  rw [measureReal_congr hcut]
  have h := block_restart_joint_probability (subsetBefore A j) (subsetNext A j) B
    (fun k => (subsetBefore_subset A j).trans (hAB k))
    (fun k => hAB k (subsetEnumeration A j).2) ht u
  simpa only [subsetBefore_card] using h

end StochasticMatching
