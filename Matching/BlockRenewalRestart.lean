import Matching.VectorRenewalCut
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Restart the full remaining exponential vector after a renewal cut.
Every later superset sum is translated by exactly the elapsed time.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def blockRestart (A : Finset ι) (j : ↥(Aᶜ)) (t : ℝ)
    (z : ι → ℝ) : ↥(Aᶜ) → ℝ :=
  Function.update (fun i => z i) j ((∑ i ∈ A, z i) + z j - t)

theorem measurable_blockRestart (A : Finset ι) (j : ↥(Aᶜ)) (t : ℝ) :
    Measurable (blockRestart A j t) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = j
  · subst i
    simp only [blockRestart, Function.update_self]
    fun_prop
  · simp only [blockRestart, Function.update_of_ne hi]
    exact measurable_pi_apply (i : ι)

theorem block_restart_law (A : Finset ι) (j : ↥(Aᶜ)) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (blockRestart A j t)
      (independentExponentials.restrict (vectorRenewalCut A j t)) =
      ENNReal.ofReal (poissonWeight t A.card) •
        (independentExponentials (ι := ↥(Aᶜ))) := by
  let F := fun z : ι → ℝ =>
    ((∑ i ∈ A, z i) + z j - t, fun i : {i : ↥(Aᶜ) // i ≠ j} => z i.1)
  have hF : Measurable F := by fun_prop
  have he : blockRestart A j t = (splitDemand j).symm ∘ F := by
    funext z
    apply (splitDemand j).injective
    simp only [MeasurableEquiv.apply_symm_apply, Function.comp_apply, splitDemand_apply]
    apply Prod.ext
    · simp [blockRestart, F]
    · funext i
      simp [blockRestart, F, i.2]
  rw [he, ← Measure.map_map (splitDemand j).symm.measurable hF,
    vector_renewal_residual_future_law A j ht, Measure.map_smul]
  congr 1
  exact ((splitDemand_preserves_measure j).symm (splitDemand j)).map_eq

noncomputable def remainingSubset (A B : Finset ι) : Finset ↥(Aᶜ) :=
  Finset.univ.filter (fun i => (i : ι) ∈ B)

theorem remainingSubset_mono (A : Finset ι) : Monotone (remainingSubset A) := by
  intro B C hBC i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBC (Finset.mem_filter.mp hi).2⟩

theorem remainingSubset_sum (A B : Finset ι) (z : ι → ℝ) :
    (∑ i ∈ remainingSubset A B, z i) = ∑ i ∈ B \ A, z i := by
  apply Finset.sum_bij (fun (i : ↥(Aᶜ)) _ => (i : ι))
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hi).2, Finset.mem_compl.mp i.2⟩
  · intro i hi k hk hik
    exact Subtype.ext hik
  · intro i hi
    exact ⟨⟨i, Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).1⟩, rfl⟩
  · intro i hi; rfl

theorem remainingSubset_card (A B : Finset ι) (hAB : A ⊆ B) :
    (remainingSubset A B).card = B.card - A.card := by
  have he : (remainingSubset A B).map ⟨Subtype.val, Subtype.val_injective⟩ = B \ A := by
    ext i
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, remainingSubset,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, Finset.mem_compl.mp j.2⟩
    · rintro ⟨hiB, hiA⟩
      exact ⟨⟨i, Finset.mem_compl.mpr hiA⟩, hiB, rfl⟩
  have hc := congrArg Finset.card he
  simpa only [Finset.card_map, Finset.card_sdiff hAB] using hc

theorem block_restart_sum (A B : Finset ι) (hAB : A ⊆ B) (j : ↥(Aᶜ))
    (hjB : (j : ι) ∈ B) (t : ℝ) (z : ι → ℝ) :
    (∑ i ∈ remainingSubset A B, blockRestart A j t z i) = (∑ i ∈ B, z i) - t := by
  have hj : j ∈ remainingSubset A B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjB⟩
  rw [blockRestart, Finset.sum_update_of_mem hj]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.add_sum_erase (remainingSubset A B) (fun i => z i) hj
  rw [remainingSubset_sum] at hs
  have hb := Finset.sum_sdiff (f := z) hAB
  linarith

end StochasticMatching
