import Matching.ExponentialBlockSplit
import Matching.RenewalFuture

/-! Renewal conditioning on the original finite product of exponential
waiting times, with every untouched future coordinate retained.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorRenewalCut (A : Finset ι) (j : ↥(Aᶜ)) (t : ℝ) : Set (ι → ℝ) :=
  {z | (∑ i ∈ A, z i) ≤ t ∧ t < (∑ i ∈ A, z i) + z j}

theorem measurableSet_vectorRenewalCut (A : Finset ι) (j : ↥(Aᶜ)) (t : ℝ) :
    MeasurableSet (vectorRenewalCut A j t) := by
  have hm := Finset.measurable_sum A (fun i _ => measurable_pi_apply i : ∀ i ∈ A, Measurable (fun z : ι → ℝ => z i))
  exact (measurableSet_le hm measurable_const).inter
    (measurableSet_lt measurable_const (hm.add (measurable_pi_apply (j : ι))))

theorem vector_renewal_residual_future_law (A : Finset ι) (j : ↥(Aᶜ)) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (fun z : ι → ℝ =>
      ((∑ i ∈ A, z i) + z j - t, fun i : {i : ↥(Aᶜ) // i ≠ j} => z i.1))
      (independentExponentials.restrict (vectorRenewalCut A j t)) =
      ENNReal.ofReal (poissonWeight t A.card) •
        (unitExponential.prod (independentExponentials (ι := {i : ↥(Aᶜ) // i ≠ j}))) := by
  let H := {i : ↥(Aᶜ) // i ≠ j} → ℝ
  let F : (ι → ℝ) → (ℝ × ℝ) × H := fun z =>
    (((∑ i ∈ A, z i), z j), fun i => z i.1)
  let G : (ℝ × ℝ) × H → ℝ × H := fun p => (p.1.1 + p.1.2 - t, p.2)
  have hF : Measurable F := by
    exact ((Finset.measurable_sum A (fun i _ => measurable_pi_apply i)).prodMk (measurable_pi_apply (j : ι))).prodMk
      (measurable_pi_lambda _ (fun i => measurable_pi_apply (i.1 : ι)))
  have hG : Measurable G := by fun_prop
  have hE : MeasurableSet (renewalCut t ×ˢ (Set.univ : Set H)) :=
    (measurableSet_renewalCut t).prod MeasurableSet.univ
  have he : F ⁻¹' (renewalCut t ×ˢ Set.univ) = vectorRenewalCut A j t := by
    ext z
    simp [F, renewalCut, vectorRenewalCut]
  change Measure.map (G ∘ F) (independentExponentials.restrict (vectorRenewalCut A j t)) = _
  rw [← he, ← Measure.map_map hG hF, ← Measure.restrict_map hF hE,
    exponential_block_next_future_law A j]
  exact renewal_cut_with_future_law _ A.card ht

theorem vector_renewal_cut_probability (A : Finset ι) (j : ↥(Aᶜ)) {t : ℝ} (ht : 0 ≤ t) :
    (independentExponentials (ι := ι)).real (vectorRenewalCut A j t) = poissonWeight t A.card := by
  have h := congrArg (fun μ : Measure (ℝ × ({i : ↥(Aᶜ) // i ≠ j} → ℝ)) => μ Set.univ)
    (vector_renewal_residual_future_law A j ht)
  dsimp only at h
  have hm : Measurable (fun z : ι → ℝ =>
      ((∑ i ∈ A, z i) + z j - t, fun i : {i : ↥(Aᶜ) // i ≠ j} => z i.1)) := by fun_prop
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at h
  rw [measureReal_def, h, ENNReal.toReal_ofReal (poissonWeight_nonneg ht A.card)]

end StochasticMatching
