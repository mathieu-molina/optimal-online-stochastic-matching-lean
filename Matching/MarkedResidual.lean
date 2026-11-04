import Matching.HistoryResidual

/-! Split a candidate completing coordinate from the surviving demands.
The candidate time can be any measurable function of that coordinate. The
factorization is restricted to the event that all other jobs survive that time.
Identifying it with the first completion still requires service-curve hypotheses.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def splitDemand (j : ι) :
    (ι → ℝ) ≃ᵐ ℝ × ({i : ι // i ≠ j} → ℝ) := by
  classical
  exact {
    toEquiv := Equiv.funSplitAt j ℝ
    measurable_toFun := (measurable_pi_apply j).prodMk
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.1))
    measurable_invFun := by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = j
      · subst i
        simpa [Equiv.funSplitAt, Equiv.piSplitAt] using
          (measurable_fst : Measurable (fun p : ℝ × ({i : ι // i ≠ j} → ℝ) => p.1))
      · simpa [Equiv.funSplitAt, Equiv.piSplitAt, hi] using
          ((measurable_pi_apply (⟨i, hi⟩ : {i : ι // i ≠ j})).comp measurable_snd) }

omit [Fintype ι] in
@[simp] theorem splitDemand_apply (j : ι) (z : ι → ℝ) :
    splitDemand j z = (z j, fun i => z i.1) := rfl

theorem splitDemand_preserves_measure (j : ι) :
    MeasurePreserving (splitDemand j) independentExponentials
      (unitExponential.prod (independentExponentials (ι := {i : ι // i ≠ j}))) := by
  classical
  apply MeasurePreserving.symm (splitDemand j).symm
  refine ⟨(splitDemand j).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have hset : (splitDemand j).symm ⁻¹' univ.pi s =
      s j ×ˢ univ.pi (fun i : {i : ι // i ≠ j} => s i.1) := by
    ext p
    constructor
    · intro hp
      have h := mem_univ_pi.mp hp
      constructor
      · simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt] using h j
      · apply mem_univ_pi.mpr
        intro i
        simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt, i.2] using h i.1
    · rintro ⟨hp, hq⟩
      apply mem_univ_pi.mpr
      intro i
      by_cases hi : i = j
      · subst i
        simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt] using hp
      · simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt, hi] using
          mem_univ_pi.mp hq ⟨i, hi⟩
  rw [Measure.map_apply (splitDemand j).symm.measurable (MeasurableSet.univ_pi hs),
    hset, Measure.prod_prod, independentExponentials, Measure.pi_pi]
  have hprod := Fintype.prod_subtype_mul_prod_subtype
    (fun i : ι => i = j) (fun i => unitExponential (s i))
  simpa using hprod

variable {H : Type*} [MeasurableSpace H]

def candidateHistory (j : ι) (τ : ℝ → H) (z : ι → ℝ) :
    H × ({i : ι // i ≠ j} → ℝ) := (τ (z j), fun i => z i.1)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_candidateHistory (j : ι) {τ : ℝ → H} (hτ : Measurable τ) :
    Measurable (candidateHistory j τ) := by
  exact (hτ.comp (measurable_pi_apply j)).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply i.1))

theorem candidateHistory_law (j : ι) {τ : ℝ → H} (hτ : Measurable τ) :
    Measure.map (candidateHistory j τ) independentExponentials =
      (Measure.map τ unitExponential).prod
        (independentExponentials (ι := {i : ι // i ≠ j})) := by
  have hm : Measurable (Prod.map τ (id : ({i : ι // i ≠ j} → ℝ) → _)) :=
    (hτ.comp measurable_fst).prodMk measurable_snd
  have hc : candidateHistory j τ = Prod.map τ id ∘ splitDemand j := rfl
  rw [hc, ← Measure.map_map hm (splitDemand j).measurable,
    (splitDemand_preserves_measure j).map_eq]
  simpa using (Measure.map_prod_map unitExponential
    (independentExponentials (ι := {i : ι // i ≠ j})) hτ measurable_id).symm

theorem candidate_completion_factorization (j : ι) {τ : ℝ → H}
    (hτ : Measurable τ) {a : H → {i : ι // i ≠ j} → ℝ}
    (ha : Measurable a) (ha0 : ∀ u i, 0 ≤ a u i) :
    Measure.map (residualObservation a ∘ candidateHistory j τ)
      (independentExponentials.restrict
        (candidateHistory j τ ⁻¹' historySurvival a)) =
      ((Measure.map τ unitExponential).withDensity
        (fun u => independentExponentials (survivalBox (a u)))).prod
          (independentExponentials (ι := {i : ι // i ≠ j})) := by
  rw [← Measure.map_map (measurable_residualObservation ha)
    (measurable_candidateHistory j hτ),
    ← Measure.restrict_map (measurable_candidateHistory j hτ)
      (measurable_historySurvival ha), candidateHistory_law j hτ]
  exact history_survival_factorization ha ha0 (Measure.map τ unitExponential)

end StochasticMatching
