import Matching.MarkedResidual

/-! Split one coordinate from an arbitrary finite product measure. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A]

noncomputable def splitCoordinate (j : ι) :
    (ι → A) ≃ᵐ A × ({i : ι // i ≠ j} → A) := by
  classical
  exact {
    toEquiv := Equiv.funSplitAt j A
    measurable_toFun := (measurable_pi_apply j).prodMk
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.1))
    measurable_invFun := by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = j
      · subst i
        simpa [Equiv.funSplitAt, Equiv.piSplitAt] using
          (measurable_fst : Measurable (fun p : A × ({i : ι // i ≠ j} → A) => p.1))
      · simpa [Equiv.funSplitAt, Equiv.piSplitAt, hi] using
          ((measurable_pi_apply (⟨i, hi⟩ : {i : ι // i ≠ j})).comp measurable_snd) }

omit [Fintype ι] in
@[simp] theorem splitCoordinate_apply (j : ι) (z : ι → A) :
    splitCoordinate j z = (z j, fun i => z i.1) := rfl

theorem splitCoordinate_preserves_measure (μ : Measure A) [SigmaFinite μ] (j : ι) :
    MeasurePreserving (splitCoordinate j) (Measure.pi (fun _ : ι => μ))
      (μ.prod (Measure.pi (fun _ : {i : ι // i ≠ j} => μ))) := by
  classical
  apply MeasurePreserving.symm (splitCoordinate j).symm
  refine ⟨(splitCoordinate j).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have hset : (splitCoordinate j).symm ⁻¹' univ.pi s =
      s j ×ˢ univ.pi (fun i : {i : ι // i ≠ j} => s i.1) := by
    ext p
    constructor
    · intro hp
      have h := mem_univ_pi.mp hp
      constructor
      · simpa [splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt] using h j
      · apply mem_univ_pi.mpr
        intro i
        simpa [splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt, i.2] using h i.1
    · rintro ⟨hp, hq⟩
      apply mem_univ_pi.mpr
      intro i
      by_cases hi : i = j
      · subst i
        simpa [splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt] using hp
      · simpa [splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt, hi] using
          mem_univ_pi.mp hq ⟨i, hi⟩
  rw [Measure.map_apply (splitCoordinate j).symm.measurable (MeasurableSet.univ_pi hs),
    hset, Measure.prod_prod, Measure.pi_pi]
  have hprod := Fintype.prod_subtype_mul_prod_subtype
    (fun i : ι => i = j) (fun i => μ (s i))
  simpa using hprod

end StochasticMatching
