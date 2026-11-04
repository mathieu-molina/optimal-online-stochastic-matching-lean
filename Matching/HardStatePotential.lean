import Matching.HardArrivalPotential

open MeasureTheory Set
namespace StochasticMatching
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

noncomputable def hardStatePotential (T : H → ℝ) (A : H → Finset ι) : Finset ι ⊕ H → ℝ :=
  Sum.elim (fun B => 1 - hardUnmatchedFraction B)
    (fun h => hardUpperPotential (T h) (hardUnmatchedFraction (A h)))

theorem measurable_hardStatePotential (T : H → ℝ) (A : H → Finset ι)
    (hT : Measurable T) (hA : Measurable A) : Measurable (hardStatePotential T A) := by
  have hm : Measurable (fun p : ℝ × Finset ι => hardUpperPotential p.1 (hardUnmatchedFraction p.2)) := by
      apply measurable_from_prod_countable
      intro B
      exact (continuous_hardUpperPotential_time (hardUnmatchedFraction_bounds B).1).measurable
  have hleft : Measurable (fun B : Finset ι => 1 - hardUnmatchedFraction B) := measurable_of_countable _
  have hright := hm.comp (hT.prodMk hA)
  simp only [Function.comp_def] at hright
  change Measurable (Sum.elim (fun B : Finset ι => 1 - hardUnmatchedFraction B)
    (fun h : H => hardUpperPotential (T h) (hardUnmatchedFraction (A h))))
  exact hleft.sumElim hright

end StochasticMatching
