import Mathlib.MeasureTheory.Measure.Prod

/-! Reorder three independent components without changing their joint law. -/
open MeasureTheory
namespace StochasticMatching
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

theorem measurePreserving_prodMiddleSwap (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun x : A × (B × C) => (x.2.1, x.1, x.2.2))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have ha := (measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc
  have hb := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)
  have hc := measurePreserving_prodAssoc ν μ ρ
  exact hc.comp (hb.comp ha)

end StochasticMatching
