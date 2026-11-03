import Matching.KernelIntertwining
import Matching.StoppedKernel

/-! A deterministic transition driven by fresh noise. A one-step product
law yields a kernel intertwining and therefore all finite iteration laws.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A R Y : Type*} [MeasurableSpace A] [MeasurableSpace R] [MeasurableSpace Y]

noncomputable def noiseKernel (ν : Measure Y) [SFinite ν]
    (F : (A × R) × Y → A × R) : Kernel (A × R) (A × R) :=
  eventUpdateKernel (Kernel.const (A × R) ν) F

theorem noiseKernel_markov (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : (A × R) × Y → A × R) (hF : Measurable F) : IsMarkovKernel (noiseKernel ν F) :=
  eventUpdateKernel_markov _ F hF

theorem noiseKernel_after_fresh (ρ : Measure R) [SFinite ρ] (ν : Measure Y) [SFinite ν]
    (F : (A × R) × Y → A × R) (hF : Measurable F) (a : A) :
    (noiseKernel ν F ∘ₖ freshResidualKernel ρ) a =
      Measure.map (fun p : R × Y => F ((a, p.1), p.2)) (ρ.prod ν) := by
  have hm : Measurable (fun p : R × Y => F ((a, p.1), p.2)) :=
    hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  ext E hE
  rw [Kernel.comp_apply' _ _ _ hE, freshResidualKernel,
    Kernel.lintegral_id_prod ((noiseKernel ν F).measurable_coe hE), Kernel.const_apply,
    Measure.map_apply hm hE, Measure.prod_apply (hm hE)]
  apply lintegral_congr
  intro r
  change eventUpdateKernel (Kernel.const (A × R) ν) F (a, r) E = _
  rw [eventUpdateKernel_apply _ F hF]
  have hr : Measurable (fun y => F ((a, r), y)) := hF.comp measurable_prodMk_left
  rw [Measure.map_apply hr hE]
  rfl

theorem freshResidualKernel_comp_apply (ρ : Measure R) [SFinite ρ] (L : Kernel A A) (a : A) :
    (freshResidualKernel ρ ∘ₖ L) a = (L a).prod ρ := by
  ext E hE
  rw [Kernel.comp_apply' _ _ _ hE, Measure.prod_apply hE]
  apply lintegral_congr
  intro b
  rw [freshResidualKernel_apply, Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hE]

theorem noiseKernel_intertwining (ρ : Measure R) [SFinite ρ] (ν : Measure Y) [SFinite ν]
    (F : (A × R) × Y → A × R) (hF : Measurable F) (L : Kernel A A)
    (hlaw : ∀ a, Measure.map (fun p : R × Y => F ((a, p.1), p.2)) (ρ.prod ν) = (L a).prod ρ) :
    noiseKernel ν F ∘ₖ freshResidualKernel ρ = freshResidualKernel ρ ∘ₖ L := by
  ext a : 1
  rw [noiseKernel_after_fresh ρ ν F hF, freshResidualKernel_comp_apply]
  exact hlaw a

end StochasticMatching
