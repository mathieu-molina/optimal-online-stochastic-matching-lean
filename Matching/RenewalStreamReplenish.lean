import Matching.RenewalStreamsSplit
import Matching.CoordinateSplit
import Matching.ProductReorder

/-! Rebuild all renewal streams after one type has arrived. The winning
type keeps its entire future stream; every other type receives its surviving
waiting amount in front of its unchanged future. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def replenishRenewalStreams (j : σ)
    (x : ({i : σ // i ≠ j} → ℝ) × (σ → ℕ → ℝ)) : σ → ℕ → ℝ :=
  (splitCoordinate (A := ℕ → ℝ) j).symm
    (x.2 j, prependRenewalStreams (x.1, fun i => x.2 i.1))

theorem measurable_replenishRenewalStreams (j : σ) :
    Measurable (replenishRenewalStreams j) := by
  apply (splitCoordinate (A := ℕ → ℝ) j).symm.measurable.comp
  apply Measurable.prodMk ((measurable_pi_apply j).comp measurable_snd)
  apply measurable_prependRenewalStreams.comp
  exact measurable_fst.prodMk (measurable_pi_lambda _
    (fun i => (measurable_pi_apply i.1).comp measurable_snd))

theorem replenishRenewalStreams_winner (j : σ)
    (x : ({i : σ // i ≠ j} → ℝ) × (σ → ℕ → ℝ)) :
    replenishRenewalStreams j x j = x.2 j := by
  simp [replenishRenewalStreams, splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt]

theorem replenishRenewalStreams_survivor (j i : σ) (hi : i ≠ j)
    (x : ({i : σ // i ≠ j} → ℝ) × (σ → ℕ → ℝ)) :
    replenishRenewalStreams j x i = prependWaiting (x.1 ⟨i, hi⟩, x.2 i) := by
  simp [replenishRenewalStreams, splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt,
    hi, prependRenewalStreams]

theorem independentRenewalStreams_replenish_law (j : σ) :
    Measure.map (replenishRenewalStreams j)
      ((independentExponentials (ι := {i : σ // i ≠ j})).prod independentRenewalStreams) =
      independentRenewalStreams := by
  let e := splitCoordinate (A := ℕ → ℝ) j
  have hs : MeasurePreserving e independentRenewalStreams
      (infiniteExponentials.prod (independentRenewalStreams (σ := {i : σ // i ≠ j}))) :=
    splitCoordinate_preserves_measure infiniteExponentials j
  have hp := (MeasurePreserving.id (independentExponentials (ι := {i : σ // i ≠ j}))).prod hs
  have hq := measurePreserving_prodMiddleSwap
    (independentExponentials (ι := {i : σ // i ≠ j})) infiniteExponentials
    (independentRenewalStreams (σ := {i : σ // i ≠ j}))
  have hr := (MeasurePreserving.id infiniteExponentials).prod
    (show MeasurePreserving (prependRenewalStreams (σ := {i : σ // i ≠ j}))
      (independentExponentials.prod independentRenewalStreams) independentRenewalStreams from
      ⟨measurable_prependRenewalStreams, independentRenewalStreams_prepend_law⟩)
  exact ((hs.symm e).comp (hr.comp (hq.comp hp))).map_eq

end StochasticMatching
