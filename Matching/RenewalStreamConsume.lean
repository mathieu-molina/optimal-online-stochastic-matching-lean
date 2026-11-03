import Matching.CoordinateSplit
import Matching.RenewalStreamsSplit

/-! Reading the next waiting amount from one selected type stream leaves
all the remaining streams independent, and independent of the amount read. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def consumeRenewalStream (j : σ) (z : σ → ℕ → ℝ) : ℝ × (σ → ℕ → ℝ) :=
  (z j 0, Function.update z j (fun n => z j (n + 1)))

theorem measurable_consumeRenewalStream (j : σ) : Measurable (consumeRenewalStream j) := by
  apply Measurable.prodMk
  · exact (measurable_pi_apply 0).comp (measurable_pi_apply j)
  · apply measurable_pi_lambda
    intro i
    by_cases hi : i = j
    · subst i
      simp only [consumeRenewalStream, Function.update_self]
      exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp (measurable_pi_apply j))
    · simpa only [consumeRenewalStream, Function.update_of_ne hi] using (measurable_pi_apply i)

theorem independentRenewalStreams_consume_law (j : σ) :
    Measure.map (consumeRenewalStream j) independentRenewalStreams =
      unitExponential.prod independentRenewalStreams := by
  let e := splitCoordinate (A := ℕ → ℝ) j
  have hs : MeasurePreserving e independentRenewalStreams
      (infiniteExponentials.prod (independentRenewalStreams (σ := {i : σ // i ≠ j}))) :=
    splitCoordinate_preserves_measure infiniteExponentials j
  have ht : MeasurePreserving splitWaiting infiniteExponentials
      (unitExponential.prod infiniteExponentials) :=
    ⟨measurable_splitWaiting, infiniteExponentials_split_law⟩
  have hp := ht.prod (MeasurePreserving.id (independentRenewalStreams (σ := {i : σ // i ≠ j})))
  have ha := measurePreserving_prodAssoc unitExponential infiniteExponentials
    (independentRenewalStreams (σ := {i : σ // i ≠ j}))
  have hr := (MeasurePreserving.id unitExponential).prod (hs.symm e)
  have h := (hr.comp (ha.comp (hp.comp hs))).map_eq
  have hf : (Prod.map id e.symm) ∘ MeasurableEquiv.prodAssoc ∘ (Prod.map splitWaiting id) ∘ e =
      consumeRenewalStream j := by
    funext z
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i = j
      · subst i
        simp [e, splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt,
          consumeRenewalStream, splitWaiting, MeasurableEquiv.prodAssoc]
      · simp [e, splitCoordinate, Equiv.funSplitAt, Equiv.piSplitAt,
          consumeRenewalStream, splitWaiting, hi, MeasurableEquiv.prodAssoc]
  change Measure.map ((Prod.map id e.symm) ∘ MeasurableEquiv.prodAssoc ∘ (Prod.map splitWaiting id) ∘ e)
    independentRenewalStreams = _ at h
  rwa [hf] at h

end StochasticMatching
