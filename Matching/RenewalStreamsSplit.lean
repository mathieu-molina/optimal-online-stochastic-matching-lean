import Matching.InfiniteRenewalSplit
import Matching.RenewalInputCounts

/-! Simultaneous splitting of all independent type streams into current
waiting amounts and independent complete future streams. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {σ : Type*} [Fintype σ]

def splitRenewalStreams (z : σ → ℕ → ℝ) : (σ → ℝ) × (σ → ℕ → ℝ) :=
  (fun s => z s 0, fun s n => z s (n + 1))

theorem measurable_splitRenewalStreams : Measurable (splitRenewalStreams (σ := σ)) := by
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ (fun s => (measurable_pi_apply 0).comp (measurable_pi_apply s))
  · exact measurable_pi_lambda _ (fun s => measurable_pi_lambda _
      (fun n => (measurable_pi_apply (n + 1)).comp (measurable_pi_apply s)))

def prependRenewalStreams (x : (σ → ℝ) × (σ → ℕ → ℝ)) (s : σ) : ℕ → ℝ :=
  prependWaiting (x.1 s, x.2 s)

theorem measurable_prependRenewalStreams : Measurable (prependRenewalStreams (σ := σ)) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_prependWaiting.comp (((measurable_pi_apply s).comp measurable_fst).prodMk
    ((measurable_pi_apply s).comp measurable_snd))

theorem splitRenewalStreams_prepend (x : (σ → ℝ) × (σ → ℕ → ℝ)) :
    splitRenewalStreams (prependRenewalStreams x) = x := rfl

theorem prependRenewalStreams_split (z : σ → ℕ → ℝ) :
    prependRenewalStreams (splitRenewalStreams z) = z := by
  funext s
  exact prependWaiting_split (z s)

theorem independentRenewalStreams_split_law :
    Measure.map (splitRenewalStreams (σ := σ)) independentRenewalStreams =
      independentExponentials.prod independentRenewalStreams := by
  have hp := measurePreserving_pi (fun _ : σ => infiniteExponentials)
    (fun _ : σ => unitExponential.prod infiniteExponentials)
    (fun _ => (⟨measurable_splitWaiting, infiniteExponentials_split_law⟩ :
      MeasurePreserving splitWaiting infiniteExponentials (unitExponential.prod infiniteExponentials)))
  have hq := measurePreserving_arrowProdEquivProdArrow ℝ (ℕ → ℝ) σ
    (fun _ => unitExponential) (fun _ => infiniteExponentials)
  exact (hq.comp hp).map_eq

theorem independentRenewalStreams_prepend_law :
    Measure.map (prependRenewalStreams (σ := σ))
      (independentExponentials.prod independentRenewalStreams) = independentRenewalStreams := by
  rw [← independentRenewalStreams_split_law,
    Measure.map_map measurable_prependRenewalStreams measurable_splitRenewalStreams]
  change Measure.map (fun z => prependRenewalStreams (splitRenewalStreams z)) _ = _
  simp only [prependRenewalStreams_split]
  exact Measure.map_id

end StochasticMatching
