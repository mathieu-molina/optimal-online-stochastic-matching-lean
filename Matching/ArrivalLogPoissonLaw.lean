import Matching.LoggedStreamCounts

/-! The type counts read from the actual stopped input log have exactly the
independent Poisson law used by the offline matching benchmark. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def horizonIntensity (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) (s : σ) : ℝ≥0 :=
  ⟨c s * T.1, mul_nonneg (hc s) T.2.le⟩

theorem renewalArrivalPath_law (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    Measure.map (renewalArrivalPath c hc T) independentRenewalStreams =
      loggedInputTrajectory c hc Subtype.val measurable_subtype_coe (fun b => b.2)
        (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate (T, emptyArrivalMemory σ) :=
  loggedIndependentStreamPath_law c hc Subtype.val measurable_subtype_coe (fun b => b.2)
    remainingTimeUpdate measurable_remainingTimeUpdate (T, emptyArrivalMemory σ)

theorem renewalArrivalPath_counts_law (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    Measure.map (fun z => lastArrivalCounts (renewalArrivalPath c hc T z)) independentRenewalStreams =
      independentPoissons (horizonIntensity c hc T) := by
  rw [Measure.map_congr (loggedStream_last_counts_ae c hc T)]
  exact renewalTypeCounts_poisson_law (horizonIntensity c hc T)

theorem loggedInputTrajectory_counts_law (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    Measure.map lastArrivalCounts
      (loggedInputTrajectory c hc Subtype.val measurable_subtype_coe (fun b => b.2)
        (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate (T, emptyArrivalMemory σ)) =
      independentPoissons (horizonIntensity c hc T) := by
  rw [← renewalArrivalPath_law c hc T,
    Measure.map_map measurable_lastArrivalCounts (measurable_renewalArrivalPath c hc T)]
  exact renewalArrivalPath_counts_law c hc T

theorem loggedInputTrajectory_unit_counts_law (a : σ → ℝ≥0) :
    Measure.map lastArrivalCounts
      (loggedInputTrajectory (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
        Subtype.val measurable_subtype_coe (fun b => b.2)
        (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate
        ((⟨1, zero_lt_one⟩ : PositiveHorizon), emptyArrivalMemory σ)) = independentPoissons a := by
  have h := loggedInputTrajectory_counts_law (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    (⟨1, zero_lt_one⟩ : PositiveHorizon)
  have he : horizonIntensity (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
      (⟨1, zero_lt_one⟩ : PositiveHorizon) = a := by
    funext s
    apply Subtype.ext
    exact mul_one _
  rw [he] at h
  exact h

end StochasticMatching

namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem loggedTrajectory_counts_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c)) (x : RoutingCursor n H ι) :
    Measure.map lastArrivalCounts
      (s.loggedTrajectory n label N c hc hmem (x, emptyArrivalMemory σ)) =
      independentPoissons (horizonIntensity c hc (s.cursorHorizon n label x)) := by
  have h := congrArg (Measure.map (lastArrivalCounts (A := PositiveHorizon) (σ := σ)))
    (s.loggedTrajectory_input_law n label N c hc hmem (x, emptyArrivalMemory σ))
  have hf : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
      fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2)) (z k)) := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_id.sumMap ((s.measurable_cursorHorizon n label).prodMap measurable_id)).comp
      (measurable_pi_apply k)
  rw [Measure.map_map measurable_lastArrivalCounts hf, loggedInputTrajectory_counts_law] at h
  simpa only [Function.comp_def, lastArrivalCounts_map] using h

end StochasticMatching.PosteriorStage
