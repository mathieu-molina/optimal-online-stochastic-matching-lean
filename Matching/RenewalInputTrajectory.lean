import Matching.HistoryRenewalStreams
import Matching.StoppedResidualCoupling
import Matching.PosteriorLoggedInput

/-! Identify the complete typed arrival-only trajectory with a deterministic
execution of independent renewal streams, including absorbing termination.
The equality is on infinite trajectories, not just individual marginals. -/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {B : Type*} [MeasurableSpace B]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def stoppedInputHorizon (D : B → ℝ) : Unit ⊕ B → ℝ := Sum.elim (fun _ => 1) D

theorem measurable_stoppedInputHorizon (D : B → ℝ) (hD : Measurable D) :
    Measurable (stoppedInputHorizon D) := measurable_const.sumElim hD

theorem stoppedInputHorizon_pos (D : B → ℝ) (hpos : ∀ b, 0 < D b) :
    ∀ b, 0 < stoppedInputHorizon D b := by
  intro b
  cases b with
  | inl _ => exact zero_lt_one
  | inr b => exact hpos b

/-- The observed terminal state is absorbing. Its dummy positive horizon
only updates the latent streams, keeping the residual-law invariant total. -/
noncomputable def stoppedStreamUpdate (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) :
    (Unit ⊕ B) × (σ → ℕ → ℝ) → (Unit ⊕ B) × (σ → ℕ → ℝ) :=
  poissonStreamUpdate capacity hc (stoppedInputHorizon D)
    (measurable_stoppedInputHorizon D hD) (stoppedInputHorizon_pos D hpos) (stoppedEventUpdate V)

theorem stoppedPoissonStateKernel_eq (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V) :
    poissonStateKernel capacity hc (stoppedInputHorizon D)
      (measurable_stoppedInputHorizon D hD) (stoppedInputHorizon_pos D hpos) (stoppedEventUpdate V) =
      absorbingKernel (inputTransition capacity hc D hD hpos V) := by
  letI := poissonInputKernel_markov capacity hc (stoppedInputHorizon D)
    (measurable_stoppedInputHorizon D hD) (stoppedInputHorizon_pos D hpos)
  letI := poissonInputKernel_markov capacity hc D hD hpos
  ext b : 1
  cases b with
  | inl u =>
      letI := poissonNextArrival_probability capacity hc 1 zero_lt_one
      change eventUpdateKernel _ (stoppedEventUpdate V) (.inl u) = Measure.dirac (.inl ())
      rw [eventUpdateKernel_apply _ _ (measurable_stoppedEventUpdate V hV)]
      change Measure.map (fun _ => (Sum.inl () : Unit ⊕ B)) (poissonNextArrival capacity 1) = _
      rw [Measure.map_const, measure_univ, one_smul]
  | inr b =>
      change eventUpdateKernel _ (stoppedEventUpdate V) (.inr b) = eventUpdateKernel _ V b
      rw [eventUpdateKernel_apply _ _ (measurable_stoppedEventUpdate V hV),
        eventUpdateKernel_apply _ V hV]
      rfl

noncomputable def independentStreamInputPath (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (b : B) :
    (σ → ℕ → ℝ) → ℕ → Unit ⊕ B :=
  residualObservedPath (stoppedStreamUpdate capacity hc D hD hpos V) (.inr b)

theorem independentStreamInputPath_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V) (b : B) :
    Measure.map (independentStreamInputPath capacity hc D hD hpos V b) independentRenewalStreams =
      poissonInputTrajectory capacity hc D hD hpos V hV b := by
  letI := inputTransition_markov capacity hc D hD hpos V hV
  letI := poissonStateKernel_markov capacity hc (stoppedInputHorizon D)
    (measurable_stoppedInputHorizon D hD) (stoppedInputHorizon_pos D hpos)
    (stoppedEventUpdate V) (measurable_stoppedEventUpdate V hV)
  have h := poissonStreamUpdate_trajectory_law capacity hc (stoppedInputHorizon D)
    (measurable_stoppedInputHorizon D hD) (stoppedInputHorizon_pos D hpos)
    (stoppedEventUpdate V) (measurable_stoppedEventUpdate V hV) (.inr b)
  exact h.trans (markovTrajectory_congr _ _
    (stoppedPoissonStateKernel_eq capacity hc D hD hpos V hV) (.inr b))

noncomputable def loggedIndependentStreamPath (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V)
    (x : B × ArrivalMemory σ) : (σ → ℕ → ℝ) → ℕ → Unit ⊕ (B × ArrivalMemory σ) :=
  independentStreamInputPath capacity hc (fun x : B × ArrivalMemory σ => D x.1)
    (hD.comp measurable_fst) (fun x => hpos x.1) (loggedEventUpdate V id) x

theorem loggedIndependentStreamPath_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b)
    (V : B × (Unit ⊕ (ℝ × σ)) → Unit ⊕ B) (hV : Measurable V)
    (x : B × ArrivalMemory σ) :
    Measure.map (loggedIndependentStreamPath capacity hc D hD hpos V hV x) independentRenewalStreams =
      loggedInputTrajectory capacity hc D hD hpos V hV x :=
  independentStreamInputPath_law capacity hc (fun x : B × ArrivalMemory σ => D x.1)
    (hD.comp measurable_fst) (fun x => hpos x.1) (loggedEventUpdate V id)
    (measurable_loggedEventUpdate V hV id measurable_id) x

end StochasticMatching

namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem loggedTrajectory_renewal_input_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι × ArrivalMemory σ) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
        fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2)) (z k))
      (s.loggedTrajectory n label N capacity hc hmem x) =
      Measure.map (loggedIndependentStreamPath capacity hc Subtype.val measurable_subtype_coe
        (fun b => b.2) (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate
        (s.cursorHorizon n label x.1, x.2)) independentRenewalStreams := by
  rw [s.loggedTrajectory_input_law, loggedIndependentStreamPath_law]

end StochasticMatching.PosteriorStage
