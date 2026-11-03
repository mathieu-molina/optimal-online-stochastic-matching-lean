import Matching.RenewalStreamRestart

/-! Pathwise meaning of the stream restart: consume the winner's first
waiting amount, subtract service from surviving heads, and leave every
unread future amount unchanged. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching.ServiceCurveFamily
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem streamNextEvent_fst (p : ServiceCurveFamily σ) (z : σ → ℕ → ℝ) :
    (p.streamNextEvent z).1 = p.firstEvent (fun i => z i 0) := by
  classical
  by_cases hz : ∃ j, (fun i => z i 0) ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hz
    rw [streamNextEvent, p.renewalRestart_of_winner j hj, p.firstEvent_of_winner j hj]
    rfl
  · have hn := not_exists.mp hz
    have hn' : ∀ j, splitRenewalStreams z ∉
        (Prod.fst ⁻¹' variableWinner p.service p.deadline j) := hn
    rw [streamNextEvent, renewalRestart, firstEvent,
      branchSelect_of_not_mem _ _ hn', branchSelect_of_not_mem _ _ hn]

theorem streamNextEvent_winner_stream (p : ServiceCurveFamily σ) (j : σ)
    {z : σ → ℕ → ℝ} (hz : (fun i => z i 0) ∈ variableWinner p.service p.deadline j) :
    (p.streamNextEvent z).2 j = fun n => z j (n + 1) := by
  rw [streamNextEvent, p.renewalRestart_of_winner j hz]
  exact replenishRenewalStreams_winner j _

theorem streamNextEvent_survivor_stream (p : ServiceCurveFamily σ) (j i : σ) (hi : i ≠ j)
    {z : σ → ℕ → ℝ} (hz : (fun i => z i 0) ∈ variableWinner p.service p.deadline j) :
    (p.streamNextEvent z).2 i = prependWaiting
      (z i 0 - p.service i (cappedHit (p.service j) p.deadline (z j 0)), fun n => z i (n + 1)) := by
  rw [streamNextEvent, p.renewalRestart_of_winner j hz]
  exact replenishRenewalStreams_survivor j i hi _

theorem streamNextEvent_survivor_head (p : ServiceCurveFamily σ) (j i : σ) (hi : i ≠ j)
    {z : σ → ℕ → ℝ} (hz : (fun i => z i 0) ∈ variableWinner p.service p.deadline j) :
    (p.streamNextEvent z).2 i 0 =
      z i 0 - p.service i (cappedHit (p.service j) p.deadline (z j 0)) := by
  rw [p.streamNextEvent_survivor_stream j i hi hz]
  rfl

theorem streamNextEvent_survivor_tail (p : ServiceCurveFamily σ) (j i : σ) (hi : i ≠ j)
    {z : σ → ℕ → ℝ} (hz : (fun i => z i 0) ∈ variableWinner p.service p.deadline j) (n : ℕ) :
    (p.streamNextEvent z).2 i (n + 1) = z i (n + 1) := by
  rw [p.streamNextEvent_survivor_stream j i hi hz]
  rfl

theorem streamNextEvent_terminal_stream (p : ServiceCurveFamily σ)
    {z : σ → ℕ → ℝ} (hz : (fun i => z i 0) ∈ p.terminalSurvival) (i : σ) :
    (p.streamNextEvent z).2 i =
      prependWaiting (z i 0 - p.service i p.deadline, fun n => z i (n + 1)) := by
  rw [streamNextEvent, p.renewalRestart_of_terminal hz]
  rfl

end StochasticMatching.ServiceCurveFamily
