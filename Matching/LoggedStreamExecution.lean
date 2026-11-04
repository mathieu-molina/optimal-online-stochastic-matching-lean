import Matching.RenewalInputTrajectory
import Matching.ArrivalMemoryCounts
import Matching.RenewalStreamLedger
import Matching.RenewalStreamRegularity

/-! Pathwise invariants for the actual logged independent-stream execution. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

abbrev LoggedInputState (σ : Type*) := Unit ⊕ (PositiveHorizon × ArrivalMemory σ)

noncomputable def loggedStreamStep (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) :
    LoggedInputState σ × (σ → ℕ → ℝ) → LoggedInputState σ × (σ → ℕ → ℝ) :=
  stoppedStreamUpdate c hc (fun x : PositiveHorizon × ArrivalMemory σ => x.1.1)
    (measurable_subtype_coe.comp measurable_fst) (fun x => x.1.2)
    (loggedEventUpdate remainingTimeUpdate id)

def loggedStreamService (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) : HistoryServiceFamily (LoggedInputState σ) σ :=
  constantRateHistory c hc (stoppedInputHorizon (fun x : PositiveHorizon × ArrivalMemory σ => x.1.1))
    (measurable_stoppedInputHorizon _ (measurable_subtype_coe.comp measurable_fst))
    (stoppedInputHorizon_pos _ (fun x => x.1.2))

theorem measurable_loggedStreamStep (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) :
    Measurable (loggedStreamStep c hc) :=
  measurable_poissonStreamUpdate c hc _ _ _ _
    (measurable_stoppedEventUpdate _
      (measurable_loggedEventUpdate _ measurable_remainingTimeUpdate id measurable_id))

theorem loggedStreamStep_all_good (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    ∀ᵐ z ∂independentRenewalStreams, ∀ n, RenewalStreamGood (loggedStreamService c hc)
      ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z)) :=
  poissonStreamUpdate_all_good c hc _ _ _ _
    (measurable_stoppedEventUpdate _
      (measurable_loggedEventUpdate _ measurable_remainingTimeUpdate id measurable_id)) _

theorem loggedStreamStep_absorbing (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (u : Unit) (r : σ → ℕ → ℝ) : (loggedStreamStep c hc (.inl u, r)).1 = .inl () := rfl

theorem loggedStreamStep_live (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (b : PositiveHorizon) (m : ArrivalMemory σ) (r : σ → ℕ → ℝ) :
    loggedStreamStep c hc (.inr (b, m), r) =
      (loggedEventUpdate remainingTimeUpdate id ((b, m),
        ((constantRateCurve c hc b.1 b.2).streamNextEvent r).1),
        ((constantRateCurve c hc b.1 b.2).streamNextEvent r).2) := rfl

theorem loggedStreamStep_of_winner (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (b : PositiveHorizon) (m : ArrivalMemory σ) (r : σ → ℕ → ℝ) (j : σ)
    (hw : (fun i => r i 0) ∈ variableWinner (constantRateCurve c hc b.1 b.2).service b.1 j) :
    let p := constantRateCurve c hc b.1 b.2
    let u := cappedHit (p.service j) b.1 (r j 0)
    loggedStreamStep c hc (.inr (b, m), r) =
      (.inr (remainingTimeAfter (b, u), appendEvent (m, .inr (u, j))),
        (p.streamNextEvent r).2) := by
  intro p u
  rw [loggedStreamStep_live, p.streamNextEvent_fst, p.firstEvent_of_winner j hw]
  rfl

theorem loggedStreamStep_of_terminal (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (b : PositiveHorizon) (m : ArrivalMemory σ) (r : σ → ℕ → ℝ)
    (ht : (fun i => r i 0) ∈ (constantRateCurve c hc b.1 b.2).terminalSurvival) :
    (loggedStreamStep c hc (.inr (b, m), r)).1 = .inl () := by
  rw [loggedStreamStep_live, ServiceCurveFamily.streamNextEvent_fst,
    ServiceCurveFamily.firstEvent_of_terminal _ ht]
  rfl

theorem loggedStream_live_ledger (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (T : PositiveHorizon) (z : σ → ℕ → ℝ)
    (hg : ∀ n, RenewalStreamGood (loggedStreamService c hc)
      ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z)))
    (n : ℕ) (b : PositiveHorizon) (m : ArrivalMemory σ)
    (he : ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z)).1 = .inr (b, m)) :
    b.1 ≤ T.1 ∧
      RenewalStreamLedger c z (T.1 - b.1) (arrivalMemoryCounts m)
        ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z)).2 ∧
      (∑ s, arrivalMemoryCounts m s) = n := by
  induction n generalizing b m with
  | zero =>
    have he' : T = b ∧ emptyArrivalMemory σ = m := by simpa using he
    rcases he' with ⟨rfl, rfl⟩
    simp only [Function.iterate_zero, id_eq, sub_self, arrivalMemoryCounts_empty]
    exact ⟨le_rfl, renewalStreamLedger_initial c z, by simp⟩
  | succ n ih =>
    rcases hq : (loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z) with ⟨a, r⟩
    rw [Function.iterate_succ_apply', hq] at he ⊢
    cases a with
    | inl u =>
      rw [loggedStreamStep_absorbing] at he
      cases he
    | inr y =>
      rcases y with ⟨b0, m0⟩
      have hi := ih b0 m0 (by rw [hq])
      rw [hq] at hi
      have hgood := hg n
      rw [hq] at hgood
      rcases hgood.2 with ht | ⟨j, hw⟩
      · rw [loggedStreamStep_of_terminal c hc b0 m0 r ht] at he
        cases he
      · let p := constantRateCurve c hc b0.1 b0.2
        let u := cappedHit (p.service j) b0.1 (r j 0)
        have hu : 0 ≤ u := (cappedHit_bounds (z := r j 0) (p.service_continuous j) b0.2.le).1
        have hut : u < b0.1 := hw.1
        have hb : (remainingTimeAfter (b0, u)).1 = b0.1 - u := if_pos ⟨hu, hut⟩
        have hs := loggedStreamStep_of_winner c hc b0 m0 r j hw
        change loggedStreamStep c hc (.inr (b0, m0), r) =
          (.inr (remainingTimeAfter (b0, u), appendEvent (m0, .inr (u, j))),
            (p.streamNextEvent r).2) at hs
        rw [hs] at he ⊢
        have he' : remainingTimeAfter (b0, u) = b ∧ appendEvent (m0, .inr (u, j)) = m := by
          simpa using he
        rcases he' with ⟨rfl, rfl⟩
        refine ⟨by rw [hb]; linarith [hi.1], ?_, ?_⟩
        · rw [hb, arrivalMemoryCounts_append_arrival]
          have hl := hi.2.1.winner hc b0.2 j (hgood.1 j) hw
          convert hl using 1 <;> ring
        · rw [arrivalMemoryCounts_append_total, hi.2.2]

end StochasticMatching
