import Matching.LoggedStreamExecution
import Matching.LastArrivalLog

/-! The final observed arrival counts equal the original renewal counts
pathwise on the almost-sure regular set. Termination is derived from the
finite renewal count, not assumed. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def renewalArrivalPath (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (T : PositiveHorizon) (z : σ → ℕ → ℝ) : ℕ → LoggedInputState σ :=
  residualObservedPath (loggedStreamStep c hc) (.inr (T, emptyArrivalMemory σ)) z

theorem measurable_renewalArrivalPath (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    Measurable (renewalArrivalPath c hc T) :=
  measurable_residualObservedPath _ (measurable_loggedStreamStep c hc) _

theorem loggedStream_terminal_bound (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (T : PositiveHorizon) (z : σ → ℕ → ℝ)
    (hz : ∀ s n, 0 ≤ z s n) (hunb : ∀ s, ∃ n, c s * T.1 < renewalPartialSum (z s) n)
    (hg : ∀ n, RenewalStreamGood (loggedStreamService c hc)
      ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z))) :
    renewalArrivalPath c hc T z ((∑ s, infiniteRenewalCount (c s * T.1) (z s)) + 1) = .inl () := by
  let M := ∑ s, infiniteRenewalCount (c s * T.1) (z s)
  cases he : renewalArrivalPath c hc T z (M + 1) with
  | inl u => cases u; rfl
  | inr y =>
    rcases y with ⟨b, m⟩
    have h := loggedStream_live_ledger c hc T z hg (M + 1) b m he
    have hle : (∑ s, arrivalMemoryCounts m s) ≤ M := by
      apply Finset.sum_le_sum
      intro s _
      exact h.2.1.count_le hc T.2.le (by linarith [b.2]) hz hunb s
    omega

theorem loggedStream_last_counts (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s)
    (T : PositiveHorizon) (z : σ → ℕ → ℝ)
    (hz : ∀ s n, 0 ≤ z s n) (hunb : ∀ s, ∃ n, c s * T.1 < renewalPartialSum (z s) n)
    (hg : ∀ n, RenewalStreamGood (loggedStreamService c hc)
      ((loggedStreamStep c hc)^[n] (.inr (T, emptyArrivalMemory σ), z))) :
    lastArrivalCounts (renewalArrivalPath c hc T z) =
      fun s => infiniteRenewalCount (c s * T.1) (z s) := by
  let w := renewalArrivalPath c hc T z
  let S : Set (LoggedInputState σ) := {a | a = .inl ()}
  let k := firstEntryTime S w
  have hex : ∃ n, w n ∈ S := ⟨_, loggedStream_terminal_bound c hc T z hz hunb hg⟩
  have hterm : w k = .inl () := firstEntryTime_spec S w hex
  have hk : 0 < k := by
    by_contra hk
    have he : k = 0 := by omega
    rw [he] at hterm
    cases hterm
  have hprev : w (k - 1) ≠ .inl () := by
    intro he
    have hle : k ≤ k - 1 := firstEntryTime_le S w he
    omega
  rcases hq : (loggedStreamStep c hc)^[k - 1] (.inr (T, emptyArrivalMemory σ), z) with ⟨a, r⟩
  have hw : w (k - 1) = a := congrArg Prod.fst hq
  cases a with
  | inl u => cases u; exact False.elim (hprev hw)
  | inr y =>
    rcases y with ⟨b, m⟩
    have hi := loggedStream_live_ledger c hc T z hg (k - 1) b m hw
    rw [hq] at hi
    have hgood := hg (k - 1)
    rw [hq] at hgood
    have hkstep : k - 1 + 1 = k := by omega
    have hstep : (loggedStreamStep c hc (.inr (b, m), r)).1 = .inl () := by
      change ((loggedStreamStep c hc)^[k] (.inr (T, emptyArrivalMemory σ), z)).1 = _ at hterm
      rw [← hkstep, Function.iterate_succ_apply', hq] at hterm
      exact hterm
    have ht : (fun i => r i 0) ∈ (constantRateCurve c hc b.1 b.2).terminalSurvival := by
      rcases hgood.2 with ht | ⟨j, hj⟩
      · exact ht
      · rw [loggedStreamStep_of_winner c hc b m r j hj] at hstep
        cases hstep
    have hcounts : ∀ s, infiniteRenewalCount (c s * T.1) (z s) = arrivalMemoryCounts m s := by
      apply hi.2.1.terminal_count hc T.2.le (by linarith [b.2]) hz
      intro s
      have hs : c s * b.1 < r s 0 := mem_univ_pi.mp ht s
      convert hs using 1 <;> ring
    change arrivalMemoryCounts (Sum.elim (fun _ => emptyArrivalMemory σ) Prod.snd (w (k - 1))) = _
    rw [hw]
    funext s
    exact (hcounts s).symm

theorem loggedStream_last_counts_ae (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    ∀ᵐ z ∂independentRenewalStreams,
      lastArrivalCounts (renewalArrivalPath c hc T z) =
        fun s => infiniteRenewalCount (c s * T.1) (z s) := by
  filter_upwards [independentRenewalStreams_all_pos (σ := σ),
    independentRenewalStreams_unbounded (σ := σ), loggedStreamStep_all_good c hc T] with z hp hu hg
  exact loggedStream_last_counts c hc T z (fun s n => (hp s n).le) (fun s => hu s _) hg

theorem renewalArrivalPath_terminates_ae (c : σ → ℝ) (hc : ∀ s, 0 ≤ c s) (T : PositiveHorizon) :
    ∀ᵐ z ∂independentRenewalStreams, ∃ n, renewalArrivalPath c hc T z n = .inl () := by
  filter_upwards [independentRenewalStreams_all_pos (σ := σ),
    independentRenewalStreams_unbounded (σ := σ), loggedStreamStep_all_good c hc T] with z hp hu hg
  exact ⟨_, loggedStream_terminal_bound c hc T z (fun s n => (hp s n).le) (fun s => hu s _) hg⟩

end StochasticMatching
