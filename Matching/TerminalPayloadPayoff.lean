import Matching.LastLiveObservation
import Matching.TerminalPayloadProjection

/-! A terminal payload stores the observation of the preceding live state.
Thus a measurable real payoff of the stopped payload can also be read from
the last live state of the trajectory that forgets terminal payloads. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

def terminalPayoffStep (V : E ⊕ A → ℝ) : Set ((E ⊕ A) × (E ⊕ A)) :=
  {p | p.1 ∈ Set.range Sum.inr → p.2 ∈ Set.range Sum.inl → V p.2 = V p.1}

theorem measurableSet_terminalPayoffStep (V : E ⊕ A → ℝ) (hV : Measurable V) :
    MeasurableSet (terminalPayoffStep V) :=
  ((measurableSet_range_inr.preimage measurable_fst).mem.imp
    ((measurableSet_range_inl.preimage measurable_snd).mem.imp
      (measurableSet_eq_fun (hV.comp measurable_snd) (hV.comp measurable_fst)).mem)).setOf

theorem terminalPayload_lastLive_payoff_path (O : A → E) (g : E → ℝ) (d : ℝ)
    (z : ℕ → E ⊕ A) (hzero : z 0 ∈ Set.range Sum.inr)
    (hterm : ∃ k, z k ∈ Set.range Sum.inl)
    (hstep : ∀ k, (z k, z (k + 1)) ∈ terminalPayoffStep (Sum.elim g (g ∘ O))) :
    lastLiveObservation (g ∘ O) d (fun k => forgetTerminal (z k)) =
      stoppedOutput (Set.range Sum.inl) (Sum.elim g (g ∘ O)) z := by
  let m := firstEntryTime (Set.range (Sum.inl : E → E ⊕ A)) z
  have hm : z m ∈ Set.range Sum.inl := firstEntryTime_spec _ z hterm
  have hmpos : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    obtain ⟨a, ha⟩ := hzero
    rw [hm0, ← ha] at hm
    simpa using hm
  have htime : m = firstEntryTime {a | a = .inl ()} (fun k => forgetTerminal (z k)) := by
    apply firstEntryTime_eq_of_membership
    intro k
    cases hk : z k <;> simp [forgetTerminal, hk]
  cases hprev : z (m - 1) with
  | inl e =>
    have hle : m ≤ m - 1 := firstEntryTime_le (Set.range Sum.inl) z ⟨e, hprev.symm⟩
    omega
  | inr a =>
    have hnext : m - 1 + 1 = m := by omega
    have hpay := hstep (m - 1) ⟨a, hprev.symm⟩
    rw [hnext] at hpay
    have heq := hpay hm
    change Sum.elim g (g ∘ O) (z m) = Sum.elim g (g ∘ O) (z (m - 1)) at heq
    rw [hprev] at heq
    unfold lastLiveObservation stoppedOutput
    rw [← htime]
    change Sum.elim (fun _ => d) (g ∘ O) (forgetTerminal (z (m - 1))) = _
    rw [hprev]
    exact heq.symm

theorem terminalPayload_lastLive_payoff_ae (K : Kernel (E ⊕ A) (E ⊕ A)) [IsMarkovKernel K]
    (L : Kernel A (Unit ⊕ A)) (O : A → E) (hO : Measurable O)
    (g : E → ℝ) (hg : Measurable g) (d : ℝ) (a : A)
    (hlive : ∀ x, K (.inr x) = Measure.map (fun u => fillTerminal (O x, u)) (L x))
    (hterm : ∀ᵐ z ∂markovTrajectory K (.inr a), ∃ k, z k ∈ Set.range Sum.inl) :
    ∀ᵐ z ∂markovTrajectory K (.inr a),
      lastLiveObservation (g ∘ O) d (fun k => forgetTerminal (z k)) =
        stoppedOutput (Set.range Sum.inl) (Sum.elim g (g ∘ O)) z := by
  let V := Sum.elim g (g ∘ O)
  have hV : Measurable V := hg.sumElim (hg.comp hO)
  have hR := measurableSet_terminalPayoffStep V hV
  have hstep : ∀ b, ∀ᵐ y ∂K b, (b, y) ∈ terminalPayoffStep V := by
    intro b
    cases b with
    | inl e =>
      exact Filter.Eventually.of_forall (fun y h => by simpa using h)
    | inr x =>
      rw [hlive x]
      have hf : Measurable (fun u : Unit ⊕ A => fillTerminal (O x, u)) :=
        measurable_fillTerminal.comp (measurable_const.prodMk measurable_id)
      apply (ae_map_iff hf.aemeasurable
        (hR.preimage (measurable_const.prodMk measurable_id))).mpr
      exact Filter.Eventually.of_forall (fun u _ h => by
        cases u with
        | inl q => rfl
        | inr y => simpa [fillTerminal] using h)
  filter_upwards [markovTrajectory_initial_mem K (.inr a) (Set.range Sum.inr)
    measurableSet_range_inr ⟨a, rfl⟩, hterm,
    markovTrajectory_all_steps_support K _ hR hstep (.inr a)] with z hzero hz hs
  exact terminalPayload_lastLive_payoff_path O g d z hzero hz hs

end StochasticMatching
