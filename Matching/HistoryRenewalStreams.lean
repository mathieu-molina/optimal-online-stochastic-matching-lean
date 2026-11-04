import Matching.RenewalStreamRestart
import Matching.HistoryOneStep
import Matching.DeterministicResidualTrajectory
import Matching.FiniteRoutingLaw

/-! Measurable history-dependent renewal restarts and their repeated law.
The entire latent input is sampled once, and subsequent transitions are
deterministic functions of it and the observed state. -/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {H : Type*} [MeasurableSpace H]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def historyStreamNextEvent (p : HistoryServiceFamily H σ)
    (x : H × (σ → ℕ → ℝ)) : (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ) :=
  (p.curves x.1).streamNextEvent x.2

theorem measurable_historyStreamNextEvent (p : HistoryServiceFamily H σ) :
    Measurable (historyStreamNextEvent p) := by
  let v : H × (σ → ℕ → ℝ) → H × (σ → ℝ) := fun x => (x.1, fun i => x.2 i 0)
  have hv : Measurable v := by
    apply Measurable.prodMk measurable_fst
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (0 : ℕ)).comp ((measurable_pi_apply i).comp measurable_snd)
  let w : H × (σ → ℕ → ℝ) → σ → ℕ → ℝ := fun x i n => x.2 i (n + 1)
  have hw : Measurable w := measurable_pi_lambda _ (fun i : σ => measurable_pi_lambda _
    (fun n : ℕ => (measurable_pi_apply (n + 1)).comp ((measurable_pi_apply i).comp measurable_snd)))
  let F : σ → H × (σ → ℕ → ℝ) → (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ) := fun j x =>
    (Sum.inr (p.clock j (v x), j), replenishRenewalStreams j ((p.observation j (v x)).2, w x))
  let G : H × (σ → ℕ → ℝ) → (Unit ⊕ (ℝ × σ)) × (σ → ℕ → ℝ) := fun x =>
    (Sum.inl (), prependRenewalStreams ((fun i => x.2 i 0 - p.terminalThreshold x.1 i), w x))
  have he : historyStreamNextEvent p = branchSelect (fun j => v ⁻¹' p.winner j) F G := rfl
  rw [he]
  apply measurable_branchSelect
    (fun i j hij => (p.winner_disjoint hij).preimage v) (fun j => hv (p.measurable_winner j))
  · intro j
    exact (measurable_inr.comp (((p.measurable_clock j).comp hv).prodMk measurable_const)).prodMk
      ((measurable_replenishRenewalStreams j).comp
        (((p.measurable_observation j).snd.comp hv).prodMk hw))
  · apply Measurable.prodMk measurable_const
    apply measurable_prependRenewalStreams.comp
    apply Measurable.prodMk _ hw
    exact measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp hv.snd).sub
        (((measurable_pi_apply i).comp p.measurable_terminalThreshold).comp measurable_fst))

def constantRateHistory (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h) : HistoryServiceFamily H σ where
  curves h := constantRateCurve capacity hc (D h) (hpos h)
  deadline_measurable := hD
  service_at_measurable _ _ := measurable_const
  rate_at_measurable _ _ := measurable_const

noncomputable def poissonStreamUpdate (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (x : H × (σ → ℕ → ℝ)) : H × (σ → ℕ → ℝ) :=
  let q := historyStreamNextEvent (constantRateHistory capacity hc D hD hpos) x
  (U (x.1, q.1), q.2)

theorem measurable_poissonStreamUpdate (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) :
    Measurable (poissonStreamUpdate capacity hc D hD hpos U) := by
  have hq := measurable_historyStreamNextEvent (constantRateHistory capacity hc D hD hpos)
  exact (hU.comp (measurable_fst.prodMk hq.fst)).prodMk hq.snd

theorem poissonStateKernel_markov (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) :
    IsMarkovKernel (poissonStateKernel capacity hc D hD hpos U) := by
  letI := poissonInputKernel_markov capacity hc D hD hpos
  exact eventUpdateKernel_markov _ U hU

theorem poissonStreamUpdate_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) (h : H) :
    Measure.map (fun z => poissonStreamUpdate capacity hc D hD hpos U (h, z))
      independentRenewalStreams =
      (poissonStateKernel capacity hc D hD hpos U h).prod
        (independentRenewalStreams (σ := σ)) := by
  letI := poissonInputKernel_markov capacity hc D hD hpos
  letI := poissonNextArrival_probability capacity hc (D h) (hpos h)
  have hu : Measurable (fun e => U (h, e)) := hU.comp measurable_prodMk_left
  have hp := poisson_stream_next_event_law capacity hc (D h) (hpos h)
  have hm := Measure.map_prod_map (poissonNextArrival capacity (D h))
    (independentRenewalStreams (σ := σ)) hu measurable_id
  rw [Measure.map_id, ← hp,
    Measure.map_map (hu.prodMap measurable_id)
      (ServiceCurveFamily.measurable_streamNextEvent _)] at hm
  change _ = (eventUpdateKernel (poissonInputKernel capacity D hD) U h).prod _
  rw [eventUpdateKernel_apply _ U hU]
  exact hm.symm

theorem poissonStreamUpdate_iterate_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) (n : ℕ) (h : H) :
    Measure.map (fun z => (poissonStreamUpdate capacity hc D hD hpos U)^[n] (h, z))
      independentRenewalStreams =
      (iterateKernel (poissonStateKernel capacity hc D hD hpos U) n h).prod
        (independentRenewalStreams (σ := σ)) :=
  deterministicResidual_iterate_law _ _
    (measurable_poissonStreamUpdate capacity hc D hD hpos U hU) _
    (poissonStreamUpdate_law capacity hc D hD hpos U hU) n h

theorem poissonStreamUpdate_trajectory_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : H → ℝ) (hD : Measurable D) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × σ)) → H) (hU : Measurable U) (h : H) :
    letI := poissonStateKernel_markov capacity hc D hD hpos U hU
    Measure.map (residualObservedPath (poissonStreamUpdate capacity hc D hD hpos U) h)
      independentRenewalStreams = markovTrajectory (poissonStateKernel capacity hc D hD hpos U) h := by
  letI := poissonStateKernel_markov capacity hc D hD hpos U hU
  exact deterministicResidual_trajectory_law _ _
    (measurable_poissonStreamUpdate capacity hc D hD hpos U hU) _
    (poissonStreamUpdate_law capacity hc D hD hpos U hU) h

end StochasticMatching
