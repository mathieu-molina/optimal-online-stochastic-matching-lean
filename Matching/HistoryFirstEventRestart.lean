import Matching.FirstEventRestart
import Matching.HistoryOneStep
import Matching.StoppedKernel

/-! The fixed-coordinate event/residual restart is jointly measurable in
an adaptive history. Updating the history preserves fresh independent
residuals, with the history law determined by the first-event kernel.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ProbabilityTheory
namespace StochasticMatching
variable {H B ι : Type*} [MeasurableSpace H] [MeasurableSpace B]
  [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

theorem firstEventRestart_fst (p : ServiceCurveFamily (Option ι)) (z : Option ι → ℝ) :
    (firstEventRestart p z).1 = p.firstEvent z := by
  classical
  by_cases hz : ∃ j, z ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hz
    rw [firstEventRestart_of_winner p j hj, p.firstEvent_of_winner j hj]
    rfl
  · have hn := not_exists.mp hz
    rw [firstEventRestart, ServiceCurveFamily.firstEvent,
      branchSelect_of_not_mem _ _ hn, branchSelect_of_not_mem _ _ hn]

noncomputable def historyRestart (p : HistoryServiceFamily H (Option ι))
    (x : H × (Option ι → ℝ)) : (Unit ⊕ (ℝ × Option ι)) × (ι → ℝ) :=
  firstEventRestart (p.curves x.1) x.2

theorem measurable_historyRestart (p : HistoryServiceFamily H (Option ι)) :
    Measurable (historyRestart p) := by
  let F : Option ι → H × (Option ι → ℝ) → (Unit ⊕ (ℝ × Option ι)) × (ι → ℝ) :=
    fun j x => (Sum.inr (p.clock j x, j),
      fun i => x.2 (survivorSlot j i).val - (p.curves x.1).service (survivorSlot j i).val (p.clock j x))
  let G : H × (Option ι → ℝ) → (Unit ⊕ (ℝ × Option ι)) × (ι → ℝ) :=
    fun x => (Sum.inl (), fun i => x.2 (some i) - p.terminalThreshold x.1 (some i))
  have he : historyRestart p = branchSelect p.winner F G := rfl
  rw [he]
  apply measurable_branchSelect p.winner_disjoint p.measurable_winner
  · intro j
    apply Measurable.prodMk
    · exact measurable_inr.comp ((p.measurable_clock j).prodMk measurable_const)
    · apply measurable_pi_lambda
      intro i
      exact ((measurable_pi_apply (survivorSlot j i).val).comp measurable_snd).sub
        ((p.measurable_service (survivorSlot j i).val).comp
          (measurable_fst.prodMk (p.measurable_clock j)))
  · apply Measurable.prodMk measurable_const
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply (some i)).comp measurable_snd).sub
      (((measurable_pi_apply (some i)).comp p.measurable_terminalThreshold).comp measurable_fst)

noncomputable def historyEventKernel (p : HistoryServiceFamily H (Option ι)) :
    Kernel H (Unit ⊕ (ℝ × Option ι)) :=
  eventUpdateKernel (Kernel.const H (independentExponentials (ι := Option ι)))
    (fun x => (historyRestart p x).1)

instance historyEventKernel_markov (p : HistoryServiceFamily H (Option ι)) :
    IsMarkovKernel (historyEventKernel p) :=
  eventUpdateKernel_markov _ _ (measurable_historyRestart p).fst

theorem historyEventKernel_apply (p : HistoryServiceFamily H (Option ι)) (h : H) :
    historyEventKernel p h = Measure.map (p.curves h).firstEvent independentExponentials := by
  rw [historyEventKernel, eventUpdateKernel_apply _ _ (measurable_historyRestart p).fst]
  congr 1
  funext z
  exact firstEventRestart_fst (p.curves h) z

theorem historyRestart_update_law (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → B) (hU : Measurable U) (h : H) :
    Measure.map (fun z : Option ι → ℝ =>
      (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2)) independentExponentials =
      (eventUpdateKernel (historyEventKernel p) U h).prod (independentExponentials (ι := ι)) := by
  have hu : Measurable (fun e => U (h, e)) := hU.comp measurable_prodMk_left
  have hp := firstEventRestart_law (p.curves h)
  have hmap := Measure.map_prod_map (Measure.map (p.curves h).firstEvent independentExponentials)
    (independentExponentials (ι := ι)) hu measurable_id
  rw [Measure.map_id, ← hp, Measure.map_map (hu.prodMap measurable_id)
    (measurable_firstEventRestart (p.curves h))] at hmap
  rw [eventUpdateKernel_apply _ U hU, historyEventKernel_apply]
  exact hmap.symm

end StochasticMatching
