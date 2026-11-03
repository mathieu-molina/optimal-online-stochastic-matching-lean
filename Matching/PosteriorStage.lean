import Matching.RestartPosterior

/-! Posterior-policy stage data and its measurable restart. The next deadline
agrees with the true remaining time on every winner event; a positive fallback
makes the construction total on histories that cannot arise on that branch.
-/

open MeasureTheory Set
open scoped NNReal

namespace StochasticMatching

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

noncomputable def remainingDeadline (T : ℝ≥0) (D : H → ℝ) (h : H × ℝ) : ℝ := by
  classical
  exact if 0 < D h.1 - h.2 ∧ D h.1 - h.2 ≤ T then D h.1 - h.2 else T

theorem measurable_remainingDeadline (T : ℝ≥0) {D : H → ℝ} (hD : Measurable D) :
    Measurable (remainingDeadline T D) := by
  have hd : Measurable (fun h : H × ℝ => D h.1 - h.2) :=
    (hD.comp measurable_fst).sub measurable_snd
  exact Measurable.ite ((measurableSet_lt measurable_const hd).inter
    (measurableSet_le hd measurable_const)) hd measurable_const

theorem remainingDeadline_pos (T : ℝ≥0) (hT : 0 < (T : ℝ)) (D : H → ℝ) (h : H × ℝ) :
    0 < remainingDeadline T D h := by
  classical
  unfold remainingDeadline
  split_ifs with hc
  · exact hc.1
  · exact hT

theorem remainingDeadline_le (T : ℝ≥0) (D : H → ℝ) (h : H × ℝ) :
    remainingDeadline T D h ≤ T := by
  classical
  unfold remainingDeadline
  split_ifs with hc
  · exact hc.2
  · exact le_refl _

theorem remainingDeadline_eq (T : ℝ≥0) (D : H → ℝ) (h : H × ℝ)
    (ht : 0 ≤ h.2) (htD : h.2 < D h.1) (hDT : D h.1 ≤ T) :
    remainingDeadline T D h = D h.1 - h.2 := by
  classical
  exact if_pos ⟨sub_pos.mpr htD, (sub_le_self _ ht).trans hDT⟩

structure PosteriorStage (H ι : Type*) [MeasurableSpace H] where
  data : PosteriorData H ι
  initial : H → (ι → ℝ)
  measurable_initial : Measurable initial
  horizon : ℝ≥0
  horizon_pos : 0 < (horizon : ℝ)
  deadline : H → ℝ
  measurable_deadline : Measurable deadline
  deadline_pos : ∀ h, 0 < deadline h
  deadline_le : ∀ h, deadline h ≤ horizon

namespace PosteriorStage

variable (s : PosteriorStage H ι)

noncomputable def service : HistoryServiceFamily H ι :=
  s.data.historyService s.measurable_initial s.horizon s.measurable_deadline
    s.deadline_pos s.deadline_le

noncomputable def next (j : ι) : PosteriorStage (H × ℝ) {i : ι // i ≠ j} where
  data := s.data.restartData s.service s.measurable_initial j
  initial := PosteriorData.restartInitial s.service s.initial j
  measurable_initial := PosteriorData.measurable_restartInitial s.service s.measurable_initial j
  horizon := s.horizon
  horizon_pos := s.horizon_pos
  deadline := remainingDeadline s.horizon s.deadline
  measurable_deadline := measurable_remainingDeadline s.horizon s.measurable_deadline
  deadline_pos := remainingDeadline_pos s.horizon s.horizon_pos s.deadline
  deadline_le := remainingDeadline_le s.horizon s.deadline

theorem next_deadline_on_winner {j : ι} {x : H × (ι → ℝ)}
    (hx : x ∈ s.service.winner j) :
    (s.next j).deadline (x.1, s.service.clock j x) =
      s.deadline x.1 - s.service.clock j x := by
  apply remainingDeadline_eq
  · exact (cappedHit_bounds ((s.service.curves x.1).service_continuous j)
      (s.service.curves x.1).deadline_pos.le).1
  · exact hx.1
  · exact s.deadline_le x.1

theorem next_rate_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    (j : ι) (i : {i : ι // i ≠ j}) :
    (fun x : H × (ι → ℝ) => posteriorRate (s.next j).data.allocation
      (x.1, s.service.clock j x) ((s.next j).initial (x.1, s.service.clock j x)) i)
      =ᵐ[(ν.prod independentExponentials).restrict (s.service.winner j)]
    ((ν.prod independentExponentials).restrict (s.service.winner j))[
      fun x => s.data.allocation (x.1, s.initial x.1 + x.2) i.1 |
      (inferInstance : MeasurableSpace (H × ℝ)).comap
        (fun x => (x.1, s.service.clock j x))] :=
  s.data.restart_rate_conditionalExpectation s.service ν j s.measurable_initial i

end PosteriorStage
end StochasticMatching
