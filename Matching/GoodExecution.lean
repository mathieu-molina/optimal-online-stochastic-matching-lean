import Matching.PosteriorTrace
import Matching.ServiceExecution

/-! Almost-sure validity of every recursive branch: incoming active residuals
are positive, and each nonterminal stage has a genuine unique winner. The
property is propagated through the actual observation map on one sample space.
-/

open MeasureTheory Set

namespace StochasticMatching.PosteriorStage

universe u v

def GoodExecution : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    PosteriorStage H ι → H × (ι → ℝ) → Prop
  | 0, _, _, _, _, _, _, x => ∀ i, 0 < x.2 i
  | n + 1, _, _, _, _, _, s, x => (∀ i, 0 < x.2 i) ∧
      (x ∈ s.service.terminalEvent ∨ ∃ j, x ∈ s.service.winner j ∧
        GoodExecution n (s.next j) (s.service.observation j x))

variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem goodExecution_ae (n : ℕ) (s : PosteriorStage H ι) (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, GoodExecution n s x := by
  induction n generalizing H ι with
  | zero =>
    have hm : MeasurableSet {x : H × (ι → ℝ) | ∀ i, 0 < x.2 i} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const
        ((measurable_pi_apply i).comp measurable_snd))
    exact (Measure.ae_prod_mem_iff_ae_ae_mem hm).mpr
      (Filter.Eventually.of_forall (fun _ => independentExponentials_ae_pos))
  | succ n ih =>
    have hpos : ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), ∀ i, 0 < x.2 i := by
      have hm : MeasurableSet {x : H × (ι → ℝ) | ∀ i, 0 < x.2 i} := by
        simp only [setOf_forall]
        exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const
          ((measurable_pi_apply i).comp measurable_snd))
      exact (Measure.ae_prod_mem_iff_ae_ae_mem hm).mpr
        (Filter.Eventually.of_forall (fun _ => independentExponentials_ae_pos))
    have hall : ∀ᵐ x ∂ν.prod independentExponentials,
        ∀ j, x ∈ s.service.winner j → GoodExecution n (s.next j) (s.service.observation j x) := by
      apply ae_all_iff.mpr
      intro j
      apply (ae_restrict_iff' (s.service.measurable_winner j)).mp
      apply ae_of_ae_map (s.service.measurable_observation j).aemeasurable
      rw [s.service.first_completion_factorization]
      exact ih (s.next j) (s.service.markedHistoryMeasure ν j)
    filter_upwards [hpos, hall, s.service.no_completion_or_unique_ae ν] with x hp hc hx
    refine ⟨hp, ?_⟩
    rcases hx with ht | ⟨j, hj, _⟩
    · exact Or.inl ht
    · exact Or.inr ⟨j, hj, hc j hj⟩

theorem winner_clock_pos (s : PosteriorStage H ι) (x : H × (ι → ℝ)) (j : ι)
    (hx : 0 < x.2 j) : 0 < s.service.clock j x := by
  apply cappedHit_pos ((s.service.curves x.1).service_continuous j)
    (s.service.curves x.1).deadline_pos
  rw [(s.service.curves x.1).service_zero]
  exact hx

theorem next_original_demand (s : PosteriorStage H ι) (x : H × (ι → ℝ))
    (j : ι) (i : {i : ι // i ≠ j}) :
    (s.next j).initial (s.service.observation j x).1 i + (s.service.observation j x).2 i =
      s.initial x.1 i.1 + x.2 i.1 := by
  change (s.initial x.1 i.1 + (s.service.curves x.1).service i.1 (s.service.clock j x)) +
    (x.2 i.1 - (s.service.curves x.1).service i.1 (s.service.clock j x)) = _
  ring

theorem winner_revealed_demand (s : PosteriorStage H ι) (x : H × (ι → ℝ)) (j : ι)
    (hx : 0 < x.2 j) (hj : x ∈ s.service.winner j) :
    s.initial x.1 j + (s.service.curves x.1).service j (s.service.clock j x) =
      s.initial x.1 j + x.2 j := by
  congr 1
  exact (s.service.curves x.1).winner_service_eq hx hj

theorem next_total_deadline (s : PosteriorStage H ι) (elapsed : H → ℝ)
    (x : H × (ι → ℝ)) (j : ι) (hj : x ∈ s.service.winner j) :
    elapsed x.1 + s.service.clock j x + (s.next j).deadline (s.service.observation j x).1 =
      elapsed x.1 + s.deadline x.1 := by
  change elapsed x.1 + s.service.clock j x +
    (s.next j).deadline (x.1, s.service.clock j x) = _
  rw [s.next_deadline_on_winner hj]
  ring

end StochasticMatching.PosteriorStage
