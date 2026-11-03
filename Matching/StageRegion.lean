import Matching.AdmissibleStage

/-! Measurable regions of valid stage histories. These regions carry the
invariants needed by the comparison argument and retain full mass after every
actual marked completion. No measurability of an uncountable allocation-cap
predicate is assumed.
-/

open MeasureTheory Set
namespace StochasticMatching

structure StageRegion {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (s : PosteriorStage H ι) where
  domain : Set H
  measurable_domain : MeasurableSet domain
  elapsed : H → ℝ
  measurable_elapsed : Measurable elapsed
  admissible : ∀ h ∈ domain, s.Admissible h
  elapsed_nonneg : ∀ h ∈ domain, 0 ≤ elapsed h
  total_deadline : ∀ h ∈ domain, elapsed h + s.deadline h = 1
  initial_bound : ∀ h ∈ domain, ∀ i, s.initial h i ≤ (s.data.bound : ℝ) * elapsed h

namespace StageRegion
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  {s : PosteriorStage H ι} (R : StageRegion s)

def nextDomain : Set (H × ℝ) :=
  {x | x.1 ∈ R.domain ∧ 0 ≤ x.2 ∧ x.2 < s.deadline x.1}

theorem measurable_nextDomain : MeasurableSet R.nextDomain :=
  (R.measurable_domain.preimage measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (s.measurable_deadline.comp measurable_fst)))

theorem remaining_deadline_eq {x : H × ℝ} (hx : x ∈ R.nextDomain) :
    remainingDeadline s.horizon s.deadline x = s.deadline x.1 - x.2 :=
  remainingDeadline_eq s.horizon s.deadline x hx.2.1 hx.2.2 (s.deadline_le x.1)

noncomputable def next (j : ι) : StageRegion (s.next j) where
  domain := R.nextDomain
  measurable_domain := R.measurable_nextDomain
  elapsed x := R.elapsed x.1 + x.2
  measurable_elapsed := (R.measurable_elapsed.comp measurable_fst).add measurable_snd
  admissible x hx := s.next_admissible x.1 (R.admissible x.1 hx.1) j ⟨hx.2.1, hx.2.2.le⟩
  elapsed_nonneg x hx := add_nonneg (R.elapsed_nonneg x.1 hx.1) hx.2.1
  total_deadline x hx := by
    change R.elapsed x.1 + x.2 + remainingDeadline s.horizon s.deadline x = 1
    rw [R.remaining_deadline_eq hx]
    linarith [R.total_deadline x.1 hx.1]
  initial_bound x hx i := s.next_initial_bound x.1 (R.elapsed x.1)
    (R.initial_bound x.1 hx.1) j ⟨hx.2.1, hx.2.2.le⟩ i

theorem elapsed_le_one {h : H} (hh : h ∈ R.domain) : R.elapsed h ≤ 1 := by
  have hD := s.deadline_pos h
  linarith [R.total_deadline h hh]

theorem initial_le_bound {h : H} (hh : h ∈ R.domain) (i : ι) :
    s.initial h i ≤ (s.data.bound : ℝ) := by
  have hi := R.initial_bound h hh i
  have ht := R.elapsed_le_one hh
  nlinarith [s.data.bound.coe_nonneg]

theorem winner_extended_mem {x : H × (ι → ℝ)} (hx : x.1 ∈ R.domain) {j : ι}
    (hw : x ∈ s.service.winner j) : (s.service.observation j x).1 ∈ R.nextDomain := by
  refine ⟨hx, ?_, hw.1⟩
  exact (cappedHit_bounds ((s.service.curves x.1).service_continuous j)
    (s.service.curves x.1).deadline_pos.le).1

theorem next_concentrated (ν : Measure H) (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (j : ι) :
    ∀ᵐ h ∂s.service.markedHistoryMeasure ν j, h ∈ (R.next j).domain := by
  have hmap : Measure.map (fun x : H × (ι → ℝ) => (x.1, s.service.clock j x))
      ((ν.prod independentExponentials).restrict (s.service.winner j)) =
      s.service.markedHistoryMeasure ν j := by
    have h := congrArg
      (Measure.map (Prod.fst : (H × ℝ) × ({i : ι // i ≠ j} → ℝ) → H × ℝ))
      (s.service.first_completion_factorization ν j)
    rw [Measure.map_map measurable_fst (s.service.measurable_observation j)] at h
    simpa only [Function.comp_def, HistoryServiceFamily.observation,
      Measure.map_fst_prod, measure_univ, one_smul] using h
  have hp : ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), x.1 ∈ R.domain := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (R.measurable_domain.preimage measurable_fst)).mpr
    filter_upwards [hν] with h hh
    exact Filter.Eventually.of_forall (fun _ => hh)
  rw [← hmap]
  apply (ae_map_iff (measurable_fst.prodMk (s.service.measurable_clock j)).aemeasurable
    (R.next j).measurable_domain).mpr
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem (s.service.measurable_winner j)] with x hx hw
  exact R.winner_extended_mem hx hw

end StageRegion
end StochasticMatching
