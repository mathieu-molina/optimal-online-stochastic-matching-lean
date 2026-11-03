import Matching.StageExpectation
import Matching.ConditionalDemand

/-! The actual unallocated-demand budget and its conservation on survivor
coordinates. Removing a completed coordinate can only decrease this budget.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def unallocated (x : H × (ι → ℝ)) : ℝ :=
  ∑ i, ((s.initial x.1 + x.2) i - s.data.allocation (x.1, s.initial x.1 + x.2) i)

noncomputable def meanUnallocated (h : H) : ℝ :=
  ∑ i, (s.initial h i + 1 - posteriorRate s.data.allocation h (s.initial h) i)

theorem measurable_unallocated : Measurable s.unallocated := by
  apply Finset.measurable_sum
  intro i _
  have hv := (s.measurable_initial.comp measurable_fst).add measurable_snd
  exact ((measurable_pi_apply i).comp hv).sub
    ((measurable_pi_apply i).comp (s.data.measurable_allocation.comp (measurable_fst.prodMk hv)))

theorem integrable_unallocated_fiber (h : H) :
    Integrable (fun z => s.unallocated (h, z)) independentExponentials := by
  apply integrable_finset_sum
  intro i _
  exact ((integrable_const (s.initial h i)).add (integrable_exponential_coordinate i)).sub
    (s.data.integrable_shifted_allocation h (s.initial h) i)

theorem meanUnallocated_eq_integral (h : H) :
    s.meanUnallocated h = ∫ z, s.unallocated (h, z) ∂independentExponentials := by
  unfold meanUnallocated unallocated
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact s.data.posterior_gap_eq h (s.initial h) i
  · intro i _
    exact ((integrable_const (s.initial h i)).add (integrable_exponential_coordinate i)).sub
      (s.data.integrable_shifted_allocation h (s.initial h) i)

theorem measurable_meanUnallocated : Measurable s.meanUnallocated := by
  have he : s.meanUnallocated = fun h => ∫ z, s.unallocated (h, z) ∂independentExponentials :=
    funext s.meanUnallocated_eq_integral
  rw [he]
  exact s.measurable_unallocated.stronglyMeasurable.integral_prod_right'.measurable

theorem unallocated_nonneg {x : H × (ι → ℝ)} (ha : s.Admissible x.1)
    (hz : ∀ i, 0 ≤ x.2 i) : 0 ≤ s.unallocated x := by
  apply Finset.sum_nonneg
  intro i _
  exact sub_nonneg.mpr (ha.2 (s.initial x.1 + x.2)
    (fun i => add_nonneg (ha.1 i) (hz i)) i)

theorem meanUnallocated_nonneg {h : H} (ha : s.Admissible h) : 0 ≤ s.meanUnallocated h := by
  apply Finset.sum_nonneg
  intro i _
  exact s.data.posterior_gap_nonneg_at h ha.2 (s.initial h) ha.1 i

theorem meanUnallocated_le (R : StageRegion s) {h : H} (hh : h ∈ R.domain) :
    s.meanUnallocated h ≤ (Fintype.card ι : ℝ) * ((s.data.bound : ℝ) + 1) := by
  calc
    _ ≤ ∑ _i : ι, ((s.data.bound : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := R.initial_le_bound hh i
      have hr := posteriorRate_nonneg s.data.allocation_nonneg h (s.initial h) i
      linarith
    _ = _ := by simp; ring

theorem next_allocation_on_winner {x : H × (ι → ℝ)} {j : ι}
    (hz : 0 < x.2 j) (hw : x ∈ s.service.winner j) (i : {i : ι // i ≠ j}) :
    (s.next j).data.allocation ((s.service.observation j x).1,
      (s.next j).initial (s.service.observation j x).1 + (s.service.observation j x).2) i =
      s.data.allocation (x.1, s.initial x.1 + x.2) i.1 := by
  have hv := PosteriorData.reconstruct_add_initial s.service s.initial j
    (s.service.observation j x).1 (s.service.observation j x).2
  have hr := (s.service.curves x.1).reconstruct_first_observation hz hw
  change s.initial x.1 + (s.service.curves x.1).reconstructMarked j
    (variableObservation (s.service.curves x.1).service (s.service.curves x.1).deadline j x.2) = _ at hv
  rw [hr] at hv
  change s.data.allocation (x.1, (splitDemand j).symm
    (s.initial x.1 j + (s.service.curves x.1).service j (s.service.clock j x),
      (s.next j).initial (s.service.observation j x).1 + (s.service.observation j x).2)) i.1 = _
  exact congrArg (fun z => s.data.allocation (x.1, z) i.1) hv.symm

theorem next_unallocated_eq {x : H × (ι → ℝ)} {j : ι}
    (hz : 0 < x.2 j) (hw : x ∈ s.service.winner j) :
    (s.next j).unallocated (s.service.observation j x) =
      ∑ i : {i : ι // i ≠ j}, ((s.initial x.1 + x.2) i.1 -
        s.data.allocation (x.1, s.initial x.1 + x.2) i.1) := by
  unfold unallocated
  apply Finset.sum_congr rfl
  intro i _
  rw [s.next_allocation_on_winner hz hw i]
  congr 1
  exact s.next_original_demand x j i

theorem next_unallocated_le {x : H × (ι → ℝ)} (ha : s.Admissible x.1)
    (hz : ∀ i, 0 < x.2 i) {j : ι} (hw : x ∈ s.service.winner j) :
    (s.next j).unallocated (s.service.observation j x) ≤ s.unallocated x := by
  rw [s.next_unallocated_eq (hz j) hw]
  let f := fun i => (s.initial x.1 + x.2) i - s.data.allocation (x.1, s.initial x.1 + x.2) i
  have hs : (∑ i : {i : ι // i ≠ j}, f i.1) = ∑ i ∈ Finset.univ.erase j, f i :=
    (Finset.sum_subtype (Finset.univ.erase j) (by simp) f).symm
  have hn : 0 ≤ f j := sub_nonneg.mpr
    (ha.2 (s.initial x.1 + x.2) (fun i => add_nonneg (ha.1 i) (hz i).le) j)
  have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ j)
  change (∑ i : {i : ι // i ≠ j}, f i.1) ≤ ∑ i, f i
  rw [hs]
  linarith

end StochasticMatching.PosteriorStage
