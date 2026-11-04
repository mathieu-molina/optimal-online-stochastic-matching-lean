import Matching.PosteriorComparison
import Matching.GoodExecution

/-! Local admissibility at an actually reached history. The allocation cap is
preserved after revealing a completed demand; impossible histories need not
satisfy the invariant.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching

namespace PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] (p : PosteriorData H ι)

theorem posterior_gap_nonneg_at (h : H)
    (hcap : ∀ z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ι) :
    0 ≤ x i + 1 - posteriorRate p.allocation h x i := by
  rw [p.posterior_gap_eq]
  apply integral_nonneg_of_ae
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  exact sub_nonneg.mpr (hcap (x + z) (fun j => add_nonneg (hx j) (hz j).le) i)

end PosteriorData

namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

def Admissible (h : H) : Prop :=
  (∀ i, 0 ≤ s.initial h i) ∧
    ∀ z, (∀ i, 0 ≤ z i) → ∀ i, s.data.allocation (h, z) i ≤ z i

theorem next_initial_nonneg (h : H) (hx : ∀ i, 0 ≤ s.initial h i) (j : ι) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) (i : {i : ι // i ≠ j}) :
    0 ≤ (s.next j).initial (h, t) i :=
  add_nonneg (hx i.1) ((s.service.curves h).service_nonneg ht i.1)

theorem next_allocation_cap (h : H) (ha : s.Admissible h) (j : ι) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline)
    (z : {i : ι // i ≠ j} → ℝ) (hz : ∀ i, 0 ≤ z i) (i : {i : ι // i ≠ j}) :
    (s.next j).data.allocation ((h, t), z) i ≤ z i := by
  let c := s.initial h j + (s.service.curves h).service j t
  have hc : 0 ≤ c := add_nonneg (ha.1 j) ((s.service.curves h).service_nonneg ht j)
  have hn : ∀ k, 0 ≤ (splitDemand j).symm (c, z) k := by
    intro k
    by_cases hk : k = j
    · subst k
      simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt] using hc
    · simpa [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt, hk] using hz ⟨k, hk⟩
  have hcap := ha.2 ((splitDemand j).symm (c, z)) hn i.1
  change s.data.allocation (h, (splitDemand j).symm (c, z)) i.1 ≤ z i
  have he : (splitDemand j).symm (c, z) i.1 = z i := by
    simp [splitDemand, Equiv.funSplitAt, Equiv.piSplitAt, i.2]
  rw [he] at hcap
  exact hcap

theorem next_admissible (h : H) (ha : s.Admissible h) (j : ι) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) :
    (s.next j).Admissible (h, t) :=
  ⟨s.next_initial_nonneg h ha.1 j ht, s.next_allocation_cap h ha j ht⟩

theorem next_admissible_on_winner {x : H × (ι → ℝ)} (ha : s.Admissible x.1)
    {j : ι} (hw : x ∈ s.service.winner j) :
    (s.next j).Admissible (s.service.observation j x).1 := by
  apply s.next_admissible x.1 ha j
  exact cappedHit_bounds ((s.service.curves x.1).service_continuous j)
    (s.service.curves x.1).deadline_pos.le

theorem flow_gap_nonneg_at (h : H) (ha : s.Admissible h) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) (i : ι) :
    0 ≤ s.initial h i + (s.service.curves h).service i t + 1 -
      (s.service.curves h).rate i t := by
  rw [s.rate_eq_posterior]
  exact s.data.posterior_gap_nonneg_at h ha.2 _
    (fun i => add_nonneg (ha.1 i) ((s.service.curves h).service_nonneg ht i)) i

theorem comparison_first_step_bound_at (elapsed : ℝ) (h : H) (ha : s.Admissible h)
    (hT : elapsed + s.deadline h = 1) :
    (∑ i, Comparison.continuation elapsed (s.initial h i)) -
      (∫ t in (0 : ℝ)..s.deadline h,
        survivalCurve (fun u i => (s.service.curves h).service i u) t *
          Comparison.lossKernel (elapsed + t) *
            ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 -
              (s.service.curves h).rate i t)) ≤
      ∫ t in (0 : ℝ)..s.deadline h,
        survivalCurve (fun u i => (s.service.curves h).service i u) t *
          ∑ j, (s.service.curves h).rate j t *
            (1 + ∑ i : {i : ι // i ≠ j},
              Comparison.continuation (elapsed + t) ((s.next j).initial (h, t) i)) := by
  have hb := (s.service.curves h).comparison_first_step_lower_bound elapsed (s.initial h)
    (le_of_eq hT) ha.1 (fun t ht i => s.flow_gap_nonneg_at h ha ht i)
  change (s.service.curves h).comparisonPotential elapsed (s.initial h) 0 - _ ≤
    _ * (s.service.curves h).comparisonPotential elapsed (s.initial h) (s.deadline h) + _ at hb
  rw [s.comparison_terminal_zero h hT, mul_zero, zero_add] at hb
  simpa only [ServiceCurveFamily.comparisonPotential, (s.service.curves h).service_zero,
    add_zero, s.comparison_jump_eq_restart] using hb

theorem rate_le_bound (h : H) (t : ℝ) (i : ι) :
    (s.service.curves h).rate i t ≤ (s.data.bound : ℝ) :=
  posteriorRate_le s.data.measurable_allocation s.data.allocation_nonneg
    s.data.allocation_le h (s.data.flow h (s.initial h) s.horizon t) i

theorem service_le_bound (h : H) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) (i : ι) :
    (s.service.curves h).service i t ≤ (s.data.bound : ℝ) * t :=
  (s.service.curves h).service_le ht (fun i u _ => s.rate_le_bound h u i) i

theorem next_initial_bound (h : H) (elapsed : ℝ)
    (hx : ∀ i, s.initial h i ≤ (s.data.bound : ℝ) * elapsed) (j : ι) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) (i : {i : ι // i ≠ j}) :
    (s.next j).initial (h, t) i ≤ ((s.next j).data.bound : ℝ) * (elapsed + t) := by
  change s.initial h i.1 + (s.service.curves h).service i.1 t ≤
    (s.data.bound : ℝ) * (elapsed + t)
  have hi := hx i.1
  have hs := s.service_le_bound h ht i.1
  nlinarith

end PosteriorStage
end StochasticMatching
