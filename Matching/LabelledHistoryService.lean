import Matching.LabelFeasibility
import Matching.HistoryShift

/-! Turn a posterior stage's changing active-coordinate space into fixed
original job labels, preserving continuous curves and measurable histories.
-/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {H ι J : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J]

namespace ServiceCurveFamily
noncomputable def labelled (p : ServiceCurveFamily ι) (label : ι → J) : ServiceCurveFamily J where
  deadline := p.deadline
  deadline_pos := p.deadline_pos
  service j t := labelLift label (fun i => p.service i t) j
  rate j t := labelLift label (fun i => p.rate i t) j
  service_continuous j := by
    apply (continuous_apply j).comp
    apply (labelLift label).continuous.comp
    exact continuous_pi (fun i => p.service_continuous i)
  rate_continuous j := by
    apply (continuous_apply j).comp
    apply (labelLift label).continuous.comp
    exact continuous_pi (fun i => p.rate_continuous i)
  service_monotone j := by
    intro t ht u hu htu
    simp only [labelLift_apply]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact p.service_monotone i ht hu htu
    · exact le_rfl
  service_zero j := by simp [labelLift_apply, p.service_zero]
  rate_nonneg j t ht := labelLift_nonneg label _ (fun i => p.rate_nonneg i t ht) j
  service_deriv j t ht := by
    simp only [labelLift_apply]
    apply HasDerivAt.sum
    intro i _
    by_cases hi : label i = j
    · simpa only [hi, if_true] using p.service_deriv i t ht
    · simpa only [hi, if_false] using hasDerivAt_const t (0 : ℝ)

theorem labelled_service_at_label (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) (i : ι) (t : ℝ) :
    (p.labelled label).service (label i) t = p.service i t := labelLift_at_label label hinj _ i

theorem labelled_rate_at_label (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) (i : ι) (t : ℝ) :
    (p.labelled label).rate (label i) t = p.rate i t := labelLift_at_label label hinj _ i

theorem labelled_service_off_labels (p : ServiceCurveFamily ι) (label : ι → J)
    (j : J) (hj : ∀ i, label i ≠ j) (t : ℝ) : (p.labelled label).service j t = 0 :=
  labelLift_off_labels label _ hj

theorem labelled_rate_off_labels (p : ServiceCurveFamily ι) (label : ι → J)
    (j : J) (hj : ∀ i, label i ≠ j) (t : ℝ) : (p.labelled label).rate j t = 0 :=
  labelLift_off_labels label _ hj
end ServiceCurveFamily

namespace HistoryServiceFamily
noncomputable def labelled (p : HistoryServiceFamily H ι) (label : ι → J) : HistoryServiceFamily H J where
  curves h := (p.curves h).labelled label
  deadline_measurable := p.deadline_measurable
  service_at_measurable j t :=
    ((measurable_pi_apply j).comp (labelLift label).continuous.measurable).comp
      (measurable_pi_lambda _ (fun i => p.service_at_measurable i t))
  rate_at_measurable j t :=
    ((measurable_pi_apply j).comp (labelLift label).continuous.measurable).comp
      (measurable_pi_lambda _ (fun i => p.rate_at_measurable i t))
end HistoryServiceFamily

namespace PosteriorStage
noncomputable def routingService (s : PosteriorStage H ι) (label : ι → J) :
    HistoryServiceFamily (H × ℝ) J := (s.service.labelled label).shifted

theorem routingService_rate_mem (s : PosteriorStage H ι) (label : ι → J) {P : Set (J → ℝ)}
    (hPc : Convex ℝ P) (hPclosed : IsClosed P) (hmem : s.data.FeasibleAllocation label P)
    (x : H × ℝ) (u : ℝ) (hu : u ∈ Icc 0 ((s.routingService label).curves x).deadline) :
    (fun j => ((s.routingService label).curves x).rate j u) ∈ P := by
  exact HistoryServiceFamily.shifted_rate_mem (s.service.labelled label) P
    (fun h t _ => s.lifted_rate_mem label hPc hPclosed hmem h t) x u hu

theorem routingService_frozen (s : PosteriorStage H ι) (label : ι → J)
    (j : J) (hj : ∀ i, label i ≠ j) (x : H × ℝ) (u : ℝ) :
    ((s.routingService label).curves x).service j u = 0 := by
  change labelLift label _ j - labelLift label _ j = 0
  rw [labelLift_off_labels label _ hj, labelLift_off_labels label _ hj, sub_self]

theorem routingService_rate_frozen (s : PosteriorStage H ι) (label : ι → J)
    (j : J) (hj : ∀ i, label i ≠ j) (x : H × ℝ) (u : ℝ) :
    ((s.routingService label).curves x).rate j u = 0 := labelLift_off_labels label _ hj
end PosteriorStage
end StochasticMatching
