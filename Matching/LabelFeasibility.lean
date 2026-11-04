import Matching.PosteriorFeasibility
import Matching.PosteriorStage

/-! Lift changing active-coordinate types back to fixed original labels.
Closed convex feasibility is preserved by posterior averaging, and downward
closure preserves it when a completed coordinate is removed at a restart.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq J]

noncomputable def labelLift (label : ι → J) : (ι → ℝ) →L[ℝ] (J → ℝ) :=
  ContinuousLinearMap.pi (fun j => ∑ i, if label i = j then ContinuousLinearMap.proj i else 0)

theorem labelLift_apply (label : ι → J) (v : ι → ℝ) (j : J) :
    labelLift label v j = ∑ i, if label i = j then v i else 0 := by
  simp only [labelLift, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem labelLift_at_label (label : ι → J) (hinj : Function.Injective label)
    (v : ι → ℝ) (i : ι) : labelLift label v (label i) = v i := by
  classical
  rw [labelLift_apply]
  simp [hinj.eq_iff]

theorem labelLift_off_labels (label : ι → J) (v : ι → ℝ) {j : J}
    (hj : ∀ i, label i ≠ j) : labelLift label v j = 0 := by
  rw [labelLift_apply]
  simp only [hj, if_false, Finset.sum_const_zero]

theorem labelLift_id (v : J → ℝ) : labelLift (id : J → J) v = v := by
  funext j
  exact labelLift_at_label id Function.injective_id v j

theorem labelLift_nonneg (label : ι → J) (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∀ j, 0 ≤ labelLift label v j := by
  intro j
  rw [labelLift_apply]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hv i
  · exact le_refl 0

theorem labelLift_restrict_le [DecidableEq ι] (label : ι → J) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (j : ι) :
    ∀ a, labelLift (fun i : {i : ι // i ≠ j} => label i.1) (fun i => v i.1) a ≤ labelLift label v a := by
  intro a
  rw [labelLift_apply, labelLift_apply]
  let f : ι → ℝ := fun i => if label i = a then v i else 0
  have hs : (∑ i : {i : ι // i ≠ j}, f i.1) = ∑ i ∈ Finset.univ.erase j, f i :=
    (Finset.sum_subtype (Finset.univ.erase j) (by simp) f).symm
  have hn : 0 ≤ f j := by
    unfold f
    split_ifs
    · exact hv j
    · exact le_refl 0
  have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ j)
  change (∑ i : {i : ι // i ≠ j}, f i.1) ≤ ∑ i, f i
  rw [hs]
  linarith

namespace PosteriorData
variable {H : Type*} [MeasurableSpace H] (p : PosteriorData H ι)

def FeasibleAllocation (label : ι → J) (P : Set (J → ℝ)) : Prop :=
  ∀ h z, labelLift label (p.allocation (h, z)) ∈ P

theorem lifted_posteriorRate_mem (label : ι → J) {P : Set (J → ℝ)}
    (hPc : Convex ℝ P) (hPclosed : IsClosed P) (hmem : p.FeasibleAllocation label P)
    (h : H) (x : ι → ℝ) : labelLift label (posteriorRate p.allocation h x) ∈ P := by
  rw [p.posteriorRate_eq_integral, ← (labelLift label).integral_comp_comm (p.allocation_integrable h x)]
  exact hPc.integral_mem hPclosed (Filter.Eventually.of_forall (fun z => hmem h (x + z)))
    ((labelLift label).integrable_comp (p.allocation_integrable h x))

end PosteriorData
namespace PosteriorStage
variable {H : Type*} [MeasurableSpace H] [DecidableEq ι] (s : PosteriorStage H ι)

theorem next_feasibleAllocation (label : ι → J) {P : Set (J → ℝ)}
    (hPdown : NonnegDownwardClosed P) (hmem : s.data.FeasibleAllocation label P) (j : ι) :
    (s.next j).data.FeasibleAllocation (fun i => label i.1) P := by
  intro h z
  let c := s.initial h.1 j + (s.service.curves h.1).service j h.2
  let v := s.data.allocation (h.1, (splitDemand j).symm (c, z))
  have hv : ∀ i, 0 ≤ v i := s.data.allocation_nonneg h.1 ((splitDemand j).symm (c, z))
  change labelLift (fun i : {i : ι // i ≠ j} => label i.1) (fun i => v i.1) ∈ P
  exact hPdown (hmem h.1 ((splitDemand j).symm (c, z)))
    (labelLift_nonneg _ _ (fun i => hv i.1)) (labelLift_restrict_le label v hv j)

theorem lifted_rate_mem (label : ι → J) {P : Set (J → ℝ)}
    (hPc : Convex ℝ P) (hPclosed : IsClosed P) (hmem : s.data.FeasibleAllocation label P)
    (h : H) (t : ℝ) : labelLift label (fun i => (s.service.curves h).rate i t) ∈ P :=
  s.data.lifted_posteriorRate_mem label hPc hPclosed hmem h
    (s.data.flow h (s.initial h) s.horizon t)

end PosteriorStage
end StochasticMatching
