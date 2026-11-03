import Matching.RatePath
import Matching.BudgetFunctions

/-! Integrate the concrete original-coordinate rate path. Compact feasible
regions give local integrability and continuous cumulative service; before the
first actual segment endpoint this integral is exactly the constructed ODE
service, lifted to the original labels.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

noncomputable def cumulativePath (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) (t : ℝ) : J → ℝ :=
  ∫ u in (0 : ℝ)..t, ratePath n s label (u, x)

theorem cumulativePath_zero (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) : cumulativePath n s label x 0 = 0 := by
  simp [cumulativePath]

theorem ratePath_intervalIntegrable (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (x : H × (ι → ℝ)) (a b : ℝ) :
    IntervalIntegrable (fun t => ratePath n s label (t, x)) volume a b := by
  obtain ⟨C, hC⟩ := hPcompact.isBounded.exists_norm_le
  have hm : Measurable (fun t => ratePath n s label (t, x)) :=
    (measurable_ratePath n s label).comp (measurable_id.prodMk measurable_const)
  have hi : ∀ c d : ℝ, IntegrableOn (fun t => ratePath n s label (t, x)) (Ioc c d) := by
    intro c d
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    exact hC _ (ratePath_feasible n s label hP0 hPc hPcompact.isClosed hPdown hmem (t, x))
  exact ⟨hi a b, hi b a⟩

theorem continuous_cumulativePath (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (x : H × (ι → ℝ)) :
    Continuous (cumulativePath n s label x) :=
  intervalIntegral.continuous_primitive
    (ratePath_intervalIntegrable n s label hP0 hPc hPcompact hPdown hmem x) 0

theorem ratePath_before_stop (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < s.service.stopClock x) :
    ratePath (n + 1) s label (t, x) = s.currentRate label (t, x) := by
  classical
  have hD : t < s.deadline x.1 := ht.trans_le (s.service.stopClock_bounds x).2
  change (if 0 ≤ t ∧ t < s.deadline x.1 then branchSelect s.queryWinner _ _ (t, x) else 0) = _
  rw [if_pos ⟨ht0, hD⟩]
  by_cases hw : ∃ j, x ∈ s.service.winner j
  · obtain ⟨j, hj⟩ := hw
    have hq : (t, x) ∈ s.queryWinner j := hj
    rw [branchSelect_of_mem s.queryWinner_disjoint _ _ hq]
    rw [s.service.stopClock_winner hj] at ht
    exact if_pos ht
  · have hn : ∀ j, (t, x) ∉ s.queryWinner j := fun j hj => hw ⟨j, hj⟩
    rw [branchSelect_of_not_mem _ _ hn]

theorem cumulativePath_first_segment (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : H × (ι → ℝ)) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s.service.stopClock x) :
    cumulativePath (n + 1) s label x t =
      labelLift label (fun i => (s.service.curves x.1).service i t) := by
  let r : ℝ → (ι → ℝ) := fun u i => (s.service.curves x.1).rate i u
  have hr : Continuous r := continuous_pi (fun i => (s.service.curves x.1).rate_continuous i)
  have hri := hr.intervalIntegrable (μ := volume) 0 t
  have htD : t ∈ Icc 0 (s.service.curves x.1).deadline :=
    ⟨ht0, ht.trans (s.service.stopClock_bounds x).2⟩
  have hs : (∫ u in (0 : ℝ)..t, r u) = fun i => (s.service.curves x.1).service i t := by
    funext i
    have hc := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hri
    have hc' : (∫ u in (0 : ℝ)..t, r u) i =
        ∫ u in (0 : ℝ)..t, (s.service.curves x.1).rate i u := by
      simpa only [ContinuousLinearMap.proj_apply, r] using hc.symm
    exact hc'.trans ((s.service.curves x.1).service_eq_integral htD i).symm
  calc
    _ = ∫ u in (0 : ℝ)..t, labelLift label (r u) := by
      unfold cumulativePath
      rw [intervalIntegral.integral_of_le ht0, intervalIntegral.integral_of_le ht0,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact ratePath_before_stop n s label x hu.1.le (hu.2.trans_le ht)
    _ = labelLift label (∫ u in (0 : ℝ)..t, r u) := by
      exact (labelLift label).intervalIntegral_comp_comm hri
    _ = _ := congrArg (labelLift label) hs

end StochasticMatching.PosteriorStage
