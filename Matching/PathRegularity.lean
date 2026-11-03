import Matching.RateIntegral

/-! Joint measurability of cumulative service, positivity of the rate path,
and monotonicity of service on the original labels.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem measurable_cumulativePath (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (fun q : ℝ × (H × (ι → ℝ)) => cumulativePath n s label q.2 q.1) := by
  have hr : Measurable (fun q : (ℝ × (H × (ι → ℝ))) × ℝ => ratePath n s label (q.2, q.1.2)) :=
    (measurable_ratePath n s label).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hp : Measurable (fun q : (ℝ × (H × (ι → ℝ))) × ℝ =>
      if 0 < q.2 ∧ q.2 ≤ q.1.1 then ratePath n s label (q.2, q.1.2) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))) hr measurable_const
  have hm : Measurable (fun q : (ℝ × (H × (ι → ℝ))) × ℝ =>
      if q.1.1 < q.2 ∧ q.2 ≤ 0 then ratePath n s label (q.2, q.1.2) else 0) :=
    Measurable.ite ((measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) hr measurable_const
  have hmeas := (hp.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hmeas using 1
  funext q
  rw [cumulativePath, intervalIntegral]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator, mem_Ioc]

theorem ratePath_nonneg (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (q : ℝ × (H × (ι → ℝ))) (a : J) : 0 ≤ ratePath n s label q a := by
  let P : Set (J → ℝ) := {v | ∀ a, 0 ≤ v a}
  have hPc : Convex ℝ P := by
    intro v hv w hw a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hv i)) (mul_nonneg hb (hw i))
  have hPclosed : IsClosed P := by
    change IsClosed {v : J → ℝ | ∀ a, 0 ≤ v a}
    simp only [setOf_forall]
    exact isClosed_iInter (fun a => isClosed_le continuous_const (continuous_apply a))
  have hPdown : NonnegDownwardClosed P := by
    intro v w _ hw _
    exact hw
  have hmem : s.data.FeasibleAllocation label P := by
    intro h z
    exact labelLift_nonneg label _ (s.data.allocation_nonneg h z)
  exact ratePath_feasible n s label (P := P) (fun _ => le_refl 0) hPc hPclosed hPdown hmem q a

theorem cumulativePath_monotone (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (x : H × (ι → ℝ)) (i : J) :
    Monotone (fun t => cumulativePath n s label x t i) := by
  intro a b hab
  have hi := ratePath_intervalIntegrable n s label hP0 hPc hPcompact hPdown hmem x
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  have hp := (ContinuousLinearMap.proj i : (J → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm (hi a b)
  simp only [ContinuousLinearMap.proj_apply] at hp
  have hn : 0 ≤ (∫ t in a..b, ratePath n s label (t, x)) i := by
    rw [← hp]
    exact intervalIntegral.integral_nonneg_of_forall hab (fun t => ratePath_nonneg n s label (t, x) i)
  have hs' := congrArg (fun v : J → ℝ => v i) hs
  change cumulativePath n s label x a i + (∫ t in a..b, ratePath n s label (t, x)) i =
    cumulativePath n s label x b i at hs'
  linarith

end StochasticMatching.PosteriorStage
