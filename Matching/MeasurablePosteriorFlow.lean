import Matching.PosteriorTrajectory

/-! Joint measurability of the posterior ODE flow, proved by measurable
Picard approximations and their factorial convergence bound. This removes
the measurability obligation left by pointwise ODE existence.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StochasticMatching

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι]

theorem measurable_history_intervalIntegral {F : H × ℝ → (ι → ℝ)} (hF : Measurable F) :
    Measurable (fun x : H × ℝ => ∫ u in (0 : ℝ)..x.2, F (x.1, u)) := by
  let G : (H × ℝ) × ℝ → (ι → ℝ) := fun q => F (q.1.1, q.2)
  have hG : Measurable G :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hposSet : MeasurableSet {q : (H × ℝ) × ℝ | q.2 ∈ Ioc 0 q.1.2} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hnegSet : MeasurableSet {q : (H × ℝ) × ℝ | q.2 ∈ Ioc q.1.2 0} :=
    (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hp : Measurable (fun x : H × ℝ => ∫ u in Ioc 0 x.2, F (x.1, u)) := by
    have h := (hG.indicator hposSet).stronglyMeasurable.integral_prod_right'
      (ν := volume)
    convert h.measurable using 1
    funext x
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hn : Measurable (fun x : H × ℝ => ∫ u in Ioc x.2 0, F (x.1, u)) := by
    have h := (hG.indicator hnegSet).stronglyMeasurable.integral_prod_right'
      (ν := volume)
    convert h.measurable using 1
    funext x
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  exact hp.sub hn

noncomputable def flowTime (T : ℝ≥0) (t : ℝ) : ℝ :=
  projIcc (-1) ((T : ℝ) + 1) (by linarith [T.coe_nonneg]) t

theorem continuous_flowTime (T : ℝ≥0) : Continuous (flowTime T) :=
  continuous_subtype_val.comp continuous_projIcc

namespace PosteriorData

variable (p : PosteriorData H ι)

noncomputable def approximation (ξ : H → (ι → ℝ)) (T : ℝ≥0) : ℕ → H → ℝ → (ι → ℝ)
  | 0, h, _ => ξ h
  | n + 1, h, t => ξ h + ∫ u in (0 : ℝ)..flowTime T t,
      posteriorRate p.allocation h (approximation ξ T n h u)

theorem measurable_approximation {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun x : H × ℝ => p.approximation ξ T n x.1 x.2) := by
  induction n with
  | zero => exact hξ.comp measurable_fst
  | succ n ih =>
    change Measurable (fun x : H × ℝ => ξ x.1 +
      ∫ u in (0 : ℝ)..flowTime T x.2,
        posteriorRate p.allocation x.1 (p.approximation ξ T n x.1 u))
    have hm : Measurable (fun x : H × ℝ =>
        posteriorRate p.allocation x.1 (p.approximation ξ T n x.1 x.2)) :=
      (measurable_posteriorRate p.measurable_allocation).comp (measurable_fst.prodMk ih)
    have hi : Measurable (fun x : H × ℝ => ∫ u in (0 : ℝ)..x.2,
        posteriorRate p.allocation x.1 (p.approximation ξ T n x.1 u)) :=
      measurable_history_intervalIntegral hm
    have hc : Measurable (fun x : H × ℝ => (x.1, flowTime T x.2)) :=
      measurable_fst.prodMk ((continuous_flowTime T).measurable.comp measurable_snd)
    have hcomp := hi.comp hc
    have hbase : Measurable (fun x : H × ℝ => ξ x.1) := hξ.comp measurable_fst
    have hadd := hbase.add hcomp
    simpa only [Function.comp_def, Pi.add_apply] using hadd

theorem approximation_eq_iterate (ξ : H → (ι → ℝ)) (T : ℝ≥0) (n : ℕ) (h : H) (t : ℝ) :
    p.approximation ξ T n h t =
      (PicardLindelof.FunSpace.next^[n] (default : (p.picard h (ξ h) T).FunSpace))
        ((p.picard h (ξ h) T).proj t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PicardLindelof.FunSpace.next_apply]
    change ξ h + (∫ u in (0 : ℝ)..flowTime T t,
        posteriorRate p.allocation h (p.approximation ξ T n h u)) =
      ξ h + (∫ u in (0 : ℝ)..flowTime T t,
        posteriorRate p.allocation h
          ((PicardLindelof.FunSpace.next^[n] (default : (p.picard h (ξ h) T).FunSpace))
            ((p.picard h (ξ h) T).proj u)))
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    exact congrArg (posteriorRate p.allocation h) (ih u)

theorem approximation_tendsto (ξ : H → (ι → ℝ)) (T : ℝ≥0) (h : H) (t : ℝ) :
    Tendsto (fun n => p.approximation ξ T n h t) atTop (𝓝 (p.flow h (ξ h) T t)) := by
  let v := p.picard h (ξ h) T
  let f := p.fixedCurve h (ξ h) T
  have hfix (n : ℕ) : PicardLindelof.FunSpace.next^[n] f = f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact p.fixedCurve_next h (ξ h) T
  have hb (n : ℕ) : dist (p.approximation ξ T n h t) (p.flow h (ξ h) T t) ≤
      ((v.L : ℝ) * |((v.proj t : Icc v.tMin v.tMax) : ℝ) - v.t₀|) ^ n / n.factorial *
        dist (default : v.FunSpace) f := by
    rw [p.approximation_eq_iterate]
    simpa only [hfix] using PicardLindelof.FunSpace.dist_iterate_next_apply_le
      (default : v.FunSpace) f n (v.proj t)
  have hz : Tendsto (fun n : ℕ =>
      ((v.L : ℝ) * |((v.proj t : Icc v.tMin v.tMax) : ℝ) - v.t₀|) ^ n / n.factorial *
        dist (default : v.FunSpace) f) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop
        ((v.L : ℝ) * |((v.proj t : Icc v.tMin v.tMax) : ℝ) - v.t₀|)).mul_const
          (dist (default : v.FunSpace) f)
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hb hz)

theorem measurable_flow {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (T : ℝ≥0) :
    Measurable (fun x : H × ℝ => p.flow x.1 (ξ x.1) T x.2) := by
  apply measurable_of_tendsto_metrizable (fun n => p.measurable_approximation hξ T n)
  exact tendsto_pi_nhds.mpr (fun x => p.approximation_tendsto ξ T x.1 x.2)

end PosteriorData
end StochasticMatching
