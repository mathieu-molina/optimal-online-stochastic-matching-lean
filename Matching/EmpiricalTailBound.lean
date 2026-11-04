import Matching.ExponentialSumLaw
import Mathlib.Probability.Integration

/-! A square-root bound for the mean fluctuation of an empirical exponential
tail count. This is the probabilistic estimate for the offline hard-instance
benchmark. It follows from independence and second moments. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace StochasticMatching

theorem integrable_of_abs_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  let c := ∫ x, |f x| ∂μ
  have he (x : Ω) : (|f x| - c) ^ 2 = f x ^ 2 - (2 * c) * |f x| + c ^ 2 := by
    nlinarith [sq_abs (f x)]
  have h0 := integral_nonneg (μ := μ) (fun x => sq_nonneg (|f x| - c))
  simp_rw [he] at h0
  have hsub : Integrable (fun x => f x ^ 2 - (2 * c) * |f x|) μ := hf2.sub (hf.abs.const_mul (2 * c))
  rw [integral_add hsub (integrable_const (c ^ 2)),
    integral_sub hf2 (hf.abs.const_mul (2 * c)), integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] at h0
  have hs : c ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by change 0 ≤ _ - 2 * c * c + c ^ 2 at h0; nlinarith
  exact (Real.le_sqrt (integral_nonneg (fun x => abs_nonneg (f x)))
    (integral_nonneg (fun x => sq_nonneg (f x)))).mpr hs

theorem integral_sq_sum_diagonal {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
    (μ : Measure Ω) (f : κ → Ω → ℝ) (d : κ → ℝ)
    (hi : ∀ i j, Integrable (fun x => f i x * f j x) μ)
    (hd : ∀ i, (∫ x, f i x * f i x ∂μ) = d i)
    (hc : ∀ i j, i ≠ j → (∫ x, f i x * f j x ∂μ) = 0) :
    (∫ x, (∑ i, f i x) ^ 2 ∂μ) = ∑ i, d i := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi j i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hi j i)]
  rw [Finset.sum_eq_single i]
  · exact hd i
  · intro j _ hji
    exact hc j i hji
  · simp

noncomputable def tailIndicator (t z : ℝ) : ℝ := if t < z then 1 else 0

theorem tailIndicator_measurable (t : ℝ) : Measurable (tailIndicator t) := by
  exact measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const

theorem tailIndicator_bounds (t z : ℝ) : 0 ≤ tailIndicator t z ∧ tailIndicator t z ≤ 1 := by
  unfold tailIndicator
  split_ifs <;> norm_num

theorem tailIndicator_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, tailIndicator t z ∂unitExponential) = Real.exp (-t) := by
  change (∫ z, (Ioi t).indicator (fun _ => (1 : ℝ)) z ∂unitExponential) = _
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one,
    unitExponential_real_Ioi ht]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def centeredTail (t : ℝ) (i : ι) (z : ι → ℝ) : ℝ :=
  tailIndicator t (z i) - Real.exp (-t)

theorem centeredTail_measurable (t : ℝ) (i : ι) : Measurable (centeredTail t i) :=
  ((tailIndicator_measurable t).comp (measurable_pi_apply i)).sub_const _

theorem centeredTail_abs_le {t : ℝ} (ht : 0 ≤ t) (i : ι) (z : ι → ℝ) :
    |centeredTail t i z| ≤ 1 := by
  have hp := Real.exp_nonneg (-t)
  have hp1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hi := tailIndicator_bounds t (z i)
  exact abs_le.mpr ⟨by unfold centeredTail; linarith, by unfold centeredTail; linarith⟩

theorem centeredTail_integrable {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    Integrable (centeredTail t i) independentExponentials :=
  integrable_of_abs_bounded _ (centeredTail_measurable t i) 1 (centeredTail_abs_le ht i)

theorem centeredTail_integral {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    (∫ z, centeredTail t i z ∂independentExponentials) = 0 := by
  have hi : Integrable (fun z : ι → ℝ => tailIndicator t (z i)) independentExponentials :=
    integrable_of_abs_bounded _ ((tailIndicator_measurable t).comp (measurable_pi_apply i)) 1
      (fun z => by rw [abs_of_nonneg (tailIndicator_bounds t _).1]; exact (tailIndicator_bounds t _).2)
  unfold centeredTail
  rw [integral_sub hi (integrable_const _), integral_const, measureReal_univ_eq_one, one_smul]
  have h := integral_map_of_stronglyMeasurable (μ := independentExponentials)
    (measurable_pi_apply i) (tailIndicator_measurable t).stronglyMeasurable
  rw [independentExponentials_coordinate_law, tailIndicator_integral ht] at h
  rw [← h, sub_self]

theorem centeredTail_product_integrable {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    Integrable (fun z => centeredTail t i z * centeredTail t j z) independentExponentials := by
  apply integrable_of_abs_bounded _ ((centeredTail_measurable t i).mul (centeredTail_measurable t j)) 1
  intro z
  rw [abs_mul]
  exact mul_le_one₀ (centeredTail_abs_le ht i z) (abs_nonneg _) (centeredTail_abs_le ht j z)

theorem centeredTail_cross {t : ℝ} (ht : 0 ≤ t) (i j : ι) (hij : i ≠ j) :
    (∫ z, centeredTail t i z * centeredTail t j z ∂independentExponentials) = 0 := by
  have h := (independentExponentials_coordinates_independent.indepFun hij).comp
    ((tailIndicator_measurable t).sub_const (Real.exp (-t)))
    ((tailIndicator_measurable t).sub_const (Real.exp (-t)))
  have he := h.integral_mul_of_integrable (centeredTail_integrable ht i) (centeredTail_integrable ht j)
  change (∫ z, centeredTail t i z * centeredTail t j z ∂independentExponentials) =
    (∫ z, centeredTail t i z ∂independentExponentials) *
      (∫ z, centeredTail t j z ∂independentExponentials) at he
  simpa only [centeredTail_integral ht, mul_zero] using he

theorem centeredTail_square {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    (∫ z, centeredTail t i z * centeredTail t i z ∂independentExponentials) =
      Real.exp (-t) * (1 - Real.exp (-t)) := by
  let p := Real.exp (-t)
  have he (z : ι → ℝ) : centeredTail t i z * centeredTail t i z =
      (1 - 2 * p) * centeredTail t i z + p * (1 - p) := by
    unfold centeredTail tailIndicator
    split_ifs <;> dsimp [p] <;> ring
  simp_rw [he]
  rw [integral_add ((centeredTail_integrable ht i).const_mul _) (integrable_const _),
    integral_const_mul, centeredTail_integral ht i]
  simp [p]

noncomputable def empiricalTail (z : ι → ℝ) (t : ℝ) : ℝ := ∑ i, tailIndicator t (z i)

theorem empiricalTail_mean_abs_bound {t : ℝ} (ht : 0 ≤ t) :
    (∫ z : ι → ℝ, |empiricalTail z t - (Fintype.card ι : ℝ) * Real.exp (-t)|
      ∂independentExponentials) ≤ Real.sqrt ((Fintype.card ι : ℝ) * Real.exp (-t)) := by
  have he (z : ι → ℝ) : empiricalTail z t - (Fintype.card ι : ℝ) * Real.exp (-t) =
      ∑ i, centeredTail t i z := by
    simp [empiricalTail, centeredTail, Finset.sum_sub_distrib, nsmul_eq_mul]
  simp_rw [he]
  have hi := integrable_finset_sum Finset.univ (fun (i : ι) _ => centeredTail_integrable ht i)
  have hi2 : Integrable (fun z : ι → ℝ => (∑ i, centeredTail t i z) ^ 2) independentExponentials := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      centeredTail_product_integrable ht j i))
  apply (integral_abs_le_sqrt_integral_sq _ hi hi2).trans
  rw [integral_sq_sum_diagonal _ (centeredTail t) (fun _ => Real.exp (-t) * (1 - Real.exp (-t)))
    (centeredTail_product_integrable ht) (centeredTail_square ht) (centeredTail_cross ht)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply Real.sqrt_le_sqrt
  have hp := Real.exp_nonneg (-t)
  have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm (mul_self_nonneg (Real.exp (-t)))]

end StochasticMatching
