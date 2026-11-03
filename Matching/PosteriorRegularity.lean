import Matching.PosteriorMean

/-! Quantitative regularity of posterior rates. Bounded measurable allocations
become globally Lipschitz in the active service coordinates after exponential
averaging. Dependence on history is jointly measurable.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι]

theorem shiftedMean_l1_bound {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ} (hM : ∀ z, f z ≤ M) (x y : ι → ℝ) :
    |shiftedMean f x - shiftedMean f y| ≤ M * ∑ i, |x i - y i| := by
  let v : ι → ℝ := fun i => min (x i) (y i)
  have hx : v + (x - v) = x := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hy : v + (y - v) = y := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hx0 : ∀ i, 0 ≤ (x - v) i := fun i => sub_nonneg.mpr (min_le_left _ _)
  have hy0 : ∀ i, 0 ≤ (y - v) i := fun i => sub_nonneg.mpr (min_le_right _ _)
  have hbx := shiftedMean_increment_le hf h0 hM v hx0
  have hby := shiftedMean_increment_le hf h0 hM v hy0
  rw [hx] at hbx
  rw [hy] at hby
  have hcoord (i : ι) : (x i - v i) + (y i - v i) = |x i - y i| := by
    by_cases h : x i ≤ y i
    · simp only [v, min_eq_left h, sub_self, zero_add,
        abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [v, min_eq_right (le_of_not_ge h), sub_self, add_zero,
        abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
  calc
    |shiftedMean f x - shiftedMean f y| ≤
        |shiftedMean f x - shiftedMean f v| + |shiftedMean f v - shiftedMean f y| :=
      abs_sub_le _ _ _
    _ = |shiftedMean f x - shiftedMean f v| + |shiftedMean f y - shiftedMean f v| := by
      rw [abs_sub_comm (shiftedMean f v)]
    _ ≤ M * ∑ i, (x - v) i + M * ∑ i, (y - v) i := add_le_add hbx hby
    _ = M * ∑ i, |x i - y i| := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hcoord i)

theorem shiftedMean_lipschitz {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ≥0} (hM : ∀ z, f z ≤ M) :
    LipschitzWith (M * (Fintype.card ι : ℝ≥0)) (shiftedMean f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (shiftedMean f x) (shiftedMean f y) ≤ M * ∑ i, |x i - y i| :=
      shiftedMean_l1_bound hf h0 hM x y
    _ ≤ (M : ℝ) * ∑ _ : ι, dist x y := by
      apply mul_le_mul_of_nonneg_left _ M.coe_nonneg
      apply Finset.sum_le_sum
      intro i _
      exact dist_le_pi_dist x y i
    _ = ↑(M * (Fintype.card ι : ℝ≥0)) * dist x y := by simp [mul_assoc]

theorem continuous_shiftedMean {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ≥0} (hM : ∀ z, f z ≤ M) :
    Continuous (shiftedMean f) := (shiftedMean_lipschitz hf h0 hM).continuous

variable {H : Type*} [MeasurableSpace H]

theorem measurable_history_shiftedMean {f : H × (ι → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (fun x : H × (ι → ℝ) => shiftedMean (fun z => f (x.1, z)) x.2) := by
  have hm : Measurable (fun q : (H × (ι → ℝ)) × (ι → ℝ) => f (q.1.1, q.1.2 + q.2)) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

noncomputable def posteriorRate (Y : H × (ι → ℝ) → (ι → ℝ)) (h : H) (x : ι → ℝ) (i : ι) : ℝ :=
  shiftedMean (fun z => Y (h, z) i) x

theorem measurable_posteriorRate {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y) :
    Measurable (Function.uncurry (posteriorRate Y)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_history_shiftedMean ((measurable_pi_apply i).comp hY)

theorem posteriorRate_nonneg {Y : H × (ι → ℝ) → (ι → ℝ)}
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) (h : H) (x : ι → ℝ) (i : ι) :
    0 ≤ posteriorRate Y h x i := shiftedMean_nonneg (h0 h · i) x

theorem posteriorRate_le {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ} (hM : ∀ h z i, Y (h, z) i ≤ M)
    (h : H) (x : ι → ℝ) (i : ι) : posteriorRate Y h x i ≤ M := by
  exact shiftedMean_le (((measurable_pi_apply i).comp hY).comp
    (measurable_const.prodMk measurable_id)) (h0 h · i) (hM h · i) x

theorem posteriorRate_lipschitz {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ≥0} (hM : ∀ h z i, Y (h, z) i ≤ M) (h : H) :
    LipschitzWith (M * (Fintype.card ι : ℝ≥0)) (posteriorRate Y h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro i
  exact (shiftedMean_lipschitz (((measurable_pi_apply i).comp hY).comp
    (measurable_const.prodMk measurable_id)) (h0 h · i) (hM h · i)).dist_le_mul x y

theorem posteriorRate_norm_le {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ≥0} (hM : ∀ h z i, Y (h, z) i ≤ M)
    (h : H) (x : ι → ℝ) : ‖posteriorRate Y h x‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg M.coe_nonneg).mpr
  intro i
  rw [Real.norm_of_nonneg (posteriorRate_nonneg h0 h x i)]
  exact posteriorRate_le hY h0 hM h x i

end StochasticMatching
