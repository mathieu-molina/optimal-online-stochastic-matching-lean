import Matching.HardDegreeLaw
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Analytic upper-bound potential for the symmetric Poisson hard instance.
The second argument is the fraction of unmatched vertices. The terminal
value is the matched fraction, and the initial value is `1 - e / e^e`.
The generator inequality is proved for every finite jump size. -/
open Set
namespace StochasticMatching

noncomputable def hardUpperPotential (T u : ℝ) : ℝ :=
  1 - Real.exp (1 - Real.exp T) * u ^ (Real.exp T)

noncomputable def hardUpperTimeDerivative (T u : ℝ) : ℝ :=
  Real.exp (1 - Real.exp T) * Real.exp T * u ^ (Real.exp T) * (1 - Real.log u)

noncomputable def hardSuccessProbability (u : ℝ) : ℝ := u * (1 - Real.log u)

theorem hardUpperPotential_terminal (u : ℝ) : hardUpperPotential 0 u = 1 - u := by
  simp [hardUpperPotential]

theorem hardUpperPotential_initial : hardUpperPotential 1 1 = Comparison.ratio := by
  simp [hardUpperPotential, Comparison.ratio]

theorem hardUpperPotential_zero (T : ℝ) : hardUpperPotential T 0 = 1 := by
  simp [hardUpperPotential, Real.zero_rpow (Real.exp_pos T).ne']

theorem hardUpperPotential_ge_matched {T u : ℝ} (hT : 0 ≤ T) (hu : u ∈ Icc (0 : ℝ) 1) :
    1 - u ≤ hardUpperPotential T u := by
  have hp : 1 ≤ Real.exp T := Real.one_le_exp_iff.mpr hT
  have hA : Real.exp (1 - Real.exp T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow := Real.rpow_le_self_of_le_one hu.1 hu.2 hp
  have he := mul_le_mul hA hpow (Real.rpow_nonneg hu.1 _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_mul] at he
  unfold hardUpperPotential
  linarith

theorem hardUpperPotential_bounds {T u : ℝ} (hT : 0 ≤ T) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ hardUpperPotential T u ∧ hardUpperPotential T u ≤ 1 := by
  constructor
  · exact (sub_nonneg.mpr hu.2).trans (hardUpperPotential_ge_matched hT hu)
  · unfold hardUpperPotential
    exact sub_le_self _ (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hu.1 _))

theorem hardUpperPotential_antitone (T : ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    hardUpperPotential T v ≤ hardUpperPotential T u := by
  unfold hardUpperPotential
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hu huv (Real.exp_nonneg T)) (Real.exp_nonneg _)) _

theorem hardUpperPotential_exp {u : ℝ} (hu : 0 < u) (T : ℝ) :
    hardUpperPotential T u = 1 - Real.exp (1 - Real.exp T + Real.log u * Real.exp T) := by
  rw [hardUpperPotential, Real.rpow_def_of_pos hu, Real.exp_add]

theorem hardUpperPotential_hasDerivAt {u : ℝ} (hu : 0 ≤ u) (T : ℝ) :
    HasDerivAt (fun t => hardUpperPotential t u) (hardUpperTimeDerivative T u) T := by
  rcases eq_or_lt_of_le hu with he | hu
  · subst u
    simp only [hardUpperPotential_zero]
    convert hasDerivAt_const T (1 : ℝ) using 1
    simp [hardUpperTimeDerivative, Real.zero_rpow (Real.exp_pos T).ne']
  · have he := ((hasDerivAt_const T (1 : ℝ)).sub (Real.hasDerivAt_exp T)).add
      ((Real.hasDerivAt_exp T).const_mul (Real.log u))
    have hd := (hasDerivAt_const T (1 : ℝ)).sub he.exp
    simp_rw [← hardUpperPotential_exp hu] at hd
    convert hd using 1
    rw [hardUpperTimeDerivative, Real.rpow_def_of_pos hu, Real.exp_add]
    ring

theorem rpow_backward_increment {u δ p : ℝ} (hu : 0 < u) (hδ : 0 ≤ δ) (hδu : δ ≤ u)
    (hp : 1 ≤ p) : u ^ p - (u - δ) ^ p ≤ p * u ^ (p - 1) * δ := by
  have hdiv : δ / u ≤ 1 := (div_le_one hu).mpr hδu
  have hbase : 0 ≤ 1 + -(δ / u) := by linarith
  have h := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ -(δ / u)) hp
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hu.le p)
  rw [← Real.mul_rpow hu.le hbase] at hm
  have he : u * (1 + -(δ / u)) = u - δ := by field_simp; ring
  rw [Real.rpow_sub_one hu.ne']
  rw [he] at hm
  have halg : u ^ p * (1 + p * -(δ / u)) = u ^ p - p * (u ^ p / u) * δ := by ring
  rw [halg] at hm
  linarith

theorem hardUpperPotential_increment {T u δ : ℝ} (hT : 0 ≤ T) (hu : 0 < u)
    (hδ : 0 ≤ δ) (hδu : δ ≤ u) :
    hardUpperPotential T (u - δ) - hardUpperPotential T u ≤
      Real.exp (1 - Real.exp T) * Real.exp T * u ^ (Real.exp T - 1) * δ := by
  have h := mul_le_mul_of_nonneg_left
    (rpow_backward_increment hu hδ hδu (Real.one_le_exp_iff.mpr hT))
    (Real.exp_nonneg (1 - Real.exp T))
  unfold hardUpperPotential
  nlinarith

theorem hardSuccessProbability_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ hardSuccessProbability u := by
  have hl : Real.log u ≤ 0 := Real.log_nonpos hu.1 hu.2
  exact mul_nonneg hu.1 (by linarith)

theorem hardUpperPotential_generator {T u m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    (hu : u ∈ Icc (0 : ℝ) 1) (hjump : 1 / m ≤ u) :
    m * hardSuccessProbability u *
      (hardUpperPotential T (u - 1 / m) - hardUpperPotential T u) ≤
        hardUpperTimeDerivative T u := by
  have hup : 0 < u := (one_div_pos.mpr hm).trans_le hjump
  have h := mul_le_mul_of_nonneg_left
    (hardUpperPotential_increment hT hup (one_div_nonneg.mpr hm.le) hjump)
    (mul_nonneg hm.le (hardSuccessProbability_nonneg hu))
  apply h.trans_eq
  rw [hardSuccessProbability, hardUpperTimeDerivative, Real.rpow_sub_one hup.ne']
  field_simp
  <;> ring

end StochasticMatching
