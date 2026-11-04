import Matching.ComparisonPotential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! The degree distribution in the unweighted matching hard instance.
Index k represents degree k+2. Its probability generating function is
Psi(x) = x + (1-x) log(1-x). This is setup for the upper-bound direction;
it does not by itself assert a competitive-ratio impossibility theorem. -/
open Filter Real
open scoped BigOperators Topology ENNReal NNReal
namespace StochasticMatching

noncomputable def hardDegreeWeight (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * (k + 2))

theorem hardDegreeWeight_pos (k : ℕ) : 0 < hardDegreeWeight k := by
  unfold hardDegreeWeight
  positivity

theorem hardDegreeWeight_telescoping (k : ℕ) :
    hardDegreeWeight k = 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
  unfold hardDegreeWeight
  field_simp
  <;> ring

theorem hardDegreeWeight_partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, hardDegreeWeight k) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hardDegreeWeight_telescoping]
    push_cast
    ring

theorem hardDegreeWeight_hasSum : HasSum hardDegreeWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => (hardDegreeWeight_pos k).le) 1).mpr
  simp_rw [hardDegreeWeight_partial_sum]
  simpa using tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def hardDegreePMF : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (hardDegreeWeight k),
    ENNReal.hasSum_coe.mpr (by
      simpa only [ENNReal.coe_toNNReal (ne_of_lt ENNReal.ofReal_lt_top),
        Real.toNNReal_one, ENNReal.coe_one] using
        hardDegreeWeight_hasSum.toNNReal (fun k => (hardDegreeWeight_pos k).le))⟩

noncomputable def hardGeneratingFunction (x : ℝ) : ℝ := x + (1 - x) * Real.log (1 - x)

theorem hardDegreeWeight_generating {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k => hardDegreeWeight k * x ^ (k + 2)) (hardGeneratingFunction x) := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have htail : HasSum (fun k : ℕ => x ^ (k + 2) / ((k : ℝ) + 2)) (-Real.log (1 - x) - x) := by
    have h := (hasSum_nat_add_iff' 1).mpr hlog
    norm_num [Nat.cast_add, add_assoc] at h ⊢
    exact h
  have h := (hlog.mul_left x).sub htail
  have he (k : ℕ) : x * (x ^ (k + 1) / ((k : ℝ) + 1)) - x ^ (k + 2) / ((k : ℝ) + 2) =
      hardDegreeWeight k * x ^ (k + 2) := by
    rw [hardDegreeWeight_telescoping]
    rw [show x * (x ^ (k + 1) / ((k : ℝ) + 1)) = x ^ (k + 2) / ((k : ℝ) + 1) by
      rw [← mul_div_assoc, ← pow_succ']]
    ring
  convert h using 1
  · funext k
    exact (he k).symm
  · unfold hardGeneratingFunction
    ring

theorem hardDegreeWeight_generating_one :
    HasSum (fun k => hardDegreeWeight k * (1 : ℝ) ^ (k + 2)) (hardGeneratingFunction 1) := by
  simpa [hardGeneratingFunction] using hardDegreeWeight_hasSum

theorem hardGeneratingFunction_zero : hardGeneratingFunction 0 = 0 := by simp [hardGeneratingFunction]
theorem hardGeneratingFunction_one : hardGeneratingFunction 1 = 1 := by simp [hardGeneratingFunction]

theorem hardDegreeWeight_generating_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun k => hardDegreeWeight k * x ^ (k + 2)) (hardGeneratingFunction x) := by
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · exact hardDegreeWeight_generating hx.1 hlt
  · exact hardDegreeWeight_generating_one

theorem hardGeneratingFunction_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ hardGeneratingFunction x :=
  (hardDegreeWeight_generating_Icc hx).tsum_eq ▸
    tsum_nonneg (fun k => mul_nonneg (hardDegreeWeight_pos k).le (pow_nonneg hx.1 _))

theorem hardGeneratingFunction_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    hardGeneratingFunction x ≤ 1 := by
  apply hasSum_le _ (hardDegreeWeight_generating_Icc hx) hardDegreeWeight_hasSum
  intro k
  exact mul_le_of_le_one_right (hardDegreeWeight_pos k).le (pow_le_one₀ hx.1 hx.2)

theorem one_sub_hardGeneratingFunction (x : ℝ) :
    1 - hardGeneratingFunction x = (1 - x) * (1 - Real.log (1 - x)) := by
  unfold hardGeneratingFunction
  ring

theorem hasDerivAt_hardGeneratingFunction {x : ℝ} (hx : x < 1) :
    HasDerivAt hardGeneratingFunction (-Real.log (1 - x)) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hn : 1 - x ≠ 0 := by linarith
  have hd := (hasDerivAt_id x).add (h.mul (h.log (by simpa using hn)))
  convert hd using 1
  dsimp
  field_simp [hn]
  <;> ring

end StochasticMatching
