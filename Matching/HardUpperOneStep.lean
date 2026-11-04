import Matching.HardUpperPotential
import Matching.FirstStepIdentity

/-! The finite-horizon Bellman supersolution inequality. It includes the
no-arrival atom and integrates over the first Poisson arrival, without a
fluid limit or a fixed-count approximation. -/
open MeasureTheory Set
namespace StochasticMatching

theorem continuous_hardUpperPotential_time {u : ℝ} (hu : 0 ≤ u) :
    Continuous (fun T => hardUpperPotential T u) :=
  continuous_iff_continuousAt.mpr (fun T => (hardUpperPotential_hasDerivAt hu T).continuousAt)

theorem continuous_hardUpperTimeDerivative_time {u : ℝ} (hu : 0 ≤ u) :
    Continuous (fun T => hardUpperTimeDerivative T u) := by
  rcases eq_or_lt_of_le hu with he | hu
  · subst u
    have he (T : ℝ) : hardUpperTimeDerivative T 0 = 0 := by
      simp [hardUpperTimeDerivative, Real.zero_rpow (Real.exp_pos T).ne']
    simp_rw [he]
    exact continuous_const
  · simp only [hardUpperTimeDerivative, Real.rpow_def_of_pos hu]
    fun_prop

theorem hardUpper_one_step {T u m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    (hu : u ∈ Icc (0 : ℝ) 1) (hjump : 1 / m ≤ u) :
    Real.exp (-m * T) * (1 - u) +
      (∫ t in (0 : ℝ)..T, Real.exp (-m * t) * m *
        ((1 - hardSuccessProbability u) * hardUpperPotential (T - t) u +
          hardSuccessProbability u * hardUpperPotential (T - t) (u - 1 / m))) ≤
      hardUpperPotential T u := by
  let S : ℝ → ℝ := fun t => Real.exp (-m * t)
  let F : ℝ → ℝ := fun t => hardUpperPotential (T - t) u
  let D : ℝ → ℝ := fun t => -hardUpperTimeDerivative (T - t) u
  let J : ℝ → ℝ := fun t => m *
    ((1 - hardSuccessProbability u) * hardUpperPotential (T - t) u +
      hardSuccessProbability u * hardUpperPotential (T - t) (u - 1 / m))
  have hS : Continuous S := by dsimp [S]; fun_prop
  have hF : Continuous F := (continuous_hardUpperPotential_time hu.1).comp
    (continuous_const.sub continuous_id)
  have hD : Continuous D := ((continuous_hardUpperTimeDerivative_time hu.1).comp
    (continuous_const.sub continuous_id)).neg
  have hG : Continuous (fun t => hardUpperPotential (T - t) (u - 1 / m)) :=
    (continuous_hardUpperPotential_time (sub_nonneg.mpr hjump)).comp
      (continuous_const.sub continuous_id)
  have hJ : Continuous J := continuous_const.mul ((continuous_const.mul hF).add (continuous_const.mul hG))
  have hSd (t : ℝ) : HasDerivAt S (-m * S t) t := by
    convert ((hasDerivAt_id t).const_mul (-m)).exp using 1 <;> simp [S, mul_comm]
  have hFd (t : ℝ) : HasDerivAt F (D t) t := by
    convert (hardUpperPotential_hasDerivAt hu.1 (T - t)).comp t
      ((hasDerivAt_const t T).sub (hasDerivAt_id t)) using 1 <;> simp [F, D]
  have hid := first_step_identity T S F D (fun _ => m) J hS hF hD continuous_const hJ
    (by simp [S]) (fun t _ => hSd t) (fun t _ => hFd t)
  have hcont : Continuous (fun t => S t * (D t + J t - m * F t)) := by fun_prop
  have hle : (∫ t in (0 : ℝ)..T, S t * (D t + J t - m * F t)) ≤ 0 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hT (hcont.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T) (g := fun _ => (0 : ℝ)) ?_
    · simpa using h
    intro t ht
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    have hg := hardUpperPotential_generator (sub_nonneg.mpr ht.2) hm hu hjump
    dsimp [D, J, F]
    nlinarith
  rw [← hid] at hle
  have hterm : F T = 1 - u := by simp [F, hardUpperPotential_terminal]
  have hzero : F 0 = hardUpperPotential T u := by simp [F]
  rw [hterm, hzero] at hle
  have he : (fun t => S t * J t) = fun t => Real.exp (-m * t) * m *
      ((1 - hardSuccessProbability u) * hardUpperPotential (T - t) u +
        hardSuccessProbability u * hardUpperPotential (T - t) (u - 1 / m)) := by
    funext t
    dsimp [S, J]
    ring
  rw [he] at hle
  exact sub_nonpos.mp hle

end StochasticMatching
