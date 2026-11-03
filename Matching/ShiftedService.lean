import Matching.ServiceExecution

/-! Deterministic restart of an unfinished service segment. A rejected
arrival advances time and subtracts provided service without changing the
future job-completion times.
-/

open MeasureTheory Set
namespace StochasticMatching

theorem cappedHit_shift {a : ℝ → ℝ} (ha : Continuous a) {T s z : ℝ}
    (hm : MonotoneOn a (Icc 0 T)) (hs0 : 0 ≤ s) (hsT : s < T) (hz : a s < z) :
    cappedHit (fun u => a (s + u) - a s) (T - s) (z - a s) = cappedHit a T z - s := by
  let b : ℝ → ℝ := fun u => a (s + u) - a s
  have hb : Continuous b := (ha.comp (continuous_const.add continuous_id)).sub continuous_const
  have hT : 0 ≤ T := hs0.trans hsT.le
  have hD : 0 ≤ T - s := sub_nonneg.mpr hsT.le
  have hbmono : MonotoneOn b (Icc 0 (T-s)) := by
    intro u hu v hv huv
    exact sub_le_sub_right (hm ⟨by linarith [hu.1], by linarith [hu.2]⟩
      ⟨by linarith [hv.1], by linarith [hv.2]⟩ (by linarith)) _
  have hτ : s < cappedHit a T z := by
    exact lt_of_not_ge (fun h => (not_le.mpr hz) ((cappedHit_le_iff ha hT hm hs0 hsT).mp h))
  have hτT := (cappedHit_bounds (z := z) ha hT).2
  have hη := cappedHit_bounds (z := z - a s) hb hD
  change cappedHit b (T-s) (z-a s) = _
  apply le_antisymm
  · by_cases hlast : cappedHit a T z < T
    · have hreached := (cappedHit_le_iff ha hT hm (cappedHit_bounds ha hT).1 hlast).mp le_rfl
      apply cappedHit_le_of_reached hbmono ⟨by linarith, by linarith⟩
      dsimp only [b]
      simpa only [add_sub_cancel] using sub_le_sub_right hreached (a s)
    · have he : cappedHit a T z = T := le_antisymm hτT (le_of_not_gt hlast)
      simpa only [he] using hη.2
  · by_cases hlast : cappedHit b (T-s) (z-a s) < T-s
    · have hreached := (cappedHit_le_iff hb hD hbmono hη.1 hlast).mp le_rfl
      have horig : cappedHit a T z ≤ s + cappedHit b (T-s) (z-a s) := by
        apply cappedHit_le_of_reached hm ⟨by linarith [hη.1], by linarith [hη.2]⟩
        dsimp only [b] at hreached
        linarith
      linarith
    · linarith [hη.2]

namespace ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def afterTime (p : ServiceCurveFamily ι) (s : ℝ) (hs0 : 0 ≤ s)
    (hsT : s < p.deadline) : ServiceCurveFamily ι where
  deadline := p.deadline - s
  deadline_pos := sub_pos.mpr hsT
  service i u := p.service i (s + u) - p.service i s
  rate i u := p.rate i (s + u)
  service_continuous i := ((p.service_continuous i).comp (continuous_const.add continuous_id)).sub continuous_const
  rate_continuous i := (p.rate_continuous i).comp (continuous_const.add continuous_id)
  service_monotone i := by
    intro u hu v hv huv
    exact sub_le_sub_right (p.service_monotone i
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
      ⟨by linarith [hv.1], by linarith [hv.2]⟩ (by linarith)) _
  service_zero i := by simp
  rate_nonneg i u hu := p.rate_nonneg i _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  service_deriv i u hu := by
    have h := (p.service_deriv i (s+u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp u
      ((hasDerivAt_id u).const_add s)
    simpa only [mul_one] using h.sub_const (p.service i s)

theorem afterTime_clock (p : ServiceCurveFamily ι) (s : ℝ) (hs0 : 0 ≤ s)
    (hsT : s < p.deadline) (i : ι) {z : ℝ} (hz : p.service i s < z) :
    cappedHit ((p.afterTime s hs0 hsT).service i) (p.afterTime s hs0 hsT).deadline
      (z - p.service i s) = cappedHit (p.service i) p.deadline z - s :=
  cappedHit_shift (p.service_continuous i) (p.service_monotone i) hs0 hsT hz

end ServiceCurveFamily
end StochasticMatching
