import Matching.RenewalStreamEvolution
import Matching.RenewalCountCut

/-! Pathwise accounting for consumption of the original, once-sampled streams.
The ledger retains both the original partial sums and all unread tail values. -/
open MeasureTheory Set
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

structure RenewalStreamLedger (c : σ → ℝ) (z : σ → ℕ → ℝ)
    (t : ℝ) (k : σ → ℕ) (r : σ → ℕ → ℝ) : Prop where
  past : ∀ s, renewalPartialSum (z s) (k s) ≤ c s * t
  head : ∀ s, r s 0 = renewalPartialSum (z s) (k s + 1) - c s * t
  tail : ∀ s n, r s (n + 1) = z s (k s + n + 1)

theorem renewalStreamLedger_initial (c : σ → ℝ) (z : σ → ℕ → ℝ) :
    RenewalStreamLedger c z 0 0 z := by
  constructor
  · intro s; simp [renewalPartialSum]
  · intro s; simp [renewalPartialSum]
  · intro s n; simp

theorem RenewalStreamLedger.winner {c : σ → ℝ} (hc : ∀ s, 0 ≤ c s)
    {z r : σ → ℕ → ℝ} {t : ℝ} {k : σ → ℕ} (h : RenewalStreamLedger c z t k r)
    {D : ℝ} (hD : 0 < D) (j : σ) (hpos : 0 < r j 0)
    (hw : (fun i => r i 0) ∈ variableWinner (constantRateCurve c hc D hD).service D j) :
    let p := constantRateCurve c hc D hD
    let u := cappedHit (p.service j) D (r j 0)
    RenewalStreamLedger c z (t + u) (Function.update k j (k j + 1)) (p.streamNextEvent r).2 := by
  intro p u
  have hu : 0 ≤ u := (cappedHit_bounds (z := r j 0) (p.service_continuous j) hD.le).1
  have he : c j * u = r j 0 := p.winner_service_eq hpos hw
  constructor
  · intro s
    by_cases hs : s = j
    · subst s
      rw [Function.update_self]
      have hh := h.head j
      nlinarith
    · rw [Function.update_of_ne hs]
      exact (h.past s).trans (by nlinarith [mul_nonneg (hc s) hu])
  · intro s
    by_cases hs : s = j
    · subst s
      rw [Function.update_self, p.streamNextEvent_winner_stream j hw]
      have hh := h.head j
      have ht := h.tail j 0
      rw [renewalPartialSum_succ (z j) (k j + 1)]
      simpa only [Nat.add_zero] using (show r j 1 =
        renewalPartialSum (z j) (k j + 1) + z j (k j + 1) - c j * (t + u) by nlinarith)
    · rw [Function.update_of_ne hs, p.streamNextEvent_survivor_head j s hs hw]
      change r s 0 - c s * u = _
      rw [h.head s]
      ring
  · intro s n
    by_cases hs : s = j
    · subst s
      rw [Function.update_self, p.streamNextEvent_winner_stream j hw]
      dsimp only
      rw [h.tail j (n + 1)]
      congr 1
      omega
    · rw [Function.update_of_ne hs, p.streamNextEvent_survivor_tail j s hs hw, h.tail s n]

theorem RenewalStreamLedger.count_le {c : σ → ℝ} (hc : ∀ s, 0 ≤ c s)
    {z r : σ → ℕ → ℝ} {t T : ℝ} {k : σ → ℕ} (h : RenewalStreamLedger c z t k r)
    (hT : 0 ≤ T) (ht : t ≤ T) (hz : ∀ s n, 0 ≤ z s n)
    (hunb : ∀ s, ∃ n, c s * T < renewalPartialSum (z s) n) (s : σ) :
    k s ≤ infiniteRenewalCount (c s * T) (z s) :=
  le_infiniteRenewalCount_of_sum_le (mul_nonneg (hc s) hT) (hz s) (hunb s)
    ((h.past s).trans (mul_le_mul_of_nonneg_left ht (hc s)))

theorem RenewalStreamLedger.terminal_count {c : σ → ℝ} (hc : ∀ s, 0 ≤ c s)
    {z r : σ → ℕ → ℝ} {t T : ℝ} {k : σ → ℕ} (h : RenewalStreamLedger c z t k r)
    (hT : 0 ≤ T) (ht : t ≤ T) (hz : ∀ s n, 0 ≤ z s n)
    (hterm : ∀ s, c s * (T - t) < r s 0) (s : σ) :
    infiniteRenewalCount (c s * T) (z s) = k s := by
  apply infiniteRenewalCount_eq_of_cut (mul_nonneg (hc s) hT) (hz s)
    ((h.past s).trans (mul_le_mul_of_nonneg_left ht (hc s)))
  have hh := h.head s
  have hs := hterm s
  nlinarith

end StochasticMatching
