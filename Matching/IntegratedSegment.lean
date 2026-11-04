import Matching.TimedRun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Service increments obtained from actual time integrals. -/

open MeasureTheory

namespace StochasticMatching

variable {ι : Type*}

noncomputable def segmentWork (r : ℝ → ι → ℝ) (a b : ℝ) (i : ι) : ℝ :=
  ∫ t in a..b, r t i

theorem segmentWork_nonneg {r : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hr : ∀ i, ∀ t ∈ Set.Icc a b, 0 ≤ r t i) (i : ι) :
    0 ≤ segmentWork r a b i :=
  intervalIntegral.integral_nonneg hab (hr i)

theorem segmentWork_le {r : ℝ → ι → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hI : ∀ i, IntervalIntegrable (fun t => r t i) volume a b)
    (hr : ∀ i, ∀ t ∈ Set.Icc a b, r t i ≤ M) (i : ι) :
    segmentWork r a b i ≤ M * (b - a) := by
  have h := intervalIntegral.integral_mono_on hab (hI i)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b) (hr i)
  simpa [segmentWork, mul_comm] using h

theorem segmentWork_zero_of_rate_zero {r : ℝ → ι → ℝ} {a b : ℝ}
    (hab : a ≤ b) (i : ι) (hr : ∀ t ∈ Set.Icc a b, r t i = 0) :
    segmentWork r a b i = 0 := by
  have heq : (∫ t in a..b, r t i) = ∫ _ in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hr t (by simpa only [Set.uIcc_of_le hab] using ht)
  simpa [segmentWork] using heq

theorem segmentWork_add_adjacent {r : ℝ → ι → ℝ} {a b c : ℝ}
    (hab : ∀ i, IntervalIntegrable (fun t => r t i) volume a b)
    (hbc : ∀ i, IntervalIntegrable (fun t => r t i) volume b c) (i : ι) :
    segmentWork r a b i + segmentWork r b c i = segmentWork r a c i :=
  intervalIntegral.integral_add_adjacent_intervals (hab i) (hbc i)

theorem segmentWork_self (r : ℝ → ι → ℝ) (a : ℝ) (i : ι) :
    segmentWork r a a i = 0 := by simp [segmentWork]

variable [DecidableEq ι]
open CompletionState

/-- A segment reaching exactly one fresh completion supplies both the state
invariant and a bounded timed step. Other unfinished jobs must stay below demand
at the endpoint; completed jobs receive zero rate throughout the segment. -/
theorem integrated_completion_step {z : ι → ℝ} {s : CompletionState ι}
    (hs : Valid z s) (r : ℝ → ι → ℝ) (a b M : ℝ) (j : ι)
    (hab : a ≤ b) (hj : j ∉ s.completed)
    (hI : ∀ i, IntervalIntegrable (fun t => r t i) volume a b)
    (hlo : ∀ i, ∀ t ∈ Set.Icc a b, 0 ≤ r t i)
    (hhi : ∀ i, ∀ t ∈ Set.Icc a b, r t i ≤ M)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Set.Icc a b, r t i = 0)
    (hhit : s.served j + segmentWork r a b j = z j)
    (hrest : ∀ i, i ∉ insert j s.completed →
      s.served i + segmentWork r a b i < z i) :
    Valid z (afterCompletion s (segmentWork r a b) j) ∧
      BoundedCompletionStep M (b - a) s
        (afterCompletion s (segmentWork r a b) j) := by
  have hnonneg := segmentWork_nonneg hab hlo
  have hzero : ∀ i ∈ s.completed, segmentWork r a b i = 0 := by
    intro i hi
    exact segmentWork_zero_of_rate_zero hab i (hfrozen i hi)
  refine ⟨afterCompletion_valid hs _ j hnonneg hzero hhit hrest, ?_⟩
  refine ⟨afterCompletion_step s _ j hj hnonneg hzero, sub_nonneg.mpr hab, ?_⟩
  intro i
  change s.served i + segmentWork r a b i - s.served i ≤ M * (b - a)
  simpa using segmentWork_le hab hI hhi i

end StochasticMatching
