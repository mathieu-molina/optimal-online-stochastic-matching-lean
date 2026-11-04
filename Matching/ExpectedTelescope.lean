import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
Finite telescoping of local conditional identities. These lemmas handle the
expectation/tower-property part of a finite-stage Dynkin argument. They do not
establish a generator identity for the posterior scheduling policy.
-/

open MeasureTheory
open scoped BigOperators

namespace StochasticMatching

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_eq_of_conditional_eq [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (h : μ[f | m] =ᵐ[μ] μ[g | m]) :
    (∫ ω, f ω ∂μ) = ∫ ω, g ω ∂μ := by
  have hi := integral_congr_ae h
  simpa only [integral_condExp hm] using hi

theorem expected_telescope
    (n : ℕ) (F G : ℕ → Ω → ℝ)
    (hF : ∀ k ≤ n, Integrable (F k) μ)
    (hG : ∀ k < n, Integrable (G k) μ)
    (hstep : ∀ k < n,
      (∫ ω, F (k + 1) ω - F k ω ∂μ) = ∫ ω, G k ω ∂μ) :
    (∫ ω, F n ω ∂μ) =
      (∫ ω, F 0 ω ∂μ) + ∫ ω, ∑ k ∈ Finset.range n, G k ω ∂μ := by
  have hlocal : ∀ k ∈ Finset.range n,
      (∫ ω, G k ω ∂μ) = (∫ ω, F (k + 1) ω ∂μ) - ∫ ω, F k ω ∂μ := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [← hstep k hkn]
    exact integral_sub (hF (k + 1) (by omega)) (hF k (by omega))
  rw [integral_finset_sum (Finset.range n) (fun k hk => hG k (Finset.mem_range.mp hk))]
  have hsum : (∑ k ∈ Finset.range n, ∫ ω, G k ω ∂μ) =
      (∫ ω, F n ω ∂μ) - ∫ ω, F 0 ω ∂μ := by
    calc
      _ = ∑ k ∈ Finset.range n,
          ((∫ ω, F (k + 1) ω ∂μ) - ∫ ω, F k ω ∂μ) :=
        Finset.sum_congr rfl hlocal
      _ = _ := Finset.sum_range_sub (fun k => ∫ ω, F k ω ∂μ) n
  linarith

theorem expected_telescope_of_conditional [IsFiniteMeasure μ]
    (n : ℕ) (F G : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ k < n, m k ≤ mΩ)
    (hF : ∀ k ≤ n, Integrable (F k) μ)
    (hG : ∀ k < n, Integrable (G k) μ)
    (hstep : ∀ k < n,
      μ[(fun ω => F (k + 1) ω - F k ω) | m k] =ᵐ[μ] μ[G k | m k]) :
    (∫ ω, F n ω ∂μ) =
      (∫ ω, F 0 ω ∂μ) + ∫ ω, ∑ k ∈ Finset.range n, G k ω ∂μ := by
  apply expected_telescope n F G hF hG
  intro k hk
  exact integral_eq_of_conditional_eq (hm k hk) (hstep k hk)

theorem expected_telescope_lower_bound
    (n : ℕ) (F G : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (hF : ∀ k ≤ n, Integrable (F k) μ)
    (hG : ∀ k < n, Integrable (G k) μ)
    (hstep : ∀ k < n,
      (∫ ω, F (k + 1) ω - F k ω ∂μ) = ∫ ω, G k ω ∂μ)
    (hlower : ∀ k < n, b k ≤ ∫ ω, G k ω ∂μ) :
    (∫ ω, F 0 ω ∂μ) + ∑ k ∈ Finset.range n, b k ≤ ∫ ω, F n ω ∂μ := by
  rw [expected_telescope n F G hF hG hstep]
  apply add_le_add_left
  rw [integral_finset_sum (Finset.range n) (fun k hk => hG k (Finset.mem_range.mp hk))]
  exact Finset.sum_le_sum (fun k hk => hlower k (Finset.mem_range.mp hk))

/-- A random number of completed stages can be extended to a fixed length
by assigning zero cost after its terminal stage. -/
theorem sum_stopped_cost (n τ : ℕ) (hτ : τ ≤ n) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, if k < τ then g k else 0) =
      ∑ k ∈ Finset.range τ, g k := by
  have hsubset : Finset.range τ ⊆ Finset.range n := Finset.range_mono hτ
  calc
    _ = ∑ k ∈ Finset.range τ, if k < τ then g k else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      exact if_neg (not_lt.mpr hk)
    _ = _ := Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))

theorem expected_stopped_telescope [IsFiniteMeasure μ]
    (n : ℕ) (τ : Ω → ℕ) (hτ : ∀ ω, τ ω ≤ n)
    (F G : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ k < n, m k ≤ mΩ)
    (hF : ∀ k ≤ n, Integrable (fun ω => F (min k (τ ω)) ω) μ)
    (hG : ∀ k < n, Integrable (fun ω => if k < τ ω then G k ω else 0) μ)
    (hstep : ∀ k < n,
      μ[(fun ω => F (min (k + 1) (τ ω)) ω - F (min k (τ ω)) ω) | m k] =ᵐ[μ]
        μ[(fun ω => if k < τ ω then G k ω else 0) | m k]) :
    (∫ ω, F (τ ω) ω ∂μ) =
      (∫ ω, F 0 ω ∂μ) + ∫ ω, ∑ k ∈ Finset.range (τ ω), G k ω ∂μ := by
  have ht := expected_telescope_of_conditional n
    (fun k ω => F (min k (τ ω)) ω)
    (fun k ω => if k < τ ω then G k ω else 0) m hm hF hG hstep
  simpa only [Nat.min_eq_right (hτ _), Nat.zero_min,
    sum_stopped_cost n _ (hτ _) (fun k => G k _)] using ht

end StochasticMatching
