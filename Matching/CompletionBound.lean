import Mathlib.Data.Fintype.Card

namespace StochasticMatching

/-- Each step completes one previously unfinished job. Therefore the number
of such steps cannot exceed the number of initially unfinished jobs. -/
theorem completion_count_bound {ι : Type*} [Fintype ι]
    (done : ℕ → Finset ι) (n : ℕ)
    (step : ∀ k < n, (done (k + 1)).card = (done k).card + 1) :
    n ≤ Fintype.card ι - (done 0).card := by
  have count : ∀ k ≤ n, (done k).card = (done 0).card + k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        rw [step k (by omega), ih (by omega)]
        omega
  have bound := Finset.card_le_univ (done n)
  rw [count n (by omega)] at bound
  omega

end StochasticMatching
