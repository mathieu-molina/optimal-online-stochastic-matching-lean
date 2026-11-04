import Matching.AdaptiveLaw

/-! A budget equal to the number of jobs never forces an adaptive execution
to stop while active jobs remain. Each recursive completion removes one label.
-/

open MeasureTheory Set

namespace StochasticMatching

theorem survivor_card {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    Fintype.card {i : ι // i ≠ j} + 1 = Fintype.card ι := by
  have h := Fintype.card_subtype_compl (fun i : ι => i = j)
  have hp : Fintype.card {i : ι // i = j} = 1 := by
    simp
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  rw [hp] at h
  calc
    Fintype.card {i : ι // i ≠ j} + 1 = (Fintype.card ι - 1) + 1 :=
      congrArg (fun a : ℕ => a + 1) h
    _ = Fintype.card ι := Nat.sub_add_cancel hn

namespace AdaptivePlan

universe u v w

variable {E : Type w} [MeasurableSpace E]

def Exhaustive : {n : ℕ} → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    AdaptivePlan E n H ι → Prop
  | 0, _, ι, _, _, _, _ => IsEmpty ι
  | n + 1, _, _, _, _, _, p => ∀ j, Exhaustive (p.2.2 j)

theorem exhaustive_of_card_le {n : ℕ} {H : Type u} {ι : Type v}
    [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
    (p : AdaptivePlan E n H ι) (hn : Fintype.card ι ≤ n) : Exhaustive p := by
  induction n generalizing H ι with
  | zero =>
    exact Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
  | succ n ih =>
    intro j
    apply ih
    have hc := survivor_card j
    omega

end AdaptivePlan
end StochasticMatching
