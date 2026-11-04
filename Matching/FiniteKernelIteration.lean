import Mathlib.Probability.Kernel.Composition.CompMap

/-! Finite iteration preserves a measurable projection whenever the one-step
kernels do. This is the induction principle for comparing whole finite
histories of routing and scheduling processes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

noncomputable def iterateKernel (K : Kernel A A) : ℕ → Kernel A A
  | 0 => Kernel.id
  | n + 1 => K ∘ₖ iterateKernel K n

@[simp] theorem iterateKernel_zero (K : Kernel A A) : iterateKernel K 0 = Kernel.id := rfl
@[simp] theorem iterateKernel_succ (K : Kernel A A) (n : ℕ) :
    iterateKernel K (n + 1) = K ∘ₖ iterateKernel K n := rfl

instance iterateKernel_markov (K : Kernel A A) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (iterateKernel K n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel A A); infer_instance
  | succ n ih => letI := ih; change IsMarkovKernel (K ∘ₖ iterateKernel K n); infer_instance

theorem iterateKernel_add (K : Kernel A A) (m n : ℕ) :
    iterateKernel K (m + n) = iterateKernel K m ∘ₖ iterateKernel K n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, iterateKernel_succ, ih, iterateKernel_succ, Kernel.comp_assoc]

theorem iterateKernel_projection (K : Kernel A A) (L : Kernel B B)
    (f : A → B) (hf : Measurable f)
    (hstep : ∀ a, Measure.map f (K a) = L (f a)) (n : ℕ) (a : A) :
    Measure.map f (iterateKernel K n a) = iterateKernel L n (f a) := by
  have hone : Kernel.deterministic f hf ∘ₖ K = L ∘ₖ Kernel.deterministic f hf := by
    rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext a E hE
    rw [Kernel.map_apply _ hf, Kernel.comap_apply]
    exact congrArg (fun μ : Measure B => μ E) (hstep a)
  have hn : Kernel.deterministic f hf ∘ₖ iterateKernel K n =
      iterateKernel L n ∘ₖ Kernel.deterministic f hf := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterateKernel_succ, ← Kernel.comp_assoc, hone, Kernel.comp_assoc, ih,
        ← Kernel.comp_assoc, ← iterateKernel_succ]
  rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at hn
  have h := congrArg (fun Q : Kernel A B => Q a) hn
  simpa only [Kernel.map_apply _ hf, Kernel.comap_apply] using h

theorem iterateKernel_invariant (K : Kernel A A) (S : Set A) (hS : MeasurableSet S)
    (hstep : ∀ a ∈ S, ∀ᵐ b ∂K a, b ∈ S) (n : ℕ) (a : A) (ha : a ∈ S) :
    ∀ᵐ b ∂iterateKernel K n a, b ∈ S := by
  induction n with
  | zero => change ∀ᵐ b ∂Measure.dirac a, b ∈ S; exact (ae_dirac_iff hS).mpr ha
  | succ n ih =>
    apply Kernel.ae_comp_of_ae_ae hS
    exact ih.mono (fun b hb => hstep b hb)

end StochasticMatching
