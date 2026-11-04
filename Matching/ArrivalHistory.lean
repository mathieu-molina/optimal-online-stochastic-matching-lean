import Matching.MeasurableCursorBranches

/-! Measurable event histories retaining every arrival's waiting time and
type. A separate counter makes the meaningful finite prefix explicit.
-/
open MeasureTheory Set
namespace StochasticMatching
abbrev EventMemory (E : Type*) := ℕ × (ℕ → E)

def appendEvent {E : Type*} (x : EventMemory E × E) : EventMemory E :=
  (x.1.1 + 1, Function.update x.1.2 x.1.1 x.2)

theorem measurable_appendEvent {E : Type*} [MeasurableSpace E] : Measurable (appendEvent (E := E)) := by
  classical
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun n : ℕ => n + 1)).comp (measurable_fst.comp measurable_fst)
  · apply measurable_pi_lambda
    intro k
    have he' : MeasurableSet {x : EventMemory E × E | x.1.1 = k} :=
      (measurable_fst.comp measurable_fst) (measurableSet_singleton k)
    have he : MeasurableSet {x : EventMemory E × E | k = x.1.1} := by
      simpa only [eq_comm] using he'
    have hm : Measurable (fun x : EventMemory E × E => if k = x.1.1 then x.2 else x.1.2 k) :=
      Measurable.ite he measurable_snd
        ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst))
    convert hm using 1
    funext x
    simp only [Function.update_apply]

theorem appendEvent_at_last {E : Type*} (m : EventMemory E) (e : E) :
    (appendEvent (m, e)).2 m.1 = e := Function.update_self _ _ _

theorem appendEvent_preserves_prefix {E : Type*} (m : EventMemory E) (e : E)
    (k : ℕ) (hk : k < m.1) : (appendEvent (m, e)).2 k = m.2 k :=
  Function.update_of_ne (Nat.ne_of_lt hk) _ _

def attachMemory {A M : Type*} (x : M × (Unit ⊕ A)) : Unit ⊕ (A × M) :=
  Sum.elim (fun _ => .inl ()) (fun a => .inr (a, x.1)) x.2

theorem measurable_attachMemory {A M : Type*} [MeasurableSpace A] [MeasurableSpace M] :
    Measurable (attachMemory (A := A) (M := M)) :=
  measurable_prod_sum_elim (fun _ : M × Unit => (Sum.inl () : Unit ⊕ (A × M)))
    (fun x : M × A => Sum.inr (x.2, x.1)) measurable_const
    (measurable_inr.comp (measurable_snd.prodMk measurable_fst))

theorem attachMemory_map {A B M : Type*} (f : A → B) (m : M) (u : Unit ⊕ A) :
    Sum.map id (fun x : A × M => (f x.1, x.2)) (attachMemory (m, u)) =
      attachMemory (m, Sum.map id f u) := by cases u <;> rfl

theorem attachMemory_fst {A M : Type*} (m : M) (u : Unit ⊕ A) :
    Sum.map id Prod.fst (attachMemory (m, u)) = u := by cases u <;> rfl

def loggedEventUpdate {A E F : Type*} (U : A × E → Unit ⊕ A) (g : E → F)
    (x : (A × EventMemory F) × E) : Unit ⊕ (A × EventMemory F) :=
  attachMemory (appendEvent (x.1.2, g x.2), U (x.1.1, x.2))

theorem measurable_loggedEventUpdate {A E F : Type*} [MeasurableSpace A] [MeasurableSpace E]
    [MeasurableSpace F] (U : A × E → Unit ⊕ A) (hU : Measurable U) (g : E → F) (hg : Measurable g) :
    Measurable (loggedEventUpdate U g) :=
  measurable_attachMemory.comp
    ((measurable_appendEvent.comp ((measurable_snd.comp measurable_fst).prodMk (hg.comp measurable_snd))).prodMk
      (hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem loggedEventUpdate_projection {A B E F : Type*}
    (U : A × E → Unit ⊕ A) (V : B × F → Unit ⊕ B) (f : A → B) (g : E → F)
    (hUV : ∀ a e, Sum.map id f (U (a, e)) = V (f a, g e))
    (x : A × EventMemory F) (e : E) :
    Sum.map id (fun y : A × EventMemory F => (f y.1, y.2)) (loggedEventUpdate U g (x, e)) =
      loggedEventUpdate V id ((f x.1, x.2), g e) := by
  unfold loggedEventUpdate
  rw [attachMemory_map, hUV]
  rfl

theorem loggedEventUpdate_fst {A E F : Type*}
    (U : A × E → Unit ⊕ A) (g : E → F) (x : A × EventMemory F) (e : E) :
    Sum.map id Prod.fst (loggedEventUpdate U g (x, e)) = U (x.1, e) :=
  attachMemory_fst _ _

end StochasticMatching
