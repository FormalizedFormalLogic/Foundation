import Foundation.FirstOrder.SetTheory.Basic

/-!
# Well-Founded Model of Set Theory

In type theory, a transitive model (at the meta level) is nonsense. Therefore, we instead work with a well-founded model.
-/

namespace LO.FirstOrder.SetTheory

class WellFoundedModel (V : Type*) extends SetStructure V where
  wf : WellFounded (α := V) (· ∈ ·)

namespace WellFoundedModel

variable {V : Type*} [WellFoundedModel V]

instance : IsWellFounded (α := V) (· ∈ ·) := ⟨wf⟩

instance : WellFoundedRelation V where
  rel := (· ∈ ·)
  wf := wf

noncomputable def rec' {C : V → Sort*}
    (h : (x : V) → ((y : V) → y ∈ x → C y) → C x)
    (x : V) : C x :=
  WellFounded.recursion wf x h

theorem ind {P : V → Prop}
    (h : ∀ x, (∀ y ∈ x, P y) → P x)
    (x : V) : P x :=
  WellFounded.induction wf x h

end WellFoundedModel

end LO.FirstOrder.SetTheory
