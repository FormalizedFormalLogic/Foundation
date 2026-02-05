module

public import Foundation.FirstOrder.SetTheory.Universe

@[expose] public section
namespace LO.FirstOrder.SetTheory

abbrev TransitiveModel.{u} := Set Universe.{u}

namespace TransitiveModel

variable {U : TransitiveModel}

lemma wellFounded : WellFounded (α := U) (· ∈ ·) := Universe.wellFounded.onFun (f := Subtype.val)

@[elab_as_elim]
theorem ind {P : U → Prop} (ind : ∀ x, (∀ y ∈ x, P y) → P x) (x : U) : P x :=
  wellFounded.induction x ind

noncomputable def model [Small U] : Universe := .mk U

end TransitiveModel

end LO.FirstOrder.SetTheory
