module

public import Foundation.ProvabilityLogic.Kripke.Basic

/-!
# Rooted Kripke models
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

structure RootedModel (κ : Type*) [Nonempty κ] (α : Type*) extends Model κ α where
  root : κ
  root_rel : ∀ x, x ≠ root → toModel.Rel root x

namespace RootedModel

variable {M : RootedModel κ α} {x : M.World}

abbrev NonRoot (M : RootedModel κ α) := { x : M.World // x ≠ M.root }

@[simp, grind .]
lemma not_rel_root [IsTrans _ M.Rel] [Std.Irrefl M.Rel] : x ⊀ M.root := by
  by_cases hx : x = M.root;
  . subst hx;
    exact Std.Irrefl.irrefl (r := M.Rel) _;
  . exact fun h ↦ Std.Irrefl.irrefl (r := M.Rel) _ (IsTrans.trans _ _ _ h (M.root_rel x hx));

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
