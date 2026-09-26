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
  root : toModel.World
  root_rel : ∀ x, x ≠ root → root ≺ x

namespace RootedModel

instance : CoeFun (RootedModel κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

variable {M : RootedModel κ α} {x : M.World}

abbrev NonRoot (M : RootedModel κ α) := { x : M.World // x ≠ M.root }

@[simp, grind .]
lemma not_rel_root [IsTrans _ M.Rel] [Std.Irrefl M.Rel] : x ⊀ M.root := by
  by_cases hx : x = M.root;
  · subst hx;
    exact Std.Irrefl.irrefl (r := M.Rel) _;
  · by_contra!;
    exact Std.Irrefl.irrefl (r := M.Rel) _ (IsTrans.trans _ _ _ this (M.root_rel x hx));

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
