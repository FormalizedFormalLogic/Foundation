module

public import Foundation.ProvabilityLogic.Logic.Basic
public import Foundation.ProvabilityLogic.Formula.Substitution

/-!
# Quasi-normal sums of logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula

variable {α : Type*}

@[grind]
inductive Logic.sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {A}    : A ∈ L₁ → sumQuasiNormal L₁ L₂ A
  | mem₂ {A}    : A ∈ L₂ → sumQuasiNormal L₁ L₂ A
  | mdp  {A B}  : sumQuasiNormal L₁ L₂ (A 🡒 B) → sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ B
  | subst {A s} : sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ (A⟦s⟧)

infix:50 " +ᴸ " => Logic.sumQuasiNormal

namespace Logic.sumQuasiNormal

variable {L₁ L₂ X Y : Logic α}

@[grind .] lemma subset_left : L₁ ⊆ (L₁ +ᴸ L₂) := fun _ ↦ mem₁

@[grind .] lemma subset_right : L₂ ⊆ (L₁ +ᴸ L₂) := fun _ ↦ mem₂

lemma subset_iff : (L₁ +ᴸ X) ⊆ (L₁ +ᴸ Y) ↔ X ⊆ (L₁ +ᴸ Y) := by
  constructor;
  . intro h A hA;
    exact h (mem₂ hA);
  . intro h A hA;
    induction hA with
    | mem₁ hA => exact mem₁ hA;
    | mem₂ hA => exact h hA;
    | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
    | subst _ ih => exact subst ih;

end Logic.sumQuasiNormal

end FFL.ProvabilityLogic

end
