module

public import Foundation.ProvabilityLogic.Logic.SumQuasiNormal

/-!
# Normal sums of logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Formula

variable {α : Type*}

@[grind]
inductive Logic.sumNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {A}    : A ∈ L₁ → sumNormal L₁ L₂ A
  | mem₂ {A}    : A ∈ L₂ → sumNormal L₁ L₂ A
  | mdp  {A B}  : sumNormal L₁ L₂ (A 🡒 B) → sumNormal L₁ L₂ A → sumNormal L₁ L₂ B
  | subst {A s} : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (A⟦s⟧)
  | nec  {A}    : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (□A)

infix:50 " ⊕ᴸ " => Logic.sumNormal

namespace Logic.sumNormal

variable {L₁ L₂ : Logic α}

@[grind .] lemma subset_left : L₁ ⊆ (L₁ ⊕ᴸ L₂) := fun _ ↦ mem₁

@[grind .] lemma subset_right : L₂ ⊆ (L₁ ⊕ᴸ L₂) := fun _ ↦ mem₂

lemma sumQuasiNormal_subset : (L₁ +ᴸ L₂) ⊆ (L₁ ⊕ᴸ L₂) := by
  intro A h;
  induction h with
  | mem₁ h => exact mem₁ h;
  | mem₂ h => exact mem₂ h;
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
  | subst _ ih => exact subst ih;

end Logic.sumNormal

end FFL.ProvabilityLogic

end
