import Logic.Propositional.Intuitionistic.Kripke.Semantics

universe u v

namespace LO.Propositional.Intuitionistic

@[simp]
def Formula.ExtendedKripkeSatisfies (P : Kripke.Model α β → Prop) (M : Kripke.Model α β) (w : α) (p : Formula β) : Prop := (P M) ∧ (p.KripkeSatisfies M w)
notation w " ⊩[" P "," M "] " p => Formula.ExtendedKripkeSatisfies P M w p

namespace Formula.ExtendedKripkeSatisfies

variable {P : Kripke.Model α β → Prop} {M : Kripke.Model α β}

local notation w "⊩" p => w ⊩[P, M] p

@[simp] lemma iff_int {p : Formula β} : (w ⊩[λ _ => True, M] p) ↔ (w ⊩ⁱ[M] p) := by simp;

end Formula.ExtendedKripkeSatisfies

@[simp]
def Theory.ExtendedKripkeSatisfies (P : Kripke.Model α β → Prop) (M : Kripke.Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, (w ⊩[P, M] p)
notation w " ⊩[" P "," M "] " Γ => Theory.ExtendedKripkeSatisfies P M w Γ

namespace Theory.ExtendedKripkeSatisfies

@[simp] lemma iff_int {Γ : Theory β} : (w ⊩[λ _ => True, M] Γ) ↔ (w ⊩ⁱ[M] Γ) := by simp [Theory.KripkeSatisfies];

end Theory.ExtendedKripkeSatisfies

@[simp]
def Formula.ExtendedKripkeConsequence (P : ∀ {α : Type u}, Kripke.Model α β → Prop) (Γ : Theory β) (p : Formula β) : Prop := ∀ {α : Type u}, ∀ (M : Kripke.Model α β) w, (w ⊩[(@P α), M] Γ) → (w ⊩[(@P α), M] p)
notation:50 Γ " ⊨[" P "] " p => Formula.ExtendedKripkeConsequence P Γ p

namespace Formula.ExtendedKripkeConsequence

-- variable {Γ : Theory β} {p q r : Formula β} {P : ∀ {α : Type u}, Kripke.Model α β → Prop}

/-
@[simp]
lemma iff_int : (Formula.ExtendedKripkeConsequence (λ _ => True) Γ p) ↔ (Formula.KripkeConsequence Γ p) := by
  simp [Formula.KripkeConsequence, Theory.KripkeSatisfies];
-/

end Formula.ExtendedKripkeConsequence

end LO.Propositional.Intuitionistic
