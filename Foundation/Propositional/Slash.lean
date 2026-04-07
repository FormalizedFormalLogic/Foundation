module

public import Foundation.Propositional.Logic.Basic
public import Foundation.Propositional.Entailment.Corsi

@[expose] public section

namespace LO.Propositional

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} {φ ψ : Formula α}

section

/-
  Context-less version of Aczel's slash.
-/
@[grind]
def AczelSlash (𝓢 : S) : Formula α → Prop
  | #a => 𝓢 ⊢ #a
  | ⊥ => False
  | φ ⋎ ψ => AczelSlash 𝓢 φ ∨ AczelSlash 𝓢 ψ
  | φ ⋏ ψ => AczelSlash 𝓢 φ ∧ AczelSlash 𝓢 ψ
  | φ 🡒 ψ => 𝓢 ⊢ (φ 🡒 ψ) ∧ (AczelSlash 𝓢 φ → AczelSlash 𝓢 ψ)
notation:50 "∕ₐ[" 𝓢 "] " φ:max => AczelSlash 𝓢 φ

namespace AczelSlash

@[grind =] lemma def_atom {a : α} : ∕ₐ[𝓢] (#a) ↔ 𝓢 ⊢ #a := by grind;
@[simp, grind .] lemma def_bot : ¬(∕ₐ[𝓢] ⊥) := by tauto;


@[grind =] lemma def_or  : ∕ₐ[𝓢] (φ ⋎ ψ) ↔ ∕ₐ[𝓢] φ ∨ ∕ₐ[𝓢] ψ := by simp [AczelSlash];
@[grind =] lemma def_and : ∕ₐ[𝓢] (φ ⋏ ψ) ↔ ∕ₐ[𝓢] φ ∧ ∕ₐ[𝓢] ψ := by simp [AczelSlash];
@[grind =] lemma def_imp : ∕ₐ[𝓢] (φ 🡒 ψ) ↔ 𝓢 ⊢ (φ 🡒 ψ) ∧ (∕ₐ[𝓢] φ → ∕ₐ[𝓢] ψ) := by simp [AczelSlash];
@[grind =] lemma def_neg : ∕ₐ[𝓢] (∼φ) ↔ 𝓢 ⊢ ∼φ ∧ ¬∕ₐ[𝓢] φ := by simp [Formula.neg_def, def_imp];
@[grind =] lemma def_top : ∕ₐ[𝓢] ⊤ ↔ 𝓢 ⊢ ⊤ := by grind [Formula.top_def];

@[grind <=]
lemma mdp : ∕ₐ[𝓢] (φ 🡒 ψ) → ∕ₐ[𝓢] φ → ∕ₐ[𝓢] ψ := by grind;

end AczelSlash


lemma disjunctive_of_iff_aczelSlash_provable (h : ∀ {φ : Formula α}, ∕ₐ[𝓢] φ ↔ 𝓢 ⊢ φ) : Entailment.Disjunctive 𝓢 := ⟨by grind⟩

end

end LO.Propositional

end
