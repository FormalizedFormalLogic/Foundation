import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi

namespace LO.Propositional

variable {α : Type*}
variable {L : Logic α} {φ ψ : Formula α}

def KleeneSlash (L : Logic α) : Formula α → Prop
  | #a => L ⊢ #a
  | ⊥ => False
  | φ ⋎ ψ => KleeneSlash L φ ∨ KleeneSlash L ψ
  | φ ⋏ ψ => KleeneSlash L φ ∧ KleeneSlash L ψ
  | φ ➝ ψ => L ⊢ (φ ➝ ψ) ∧ (KleeneSlash L φ → KleeneSlash L ψ)
notation:50 "∕[" L "] " φ:max => KleeneSlash L φ

namespace KleeneSlash

lemma def_atom {a : α} : ∕[L] (#a) ↔ L ⊢ #a := by simp [KleeneSlash];

@[simp, grind .]
lemma def_bot : ¬(∕[L] ⊥) := by simp [KleeneSlash];

@[simp, grind .]
lemma def_top [Entailment.HasImpId L] : ∕[L] ⊤ := by
  rw [Formula.top_def];
  constructor;
  . exact Entailment.Corsi.impId;
  . tauto;

@[grind =] lemma def_or  : ∕[L] (φ ⋎ ψ) ↔ ∕[L] φ ∨ ∕[L] ψ := by simp [KleeneSlash];
@[grind =] lemma def_and : ∕[L] (φ ⋏ ψ) ↔ ∕[L] φ ∧ ∕[L] ψ := by simp [KleeneSlash];
@[grind =] lemma def_imp : ∕[L] (φ ➝ ψ) ↔ L ⊢ (φ ➝ ψ) ∧ (∕[L] φ → ∕[L] ψ) := by simp [KleeneSlash];
@[grind =] lemma def_neg : ∕[L] (∼φ) ↔ L ⊢ ∼φ ∧ ¬∕[L] φ := by simp [Formula.neg_def, def_imp];

lemma mdp : ∕[L] (φ ➝ ψ) → ∕[L] φ → ∕[L] ψ := by
  rintro ⟨hφψ₁, hφψ₂⟩ hφ;
  apply hφψ₂ hφ;

end KleeneSlash


class Logic.KleeneSlashable (L : Logic α) where
  iff_ks_provable : ∀ {φ : Formula α}, ∕[L] φ ↔ L ⊢ φ
export Logic.KleeneSlashable (iff_ks_provable)

theorem disjunctive_of_KleeneSlashable [L.KleeneSlashable] (hA : L ⊢ φ ⋎ ψ) : L ⊢ φ ∨ L ⊢ ψ := by
  rcases iff_ks_provable.mpr hA with hφ | hψ;
  . left; apply iff_ks_provable.mp hφ;
  . right; apply iff_ks_provable.mp hψ;

instance instDisjunctive_of_KleeneSlashable [L.KleeneSlashable] : Entailment.Disjunctive L := ⟨disjunctive_of_KleeneSlashable⟩

end LO.Propositional
