module
import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi

namespace LO.Propositional

variable {α : Type*}
variable {L : Logic α} {Γ} {φ ψ : Formula α}

section

/-
  Context-less version of Aczel's slash.
-/
@[grind]
def AczelSlash (L : Logic α) : Formula α → Prop
  | #a => L ⊢ #a
  | ⊥ => False
  | φ ⋎ ψ => AczelSlash L φ ∨ AczelSlash L ψ
  | φ ⋏ ψ => AczelSlash L φ ∧ AczelSlash L ψ
  | φ ➝ ψ => L ⊢ (φ ➝ ψ) ∧ (AczelSlash L φ → AczelSlash L ψ)
notation:50 "∕ₐ[" L "] " φ:max => AczelSlash L φ

namespace AczelSlash

@[grind =] lemma def_atom {a : α} : ∕ₐ[L] (#a) ↔ L ⊢ #a := by simp [AczelSlash];
@[simp, grind .] lemma def_bot : ¬(∕ₐ[L] ⊥) := by simp [AczelSlash];

@[simp, grind .]
lemma def_top [Entailment.HasImpId L] : ∕ₐ[L] ⊤ := by
  rw [Formula.top_def];
  constructor;
  . exact Entailment.Corsi.impId;
  . tauto;

@[grind =] lemma def_or  : ∕ₐ[L] (φ ⋎ ψ) ↔ ∕ₐ[L] φ ∨ ∕ₐ[L] ψ := by simp [AczelSlash];
@[grind =] lemma def_and : ∕ₐ[L] (φ ⋏ ψ) ↔ ∕ₐ[L] φ ∧ ∕ₐ[L] ψ := by simp [AczelSlash];
@[grind =] lemma def_imp : ∕ₐ[L] (φ ➝ ψ) ↔ L ⊢ (φ ➝ ψ) ∧ (∕ₐ[L] φ → ∕ₐ[L] ψ) := by simp [AczelSlash];
@[grind =] lemma def_neg : ∕ₐ[L] (∼φ) ↔ L ⊢ ∼φ ∧ ¬∕ₐ[L] φ := by simp [Formula.neg_def, def_imp];

@[grind <=]
lemma mdp : ∕ₐ[L] (φ ➝ ψ) → ∕ₐ[L] φ → ∕ₐ[L] ψ := by
  rintro ⟨hφψ₁, hφψ₂⟩ hφ;
  apply hφψ₂ hφ;

end AczelSlash


class Logic.AczelSlashable (L : Logic α) where
  iff_ks_provable : ∀ {φ : Formula α}, ∕ₐ[L] φ ↔ L ⊢ φ
export Logic.AczelSlashable (iff_ks_provable)

theorem disjunctive_of_AczelSlashable [L.AczelSlashable] (hA : L ⊢ φ ⋎ ψ) : L ⊢ φ ∨ L ⊢ ψ := by
  rcases iff_ks_provable.mpr hA with hφ | hψ;
  . left; apply iff_ks_provable.mp hφ;
  . right; apply iff_ks_provable.mp hψ;

instance instDisjunctive_of_AczelSlashable [L.AczelSlashable] : Entailment.Disjunctive L := ⟨disjunctive_of_AczelSlashable⟩

end

end LO.Propositional
