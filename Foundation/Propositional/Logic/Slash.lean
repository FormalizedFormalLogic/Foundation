module

public import Foundation.Propositional.Logic.Basic
public import Foundation.Propositional.Entailment.Corsi

@[expose] public section

namespace LO.Propositional

variable {α : Type*}
variable {L : Logic α} {Γ} {φ ψ : Formula α}

section

/-
  Context-less version of Aczel's slash.
-/
@[grind]
def AczelSlash (L : Logic α) : Formula α → Prop
  | #a => #a ∈ L
  | ⊥ => False
  | φ ⋎ ψ => AczelSlash L φ ∨ AczelSlash L ψ
  | φ ⋏ ψ => AczelSlash L φ ∧ AczelSlash L ψ
  | φ 🡒 ψ => (φ 🡒 ψ) ∈ L ∧ (AczelSlash L φ → AczelSlash L ψ)
notation:50 "∕ₐ[" L "] " φ:max => AczelSlash L φ

namespace AczelSlash

@[grind =] lemma def_atom {a : α} : ∕ₐ[L] (#a) ↔ #a ∈ L := by grind;
@[simp, grind .] lemma def_bot : ¬(∕ₐ[L] ⊥) := by tauto;


@[grind =] lemma def_or  : ∕ₐ[L] (φ ⋎ ψ) ↔ ∕ₐ[L] φ ∨ ∕ₐ[L] ψ := by simp [AczelSlash];
@[grind =] lemma def_and : ∕ₐ[L] (φ ⋏ ψ) ↔ ∕ₐ[L] φ ∧ ∕ₐ[L] ψ := by simp [AczelSlash];
@[grind =] lemma def_imp : ∕ₐ[L] (φ 🡒 ψ) ↔ (φ 🡒 ψ) ∈ L ∧ (∕ₐ[L] φ → ∕ₐ[L] ψ) := by simp [AczelSlash];
@[grind =] lemma def_neg : ∕ₐ[L] (∼φ) ↔ ∼φ ∈ L ∧ ¬∕ₐ[L] φ := by simp [Formula.neg_def, def_imp];

@[simp, grind =]
lemma def_top : ∕ₐ[L] ⊤ ↔ ⊤ ∈ L := by grind [Formula.top_def];

@[grind <=]
lemma mdp : ∕ₐ[L] (φ 🡒 ψ) → ∕ₐ[L] φ → ∕ₐ[L] ψ := by
  rintro ⟨hφψ₁, hφψ₂⟩ hφ;
  apply hφψ₂ hφ;

end AczelSlash


class Logic.Disjunctive (L : Logic α) where
  disjunctive : ∀ {φ ψ}, φ ⋎ ψ ∈ L → φ ∈ L ∨ ψ ∈ L


class Logic.AczelSlashable (L : Logic α) where
  iff_ks_provable : ∀ {φ : Formula α}, ∕ₐ[L] φ ↔ φ ∈ L
export Logic.AczelSlashable (iff_ks_provable)

theorem disjunctive_of_AczelSlashable [L.AczelSlashable] (hA : φ ⋎ ψ ∈ L) : φ ∈ L ∨ ψ ∈ L := by
  rcases iff_ks_provable.mpr hA with hφ | hψ;
  . left;  apply iff_ks_provable.mp hφ;
  . right; apply iff_ks_provable.mp hψ;

instance instDisjunctive_of_AczelSlashable [L.AczelSlashable] : L.Disjunctive := ⟨disjunctive_of_AczelSlashable⟩

end

end LO.Propositional

end
