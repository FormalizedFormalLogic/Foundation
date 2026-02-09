module

public import Foundation.Syntax.Predicate.Rew

@[expose] public section

namespace LO.FirstOrder

namespace Semiterm

variable {L : Language} [L.Relational]

lemma bvar_or_fvar_of_relational (t : Semiterm L ξ n) : (∃ x, t = #x) ∨ (∃ x, t = &x) :=
  match t with
  |        #x => by simp
  |        &x => by simp
  | .func f _ => Language.Relational.func_empty _ |>.elim' f

lemma fvar_of_relational (t : Term L ξ) : ∃ x, t = &x := by
  rcases bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact finZeroElim (α := fun _ ↦ _) x
  · exact ⟨x, rfl⟩

variable {M : Type*} (bv : Fin n → M) (fv : ξ → M)

def relationalVal : Semiterm L ξ n → M
  |        #x => bv x
  |        &x => fv x
  | .func f _ => Language.Relational.func_empty _ |>.elim' f

variable {bv fv}

@[simp] lemma relationalVal_bvar : (#x : Semiterm L ξ n).relationalVal bv fv = bv x := rfl

@[simp] lemma relationalVal_fvar : (&x : Semiterm L ξ n).relationalVal bv fv = fv x := rfl

lemma relationalVal_rew {bv : Fin n₂ → M} {fv : ξ₂ → M} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    relationalVal bv fv (ω t) = relationalVal (relationalVal bv fv ∘ ω ∘ bvar) (relationalVal bv fv ∘ ω ∘ fvar) t := by
  rcases bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp

@[simp] lemma relationalVal_bShift (x : M) (t : Semiterm L ξ n) :
    relationalVal (x :> bv) fv (Rew.bShift t) = relationalVal bv fv t := by
  simp [relationalVal_rew, Function.comp_def]

end Semiterm

end LO.FirstOrder

end
