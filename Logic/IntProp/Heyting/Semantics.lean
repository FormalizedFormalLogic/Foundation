import Logic.IntProp.Deduction

namespace LO.IntProp

variable {α : Type*}

namespace Formula

def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊤      => ⊤
  | ⊥      => ⊥
  | p ⋏ q  => p.hVal v ⊓ q.hVal v
  | p ⋎ q  => p.hVal v ⊔ q.hVal v
  | p ➝ q  => p.hVal v ⇨ q.hVal v
  | ∼p     => (p.hVal v)ᶜ

variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)

@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl

@[simp] lemma hVal_verum : (⊤ : Formula α).hVal v = ⊤ := rfl

@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl

@[simp] lemma hVal_and (p q : Formula α) : (p ⋏ q).hVal v = p.hVal v ⊓ q.hVal v := rfl

@[simp] lemma hVal_or (p q : Formula α) : (p ⋎ q).hVal v = p.hVal v ⊔ q.hVal v := rfl

@[simp] lemma hVal_imp (p q : Formula α) : (p ➝ q).hVal v = p.hVal v ⇨ q.hVal v := rfl

@[simp] lemma hVal_neg (p : Formula α) : (∼p).hVal v = (p.hVal v)ᶜ := rfl

end Formula

structure HeytingSemantics (α : Type*) where
  Algebra : Type*
  valAtom : α → Algebra
  [heyting : HeytingAlgebra Algebra]
  [nontrivial : Nontrivial Algebra]

namespace HeytingSemantics

variable (ℍ : HeytingSemantics α)

instance : CoeSort (HeytingSemantics α) (Type _) := ⟨Algebra⟩

instance : HeytingAlgebra ℍ := ℍ.heyting

instance : Nontrivial ℍ := ℍ.nontrivial

def val (ℍ : HeytingSemantics α) (p : Formula α) : ℍ := p.hVal ℍ.valAtom

scoped [LO.IntProp] infix:45 " ⊧ₕ " => LO.IntProp.HeytingSemantics.val

@[simp] lemma val_verum : (ℍ ⊧ₕ ⊤) = ⊤ := rfl

@[simp] lemma val_falsum : (ℍ ⊧ₕ ⊥) = ⊥ := rfl

@[simp] lemma val_and (p q : Formula α) : (ℍ ⊧ₕ p ⋏ q) = (ℍ ⊧ₕ p) ⊓ (ℍ ⊧ₕ q) := rfl

@[simp] lemma val_or (p q : Formula α) : (ℍ ⊧ₕ p ⋎ q) = (ℍ ⊧ₕ p) ⊔ (ℍ ⊧ₕ q) := rfl

@[simp] lemma val_imply (p q : Formula α) : (ℍ ⊧ₕ p ➝ q) = (ℍ ⊧ₕ p) ⇨ (ℍ ⊧ₕ q) := rfl

instance : Semantics (Formula α) (HeytingSemantics α) := ⟨fun ℍ p ↦ (ℍ ⊧ₕ p) = ⊤⟩

lemma val_def (ℍ : HeytingSemantics α) (p : Formula α) : ℍ ⊧ p ↔ p.hVal ℍ.valAtom = ⊤ := by rfl

instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.Bot (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ p q} ↦ by simp [val_def]⟩

end HeytingSemantics
