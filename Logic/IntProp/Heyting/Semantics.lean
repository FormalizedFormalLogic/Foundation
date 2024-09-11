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
  | p ⟶ q  => p.hVal v ⇨ q.hVal v
  | ~p     => (p.hVal v)ᶜ

variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)

@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl

@[simp] lemma hVal_verum : (⊤ : Formula α).hVal v = ⊤ := rfl

@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl

@[simp] lemma hVal_and (p q : Formula α) : (p ⋏ q).hVal v = p.hVal v ⊓ q.hVal v := rfl

@[simp] lemma hVal_or (p q : Formula α) : (p ⋎ q).hVal v = p.hVal v ⊔ q.hVal v := rfl

@[simp] lemma hVal_imp (p q : Formula α) : (p ⟶ q).hVal v = p.hVal v ⇨ q.hVal v := rfl

@[simp] lemma hVal_neg (p : Formula α) : (~p).hVal v = (p.hVal v)ᶜ := rfl

end Formula

structure HeytingSemantics (α : Type*) where
  Algebra : Type*
  valAtom : α → Algebra
  [heyting : HeytingAlgebra Algebra]

namespace HeytingSemantics

instance : CoeSort (HeytingSemantics α) (Type _) := ⟨Algebra⟩

instance (ℍ : HeytingSemantics α) : HeytingAlgebra ℍ := ℍ.heyting

def Val (ℍ : HeytingSemantics α) (p : Formula α) : Prop := p.hVal ℍ.valAtom = ⊤

instance : Semantics (Formula α) (HeytingSemantics α) := ⟨Val⟩

lemma val_def (ℍ : HeytingSemantics α) (p : Formula α) : ℍ ⊧ p ↔ p.hVal ℍ.valAtom = ⊤ := by rfl

instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ p q} ↦ by simp [val_def]⟩

end HeytingSemantics
