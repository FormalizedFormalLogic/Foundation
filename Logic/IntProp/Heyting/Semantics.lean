import Logic.IntProp.Deduction
import Logic.Vorspiel.Order

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

def hVal (ℍ : HeytingSemantics α) (p : Formula α) : ℍ := p.hVal ℍ.valAtom

scoped [LO.IntProp] infix:45 " ⊧ₕ " => LO.IntProp.HeytingSemantics.hVal

@[simp] lemma hVal_verum : (ℍ ⊧ₕ ⊤) = ⊤ := rfl

@[simp] lemma hVal_falsum : (ℍ ⊧ₕ ⊥) = ⊥ := rfl

@[simp] lemma hVal_and (p q : Formula α) : (ℍ ⊧ₕ p ⋏ q) = (ℍ ⊧ₕ p) ⊓ (ℍ ⊧ₕ q) := rfl

@[simp] lemma hVal_or (p q : Formula α) : (ℍ ⊧ₕ p ⋎ q) = (ℍ ⊧ₕ p) ⊔ (ℍ ⊧ₕ q) := rfl

@[simp] lemma hVal_imply (p q : Formula α) : (ℍ ⊧ₕ p ➝ q) = (ℍ ⊧ₕ p) ⇨ (ℍ ⊧ₕ q) := rfl

@[simp] lemma hVal_iff (p q : Formula α) : (ℍ ⊧ₕ p ⭤ q) = bihimp (ℍ ⊧ₕ p) (ℍ ⊧ₕ q) := by simp [LogicalConnective.iff, bihimp, inf_comm]

@[simp] lemma hVal_not (p : Formula α) : (ℍ ⊧ₕ ∼p) = (ℍ ⊧ₕ p)ᶜ := rfl

instance : Semantics (Formula α) (HeytingSemantics α) := ⟨fun ℍ p ↦ (ℍ ⊧ₕ p) = ⊤⟩

lemma val_def {ℍ : HeytingSemantics α} {p : Formula α} : ℍ ⊧ p ↔ p.hVal ℍ.valAtom = ⊤ := by rfl

lemma val_def' {ℍ : HeytingSemantics α} {p : Formula α} : ℍ ⊧ p ↔ (ℍ ⊧ₕ p) = ⊤ := by rfl

instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.Bot (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ p q} ↦ by simp [val_def]⟩

@[simp] lemma val_imply {p q : Formula α} : ℍ ⊧ p ➝ q ↔ (ℍ ⊧ₕ p) ≤ (ℍ ⊧ₕ q) := by
  simp [val_def]; rfl

@[simp] lemma val_iff {p q : Formula α} : ℍ ⊧ p ⭤ q ↔ (ℍ ⊧ₕ p) = (ℍ ⊧ₕ q) := by
  simp [LogicalConnective.iff, antisymm_iff]

lemma val_not (p : Formula α) : ℍ ⊧ ∼p ↔ (ℍ ⊧ₕ p) = ⊥ := by simp [val_def]; rw [←HeytingAlgebra.himp_bot, himp_eq_top_iff, le_bot_iff]; rfl

@[simp] lemma val_or (p q : Formula α) : ℍ ⊧ p ⋎ q ↔ (ℍ ⊧ₕ p) ⊔ (ℍ ⊧ₕ q) = ⊤ := by
  simp [val_def]; rfl

def mod (T : Hilbert α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) T.axiomSet

variable {T : Hilbert α}

lemma mod_models_iff {p : Formula α} :
    mod.{_,w} T ⊧ p ↔ ∀ ℍ : HeytingSemantics.{_,w} α, ℍ ⊧* T.axiomSet → ℍ ⊧ p := by
  simp [mod, Semantics.models, Semantics.set_models_iff]

lemma sound {p : Formula α} (d : T ⊢! p) : mod T ⊧ p := by
  rcases d with ⟨d⟩
  apply mod_models_iff.mpr fun ℍ hℍ ↦ ?_
  induction d
  case eaxm p hp =>
    exact hℍ.RealizeSet hp
  case mdp p q _ _ ihpq ihp =>
    have : (ℍ ⊧ₕ p) ≤ (ℍ ⊧ₕ q) := by simpa using ihpq
    simpa [val_def'.mp ihp] using this
  case verum => simp
  case imply₁ => simp
  case imply₂ p q r => simp [himp_himp_inf_himp_inf_le]
  case and₁ => simp
  case and₂ => simp
  case and₃ => simp
  case or₁ => simp
  case or₂ => simp
  case or₃ => simp [himp_inf_himp_inf_sup_le]
  case neg_equiv p =>
    simp [Axioms.NegEquiv]

instance : Sound T (mod T)  := ⟨sound⟩

end HeytingSemantics
