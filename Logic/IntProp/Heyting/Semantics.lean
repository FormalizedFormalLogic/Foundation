import Logic.IntProp.Deduction
import Logic.Vorspiel.Order
import Logic.Logic.Lindenbaum

namespace LO.IntProp

variable {α : Type u} [DecidableEq α]

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

def mod (Λ : Hilbert α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) Λ.axiomSet

variable {Λ : Hilbert α} [Λ.IncludeEFQ]

instance : System.Intuitionistic Λ where

lemma mod_models_iff {p : Formula α} :
    mod.{_,w} Λ ⊧ p ↔ ∀ ℍ : HeytingSemantics.{_,w} α, ℍ ⊧* Λ.axiomSet → ℍ ⊧ p := by
  simp [mod, Semantics.models, Semantics.set_models_iff]

lemma sound {p : Formula α} (d : Λ ⊢! p) : mod Λ ⊧ p := by
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

instance : Sound Λ (mod Λ) := ⟨sound⟩

section

open System.Lindenbaum

variable (Λ)
variable [System.Consistent Λ]

def lindenbaum : HeytingSemantics α where
  Algebra := System.Lindenbaum Λ
  valAtom a := ⟦.atom a⟧

lemma lindenbaum_val_eq : (lindenbaum Λ ⊧ₕ p) = ⟦p⟧ := by
  induction p using Formula.rec' <;> try simp [top_def, bot_def]
  case hatom => rfl
  case hverum => rfl
  case hfalsum => rfl
  case hand ihp ihq => simp [ihp, ihq]; rw [inf_def]
  case hor ihp ihq => simp [ihp, ihq]; rw [sup_def]
  case himp ihp ihq => simp [ihp, ihq]; rw [himp_def]
  case hneg ih => simp [ih]; rw [compl_def]

variable {Λ}

lemma lindenbaum_complete_iff [System.Consistent Λ] {p : Formula α} : lindenbaum Λ ⊧ p ↔ Λ ⊢! p := by
  simp [val_def', lindenbaum_val_eq, provable_iff_eq_top]

instance : Sound Λ (lindenbaum Λ) := ⟨lindenbaum_complete_iff.mpr⟩

instance : Complete Λ (lindenbaum Λ) := ⟨lindenbaum_complete_iff.mp⟩

end

lemma complete {p : Formula α} (h : mod.{_,u} Λ ⊧ p) : Λ ⊢! p := by
  wlog Con : System.Consistent Λ
  · exact System.not_consistent_iff_inconsistent.mp Con p
  exact lindenbaum_complete_iff.mp <|
    mod_models_iff.mp h (lindenbaum Λ) ⟨fun q hq ↦ lindenbaum_complete_iff.mpr <| Deduction.eaxm! hq⟩

instance : Complete Λ (mod.{_,u} Λ) := ⟨complete⟩

end HeytingSemantics
