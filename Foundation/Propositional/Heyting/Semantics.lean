import Foundation.Propositional.Hilbert.Basic
import Foundation.Vorspiel.Order
import Foundation.Logic.LindenbaumAlgebra

namespace LO.Propositional

variable {α : Type u}

namespace Formula

def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊥      => ⊥
  | φ ⋏ ψ  => φ.hVal v ⊓ ψ.hVal v
  | φ ⋎ ψ  => φ.hVal v ⊔ ψ.hVal v
  | φ ➝ ψ  => φ.hVal v ⇨ ψ.hVal v

variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)

@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl

@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl

@[simp] lemma hVal_and (φ ψ : Formula α) : (φ ⋏ ψ).hVal v = φ.hVal v ⊓ ψ.hVal v := rfl

@[simp] lemma hVal_or (φ ψ : Formula α) : (φ ⋎ ψ).hVal v = φ.hVal v ⊔ ψ.hVal v := rfl

@[simp] lemma hVal_imp (φ ψ : Formula α) : (φ ➝ ψ).hVal v = φ.hVal v ⇨ ψ.hVal v := rfl

@[simp] lemma hVal_verum : (⊤ : Formula α).hVal v = ⊤ := by simp [Formula.top_def];

@[simp] lemma hVal_neg (φ : Formula α) : (∼φ).hVal v = (φ.hVal v)ᶜ := by simp [Formula.neg_def];

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

def hVal (ℍ : HeytingSemantics α) (φ : Formula α) : ℍ := φ.hVal ℍ.valAtom

scoped [LO.Propositional] infix:45 " ⊧ₕ " => LO.Propositional.HeytingSemantics.hVal

@[simp] lemma hVal_falsum : (ℍ ⊧ₕ ⊥) = ⊥ := rfl

@[simp] lemma hVal_and (φ ψ : Formula α) : (ℍ ⊧ₕ φ ⋏ ψ) = (ℍ ⊧ₕ φ) ⊓ (ℍ ⊧ₕ ψ) := rfl

@[simp] lemma hVal_or (φ ψ : Formula α) : (ℍ ⊧ₕ φ ⋎ ψ) = (ℍ ⊧ₕ φ) ⊔ (ℍ ⊧ₕ ψ) := rfl

@[simp] lemma hVal_imply (φ ψ : Formula α) : (ℍ ⊧ₕ φ ➝ ψ) = (ℍ ⊧ₕ φ) ⇨ (ℍ ⊧ₕ ψ) := rfl

@[simp] lemma hVal_iff (φ ψ : Formula α) : (ℍ ⊧ₕ φ ⭤ ψ) = bihimp (ℍ ⊧ₕ φ) (ℍ ⊧ₕ ψ) := by simp [LogicalConnective.iff, bihimp, inf_comm]

@[simp] lemma hVal_verum : (ℍ ⊧ₕ ⊤) = ⊤ := by simp [Formula.top_def];

@[simp] lemma hVal_not (φ : Formula α) : (ℍ ⊧ₕ ∼φ) = (ℍ ⊧ₕ φ)ᶜ := by simp [Formula.neg_def];

instance : Semantics (Formula α) (HeytingSemantics α) := ⟨fun ℍ φ ↦ (ℍ ⊧ₕ φ) = ⊤⟩

lemma val_def {ℍ : HeytingSemantics α} {φ : Formula α} : ℍ ⊧ φ ↔ φ.hVal ℍ.valAtom = ⊤ := by rfl

lemma val_def' {ℍ : HeytingSemantics α} {φ : Formula α} : ℍ ⊧ φ ↔ (ℍ ⊧ₕ φ) = ⊤ := by rfl

instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.Bot (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ φ ψ} ↦ by simp [val_def]⟩

@[simp] lemma val_imply {φ ψ : Formula α} : ℍ ⊧ φ ➝ ψ ↔ (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by
  simp [val_def]; rfl

@[simp] lemma val_iff {φ ψ : Formula α} : ℍ ⊧ φ ⭤ ψ ↔ (ℍ ⊧ₕ φ) = (ℍ ⊧ₕ ψ) := by
  simp [LogicalConnective.iff, antisymm_iff]

lemma val_not (φ : Formula α) : ℍ ⊧ ∼φ ↔ (ℍ ⊧ₕ φ) = ⊥ := by
  simp only [val_def, Formula.hVal_neg];
  rw [←HeytingAlgebra.himp_bot, himp_eq_top_iff, le_bot_iff];
  rfl

@[simp] lemma val_or (φ ψ : Formula α) : ℍ ⊧ φ ⋎ ψ ↔ (ℍ ⊧ₕ φ) ⊔ (ℍ ⊧ₕ ψ) = ⊤ := by
  simp [val_def]; rfl

def mod (Ax : Axiom α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) Ax.instances

variable {Ax : Axiom α}

lemma mod_models_iff {φ : Formula α} :
    mod.{_,w} Ax ⊧ φ ↔ ∀ ℍ : HeytingSemantics.{_,w} α, ℍ ⊧* Ax.instances → ℍ ⊧ φ := by
  simp [mod, Semantics.models, Semantics.set_models_iff]

lemma sound {φ : Formula α} (d : (Hilbert Ax) ⊢ φ) : mod (Hilbert Ax) ⊧ φ := by
  apply mod_models_iff.mpr;
  intro ℍ hℍ;
  induction d with
  | @axm φ s hφ =>
    apply hℍ.RealizeSet;
    use φ;
    grind;
  | @mdp φ ψ _ _ ihpq ihp =>
    have : (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by simpa using ihpq
    simpa [val_def'.mp ihp] using this
  | _ => simp [himp_himp_inf_himp_inf_le, himp_inf_himp_inf_sup_le]

instance : Sound (Hilbert Ax) (mod (Hilbert Ax)) := ⟨sound⟩

section

open Entailment.LindenbaumAlgebra

variable [DecidableEq α] {Ax : Axiom α} [Ax.HasEFQ] [Entailment.Consistent (Hilbert Ax)]

def lindenbaum (Ax : Axiom α) [Ax.HasEFQ] [Entailment.Consistent (Hilbert Ax)] : HeytingSemantics α where
  Algebra := Entailment.LindenbaumAlgebra (Hilbert Ax)
  valAtom a := ⟦.atom a⟧

lemma lindenbaum_val_eq : (lindenbaum Ax ⊧ₕ φ) = ⟦φ⟧ := by
  induction φ with
  | hand φ ψ ihp ihq => simp only [hVal_and, ihp, ihq]; rw [inf_def];
  | hor _ _ ihp ihq => simp only [hVal_or, ihp, ihq]; rw [sup_def];
  | himp _ _ ihp ihq => simp only [hVal_imply, ihp, ihq]; rw [himp_def];
  | _ => rfl

lemma lindenbaum_complete_iff {φ : Formula α} : lindenbaum Ax ⊧ φ ↔ (Hilbert Ax) ⊢ φ := by
  simp [val_def', lindenbaum_val_eq, provable_iff_eq_top]

instance : Sound (Hilbert Ax) (lindenbaum Ax) := ⟨lindenbaum_complete_iff.mpr⟩

instance : Complete (Hilbert Ax) (lindenbaum Ax) := ⟨lindenbaum_complete_iff.mp⟩

end

lemma complete [DecidableEq α] [Ax.HasEFQ] {φ : Formula α} (h : mod.{_,u} Ax ⊧ φ) : (Hilbert Ax) ⊢ φ := by
  wlog Con : Entailment.Consistent (Hilbert Ax)
  . exact Entailment.not_consistent_iff_inconsistent.mp Con φ
  exact lindenbaum_complete_iff.mp <|
    mod_models_iff.mp h (lindenbaum Ax) ⟨fun ψ hψ ↦ lindenbaum_complete_iff.mpr <| by grind⟩

instance [DecidableEq α] [Ax.HasEFQ] : Complete (Hilbert Ax) (mod.{_,u} Ax) := ⟨complete⟩

end HeytingSemantics

end LO.Propositional
