module

public import Foundation.Propositional.Hilbert.Minimal.Basic
public import Foundation.Logic.LindenbaumAlgebra
public import Foundation.Vorspiel.Order.Heyting

@[expose] public section

namespace LO.Propositional

variable {α : Type u}

namespace Formula

def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊥      => ⊥
  | φ ⋏ ψ  => φ.hVal v ⊓ ψ.hVal v
  | φ ⋎ ψ  => φ.hVal v ⊔ ψ.hVal v
  | φ 🡒 ψ  => φ.hVal v ⇨ ψ.hVal v

variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)

@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl

@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl

@[simp] lemma hVal_and (φ ψ : Formula α) : (φ ⋏ ψ).hVal v = φ.hVal v ⊓ ψ.hVal v := rfl

@[simp] lemma hVal_or (φ ψ : Formula α) : (φ ⋎ ψ).hVal v = φ.hVal v ⊔ ψ.hVal v := rfl

@[simp] lemma hVal_imp (φ ψ : Formula α) : (φ 🡒 ψ).hVal v = φ.hVal v ⇨ ψ.hVal v := rfl

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

@[simp] lemma hVal_imply (φ ψ : Formula α) : (ℍ ⊧ₕ φ 🡒 ψ) = (ℍ ⊧ₕ φ) ⇨ (ℍ ⊧ₕ ψ) := rfl

@[simp] lemma hVal_iff (φ ψ : Formula α) : (ℍ ⊧ₕ φ 🡘 ψ) = bihimp (ℍ ⊧ₕ φ) (ℍ ⊧ₕ ψ) := by simp [LogicalConnective.iff, bihimp, inf_comm]

@[simp] lemma hVal_verum : (ℍ ⊧ₕ ⊤) = ⊤ := by simp [Formula.top_def];

@[simp] lemma hVal_not (φ : Formula α) : (ℍ ⊧ₕ ∼φ) = (ℍ ⊧ₕ φ)ᶜ := by simp [Formula.neg_def];

instance : Semantics (HeytingSemantics α) (Formula α) := ⟨fun ℍ φ ↦ (ℍ ⊧ₕ φ) = ⊤⟩

lemma val_def {ℍ : HeytingSemantics α} {φ : Formula α} : ℍ ⊧ φ ↔ φ.hVal ℍ.valAtom = ⊤ := by rfl

lemma val_def' {ℍ : HeytingSemantics α} {φ : Formula α} : ℍ ⊧ φ ↔ (ℍ ⊧ₕ φ) = ⊤ := by rfl

instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.Bot (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩

instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ φ ψ} ↦ by simp [val_def]⟩

@[simp] lemma val_imply {φ ψ : Formula α} : ℍ ⊧ φ 🡒 ψ ↔ (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by
  simp [val_def]; rfl

@[simp] lemma val_iff {φ ψ : Formula α} : ℍ ⊧ φ 🡘 ψ ↔ (ℍ ⊧ₕ φ) = (ℍ ⊧ₕ ψ) := by
  simp [LogicalConnective.iff, antisymm_iff]

lemma val_not (φ : Formula α) : ℍ ⊧ ∼φ ↔ (ℍ ⊧ₕ φ) = ⊥ := by
  simp only [val_def, Formula.hVal_neg];
  rw [←HeytingAlgebra.himp_bot, himp_eq_top_iff, le_bot_iff];
  rfl

@[simp] lemma val_or (φ ψ : Formula α) : ℍ ⊧ φ ⋎ ψ ↔ (ℍ ⊧ₕ φ) ⊔ (ℍ ⊧ₕ ψ) = ⊤ := by
  simp [val_def]; rfl

def mod (H : Hilbert α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) H

variable {H : Hilbert α}

lemma mod_models_iff {φ : Formula α} :
    mod.{_,w} H ⊧ φ ↔ ∀ ℍ : HeytingSemantics.{_,w} α, ℍ ⊧* H → ℍ ⊧ φ := by
  simp [mod, Semantics.models, Semantics.set_models_iff]

lemma sound {φ : Formula α} : H ⊢ φ → mod H ⊧ φ := by
  rintro ⟨d⟩;
  apply mod_models_iff.mpr;
  intro ℍ hℍ;
  induction d with
  | axm hφ => apply hℍ.models_set; assumption;
  | @mdp φ ψ _ _ ihpq ihp =>
    have : (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by simpa using ihpq
    simpa [val_def'.mp ihp] using this
  | _ => simp [himp_himp_inf_himp_inf_le, himp_inf_himp_inf_sup_le]

instance : Sound H (mod H) := ⟨sound⟩

section

open Entailment.LindenbaumAlgebra

variable [DecidableEq α] {H : Hilbert α} [Entailment.Consistent H] [Entailment.Int H]

def lindenbaum (H : Hilbert α) [Entailment.Consistent H] [Entailment.Int H] : HeytingSemantics α where
  Algebra := Entailment.LindenbaumAlgebra H
  valAtom a := ⟦.atom a⟧
  heyting := Entailment.LindenbaumAlgebra.heyting _

lemma lindenbaum_val_eq : (lindenbaum H ⊧ₕ φ) = ⟦φ⟧ := by
  induction φ with
  | hand φ ψ ihp ihq => simp_all [hVal_and]; rfl;
  | hor _ _ ihp ihq => simp_all [hVal_or]; tauto;
  | himp _ _ ihp ihq => simp_all [hVal_imply]; tauto;
  | _ => rfl

lemma lindenbaum_complete_iff {φ : Formula α} : lindenbaum H ⊧ φ ↔ H ⊢ φ := by
  grind [val_def', lindenbaum_val_eq, provable_iff_eq_top]

instance : Sound H (lindenbaum H) := ⟨lindenbaum_complete_iff.mpr⟩

instance : Complete H (lindenbaum H) := ⟨lindenbaum_complete_iff.mp⟩

end

lemma complete [DecidableEq α] [Entailment.Int H] {φ : Formula α} (h : mod.{_,u} H ⊧ φ) : H ⊢ φ := by
  wlog Con : Entailment.Consistent H
  . exact Entailment.not_consistent_iff_inconsistent.mp Con φ
  exact lindenbaum_complete_iff.mp <| mod_models_iff.mp h (lindenbaum H) $ by
    constructor;
    intro ψ hψ;
    exact lindenbaum_complete_iff.mpr $ Hilbert.of_schema hψ;

instance [DecidableEq α] [Entailment.Int H] : Complete H (mod.{_,u} H) := ⟨complete⟩

end HeytingSemantics

end LO.Propositional
end
