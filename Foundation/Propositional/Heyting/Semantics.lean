import Foundation.Propositional.Hilbert.Int
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

def mod (H : Hilbert α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) H.axiomInstances

variable {H : Hilbert α}

lemma mod_models_iff {φ : Formula α} :
    mod.{_,w} H ⊧ φ ↔ ∀ ℍ : HeytingSemantics.{_,w} α, ℍ ⊧* H.axiomInstances → ℍ ⊧ φ := by
  simp [mod, Semantics.models, Semantics.set_models_iff]

lemma sound {φ : Formula α} (d : H ⊢! φ) : mod H ⊧ φ := by
  rcases d with ⟨d⟩
  apply mod_models_iff.mpr fun ℍ hℍ ↦ ?_
  induction d
  case maxm φ hφ => exact hℍ.RealizeSet hφ;
  case mdp φ ψ _ _ ihpq ihp =>
    have : (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by simpa using ihpq
    simpa [val_def'.mp ihp] using this
  case verum => simp
  case implyS => simp
  case implyK φ ψ χ => simp [himp_himp_inf_himp_inf_le]
  case andElimL => simp
  case andElimR => simp
  case K_intro => simp
  case orIntroL => simp
  case orIntroR => simp
  case orElim => simp [himp_inf_himp_inf_sup_le]

instance : Sound H (mod H) := ⟨sound⟩

section

open Entailment.LindenbaumAlgebra

variable [DecidableEq α] (H : Hilbert α) [H.HasEFQ] [Entailment.Consistent H]

def lindenbaum : HeytingSemantics α where
  Algebra := Entailment.LindenbaumAlgebra H
  valAtom a := ⟦.atom a⟧


lemma lindenbaum_val_eq : (lindenbaum H ⊧ₕ φ) = ⟦φ⟧ := by
  induction φ using Formula.rec' with
  | hand φ ψ ihp ihq => simp only [hVal_and, ihp, ihq]; rw [inf_def];
  | hor _ _ ihp ihq => simp only [hVal_or, ihp, ihq]; rw [sup_def];
  | himp _ _ ihp ihq => simp only [hVal_imply, ihp, ihq]; rw [himp_def];
  | _ => rfl

variable {H}

omit [Entailment.Consistent H] in
lemma lindenbaum_complete_iff [Entailment.Consistent H] {φ : Formula α} : lindenbaum H ⊧ φ ↔ H ⊢! φ := by
  simp [val_def', lindenbaum_val_eq, provable_iff_eq_top]

instance : Sound H (lindenbaum H) := ⟨lindenbaum_complete_iff.mpr⟩

instance : Complete H (lindenbaum H) := ⟨lindenbaum_complete_iff.mp⟩

end

open Hilbert.Deduction

lemma complete [DecidableEq α] {φ : Formula α} [H.HasEFQ] (h : mod.{_,u} H ⊧ φ) : H ⊢! φ := by
  wlog Con : Entailment.Consistent H
  · exact Entailment.not_consistent_iff_inconsistent.mp Con φ
  exact lindenbaum_complete_iff.mp <|
    mod_models_iff.mp h (lindenbaum H) ⟨fun ψ hq ↦ lindenbaum_complete_iff.mpr <| maxm! hq⟩

instance [DecidableEq α] [H.HasEFQ] : Complete H (mod.{_,u} H) := ⟨complete⟩

end HeytingSemantics

end LO.Propositional
