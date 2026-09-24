module

public import Foundation.Propositional.Entailment.Cl
public import Foundation.Propositional.Logic.Basic
public import Foundation.Propositional.Formula.Basic

@[expose] public section

namespace FFL.Propositional

variable {α : Type*}

structure Hilbert (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

namespace Hilbert

instance : SetLike (Hilbert α) (Formula α) where
  coe := Hilbert.schema
  coe_injective := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa;

protected def Min : Hilbert α := ⟨∅, by tauto⟩
protected def Int : Hilbert α := ⟨{ Axioms.EFQ φ | φ }, by grind⟩
protected def Cl : Hilbert α := ⟨
  { Axioms.EFQ φ | φ } ∪ { Axioms.LEM φ | φ },
  by rintro φ (_ | _) <;> grind;
⟩

@[simp, grind .] lemma Int_le_Cl : (Hilbert.Int : Hilbert α).schema ⊆ Hilbert.Cl.schema := by tauto;

end Hilbert


inductive Hilbert.Proof (Λ : Hilbert α) : Formula α → Type _
| axm {φ}        : φ ∈ Λ → Hilbert.Proof Λ φ
| mdp {φ ψ}      : Hilbert.Proof Λ (φ 🡒 ψ) → Hilbert.Proof Λ φ → Hilbert.Proof Λ ψ
| verum          : Hilbert.Proof Λ <| Axioms.Verum
| implyS {φ ψ χ} : Hilbert.Proof Λ <| Axioms.ImplyS φ ψ χ
| implyK {φ ψ}   : Hilbert.Proof Λ <| Axioms.ImplyK φ ψ
| andElimL {φ ψ} : Hilbert.Proof Λ <| Axioms.AndElim₁ φ ψ
| andElimR {φ ψ} : Hilbert.Proof Λ <| Axioms.AndElim₂ φ ψ
| andIntro {φ ψ} : Hilbert.Proof Λ <| Axioms.AndInst φ ψ
| orIntroL {φ ψ} : Hilbert.Proof Λ <| Axioms.OrInst₁ φ ψ
| orIntroR {φ ψ} : Hilbert.Proof Λ <| Axioms.OrInst₂ φ ψ
| orElim {φ ψ χ} : Hilbert.Proof Λ <| Axioms.OrElim φ ψ χ

instance : Entailment (Hilbert α) (Formula α) := ⟨fun H φ => Nonempty (Hilbert.Proof H φ)⟩

namespace Hilbert

open Hilbert.Proof

variable (H : Hilbert α)

instance : Entailment.ModusPonens H := ⟨fun ⟨h₁⟩ ⟨h₂⟩ => ⟨mdp h₁ h₂⟩⟩
instance : Entailment.HasAxiomImplyK H := ⟨⟨implyK⟩⟩
instance : Entailment.HasAxiomImplyS H := ⟨⟨implyS⟩⟩
instance : Entailment.HasAxiomAndInst H := ⟨⟨andIntro⟩⟩
instance : Entailment.Minimal H where
  verum := ⟨verum⟩
  and₁ := ⟨andElimL⟩
  and₂ := ⟨andElimR⟩
  or₁ := ⟨orIntroL⟩
  or₂ := ⟨orIntroR⟩
  or₃ := ⟨orElim⟩

variable {H} {H₁ H₂ : Hilbert α} {φ : Formula α}

alias ofSchema := Hilbert.Proof.axm
@[grind <=] lemma of_schema (h : φ ∈ H) : H ⊢ φ := ⟨ofSchema h⟩

def ofLE {φ : Formula α} (h : H₁.schema ⊆ H₂.schema) : Hilbert.Proof H₁ φ → Hilbert.Proof H₂ φ
  | axm h₁ => axm <| h h₁
  | mdp h₁ h₂ => mdp (ofLE h h₁) (ofLE h h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢ φ → H₂ ⊢ φ := fun ⟨hφ⟩ => ⟨ofLE h hφ⟩

@[grind <=]
lemma weakerThan_of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⪯ H₂ :=
  Entailment.weakerThan_iff.mpr <| of_le h

def Subst {H : Hilbert α} {φ : Formula α} (s) : Hilbert.Proof H φ → Hilbert.Proof H (φ⟦s⟧)
  | axm h₁ => axm <| H.schema_closed φ h₁ s
  | mdp h₁ h₂ => mdp (Hilbert.Subst s h₁) (Hilbert.Subst s h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma subst {H : Hilbert α} (s) : H ⊢ φ → H ⊢ φ⟦s⟧ := fun ⟨hφ⟩ => ⟨Subst s hφ⟩

def ofProofSchema {φ : Formula α} (h : ∀ {φ}, φ ∈ H₁.schema → Hilbert.Proof H₂ φ) :
    Hilbert.Proof H₁ φ → Hilbert.Proof H₂ φ
  | axm h₁ => h h₁
  | mdp h₁ h₂ => mdp (ofProofSchema h h₁) (ofProofSchema h h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma of_proof_schema (h : H₂ ⊢* H₁.schema) : H₁ ⊢ φ → H₂ ⊢ φ :=
  fun ⟨hφ⟩ => ⟨ofProofSchema (fun hφ => (h hφ).some) hφ⟩

lemma weakerThan_of_provable_schema (h : H₂ ⊢* H₁.schema) : H₁ ⪯ H₂ :=
  Entailment.weakerThan_iff.mpr <| of_proof_schema h

section

instance : Entailment.Int (Hilbert.Int : Hilbert α) where
  efq := ⟨axm <| by tauto⟩

instance : Entailment.HasAxiomEFQ (Hilbert.Cl : Hilbert α) := ⟨⟨axm <| by tauto⟩⟩
instance : Entailment.HasAxiomLEM (Hilbert.Cl : Hilbert α) := ⟨⟨axm <| by tauto⟩⟩
instance : Entailment.Int (Hilbert.Cl : Hilbert α) where
instance : Entailment.Cl (Hilbert.Cl : Hilbert α) where

end

end Hilbert


namespace Hilbert

abbrev logic (H : Hilbert α) : Logic α where
  logic := Entailment.theory H
  subst s {_} := Hilbert.subst s
  mdp h₁ h₂ := Entailment.mdp (𝓢 := H) h₁ h₂;

variable {H : Hilbert α} {φ : Formula α}

lemma mem_logic_of_provable (h : H ⊢ φ) : φ ∈ H.logic := by exact h
lemma provable_of_mem_logic (h : φ ∈ H.logic) : H ⊢ φ := by exact h

@[grind =]
lemma iff_mem_logic_provable : H ⊢ φ ↔ φ ∈ H.logic := ⟨mem_logic_of_provable, provable_of_mem_logic⟩

end Hilbert


protected abbrev Int : Logic α := Hilbert.Int.logic
protected abbrev Cl : Logic α := Hilbert.Cl.logic

end FFL.Propositional

end
