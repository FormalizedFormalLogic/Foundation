module

public import Foundation.Propositional.Entailment.Corsi
public import Foundation.Propositional.Logic.Basic

@[expose] public section

namespace LO.Propositional

variable {α : Type*}

structure HilbertWF (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

namespace HilbertWF

instance : SetLike (HilbertWF α) (Formula α) where
  coe := HilbertWF.schema
  coe_injective' := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa

protected def WF : HilbertWF α := ⟨∅, by grind⟩

end HilbertWF


inductive HilbertWFProof (Λ : HilbertWF α) : Formula α → Type _
| axm {φ}                 : φ ∈ Λ → HilbertWFProof Λ φ
| andElimL {φ ψ}          : HilbertWFProof Λ $ Axioms.AndElim₁ φ ψ
| andElimR {φ ψ}          : HilbertWFProof Λ $ Axioms.AndElim₂ φ ψ
| orIntroL {φ ψ}          : HilbertWFProof Λ $ Axioms.OrInst₁ φ ψ
| orIntroR {φ ψ}          : HilbertWFProof Λ $ Axioms.OrInst₂ φ ψ
| distributeAndOr {φ ψ χ} : HilbertWFProof Λ $ Axioms.DistributeAndOr φ ψ χ
| impId {φ}               : HilbertWFProof Λ $ Axioms.ImpId φ
| efq {φ}                 : HilbertWFProof Λ $ Axioms.EFQ φ
| mdp {φ ψ}               : HilbertWFProof Λ (φ 🡒 ψ) → HilbertWFProof Λ φ → HilbertWFProof Λ ψ
| af {φ ψ}                : HilbertWFProof Λ φ → HilbertWFProof Λ (ψ 🡒 φ)
| andIR {φ ψ}             : HilbertWFProof Λ φ → HilbertWFProof Λ ψ → HilbertWFProof Λ (φ ⋏ ψ)
| ruleC {φ ψ χ}           : HilbertWFProof Λ (φ 🡒 ψ) → HilbertWFProof Λ (φ 🡒 χ) → HilbertWFProof Λ (φ 🡒 (ψ ⋏ χ))
| ruleD {φ ψ χ}           : HilbertWFProof Λ (φ 🡒 χ) → HilbertWFProof Λ (ψ 🡒 χ) → HilbertWFProof Λ (φ ⋎ ψ 🡒 χ)
| ruleI {φ ψ χ}           : HilbertWFProof Λ (φ 🡒 ψ) → HilbertWFProof Λ (ψ 🡒 χ) → HilbertWFProof Λ (φ 🡒 χ)
| ruleE {φ ψ χ ξ}         : HilbertWFProof Λ (φ 🡘 ψ) → HilbertWFProof Λ (χ 🡘 ξ) → HilbertWFProof Λ ((φ 🡒 χ) 🡘 (ψ 🡒 ξ))

instance : Entailment (HilbertWF α) (Formula α) := ⟨HilbertWFProof⟩

namespace HilbertWF

open HilbertWFProof

variable (H : HilbertWF α)

instance : Entailment.WF H where
  and₁              := andElimL
  and₂              := andElimR
  or₁               := orIntroL
  or₂               := orIntroR
  distributeAndOr!  := distributeAndOr
  impId!            := impId
  verum             := impId
  efq               := efq
  mdp               := mdp
  af!               := af
  andIR!            := andIR
  ruleC!            := ruleC
  ruleD!            := ruleD
  ruleI!            := ruleI
  ruleE!            := ruleE


variable {H} {H₁ H₂ : HilbertWF α}

alias ofSchema := HilbertWFProof.axm
@[grind <=] lemma of_schema (h : φ ∈ H) : H ⊢ φ := ⟨ofSchema h⟩

def ofLE (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁          => axm $ h h₁
  | mdp h₁ h₂       => mdp (ofLE h h₁) (ofLE h h₂)
  | andElimL        => andElimL
  | andElimR        => andElimR
  | orIntroL        => orIntroL
  | orIntroR        => orIntroR
  | distributeAndOr => distributeAndOr
  | efq             => efq
  | impId           => impId
  | af h₁           => af (ofLE h h₁)
  | andIR h₁ h₂     => andIR (ofLE h h₁) (ofLE h h₂)
  | ruleC h₁ h₂     => ruleC (ofLE h h₁) (ofLE h h₂)
  | ruleD h₁ h₂     => ruleD (ofLE h h₁) (ofLE h h₂)
  | ruleI h₁ h₂     => ruleI (ofLE h h₁) (ofLE h h₂)
  | ruleE h₁ h₂     => ruleE (ofLE h h₁) (ofLE h h₂)

lemma of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢ φ → H₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofLE h hφ⟩

@[grind <=]
lemma weakerThan_of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⪯ H₂ := Entailment.weakerThan_iff.mpr $ of_le h

def Subst {H : HilbertWF α} (s) : H ⊢! φ → H ⊢! φ⟦s⟧
  | axm h₁           => axm $ H.schema_closed _ h₁ s
  | mdp h₁ h₂        => mdp (Subst s h₁) (Subst s h₂)
  | andElimL         => andElimL
  | andElimR         => andElimR
  | orIntroL         => orIntroL
  | orIntroR         => orIntroR
  | distributeAndOr  => distributeAndOr
  | efq              => efq
  | impId            => impId
  | af h₁            => af (Subst s h₁)
  | andIR h₁ h₂     => andIR (Subst s h₁) (Subst s h₂)
  | ruleC h₁ h₂     => ruleC (Subst s h₁) (Subst s h₂)
  | ruleD h₁ h₂     => ruleD (Subst s h₁) (Subst s h₂)
  | ruleI h₁ h₂     => ruleI (Subst s h₁) (Subst s h₂)
  | ruleE h₁ h₂     => ruleE (Subst s h₁) (Subst s h₂)

lemma subst {H : HilbertWF α} (s) : H ⊢ φ → H ⊢ φ⟦s⟧ := λ ⟨hφ⟩ => ⟨Subst s hφ⟩

def ofProofSchema (h : H₂ ⊢!* H₁.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁          => h h₁
  | mdp h₁ h₂       => mdp (ofProofSchema h h₁) (ofProofSchema h h₂)
  | andElimL        => andElimL
  | andElimR        => andElimR
  | orIntroL        => orIntroL
  | orIntroR        => orIntroR
  | distributeAndOr => distributeAndOr
  | impId           => impId
  | efq             => efq
  | af h₁           => af (ofProofSchema h h₁)
  | andIR h₁ h₂     => andIR (ofProofSchema h h₁) (ofProofSchema h h₂)
  | ruleC h₁ h₂     => ruleC (ofProofSchema h h₁) (ofProofSchema h h₂)
  | ruleD h₁ h₂     => ruleD (ofProofSchema h h₁) (ofProofSchema h h₂)
  | ruleI h₁ h₂     => ruleI (ofProofSchema h h₁) (ofProofSchema h h₂)
  | ruleE h₁ h₂     => ruleE (ofProofSchema h h₁) (ofProofSchema h h₂)

lemma of_proof_schema (h : H₂ ⊢* H₁.schema) : H₁ ⊢ φ → H₂ ⊢ φ :=
  λ ⟨hφ⟩ => ⟨ofProofSchema (h · |>.get) hφ⟩

lemma weakerThan_of_provable_schema (h : H₂ ⊢* H₁.schema) : H₁ ⪯ H₂ :=
  Entailment.weakerThan_iff.mpr $ of_proof_schema h

open Entailment.Corsi in
@[induction_eliminator]
protected lemma rec_provable
  {H : HilbertWF α}
  {motive  : (φ : Formula α) → (H ⊢ φ) → Prop}
  (axm       : ∀ {φ}, (h : φ ∈ H) → motive (φ) (of_schema h))
  (mdp       : ∀ {φ ψ}, {hφψ : H ⊢ φ 🡒 ψ} → {hφ : H ⊢ φ} → (motive (φ 🡒 ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af        : ∀ {φ ψ}, {hφ : H ⊢ φ} → (motive φ hφ) → (motive (ψ 🡒 φ) (af hφ)))
  (ruleC     : ∀ {φ ψ χ}, {h₁ : H ⊢ φ 🡒 ψ} → {h₂ : H ⊢ φ 🡒 χ} → (motive (φ 🡒 ψ) h₁) → (motive (φ 🡒 χ) h₂) → (motive (φ 🡒 (ψ ⋏ χ)) (ruleC h₁ h₂)))
  (ruleD     : ∀ {φ ψ χ}, {h₁ : H ⊢ φ 🡒 χ} → {h₂ : H ⊢ ψ 🡒 χ} → (motive (φ 🡒 χ) h₁) → (motive (ψ 🡒 χ) h₂) → (motive (φ ⋎ ψ 🡒 χ) (ruleD h₁ h₂)))
  (ruleI     : ∀ {φ ψ χ}, {h₁ : H ⊢ φ 🡒 ψ} → {h₂ : H ⊢ ψ 🡒 χ} → (motive (φ 🡒 ψ) h₁) → (motive (ψ 🡒 χ) h₂) → (motive (φ 🡒 χ) (ruleI h₁ h₂)))
  (ruleE     : ∀ {φ ψ χ ξ}, {h₁ : H ⊢ φ 🡘 ψ} → {h₂ : H ⊢ χ 🡘 ξ} → (motive (φ 🡘 ψ) h₁) → (motive (χ 🡘 ξ) h₂) → (motive ((φ 🡒 χ) 🡘 (ψ 🡒 ξ)) (ruleE h₁ h₂)))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  (impId     : ∀ {φ}, (motive (Axioms.ImpId φ) impId))
  (andElimL  : ∀ {φ ψ}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR  : ∀ {φ ψ}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (efq       : ∀ {φ}, (motive (Axioms.EFQ φ) efq))
  : ∀ {φ}, (d : H ⊢ φ) → motive φ d := by rintro φ ⟨d⟩; induction d <;> grind;

section

end

abbrev logic (H : HilbertWF α) : Logic α where
  logic := Entailment.theory H
  subst s {_} := HilbertWF.subst s
  mdp := Entailment.mdp!

end HilbertWF


namespace HilbertWF

variable {H : HilbertWF α}

lemma mem_logic_of_proof (h : H ⊢! φ) : φ ∈ H.logic := ⟨h⟩

lemma mem_logic_of_provable (h : H ⊢ φ) : φ ∈ H.logic := mem_logic_of_proof h.get
lemma provable_of_mem_logic (h : φ ∈ H.logic) : H ⊢ φ := h

@[grind =]
lemma iff_mem_logic_provable : H ⊢ φ ↔ φ ∈ H.logic := ⟨mem_logic_of_provable, provable_of_mem_logic⟩

end HilbertWF

protected abbrev WF : Logic ℕ := HilbertWF.WF.logic

end LO.Propositional

end
