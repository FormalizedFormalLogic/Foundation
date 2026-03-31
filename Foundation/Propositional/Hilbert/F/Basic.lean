module

public import Foundation.Propositional.Entailment.Corsi
public import Foundation.Propositional.Logic.Basic

@[expose] public section

namespace LO.Propositional

variable {α : Type*}

structure HilbertF (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

namespace HilbertF

instance : SetLike (HilbertF α) (Formula α) where
  coe := HilbertF.schema
  coe_injective' := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa

protected def F : HilbertF α := ⟨∅, by grind⟩
protected def F_Ser : HilbertF α := ⟨{ Axioms.Ser }, by grind⟩
protected def F_Rfl : HilbertF α := ⟨{ Axioms.Rfl φ ψ | (φ) (ψ) }, by grind⟩
protected def F_Sym : HilbertF α := ⟨{ Axioms.Sym φ ψ | (φ) (ψ) }, by grind⟩
protected def F_Rfl_Sym : HilbertF α := ⟨
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Sym φ ψ | (φ) (ψ) },
  by rintro φ (_ | _) <;> grind;
⟩
protected def F_Tra1 : HilbertF α := ⟨{ Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) }, by grind⟩
protected def F_Rfl_Tra1 : HilbertF α := ⟨
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) },
  by rintro φ (_ | _) <;> grind⟩

/-
protected def F_Tra1_Hrd : HilbertF α := ⟨
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) } ∪
  { Axioms.Hrd φ | (φ) },
  by rintro φ (_ | _) <;> grind
⟩
protected def F_Rfl_Tra1_Hrd : HilbertF α := ⟨
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) } ∪
  { Axioms.Hrd φ | (φ) },
  by rintro φ ((_ | _) | _) <;> grind;
⟩
-/

@[simp, grind .] lemma F_le_F_Ser : (HilbertF.F : HilbertF α).schema ⊆ HilbertF.F_Ser.schema := by tauto
@[simp, grind .] lemma F_le_F_Rfl : (HilbertF.F : HilbertF α).schema ⊆ HilbertF.F_Rfl.schema := by tauto
@[simp, grind .] lemma F_le_F_Sym : (HilbertF.F : HilbertF α).schema ⊆ HilbertF.F_Sym.schema := by tauto
@[simp, grind .] lemma F_le_F_Tra1 : (HilbertF.F : HilbertF α).schema ⊆ HilbertF.F_Tra1.schema := by tauto
@[simp, grind .] lemma F_Rfl_le_F_Rfl_Sym : (HilbertF.F_Rfl : HilbertF α).schema ⊆ HilbertF.F_Rfl_Sym.schema  := by tauto
@[simp, grind .] lemma F_Sym_le_F_Rfl_Sym : (HilbertF.F_Sym : HilbertF α).schema ⊆ HilbertF.F_Rfl_Sym.schema  := by tauto
@[simp, grind .] lemma F_Rfl_le_F_Rfl_Tra1 : (HilbertF.F_Rfl : HilbertF α).schema ⊆ HilbertF.F_Rfl_Tra1.schema := by tauto
@[simp, grind .] lemma F_Tra1_le_F_Rfl_Tra1 : (HilbertF.F_Tra1 : HilbertF α).schema ⊆ HilbertF.F_Rfl_Tra1.schema := by tauto

end HilbertF


inductive HilbertFProof (Λ : HilbertF α) : Formula α → Type _
| axm {φ}                 : φ ∈ Λ → HilbertFProof Λ φ
| andElimL {φ ψ}          : HilbertFProof Λ $ Axioms.AndElim₁ φ ψ
| andElimR {φ ψ}          : HilbertFProof Λ $ Axioms.AndElim₂ φ ψ
| orIntroL {φ ψ}          : HilbertFProof Λ $ Axioms.OrInst₁ φ ψ
| orIntroR {φ ψ}          : HilbertFProof Λ $ Axioms.OrInst₂ φ ψ
| distributeAndOr {φ ψ χ} : HilbertFProof Λ $ Axioms.DistributeAndOr φ ψ χ
| axiomC {φ ψ χ}          : HilbertFProof Λ $ Axioms.C φ ψ χ
| axiomD {φ ψ χ}          : HilbertFProof Λ $ Axioms.D φ ψ χ
| axiomI {φ ψ χ}          : HilbertFProof Λ $ Axioms.I φ ψ χ
| impId {φ}               : HilbertFProof Λ $ Axioms.ImpId φ
| efq {φ}                 : HilbertFProof Λ $ Axioms.EFQ φ
| mdp {φ ψ}               : HilbertFProof Λ (φ 🡒 ψ) → HilbertFProof Λ φ → HilbertFProof Λ ψ
| af {φ ψ}                : HilbertFProof Λ φ → HilbertFProof Λ (ψ 🡒 φ)
| andIR {φ ψ}             : HilbertFProof Λ φ → HilbertFProof Λ ψ → HilbertFProof Λ (φ ⋏ ψ)

instance : Entailment (HilbertF α) (Formula α) := ⟨HilbertFProof⟩

namespace HilbertF

open HilbertFProof

variable (H : HilbertF α)

instance : Entailment.F H where
  and₁              := andElimL
  and₂              := andElimR
  or₁               := orIntroL
  or₂               := orIntroR
  distributeAndOr!  := distributeAndOr
  axiomC!           := axiomC
  axiomD!           := axiomD
  axiomI!           := axiomI
  impId!            := impId
  verum             := impId
  efq               := efq
  mdp               := mdp
  af!               := af
  andIR!            := andIR

variable {H} {H₁ H₂ : HilbertF α}

alias ofSchema := HilbertFProof.axm
@[grind <=] lemma of_schema (h : φ ∈ H) : H ⊢ φ := ⟨ofSchema h⟩

def ofLE (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁          => axm $ h h₁
  | mdp h₁ h₂       => mdp (ofLE h h₁) (ofLE h h₂)
  | andElimL         => andElimL
  | andElimR         => andElimR
  | orIntroL         => orIntroL
  | orIntroR         => orIntroR
  | distributeAndOr  => distributeAndOr
  | axiomC           => axiomC
  | axiomD           => axiomD
  | axiomI           => axiomI
  | impId            => impId
  | efq              => efq
  | af h₁            => af (ofLE h h₁)
  | andIR h₁ h₂     => andIR (ofLE h h₁) (ofLE h h₂)

lemma of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢ φ → H₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofLE h hφ⟩

@[grind <=]
lemma weakerThan_of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⪯ H₂ := Entailment.weakerThan_iff.mpr $ of_le h

def Subst {H : HilbertF α} (s) : H ⊢! φ → H ⊢! φ⟦s⟧
  | axm h₁           => axm $ H.schema_closed _ h₁ s
  | mdp h₁ h₂        => mdp (Subst s h₁) (Subst s h₂)
  | andElimL         => andElimL
  | andElimR         => andElimR
  | orIntroL         => orIntroL
  | orIntroR         => orIntroR
  | distributeAndOr  => distributeAndOr
  | axiomC           => axiomC
  | axiomD           => axiomD
  | axiomI           => axiomI
  | impId            => impId
  | efq              => efq
  | af h₁            => af (Subst s h₁)
  | andIR h₁ h₂      => andIR (Subst s h₁) (Subst s h₂)

lemma subst {H : HilbertF α} (s) : H ⊢ φ → H ⊢ φ⟦s⟧ := λ ⟨hφ⟩ => ⟨Subst s hφ⟩

def ofProofSchema (h : H₂ ⊢!* H₁.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁          => h h₁
  | mdp h₁ h₂       => mdp (ofProofSchema h h₁) (ofProofSchema h h₂)
  | andElimL         => andElimL
  | andElimR         => andElimR
  | orIntroL         => orIntroL
  | orIntroR         => orIntroR
  | distributeAndOr  => distributeAndOr
  | axiomC           => axiomC
  | axiomD           => axiomD
  | axiomI           => axiomI
  | impId            => impId
  | efq              => efq
  | af h₁            => af (ofProofSchema h h₁)
  | andIR h₁ h₂     => andIR (ofProofSchema h h₁) (ofProofSchema h h₂)

lemma of_proof_schema (h : H₂ ⊢* H₁.schema) : H₁ ⊢ φ → H₂ ⊢ φ :=
  λ ⟨hφ⟩ => ⟨ofProofSchema (h · |>.get) hφ⟩

lemma weakerThan_of_provable_schema (h : H₂ ⊢* H₁.schema) : H₁ ⪯ H₂ :=
  Entailment.weakerThan_iff.mpr $ of_proof_schema h

open Entailment.Corsi in
@[induction_eliminator]
protected lemma rec_provable
  {H : HilbertF α}
  {motive  : (φ : Formula α) → (H ⊢ φ) → Prop}
  (axm       : ∀ {φ}, (h : φ ∈ H) → motive (φ) (of_schema h))
  (mdp       : ∀ {φ ψ}, {hφψ : H ⊢ φ 🡒 ψ} → {hφ : H ⊢ φ} → (motive (φ 🡒 ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af        : ∀ {φ ψ}, {hφ : H ⊢ φ} → (motive φ hφ) → (motive (ψ 🡒 φ) (af hφ)))
  (andIR     : ∀ {φ ψ}, {hφ : H ⊢ φ} → {hψ : H ⊢ ψ} → (motive φ hφ) → (motive ψ hψ) → (motive (φ ⋏ ψ) (andIR hφ hψ)))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  (impId     : ∀ {φ}, (motive (Axioms.ImpId φ) impId))
  (andElimL  : ∀ {φ ψ}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR  : ∀ {φ ψ}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (axiomC     : ∀ {φ ψ χ}, (motive (Axioms.C φ ψ χ) axiomC))
  (axiomD     : ∀ {φ ψ χ}, (motive (Axioms.D φ ψ χ) axiomD))
  (axiomI     : ∀ {φ ψ χ}, (motive (Axioms.I φ ψ χ) axiomI))
  (efq       : ∀ {φ}, (motive (Axioms.EFQ φ) efq))
  : ∀ {φ}, (d : H ⊢ φ) → motive φ d := by rintro φ ⟨d⟩; induction d <;> grind;

section

instance : Entailment.HasAxiomSer (HilbertF.F_Ser : HilbertF α) where
  axiomSer! := axm $ by tauto;

instance : Entailment.HasAxiomRfl (HilbertF.F_Rfl : HilbertF α) where
  axiomRfl! {φ ψ} := axm $ by tauto;

instance : Entailment.HasAxiomSym (HilbertF.F_Sym : HilbertF α) where
  axiomSym! {φ ψ} := axm $ by tauto;

instance : Entailment.HasAxiomRfl (HilbertF.F_Rfl_Sym : HilbertF α) where
  axiomRfl! {φ ψ} := axm $ by left; tauto;
instance : Entailment.HasAxiomSym (HilbertF.F_Rfl_Sym : HilbertF α) where
  axiomSym! {φ ψ} := axm $ by right; tauto;

instance : Entailment.HasAxiomTra1 (HilbertF.F_Tra1 : HilbertF α) where
  axiomTra1! {φ ψ χ} := axm $ by use φ, ψ, χ;

instance : Entailment.HasAxiomRfl (HilbertF.F_Rfl_Tra1 : HilbertF α) where
  axiomRfl! {φ ψ} := axm $ by left; tauto;
instance : Entailment.HasAxiomTra1 (HilbertF.F_Rfl_Tra1 : HilbertF α) where
  axiomTra1! {φ ψ χ} := axm $ by right; simp;

/-
instance : Entailment.HasAxiomTra1 (HilbertF.F_Tra1_Hrd : HilbertF α) where
  axiomTra1! {φ ψ χ} := axm $ by left; simp;
instance : Entailment.HasAxiomHrd (HilbertF.F_Tra1_Hrd : HilbertF α) where
  axiomHrd! {φ} := axm $ by tauto;

instance : Entailment.HasAxiomRfl (HilbertF.F_Rfl_Tra1_Hrd : HilbertF α) where
  axiomRfl! {φ ψ} := axm $ by left; left; simp;
instance : Entailment.HasAxiomTra1 (HilbertF.F_Rfl_Tra1_Hrd : HilbertF α) where
  axiomTra1! {φ ψ χ} := axm $ by left; right; simp;
instance : Entailment.HasAxiomHrd (HilbertF.F_Rfl_Tra1_Hrd : HilbertF α) where
  axiomHrd! {φ} := axm $ by right; simp;
-/

end

abbrev logic (H : HilbertF α) : Logic α where
  logic := Entailment.theory H
  subst s {_} := HilbertF.subst s
  mdp := Entailment.mdp!

end HilbertF


namespace HilbertF

variable {H : HilbertF α}

lemma mem_logic_of_proof (h : H ⊢! φ) : φ ∈ H.logic := ⟨h⟩

lemma mem_logic_of_provable (h : H ⊢ φ) : φ ∈ H.logic := mem_logic_of_proof h.get
lemma provable_of_mem_logic (h : φ ∈ H.logic) : H ⊢ φ := h

@[grind =]
lemma iff_mem_logic_provable : H ⊢ φ ↔ φ ∈ H.logic := ⟨mem_logic_of_provable, provable_of_mem_logic⟩

end HilbertF


protected abbrev F              : Logic α := HilbertF.F.logic
protected abbrev F_Ser          : Logic α := HilbertF.F_Ser.logic
protected abbrev F_Rfl          : Logic α := HilbertF.F_Rfl.logic
protected abbrev F_Sym          : Logic α := HilbertF.F_Sym.logic
protected abbrev F_Rfl_Sym      : Logic α := HilbertF.F_Rfl_Sym.logic
protected abbrev F_Tra1         : Logic α := HilbertF.F_Tra1.logic
protected abbrev F_Rfl_Tra1     : Logic α := HilbertF.F_Rfl_Tra1.logic
/-
protected abbrev F_Tra1_Hrd     : Logic α := HilbertF.F_Tra1_Hrd.logic
protected abbrev F_Rfl_Tra1_Hrd : Logic α := HilbertF.F_Rfl_Tra1_Hrd.logic
-/

end LO.Propositional

end
