module

public import Foundation.Propositional.Entailment.Int.DNE_of_LEM
public import Foundation.Propositional.Hilbert.Axiom


@[expose] public section

namespace LO.Propositional

variable {α : Type*}

structure Hilbert (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

namespace Hilbert

instance : SetLike (Hilbert α) (Formula α) where
  coe := Hilbert.schema
  coe_injective' := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa;

protected def Min : Hilbert α := ⟨∅, by tauto⟩
protected def Int : Hilbert α := ⟨{ Axioms.EFQ φ | φ }, by grind⟩
protected def KC : Hilbert α := ⟨{ Axioms.EFQ φ | φ } ∪ { Axioms.WLEM φ | φ }, by grind⟩
protected def LC : Hilbert α := ⟨
  { Axioms.EFQ φ | φ } ∪
  { Axioms.Dummett φ ψ | (φ) (ψ) },
  by rintro φ (_ | _) <;> grind;
⟩
protected def KreiselPutnam : Hilbert α := ⟨
  { Axioms.EFQ φ | φ } ∪
  { Axioms.KreiselPutnam φ ψ χ | (φ) (ψ) (χ) },
  by rintro φ (_ | _) <;> grind;
⟩
protected def Cl : Hilbert α := ⟨
  { Axioms.EFQ φ | φ } ∪ { Axioms.LEM φ | φ },
  by rintro φ (_ | _) <;> grind;
⟩

@[simp, grind .] lemma Int_le_KC : (Hilbert.Int : Hilbert α) ≤ Hilbert.KC := by tauto;
@[simp, grind .] lemma Int_le_LC : (Hilbert.Int : Hilbert α) ≤ Hilbert.LC := by tauto;
@[simp, grind .] lemma Int_le_KreiselPutnam : (Hilbert.Int : Hilbert α) ≤ Hilbert.KreiselPutnam := by tauto;
@[simp, grind .] lemma Int_le_Cl : (Hilbert.Int : Hilbert α) ≤ Hilbert.Cl := by tauto;

end Hilbert


inductive HilbertProof (Λ : Hilbert α) : Formula α → Type _
| axm {φ}        : φ ∈ Λ → HilbertProof Λ φ
| mdp {φ ψ}      : HilbertProof Λ (φ 🡒 ψ) → HilbertProof Λ φ → HilbertProof Λ ψ
| verum          : HilbertProof Λ $ Axioms.Verum
| implyS {φ ψ χ} : HilbertProof Λ $ Axioms.ImplyS φ ψ χ
| implyK {φ ψ}   : HilbertProof Λ $ Axioms.ImplyK φ ψ
| andElimL {φ ψ} : HilbertProof Λ $ Axioms.AndElim₁ φ ψ
| andElimR {φ ψ} : HilbertProof Λ $ Axioms.AndElim₂ φ ψ
| andIntro {φ ψ} : HilbertProof Λ $ Axioms.AndInst φ ψ
| orIntroL {φ ψ} : HilbertProof Λ $ Axioms.OrInst₁ φ ψ
| orIntroR {φ ψ} : HilbertProof Λ $ Axioms.OrInst₂ φ ψ
| orElim {φ ψ χ} : HilbertProof Λ $ Axioms.OrElim φ ψ χ

instance : Entailment (Hilbert α) (Formula α) := ⟨HilbertProof⟩

namespace HilbertProof

variable (H : Hilbert α)

instance : Entailment.ModusPonens H := ⟨mdp⟩
instance : Entailment.HasAxiomImplyK H := ⟨implyK⟩
instance : Entailment.HasAxiomImplyS H := ⟨implyS⟩
instance : Entailment.HasAxiomAndInst H := ⟨andIntro⟩
instance : Entailment.Minimal H where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

variable {H}

instance : Entailment.Int (Hilbert.Int : Hilbert α) where
  efq := axm $ by tauto

instance : Entailment.KC (Hilbert.KC : Hilbert α) where
  efq  := axm $ by tauto
  wlem := axm $ by tauto

instance : Entailment.LC (Hilbert.LC : Hilbert α) where
  efq     := axm $ by tauto
  dummett := axm $ by tauto

instance : Entailment.HasAxiomEFQ (Hilbert.Cl : Hilbert α) := ⟨axm $ by tauto⟩
instance : Entailment.HasAxiomLEM (Hilbert.Cl : Hilbert α) := ⟨axm $ by tauto⟩

def ofLE {H₁ H₂ : Hilbert α} (h : H₁ ≤ H₂) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁ => axm $ h h₁
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

lemma of_le {H₁ H₂ : Hilbert α} (h : H₁ ≤ H₂) : H₁ ⊢ φ → H₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofLE h hφ⟩

def Subst {H : Hilbert α} (s) : H ⊢! φ → H ⊢! φ⟦s⟧
  | axm h₁ => axm $ H.schema_closed φ h₁ s
  | mdp h₁ h₂ => mdp (Subst s h₁) (Subst s h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma subst {H : Hilbert α} (s) : H ⊢ φ → H ⊢ φ⟦s⟧ := λ ⟨hφ⟩ => ⟨Subst s hφ⟩

end HilbertProof

@[ext]
structure Logic (α) where
  logic : Set (Formula α)
  subst : ∀ s, ∀ φ ∈ logic, φ⟦s⟧ ∈ logic
  mdp : ∀ {φ ψ}, φ 🡒 ψ ∈ logic → φ ∈ logic → ψ ∈ logic

namespace Logic

instance : SetLike (Logic α) (Formula α) where
  coe := logic
  coe_injective' _ _ := Logic.ext

class Trivial (L : Logic α) : Prop where
  eq_univ : L.logic = Set.univ

end Logic

abbrev Trivial : Logic α := ⟨Set.univ, by tauto, by tauto⟩


namespace Hilbert

abbrev logic (H : Hilbert α) : Logic α where
  logic := Entailment.theory H
  subst s {_} := HilbertProof.subst s
  mdp := Entailment.mdp!;

variable {H : Hilbert α}

lemma mem_logic_of_proof (h : H ⊢! φ) : φ ∈ H.logic := ⟨h⟩

lemma mem_logic_of_provable (h : H ⊢ φ) : φ ∈ H.logic := mem_logic_of_proof h.get
lemma provable_of_mem_logic (h : φ ∈ H.logic) : H ⊢ φ := h

@[grind =]
lemma iff_mem_logic_provable : H ⊢ φ ↔ φ ∈ H.logic := ⟨mem_logic_of_provable, provable_of_mem_logic⟩

end Hilbert


protected abbrev Int           : Logic α := Hilbert.Int.logic
protected abbrev KC            : Logic α := Hilbert.KC.logic
protected abbrev LC            : Logic α := Hilbert.LC.logic
protected abbrev KreiselPutnam : Logic α := Hilbert.KreiselPutnam.logic
protected abbrev Cl            : Logic α := Hilbert.Cl.logic

structure Logic.ExtensionOf (L : Logic α) extends Logic α where
  subset_L : ∀ {φ}, φ ∈ L → φ ∈ logic


abbrev SuperIntuitionisticLogic (α) := Logic.ExtensionOf (Propositional.Int : Logic α)


namespace SuperIntuitionisticLogic

variable {L : SuperIntuitionisticLogic α} {φ ψ : Formula α}

lemma subset_Int (h : φ ∈ Propositional.Int) : φ ∈ L.logic := L.subset_L h

lemma trivial_of_mem_bot (h : ⊥ ∈ L.toLogic) : ∀ {φ}, φ ∈ L.toLogic := L.mdp (L.subset_Int Entailment.efq!) h
instance (h : ⊥ ∈ L.toLogic) : L.Trivial := ⟨Set.eq_univ_iff_forall.mpr $ @trivial_of_mem_bot α L h⟩

class Consistent (L : SuperIntuitionisticLogic α) : Prop where
  not_mem_bot : ⊥ ∉ L.logic
attribute [simp, grind .] Consistent.not_mem_bot

lemma ssubset_univ [L.Consistent] : L.logic ⊂ Propositional.Trivial.logic := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . tauto;
  . use ⊥;
    grind;

end SuperIntuitionisticLogic



end LO.Propositional

end
