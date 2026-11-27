module

public import Foundation.ProvabilityLogic.Formula
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# Logics

A logic is a set of formulas, regarded as an `Entailment` via membership.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

abbrev Logic (α : Type*) := Set (Formula α)

open Entailment Formula

variable {α : Type*}

instance : Entailment (Logic α) (Formula α) := ⟨fun L A ↦ A ∈ L⟩

namespace Logic

variable {L L₁ L₂ : Logic α} {A : Formula α}

lemma provable_iff_mem : L ⊢ A ↔ A ∈ L := Iff.rfl

lemma weakerThan_iff : L₁ ⪯ L₂ ↔ L₁ ⊆ L₂ := ⟨fun h ↦ h.subset, fun h ↦ ⟨h⟩⟩

lemma strictlyWeakerThan_iff : L₁ ⪱ L₂ ↔ L₁ ⊂ L₂ :=
  ⟨fun h ↦ ⟨weakerThan_iff.mp h.weakerThan, fun h' ↦ h.notWT (weakerThan_iff.mpr h')⟩,
    fun h ↦ ⟨weakerThan_iff.mpr h.1, fun h' ↦ h.2 (weakerThan_iff.mp h')⟩⟩

lemma equiv_iff : L₁ ≊ L₂ ↔ L₁ = L₂ := ⟨fun h ↦ h.eq, fun h ↦ ⟨congrArg theory h⟩⟩

alias ⟨eq_of_equiv, equiv_of_eq⟩ := equiv_iff

lemma weakerThan_antisymm (h₁ : L₁ ⪯ L₂) (h₂ : L₂ ⪯ L₁) : L₁ = L₂ :=
  subset_antisymm h₁.subset h₂.subset

lemma eq_or_strictlyWeakerThan (h : L₁ ⪯ L₂) : L₁ = L₂ ∨ L₁ ⪱ L₂ :=
  (weakerThan_iff.mp h).eq_or_ssubset.imp_right strictlyWeakerThan_iff.mpr

end Logic

/-! ### Quasi-normal sums -/

/-- The derivability predicate of `Logic.sumQuasiNormal`. -/
@[grind]
inductive Logic.SumQuasiNormal (L₁ L₂ : Logic α) : Formula α → Prop
  | mem₁ {A}    : A ∈ L₁ → SumQuasiNormal L₁ L₂ A
  | mem₂ {A}    : A ∈ L₂ → SumQuasiNormal L₁ L₂ A
  | mdp  {A B}  : SumQuasiNormal L₁ L₂ (A 🡒 B) → SumQuasiNormal L₁ L₂ A → SumQuasiNormal L₁ L₂ B
  | subst {A s} : SumQuasiNormal L₁ L₂ A → SumQuasiNormal L₁ L₂ (A⟦s⟧)

def Logic.sumQuasiNormal (L₁ L₂ : Logic α) : Logic α := Set.ofPred (Logic.SumQuasiNormal L₁ L₂)

infix:50 " +ᴸ " => Logic.sumQuasiNormal

namespace Logic.sumQuasiNormal

variable {L₁ L₂ : Logic α} {A B : Formula α} {s : Substitution α α}

lemma mem₁ (h : A ∈ L₁) : A ∈ L₁ +ᴸ L₂ := SumQuasiNormal.mem₁ h

lemma mem₂ (h : A ∈ L₂) : A ∈ L₁ +ᴸ L₂ := SumQuasiNormal.mem₂ h

lemma mdp (h₁ : A 🡒 B ∈ L₁ +ᴸ L₂) (h₂ : A ∈ L₁ +ᴸ L₂) : B ∈ L₁ +ᴸ L₂ :=
  SumQuasiNormal.mdp h₁ h₂

lemma subst (h : A ∈ L₁ +ᴸ L₂) : A⟦s⟧ ∈ L₁ +ᴸ L₂ := SumQuasiNormal.subst h


variable {L₁ L₂ X Y : Logic α} {A : Formula α}

@[grind .] lemma subset_left : L₁ ⊆ (L₁ +ᴸ L₂) := fun _ ↦ mem₁

@[grind .] lemma subset_right : L₂ ⊆ (L₁ +ᴸ L₂) := fun _ ↦ mem₂

instance : L₁ ⪯ L₁ +ᴸ L₂ := ⟨subset_left⟩

lemma subset_iff : (L₁ +ᴸ X) ⊆ (L₁ +ᴸ Y) ↔ X ⊆ (L₁ +ᴸ Y) := by
  constructor;
  · exact fun h _ hA ↦ h (mem₂ hA);
  · intro h A hA;
    induction (hA : SumQuasiNormal L₁ (X) A) with
    | mem₁ hA => exact mem₁ hA;
    | mem₂ hA => exact h hA;
    | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
    | subst _ ih => exact subst ih;

lemma of_left (h : L₁ ⊢ A) : L₁ +ᴸ L₂ ⊢ A := mem₁ h

instance : ModusPonens (L₁ +ᴸ L₂) := ⟨mdp⟩
instance [HasAxiomImplyK L₁] : HasAxiomImplyK (L₁ +ᴸ L₂) := ⟨of_left implyK⟩
instance [HasAxiomImplyS L₁] : HasAxiomImplyS (L₁ +ᴸ L₂) := ⟨of_left implyS⟩
instance [HasAxiomAndInst L₁] : HasAxiomAndInst (L₁ +ᴸ L₂) := ⟨of_left and₃⟩

instance [Entailment.Minimal L₁] : Entailment.Minimal (L₁ +ᴸ L₂) where
  verum := of_left verum
  and₁ := of_left and₁
  and₂ := of_left and₂
  or₁ := of_left or₁
  or₂ := of_left or₂
  or₃ := of_left or₃

instance [Entailment.Cl L₁] : Entailment.Cl (L₁ +ᴸ L₂) where
  dne := of_left dne

end Logic.sumQuasiNormal

/-! ### Normal sums -/

/-- The derivability predicate of `Logic.sumNormal`. -/
@[grind]
inductive Logic.SumNormal (L₁ L₂ : Logic α) : Formula α → Prop
  | mem₁ {A}    : A ∈ L₁ → SumNormal L₁ L₂ A
  | mem₂ {A}    : A ∈ L₂ → SumNormal L₁ L₂ A
  | mdp  {A B}  : SumNormal L₁ L₂ (A 🡒 B) → SumNormal L₁ L₂ A → SumNormal L₁ L₂ B
  | subst {A s} : SumNormal L₁ L₂ A → SumNormal L₁ L₂ (A⟦s⟧)
  | nec  {A}    : SumNormal L₁ L₂ A → SumNormal L₁ L₂ (□A)

def Logic.sumNormal (L₁ L₂ : Logic α) : Logic α := Set.ofPred (Logic.SumNormal L₁ L₂)

infix:50 " ⊕ᴸ " => Logic.sumNormal

namespace Logic.sumNormal

variable {L₁ L₂ : Logic α} {A B : Formula α} {s : Substitution α α}

lemma mem₁ (h : A ∈ L₁) : A ∈ L₁ ⊕ᴸ L₂ := SumNormal.mem₁ h

lemma mem₂ (h : A ∈ L₂) : A ∈ L₁ ⊕ᴸ L₂ := SumNormal.mem₂ h

lemma mdp (h₁ : A 🡒 B ∈ L₁ ⊕ᴸ L₂) (h₂ : A ∈ L₁ ⊕ᴸ L₂) : B ∈ L₁ ⊕ᴸ L₂ :=
  SumNormal.mdp h₁ h₂

lemma subst (h : A ∈ L₁ ⊕ᴸ L₂) : A⟦s⟧ ∈ L₁ ⊕ᴸ L₂ := SumNormal.subst h

lemma nec (h : A ∈ L₁ ⊕ᴸ L₂) : □A ∈ L₁ ⊕ᴸ L₂ := SumNormal.nec h

@[grind .] lemma subset_left : L₁ ⊆ (L₁ ⊕ᴸ L₂) := fun _ ↦ mem₁

@[grind .] lemma subset_right : L₂ ⊆ (L₁ ⊕ᴸ L₂) := fun _ ↦ mem₂

lemma sumQuasiNormal_subset : (L₁ +ᴸ L₂) ⊆ (L₁ ⊕ᴸ L₂) := by
  intro A h;
  induction (h : SumQuasiNormal L₁ L₂ A) with
  | mem₁ h => exact mem₁ h;
  | mem₂ h => exact mem₂ h;
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
  | subst _ ih => exact subst ih;

lemma of_left (h : L₁ ⊢ A) : L₁ ⊕ᴸ L₂ ⊢ A := mem₁ h

instance : ModusPonens (L₁ ⊕ᴸ L₂) := ⟨mdp⟩
instance [HasAxiomImplyK L₁] : HasAxiomImplyK (L₁ ⊕ᴸ L₂) := ⟨of_left implyK⟩
instance [HasAxiomImplyS L₁] : HasAxiomImplyS (L₁ ⊕ᴸ L₂) := ⟨of_left implyS⟩
instance [HasAxiomAndInst L₁] : HasAxiomAndInst (L₁ ⊕ᴸ L₂) := ⟨of_left and₃⟩

instance [Entailment.Minimal L₁] : Entailment.Minimal (L₁ ⊕ᴸ L₂) where
  verum := of_left verum
  and₁ := of_left and₁
  and₂ := of_left and₂
  or₁ := of_left or₁
  or₂ := of_left or₂
  or₃ := of_left or₃

instance [Entailment.Cl L₁] : Entailment.Cl (L₁ ⊕ᴸ L₂) where
  dne := of_left dne

end Logic.sumNormal

/-! ### Normal logics generated by axiom schemata -/

/-- The derivability predicate of `Logic.normalOf`. -/
inductive Logic.NormalOf (𝔸 : Set (Formula α)) : Formula α → Prop
  | axm {A}        : A ∈ 𝔸 → NormalOf 𝔸 A
  | mdp {A B}      : NormalOf 𝔸 (A 🡒 B) → NormalOf 𝔸 A → NormalOf 𝔸 B
  | nec {A}        : NormalOf 𝔸 A → NormalOf 𝔸 (□A)
  | verum          : NormalOf 𝔸 Axioms.Verum
  | implyK {A B}   : NormalOf 𝔸 (Axioms.ImplyK A B)
  | implyS {A B C} : NormalOf 𝔸 (Axioms.ImplyS A B C)
  | andElimL {A B} : NormalOf 𝔸 (Axioms.AndElim₁ A B)
  | andElimR {A B} : NormalOf 𝔸 (Axioms.AndElim₂ A B)
  | andIntro {A B} : NormalOf 𝔸 (Axioms.AndInst A B)
  | orIntroL {A B} : NormalOf 𝔸 (Axioms.OrInst₁ A B)
  | orIntroR {A B} : NormalOf 𝔸 (Axioms.OrInst₂ A B)
  | orElim {A B C} : NormalOf 𝔸 (Axioms.OrElim A B C)
  | dne {A}        : NormalOf 𝔸 (Axioms.DNE A)
  | axiomK {A B}   : NormalOf 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)

/-- The smallest normal logic containing `𝔸`. -/
def Logic.normalOf (𝔸 : Set (Formula α)) : Logic α := Set.ofPred (Logic.NormalOf 𝔸)

namespace Logic.normalOf

variable {𝔸 : Set (Formula α)}

lemma axm {A : Formula α} (h : A ∈ 𝔸) : normalOf 𝔸 ⊢ A := NormalOf.axm h

lemma mdp {A B : Formula α} (h₁ : normalOf 𝔸 ⊢ A 🡒 B) (h₂ : normalOf 𝔸 ⊢ A) : normalOf 𝔸 ⊢ B :=
  NormalOf.mdp h₁ h₂

lemma nec {A : Formula α} (h : normalOf 𝔸 ⊢ A) : normalOf 𝔸 ⊢ □A := NormalOf.nec h

lemma verum : normalOf 𝔸 ⊢ Axioms.Verum := NormalOf.verum

lemma implyK {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.ImplyK A B := NormalOf.implyK

lemma implyS {A B C : Formula α} : normalOf 𝔸 ⊢ Axioms.ImplyS A B C := NormalOf.implyS

lemma andElimL {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.AndElim₁ A B := NormalOf.andElimL

lemma andElimR {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.AndElim₂ A B := NormalOf.andElimR

lemma andIntro {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.AndInst A B := NormalOf.andIntro

lemma orIntroL {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.OrInst₁ A B := NormalOf.orIntroL

lemma orIntroR {A B : Formula α} : normalOf 𝔸 ⊢ Axioms.OrInst₂ A B := NormalOf.orIntroR

lemma orElim {A B C : Formula α} : normalOf 𝔸 ⊢ Axioms.OrElim A B C := NormalOf.orElim

lemma dne {A : Formula α} : normalOf 𝔸 ⊢ Axioms.DNE A := NormalOf.dne

lemma axiomK {A B : Formula α} : normalOf 𝔸 ⊢ □(A 🡒 B) 🡒 □A 🡒 □B := NormalOf.axiomK

instance : ModusPonens (normalOf 𝔸) := ⟨mdp⟩
instance : HasAxiomImplyK (normalOf 𝔸) := ⟨implyK⟩
instance : HasAxiomImplyS (normalOf 𝔸) := ⟨implyS⟩
instance : HasAxiomAndInst (normalOf 𝔸) := ⟨andIntro⟩

instance : Entailment.Minimal (normalOf 𝔸) where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

instance : Entailment.Cl (normalOf 𝔸) where
  dne := dne

variable {A B : Formula α}

lemma box_mono (h : normalOf 𝔸 ⊢ A 🡒 B) : normalOf 𝔸 ⊢ □A 🡒 □B := axiomK ⨀ nec h

lemma box_and : normalOf 𝔸 ⊢ □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : normalOf 𝔸 ⊢ □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : normalOf 𝔸 ⊢ □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

variable [DecidableEq α]

lemma box_conj {Γ : FormulaFinset α} : normalOf 𝔸 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : normalOf 𝔸 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact C_of_conseq (nec this);
  | insert A Γ _ ih =>
    have h₁ :
        normalOf 𝔸 ⊢ (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : normalOf 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : normalOf 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box_insert];
    cl_prover [ih, h₁, h₂, h₃];

end Logic.normalOf

end FFL.ProvabilityLogic

end
