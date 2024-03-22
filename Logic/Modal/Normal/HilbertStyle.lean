import Logic.Logic.Deduction
import Logic.Modal.Normal.LogicSymbol
import Logic.Modal.Normal.Axioms

namespace LO.Hilbert

open LO.Deduction LO.Modal.Normal

variable {F : Type u} [ModalLogicSymbol F] [DecidableEq F] [NegDefinition F] (Bew : Set F → F → Type u)

class HasNecessitation where
  necessitation {Γ p} : (Bew ∅ p) → (Bew Γ (□p))

class HasBoxedNecessitation where
  boxed_necessitation {Γ p} : (Bew Γ p) → (Bew (Γ.box) (□p))

class HasAxiomK where
  K (Γ : Set F) (p q : F) : Bew Γ $ AxiomK p q

class HasAxiomT where
  T (Γ : Set F) (p : F) : Bew Γ $ AxiomT p

class HasAxiomD where
  D (Γ : Set F) (p : F) : Bew Γ $ AxiomD p

class HasAxiomB where
  B (Γ : Set F) (p q : F) : Bew Γ $ AxiomB p

class HasAxiom4 where
  A4 (Γ : Set F) (p : F) : Bew Γ $ Axiom4 p

class HasAxiom5 where
  A5 (Γ : Set F) (p : F) : Bew Γ $ Axiom5 p

class HasAxiomL where
  L (Γ : Set F) (p : F) : Bew Γ $ AxiomL p

class HasAxiomDot2 where
  Dot2 (Γ : Set F) (p : F) : Bew Γ $ AxiomDot2 p

class HasAxiomDot3 where
  Dot3 (Γ : Set F) (p q : F) : Bew Γ $ AxiomDot3 p q

class HasAxiomGrz where
  Grz (Γ : Set F) (p : F) : Bew Γ $ AxiomGrz p

class HasAxiomM where
  M (Γ : Set F) (p : F) : Bew Γ $ AxiomM p

class HasAxiomCD where
  CD (Γ : Set F) (p : F) : Bew Γ $ AxiomCD p

class HasAxiomC4 where
  C4 (Γ : Set F) (p : F) : Bew Γ $ AxiomC4 p

section

variable {Bew : Set F → F → Type u}

local infixr:50 " ⊢ " => Bew
local infixr:50 " ⊢! " => Deducible Bew

variable [ModalDuality F]
variable [HasDT Bew] [Minimal Bew] [HasNecessitation Bew] [HasAxiomK Bew]
variable [Classical Bew]

open HasNecessitation

def necessitation {Γ : Set F} {p} (d : (∅ : Set F) ⊢ p) : Γ ⊢ □p := HasNecessitation.necessitation d

def necessitation! {Γ : Set F} {p} (d : (∅ : Set F) ⊢! p) : Γ ⊢! □p := ⟨necessitation d.some⟩

open HasBoxedNecessitation

variable [HasBoxedNecessitation Bew]

def boxed_necessitation {Γ : Set F} {p} (d : Γ ⊢ p) : Γ.box ⊢ □p := HasBoxedNecessitation.boxed_necessitation d

def boxed_necessitation! {Γ : Set F} {p} (d : Γ ⊢! p) : Γ.box ⊢! □p := ⟨boxed_necessitation d.some⟩

def preboxed_necessitation {Γ : Set F} {p} (d : Γ.prebox ⊢ p) : Γ ⊢ □p := by
  exact Deduction.weakening' Set.prebox_box_subset $ boxed_necessitation d;

def preboxed_necessitation! {Γ : Set F} {p} (d : Γ.prebox ⊢! p) : Γ ⊢! □p := ⟨preboxed_necessitation d.some⟩

open HasAxiomK

def axiomK (Γ : Set F) (p q) :  Γ ⊢ (AxiomK p q) := HasAxiomK.K Γ p q

def axiomK' {Γ : Set F} {p q} (d₁ : Γ ⊢ (□(p ⟶ q))) (d₂ : Γ ⊢ □p) : Γ ⊢ □q := ((Hilbert.axiomK Γ p q) ⨀ d₁) ⨀ d₂

lemma axiomK! (Γ : Set F) (p q) : Γ ⊢! (AxiomK p q) := ⟨Hilbert.axiomK Γ p q⟩

lemma axiomK'! {Γ : Set F} {p q} (d₁ : Γ ⊢! (□(p ⟶ q))) (d₂ : Γ ⊢! □p) : Γ ⊢! □q := ⟨axiomK' d₁.some d₂.some⟩


def boxverum (Γ : Set F) : Γ ⊢ □⊤ := necessitation (verum _)

lemma boxverum! (Γ : Set F) : Γ ⊢! □⊤ := ⟨boxverum Γ⟩

def box_iff' {Γ : Set F} {p q : F} (d : ∅ ⊢ p ⟷ q) : Γ ⊢ (□p ⟷ □q) := by
  have dp₁ : ∅ ⊢ (□(p ⟶ q) ⟶ (□p ⟶ □q)) := Hilbert.axiomK ∅ p q;
  have dp₂ : ∅ ⊢ (□(p ⟶ q)) := necessitation $ iff_mp' d;

  have dq₁ : ∅ ⊢ (□(q ⟶ p) ⟶ (□q ⟶ □p)) := Hilbert.axiomK ∅ q p;
  have dq₂ : ∅ ⊢ (□(q ⟶ p)) := necessitation $ iff_mpr' d;

  exact iff_intro
    (Deduction.weakening' (by simp) (modus_ponens' dp₁ dp₂))
    (Deduction.weakening' (by simp) (modus_ponens' dq₁ dq₂))

lemma box_iff'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (□p ⟷ □q) := ⟨box_iff' d.some⟩

def equiv_dianeg_negbox (Γ p) : Γ ⊢ ◇~p ⟷ ~(□p) := by
  simp only [ModalDuality.dia]
  apply Hilbert.neg_iff';
  apply box_iff';
  apply iff_symm';
  apply equiv_dn;

lemma equiv_dianeg_negbox! (Γ p) : Γ ⊢! ◇~p ⟷ ~(□p) := ⟨equiv_dianeg_negbox Γ p⟩

lemma box_imp' {Γ : Set F} {p q : F} (d : ∅ ⊢ p ⟶ q) : Γ ⊢ (□p ⟶ □q) := by
  have d₁ : ∅ ⊢ □(p ⟶ q) ⟶ (□p ⟶ □q) := by apply axiomK;
  have d₂ : ∅ ⊢ □(p ⟶ q) := necessitation d;
  exact weakening' (by simp) $ modus_ponens' d₁ d₂;

lemma collect_box_and' {Γ : Set F} {p q : F} (d : Γ ⊢ □p ⋏ □q) : Γ ⊢ □(p ⋏ q) := by
  have : ∅ ⊢ p ⟶ (q ⟶ (p ⋏ q)) := by apply conj₃;
  have : ∅ ⊢ □p ⟶ □(q ⟶ (p ⋏ q)) := box_imp' (by assumption)
  have : ∅ ⊢ □p ⟶ (□q ⟶ □(p ⋏ q)) := imp_trans' (by assumption) (by apply axiomK);
  simpa using modus_ponens (modus_ponens this (conj₁' d)) (conj₂' d)

lemma collect_box_and'! {Γ : Set F} {p q : F} (d : Γ ⊢! □p ⋏ □q) : Γ ⊢! □(p ⋏ q) := ⟨collect_box_and' d.some⟩

lemma collect_box_or' {Γ : Set F} {p q : F} (d : Γ ⊢ □p ⋎ □q) : Γ ⊢ □(p ⋎ q) := by
  have : Γ ⊢ □p ⟶ □(p ⋎ q) := box_imp' (by apply disj₁);
  have : Γ ⊢ □q ⟶ □(p ⋎ q) := box_imp' (by apply disj₂);
  exact disj₃' (by assumption) (by assumption) d;

lemma collect_box_or'! {Γ : Set F} {p q : F} (d : Γ ⊢! □p ⋎ □q) : Γ ⊢! □(p ⋎ q) := ⟨collect_box_or' d.some⟩

variable [HasAxiom4 Bew]

def axiom4 (Γ : Set F) (p) :  Γ ⊢ (Axiom4 p) := HasAxiom4.A4 Γ p

def axiom4' {Γ : Set F} {p} (d₁ : Γ ⊢ □p) : Γ ⊢ □□p := (Hilbert.axiom4 Γ p) ⨀ d₁

lemma axiom4! (Γ : Set F) (p) : Γ ⊢! (Axiom4 p) := ⟨Hilbert.axiom4 Γ p⟩

lemma axiom4'! {Γ : Set F} {p} (d : Γ ⊢! □p) : Γ ⊢! □□p := ⟨axiom4' d.some⟩


variable [HasAxiomT Bew]

def axiomT (Γ : Set F) (p) :  Γ ⊢ (AxiomT p) := HasAxiomT.T Γ p

def axiomT' {Γ : Set F} {p} (d₁ : Γ ⊢ □p) : Γ ⊢ p := (Hilbert.axiomT Γ p) ⨀ d₁

lemma axiomT! (Γ : Set F) (p) : Γ ⊢! (AxiomT p) := ⟨Hilbert.axiomT Γ p⟩

lemma axiomT'! {Γ : Set F} {p} (d : Γ ⊢! □p) : Γ ⊢! p := ⟨axiomT' d.some⟩

end

section Logics

variable {F : Type u} [ModalLogicSymbol F] [NegDefinition F] [ModalDuality F] [DecidableEq F] (Bew : Set F → F → Type u)

class K [ModalDuality F] extends Hilbert.Classical Bew, HasNecessitation Bew, HasAxiomK Bew

class KD extends Hilbert.K Bew, HasAxiomD Bew

class K4 extends Hilbert.K Bew, HasAxiom4 Bew

class S4 extends Hilbert.K Bew, HasAxiomT Bew, HasAxiom4 Bew

class S5 extends Hilbert.K Bew, HasAxiomT Bew, HasAxiom5 Bew

class S4Dot2 extends Hilbert.S4 Bew, HasAxiomDot2 Bew

class S4Dot3 extends Hilbert.S4 Bew, HasAxiomDot3 Bew

class S4Grz extends Hilbert.S4 Bew, HasAxiomGrz Bew

class GL extends Hilbert.K Bew, HasAxiomL Bew

end Logics

end LO.Hilbert
