import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Supplemental
import Logic.Modal.Normal.Axioms

namespace LO.Hilbert

open LO.Deduction LO.Modal.Normal

variable {F : Type u} [StandardModalLogicalConnective F] [DecidableEq F] [NegDefinition F] (Bew : Set F → F → Type u)

class HasNecessitation where
  necessitation {Γ p} : (Bew ∅ p) → (Bew Γ (□p))

class HasBoxedNecessitation where
  boxed_necessitation {Γ p} : (Bew Γ p) → (Bew (Γ.box) (□p))

class HasAxiomK where
  K (Γ : Set F) (p q : F) : Bew Γ $ axiomK p q

class HasAxiomT where
  T (Γ : Set F) (p : F) : Bew Γ $ axiomT p

class HasAxiomD where
  D (Γ : Set F) (p : F) : Bew Γ $ axiomD p

class HasAxiomB where
  B (Γ : Set F) (p q : F) : Bew Γ $ axiomB p

class HasAxiomFour where
  Four (Γ : Set F) (p : F) : Bew Γ $ axiomFour p

class HasAxiomFive where
  Five (Γ : Set F) (p : F) : Bew Γ $ axiomFive p

class HasAxiomL where
  L (Γ : Set F) (p : F) : Bew Γ $ axiomL p

class HasAxiomDot2 where
  Dot2 (Γ : Set F) (p : F) : Bew Γ $ axiomDot2 p

class HasAxiomDot3 where
  Dot3 (Γ : Set F) (p q : F) : Bew Γ $ axiomDot3 p q

class HasAxiomGrz where
  Grz (Γ : Set F) (p : F) : Bew Γ $ axiomGrz p

class HasAxiomM where
  M (Γ : Set F) (p : F) : Bew Γ $ axiomM p

class HasAxiomCD where
  CD (Γ : Set F) (p : F) : Bew Γ $ axiomCD p

class HasAxiomC4 where
  C4 (Γ : Set F) (p : F) : Bew Γ $ axiomC4 p

section

variable {Bew : Set F → F → Type u}

local infixr:50 " ⊢ " => Bew
local infixr:50 " ⊢! " => Deducible Bew

variable [HasDT Bew] [Minimal Bew] [Classical Bew]
variable [HasNecessitation Bew] [HasBoxedNecessitation Bew]
variable [HasAxiomK Bew]
variable {Γ Δ : Set F} {p q r : F} {n m : ℕ}

open HasNecessitation
open HasBoxedNecessitation
open HasAxiomK
open StandardModalLogicalConnective

@[inference]
def necessitation (d : ∅ ⊢ p) : Γ ⊢ □p := HasNecessitation.necessitation d

@[inference]
def necessitation! (d : ∅ ⊢! p) : Γ ⊢! □p := ⟨necessitation d.some⟩

@[inference]
def multi_necessitation (d : (∅ : Set F) ⊢ p) : Γ ⊢ □^[n]p := by induction n generalizing Γ <;> deduct

@[inference]
def multi_necessitation! (d : ∅ ⊢! p) : Γ ⊢! □^[n]p := ⟨multi_necessitation d.some⟩

@[inference]
def boxed_necessitation (d : Γ ⊢ p) : Γ.box ⊢ □p := HasBoxedNecessitation.boxed_necessitation d

@[inference]
def boxed_necessitation! (d : Γ ⊢! p) : Γ.box ⊢! □p := ⟨boxed_necessitation d.some⟩

@[inference]
def preboxed_necessitation (d : □⁻¹Γ ⊢ p) : Γ ⊢ □p := weakening' (by simp; rfl) $ boxed_necessitation d

@[inference]
def preboxed_necessitation! (d : □⁻¹Γ ⊢! p) : Γ ⊢! □p := ⟨preboxed_necessitation d.some⟩

@[tautology]
def axiomK : Γ ⊢ □(p ⟶ q) ⟶ □p ⟶ □q := by apply HasAxiomK.K

@[tautology]
lemma axiomK! : Γ ⊢! □(p ⟶ q) ⟶ □p ⟶ □q := ⟨Hilbert.axiomK⟩

@[inference]
def box_distribute' (d₁ : Γ ⊢ (□(p ⟶ q))) : Γ ⊢ □p ⟶ □q := axiomK ⨀ d₁

@[inference]
lemma box_distribute'! (d : Γ ⊢! □(p ⟶ q)) : Γ ⊢! □p ⟶ □q := ⟨box_distribute' d.some⟩

@[inference]
def box_distribute_nec' (d₁ : ∅ ⊢ p ⟶ q) : Γ ⊢ □p ⟶ □q := box_distribute' $ necessitation d₁

@[inference]
lemma box_distribute_nec'! (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □p ⟶ □q := ⟨box_distribute_nec' d.some⟩

@[tautology]
def multiaxiomK : Γ ⊢ □^[n](p ⟶ q) ⟶ (□^[n]p ⟶ □^[n]q) := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih =>
    have d₁ : Γ ⊢ □□^[n](p ⟶ q) ⟶ □(□^[n]p ⟶ □^[n]q) := box_distribute_nec' ih;
    have d₂ : Γ ⊢ □(□^[n]p ⟶ □^[n]q) ⟶ □□^[n]p ⟶ □□^[n]q := by deduct;
    simpa using imp_trans' d₁ d₂;

@[inference]
def multibox_distribute' (d : Γ ⊢ □^[n](p ⟶ q)) :  Γ ⊢ □^[n]p ⟶ □^[n]q := multiaxiomK ⨀ d

@[inference]
lemma multibox_distribute'! (d : Γ ⊢! □^[n](p ⟶ q)) : Γ ⊢! □^[n]p ⟶ □^[n]q := ⟨multibox_distribute' d.some⟩

@[tautology]
def multibox_distribute_nec' (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □^[n]p ⟶ □^[n]q := multibox_distribute' $ multi_necessitation d

@[inference]
lemma multibox_distribute_nec'! (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □^[n]p ⟶ □^[n]q := ⟨multibox_distribute_nec' d.some⟩

@[inference]
def axiomK' (d₁ : Γ ⊢ (□(p ⟶ q))) (d₂ : Γ ⊢ □p) : Γ ⊢ □q := axiomK ⨀ d₁ ⨀ d₂

@[inference]
lemma axiomK'! (d₁ : Γ ⊢! (□(p ⟶ q))) (d₂ : Γ ⊢! □p) : Γ ⊢! □q := ⟨axiomK' d₁.some d₂.some⟩

@[tautology]
def box_distribute_iff : Γ ⊢ □(p ⟷ q) ⟶ (□p ⟷ □q) := by
  have : (□({p ⟷ q} : Set F)) ⊢ (□p ⟶ □q) := box_distribute' $ boxed_necessitation $ iff_mp' $ axm (by simp);
  have : (□({p ⟷ q} : Set F)) ⊢ (□q ⟶ □p) := box_distribute' $ boxed_necessitation $ iff_mpr' $ axm (by simp);
  have : (□({p ⟷ q} : Set F)) ⊢ (□p ⟷ □q) := iff_intro' (by assumption) (by assumption)
  have : ∅ ⊢ (□(p ⟷ q) ⟶ (□p ⟷ □q)) := dtr' (by simpa using this);
  deduct;

@[inference]
def box_distribute_iff' (h : Γ ⊢ □(p ⟷ q)) : Γ ⊢ (□p ⟷ □q) := box_distribute_iff ⨀ h

@[inference]
def box_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (□p ⟷ □q) := box_distribute_iff' $ necessitation h

@[inference]
lemma box_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (□p ⟷ □q) := ⟨box_iff' d.some⟩

@[inference]
def dia_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (◇p ⟷ ◇q) := by
  simp only [duality'];
  apply neg_iff';
  apply box_iff';
  apply neg_iff';
  assumption

@[inference]
lemma dia_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (◇p ⟷ ◇q) := ⟨dia_iff' d.some⟩

@[inference]
def multibox_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ □^[n]p ⟷ □^[n]q := by
  induction n generalizing Γ with
  | zero => deduct;
  | succ =>
    simp;
    apply iff_intro';
    all_goals { apply box_distribute_nec'; deduct; }

@[inference]
lemma multibox_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! □^[n]p ⟷ □^[n]q := ⟨multibox_iff' d.some⟩

@[inference]
def multidia_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ ◇^[n]p ⟷ ◇^[n]q := by
  induction n generalizing Γ with
  | zero => deduct;
  | succ n ih =>
    simp [duality];
    apply neg_iff';
    apply box_iff';
    apply neg_iff';
    apply ih;

@[inference]
lemma multidia_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! ◇^[n]p ⟷ ◇^[n]q := ⟨multidia_iff' d.some⟩

@[tautology]
def box_duality : Γ ⊢ □p ⟷ ~(◇~p) := by
  simp [duality'];
  have d₁ : Γ ⊢ □p ⟷ (□~~p) := by deduct;
  have d₂ : Γ ⊢ (□~~p) ⟷ ~~(□~~p) := by deduct;
  simpa [duality] using iff_trans' d₁ d₂

@[tautology]
lemma box_duality! : Γ ⊢! □p ⟷ ~(◇~p) := ⟨box_duality⟩

@[tautology]
def dia_duality : Γ ⊢ ◇p ⟷ ~(□~p) := by
  simp only [duality'];
  apply neg_iff';
  apply iff_id;

@[tautology]
lemma dia_duality! : Γ ⊢! ◇p ⟷ ~(□~p) := ⟨dia_duality⟩

lemma dia_duality_mp' (h : Γ ⊢ ◇p) : Γ ⊢ ~(□~p) := by deduct;

@[tautology]
def multibox_duality : Γ ⊢ □^[n]p ⟷ ~(◇^[n](~p)) := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih =>
    simp [duality'];
    exact iff_trans'
      (show Γ ⊢ □□^[n]p ⟷ ~~(□~~(□^[n]p)) by
        have : Γ ⊢ □(□^[n]p) ⟷ ~(◇~(□^[n]p)) := box_duality
        simpa [duality'];
      )
      (by
        have : ∅ ⊢ ~~(□^[n]p) ⟷ □^[n]p := by deduct;
        have : ∅ ⊢ (□^[n]p ⟷ ~(◇^[n](~p))) := by deduct;
        have : ∅ ⊢ ~~(□^[n]p) ⟷ ~(◇^[n](~p)) := iff_trans' (by assumption) (by assumption);
        have : ∅ ⊢ □~~(□^[n]p) ⟷ □~(◇^[n](~p)) := box_iff' (by assumption);
        exact weakening' (by simp) $ dn_iff' this;
      )

@[tautology]
lemma multibox_duality! {n Γ p} : Γ ⊢! □^[n]p ⟷ ~(◇^[n](~p)) := ⟨multibox_duality⟩

@[tautology]
def multidia_duality : Γ ⊢ ◇^[n]p ⟷ ~(□^[n](~p)) := by
  induction n generalizing Γ with
  | zero => apply dn;
  | succ n ih =>
    simp [duality'];
    apply neg_iff';
    apply box_iff';
    exact iff_trans' (neg_iff' $ ih) (by deduct);

@[tautology]
lemma multidia_duality! : Γ ⊢! ◇^[n]p ⟷ ~(□^[n](~p)) := ⟨multidia_duality⟩

@[tautology] def boxverum : Γ ⊢ □⊤ := by deduct;

@[tautology] lemma boxverum! : Γ ⊢! □⊤ := ⟨boxverum⟩

@[tautology] def multiboxverum : Γ ⊢ □^[n]⊤ := by deduct;

@[tautology] lemma multiboxverum! : Γ ⊢! □^[n]⊤ := ⟨multiboxverum⟩

@[tautology]
def equiv_dianeg_negbox : Γ ⊢ ◇~p ⟷ ~(□p) := by
  simp only [duality];
  apply neg_iff';
  apply box_iff';
  apply iff_symm';
  apply equiv_dn;

@[tautology]
lemma equiv_dianeg_negbox! : Γ ⊢! ◇~p ⟷ ~(□p) := ⟨equiv_dianeg_negbox⟩

@[inference] def box_imp' (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □p ⟶ □q := by deduct

@[inference] def multibox_imp' (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □^[n]p ⟶ □^[n]q := by deduct

@[inference]
def distribute_box_conj' (d : Γ ⊢ □(p ⋏ q)) : Γ ⊢ □p ⋏ □q := by
  have dp : ∅ ⊢ □(p ⋏ q) ⟶ □p := by deduct;
  have dq : ∅ ⊢ □(p ⋏ q) ⟶ □q := by deduct;
  have : Γ ⊢ □p := by simpa using dp ⨀ d;
  have : Γ ⊢ □q := by simpa using dq ⨀ d;
  exact conj₃' (by assumption) (by assumption);

@[inference]
lemma distribute_box_conj'! (d : Γ ⊢! □(p ⋏ q)) : Γ ⊢! □p ⋏ □q := ⟨distribute_box_conj' d.some⟩

@[tautology]
def distribute_box_conj : Γ ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := by apply dtr'; deduct;

@[tautology]
lemma distribute_box_conj! : Γ ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_conj⟩

def distribute_multibox_conj' (d : Γ ⊢ □^[n](p ⋏ q)) : Γ ⊢ □^[n]p ⋏ □^[n]q := by
  have dp : ∅ ⊢ □^[n](p ⋏ q) ⟶ □^[n]p := multibox_imp' (conj₁);
  have dq : ∅ ⊢ □^[n](p ⋏ q) ⟶ □^[n]q := multibox_imp' (conj₂);
  have : Γ ⊢ □^[n]p := by simpa using dp ⨀ d;
  have : Γ ⊢ □^[n]q := by simpa using dq ⨀ d;
  exact conj₃' (by assumption) (by assumption);

lemma distribute_multibox_conj'! (d : Γ ⊢! □^[n](p ⋏ q)) : Γ ⊢! □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_conj' d.some⟩

@[inference]
def collect_box_conj' (d : Γ ⊢ □p ⋏ □q) : Γ ⊢ □(p ⋏ q) := by
  have : ∅ ⊢ □p ⟶ □(q ⟶ (p ⋏ q)) := by deduct
  have : ∅ ⊢ □p ⟶ (□q ⟶ □(p ⋏ q)) := imp_trans' (by assumption) (by deduct);
  simpa using this ⨀ (conj₁' d) ⨀ (conj₂' d)

@[inference]
lemma collect_box_conj'! (d : Γ ⊢! □p ⋏ □q) : Γ ⊢! □(p ⋏ q) := ⟨collect_box_conj' d.some⟩

def collect_multibox_conj' (d : Γ ⊢ □^[n]p ⋏ □^[n]q) : Γ ⊢ □^[n](p ⋏ q) := by
  have : ∅ ⊢ □^[n]p ⟶ □^[n](q ⟶ (p ⋏ q)) := by deduct
  have : ∅ ⊢ □^[n]p ⟶ □^[n]q ⟶ □^[n](p ⋏ q) := imp_trans' (by assumption) (by deduct);
  simpa using this ⨀ (conj₁' d) ⨀ (conj₂' d)

lemma collect_multibox_conj'! (d : Γ ⊢! □^[n]p ⋏ □^[n]q) : Γ ⊢! □^[n](p ⋏ q) := ⟨collect_multibox_conj' d.some⟩

@[tautology]
def collect_box_conj : Γ ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := by apply dtr'; deduct;

@[tautology]
lemma collect_box_conj! : Γ ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_conj⟩

@[tautology]
def box_conj_iff : Γ ⊢ □(p ⋏ q) ⟷ □p ⋏ □q := by deduct

lemma box_conj_iff! : Γ ⊢! □(p ⋏ q) ⟷ □p ⋏ □q := ⟨box_conj_iff⟩

lemma box_list_conj_iff! {Γ : Set F} {Δ : List F} : Γ ⊢! □(Δ.conj) ↔ ∀ p ∈ Δ, Γ ⊢! □p := by
  induction Δ with
  | nil => simp [boxverum!];
  | cons p Δ ih =>
    simp [List.conj];
    constructor;
    . intro h;
      have d := distribute_box_conj'! h;
      constructor;
      . exact conj₁'! d
      . exact ih.mp (conj₂'! d)
    . rintro ⟨h₁, h₂⟩;
      exact collect_box_conj'! $ conj₃'! h₁ (ih.mpr h₂);

lemma box_finset_conj_iff! {Γ : Set F} {Δ : Finset F} : Γ ⊢! □(Δ.conj) ↔ ∀ p ∈ Δ, Γ ⊢! □p := by
  simp [Finset.conj, box_list_conj_iff!];

lemma multibox_list_conj_iff! {Γ : Set F} {Δ : List F} : Γ ⊢! □^[n](Δ.conj) ↔ ∀ p ∈ Δ, Γ ⊢! □^[n]p := by
  induction Δ with
  | nil => simp [multiboxverum!];
  | cons p Δ ih =>
    simp [List.conj];
    constructor;
    . intro h;
      have d := distribute_multibox_conj'! h;
      constructor;
      . exact conj₁'! d
      . exact ih.mp (conj₂'! d)
    . rintro ⟨h₁, h₂⟩;
      exact collect_multibox_conj'! $ conj₃'! h₁ (ih.mpr h₂);

lemma multibox_finset_conj_iff! {Γ : Set F} {Δ : Finset F} : Γ ⊢! □^[n](Δ.conj) ↔ ∀ p ∈ Δ, Γ ⊢! □^[n]p := by
  have : (Γ ⊢! □^[n]Δ.toList.conj) ↔ ∀ p ∈ Δ.toList, Γ ⊢! □^[n]p := multibox_list_conj_iff!;
  simpa [Finset.toList_toFinset];

@[inference]
def collect_box_disj' (d : Γ ⊢ □p ⋎ □q) : Γ ⊢ □(p ⋎ q) := by
  have : Γ ⊢ □p ⟶ □(p ⋎ q) := by deduct;
  have : Γ ⊢ □q ⟶ □(p ⋎ q) := by deduct
  exact disj₃' (by assumption) (by assumption) d;

@[inference]
lemma collect_box_disj'! (d : Γ ⊢! □p ⋎ □q) : Γ ⊢! □(p ⋎ q) := ⟨collect_box_disj' d.some⟩

@[tautology]
def distribute_dia_conj : Γ ⊢ ◇(p ⋏ q) ⟶ (◇p ⋏ ◇q) := by
  simp [duality];
  apply contra₂';
  apply dtr';
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ ~(~(□~p) ⋏ ~(□~q)) := by deduct;
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □~p ⋎ □~q := disj_dn_elim' $ neg_conj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) := collect_box_disj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) ⟶ □(~(p ⋏ q)) := box_distribute_nec' disj_neg;
  exact modus_ponens₂' (by assumption) (by assumption);

@[inference]
def distribute_dia_conj' (d : Γ ⊢ ◇(p ⋏ q)) : Γ ⊢ ◇p ⋏ ◇q := distribute_dia_conj ⨀ d

@[tautology]
def distribute_multidia_conj : Γ ⊢ ◇^[n](p ⋏ q) ⟶ (◇^[n]p ⋏ ◇^[n]q) := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih =>
    have : ∅ ⊢ ~(◇^[n]p ⋏ ◇^[n]q) ⟶ ~(◇^[n](p ⋏ q)) := contra₀' ih;
    have : ∅ ⊢ □~(◇^[n]p ⋏ ◇^[n]q) ⟶ □~(◇^[n](p ⋏ q)) := box_imp' this;
    have : ∅ ⊢ ~(□~(◇^[n](p ⋏ q))) ⟶ ~(□~(◇^[n]p ⋏ ◇^[n]q)) := contra₀' this;
    have : ∅ ⊢ ◇(◇^[n](p ⋏ q)) ⟶ ◇(◇^[n]p ⋏ ◇^[n]q) := by simpa [duality] using this;
    have : ∅ ⊢ ◇(◇^[n]p ⋏ ◇^[n]q) ⟶ (◇◇^[n]p ⋏ ◇◇^[n]q) := distribute_dia_conj
    have : ∅ ⊢ ◇(◇^[n](p ⋏ q)) ⟶ (◇^[(n + 1)]p ⋏ ◇^[(n + 1)]q) := imp_trans' (by assumption) (by simpa using this);
    simpa using weakening' (by simp) this;

@[inference]
def distribute_multidia_conj' (d : Γ ⊢ ◇^[n](p ⋏ q)) : Γ ⊢ ◇^[n]p ⋏ ◇^[n]q := distribute_multidia_conj ⨀ d

@[inference]
lemma distribute_multidia_conj'! (d : Γ ⊢! ◇^[n](p ⋏ q)) : Γ ⊢! ◇^[n]p ⋏ ◇^[n]q := ⟨distribute_multidia_conj' d.some⟩

lemma distribute_multidia_list_conj'! {Γ : Set F} {Δ : List F} (d : Γ ⊢! ◇^[n]Δ.conj) : Γ ⊢! (Δ.multidia n).conj := by
  induction Δ with
  | nil => simp_all [verum!];
  | cons p Δ ih =>
    simp_all [List.conj];
    have d := distribute_multidia_conj'! d;
    exact conj₃'! (conj₁'! d) (by apply ih; apply conj₂'! d);

lemma distribute_multidia_finset_conj'! {Γ : Set F} {Δ : Finset F} (d : Γ ⊢! ◇^[n]Δ.conj) : Γ ⊢! (Δ.multidia n).conj := by
  apply finset_conj_iff!.mpr;
  intro p hp;
  exact list_conj_iff!.mp (distribute_multidia_list_conj'! d) p (by simpa [Finset.multidia, List.multidia] using hp);

lemma distribute_dia_finset_conj'! {Δ : Finset F} (d : Γ ⊢! ◇(Δ.conj)) : Γ ⊢! Δ.dia.conj := by
  have : (Γ ⊢! ◇^[1]Δ.conj) → (Γ ⊢! (Δ.multidia 1).conj) := distribute_multidia_finset_conj'!;
  simp_all [Finset.multidia, Finset.dia];

lemma distribute_multidia_finset_conj! {n : ℕ} {Γ : Set F} {Δ : Finset F} : Γ ⊢! ◇^[n]Δ.conj ⟶ (Δ.multidia n).conj := by
  apply dtr'!;
  apply distribute_multidia_finset_conj'!;
  apply axm! (by simp);

@[tautology]
def collect_dia_disj : Γ ⊢ ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := by
  simp [duality'];
  apply contra₁';
  apply dtr';
  apply conj_neg';
  apply conj_dn_intro';
  have : (insert (□~(p ⋎ q)) Γ) ⊢ □~(p ⋎ q) ⟶ □(~p ⋏ ~q) := by deduct
  have : (insert (□~(p ⋎ q)) Γ) ⊢ □(~p ⋏ ~q) := this ⨀ (by deduct)
  have : (insert (□~(p ⋎ q)) Γ) ⊢ □~p ⋏ □~q := by deduct
  exact conj₃' (conj₁' (by deduct)) (conj₂' (by deduct));

@[inference]
def collect_dia_disj' (d : Γ ⊢ ◇p ⋎ ◇q) : Γ ⊢ ◇(p ⋎ q) := collect_dia_disj ⨀ d

variable [HasAxiomFour Bew]

@[tautology]
def axiomFour : Γ ⊢  □p ⟶ □□p := HasAxiomFour.Four Γ p

@[tautology]
lemma axiomFour! : Γ ⊢! □p ⟶ □□p := ⟨Hilbert.axiomFour⟩

@[inference]
def axiomFour' (d₁ : Γ ⊢ □p) : Γ ⊢ □□p := (Hilbert.axiomFour) ⨀ d₁

@[inference]
lemma axiomFour'! (d : Γ ⊢! □p) : Γ ⊢! □□p := ⟨axiomFour' d.some⟩


variable [HasAxiomT Bew]

@[tautology]
def axiomT :  Γ ⊢ □p ⟶ p := HasAxiomT.T Γ p

@[tautology]
lemma axiomT! : Γ ⊢! □p ⟶ p := ⟨Hilbert.axiomT⟩

@[inference]
def axiomT' (d₁ : Γ ⊢ □p) : Γ ⊢ p := (Hilbert.axiomT) ⨀ d₁

@[inference]
lemma axiomT'! (d : Γ ⊢! □p) : Γ ⊢! p := ⟨axiomT' d.some⟩

end

section Logics

variable {F : Type u} [StandardModalLogicalConnective F] [NegDefinition F] [DecidableEq F] (Bew : Set F → F → Type u)

class K extends Hilbert.Classical Bew, HasNecessitation Bew, HasAxiomK Bew

class KD extends Hilbert.K Bew, HasAxiomD Bew

class K4 extends Hilbert.K Bew, HasAxiomFour Bew

class S4 extends Hilbert.K Bew, HasAxiomT Bew, HasAxiomFour Bew

class S5 extends Hilbert.K Bew, HasAxiomT Bew, HasAxiomFive Bew

class S4Dot2 extends Hilbert.S4 Bew, HasAxiomDot2 Bew

class S4Dot3 extends Hilbert.S4 Bew, HasAxiomDot3 Bew

class S4Grz extends Hilbert.S4 Bew, HasAxiomGrz Bew

class GL extends Hilbert.K Bew, HasAxiomL Bew

end Logics

end LO.Hilbert
