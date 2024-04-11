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

variable [ModalDuality F] [ModalInj F]
variable [HasDT Bew] [Minimal Bew] [Classical Bew]
variable [HasNecessitation Bew] [HasBoxedNecessitation Bew]
variable [HasAxiomK Bew]
variable {Γ Δ : Set F} {p q r : F} {n m : ℕ}

open HasNecessitation
open HasBoxedNecessitation
open HasAxiomK

attribute [aesop 2 (rule_sets := [Deduction]) safe] ModalDuality.dia_to_box

@[inference]
def necessitation (d : ∅ ⊢ p) : Γ ⊢ □p := HasNecessitation.necessitation d

@[inference]
def necessitation! (d : ∅ ⊢! p) : Γ ⊢! □p := ⟨necessitation d.some⟩

@[inference]
def multi_necessitation (d : (∅ : Set F) ⊢ p) : Γ ⊢ □[n]p := by induction n generalizing Γ <;> deduct

@[inference]
def multi_necessitation! (d : ∅ ⊢! p) : Γ ⊢! □[n]p := ⟨multi_necessitation d.some⟩

@[inference]
def boxed_necessitation (d : Γ ⊢ p) : Γ.box ⊢ □p := HasBoxedNecessitation.boxed_necessitation d

@[inference]
def boxed_necessitation! (d : Γ ⊢! p) : Γ.box ⊢! □p := ⟨boxed_necessitation d.some⟩

@[inference]
def preboxed_necessitation (d : Γ.prebox ⊢ p) : Γ ⊢ □p := weakening' Set.prebox_box_subset $ boxed_necessitation d

@[inference]
def preboxed_necessitation! (d : Γ.prebox ⊢! p) : Γ ⊢! □p := ⟨preboxed_necessitation d.some⟩

@[tautology]
def axiomK : Γ ⊢ (AxiomK p q) := by apply HasAxiomK.K

@[tautology]
lemma axiomK! : Γ ⊢! (AxiomK p q) := ⟨Hilbert.axiomK⟩

@[inference]
def box_distribute' (d₁ : Γ ⊢ (□(p ⟶ q))) : Γ ⊢ □p ⟶ □q := axiomK ⨀ d₁

@[inference]
lemma box_distribute'! (d : Γ ⊢! □(p ⟶ q)) : Γ ⊢! □p ⟶ □q := ⟨box_distribute' d.some⟩

@[inference]
def box_distribute_nec' (d₁ : ∅ ⊢ p ⟶ q) : Γ ⊢ □p ⟶ □q := box_distribute' $ necessitation d₁

@[inference]
lemma box_distribute_nec'! (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □p ⟶ □q := ⟨box_distribute_nec' d.some⟩

@[tautology]
def multiaxiomK : Γ ⊢ □[n](p ⟶ q) ⟶ (□[n]p ⟶ □[n]q) := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih =>
    have : Γ ⊢ □□[n](p ⟶ q) ⟶ □(□[n]p ⟶ □[n]q) := by deduct;
    have : Γ ⊢ □(□[n]p ⟶ □[n]q) ⟶ □□[n]p ⟶ □□[n]q := by deduct;
    deduct;

@[inference]
def multibox_distribute' (d : Γ ⊢ □[n](p ⟶ q)) :  Γ ⊢ □[n]p ⟶ □[n]q := multiaxiomK ⨀ d

@[inference]
lemma multibox_distribute'! (d : Γ ⊢! □[n](p ⟶ q)) : Γ ⊢! □[n]p ⟶ □[n]q := ⟨multibox_distribute' d.some⟩

@[tautology]
def multibox_distribute_nec' (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □[n]p ⟶ □[n]q := multibox_distribute' $ multi_necessitation d

@[inference]
lemma multibox_distribute_nec'! (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □[n]p ⟶ □[n]q := ⟨multibox_distribute_nec' d.some⟩

@[inference]
def axiomK' (d₁ : Γ ⊢ (□(p ⟶ q))) (d₂ : Γ ⊢ □p) : Γ ⊢ □q := axiomK ⨀ d₁ ⨀ d₂

@[inference]
lemma axiomK'! (d₁ : Γ ⊢! (□(p ⟶ q))) (d₂ : Γ ⊢! □p) : Γ ⊢! □q := ⟨axiomK' d₁.some d₂.some⟩

@[tautology]
def box_distribute_iff : Γ ⊢ □(p ⟷ q) ⟶ (□p ⟷ □q) := by
  have : (Set.box {p ⟷ q}) ⊢ (□p ⟶ □q) := box_distribute' $ boxed_necessitation $ iff_mp' $ axm (by simp);
  have : (Set.box {p ⟷ q}) ⊢ (□q ⟶ □p) := box_distribute' $ boxed_necessitation $ iff_mpr' $ axm (by simp);
  have : (Set.box {p ⟷ q}) ⊢ (□p ⟷ □q) := by deduct;
  have : ({□(p ⟷ q)}) ⊢ (□p ⟷ □q) := by simpa [Set.box] using this;
  have : ∅ ⊢ (□(p ⟷ q) ⟶ (□p ⟷ □q)) := dtr (by deduct);
  deduct;

@[inference]
def box_distribute_iff' (h : Γ ⊢ □(p ⟷ q)) : Γ ⊢ (□p ⟷ □q) := box_distribute_iff ⨀ h

@[inference]
def box_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (□p ⟷ □q) := box_distribute_iff' $ necessitation h

@[inference]
lemma box_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (□p ⟷ □q) := ⟨box_iff' d.some⟩

@[inference]
def dia_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (◇p ⟷ ◇q) := by
  simp only [ModalDuality.dia_to_box];
  apply neg_iff';
  apply box_iff';
  apply neg_iff';
  assumption

@[inference]
lemma dia_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (◇p ⟷ ◇q) := ⟨dia_iff' d.some⟩

@[inference]
def multibox_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ □[n]p ⟷ □[n]q := by induction n generalizing Γ <;> deduct

@[inference]
lemma multibox_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! □[n]p ⟷ □[n]q := ⟨multibox_iff' d.some⟩

@[inference]
def multidia_iff' (h : ∅ ⊢ p ⟷ q) : Γ ⊢ ◇[n]p ⟷ ◇[n]q := by induction n generalizing Γ <;> deduct

@[inference]
lemma multidia_iff'! (d : ∅ ⊢! p ⟷ q) : Γ ⊢! ◇[n]p ⟷ ◇[n]q := ⟨multidia_iff' d.some⟩

@[tautology]
def box_duality : Γ ⊢ □p ⟷ ~(◇~p) := by
  simp [ModalDuality.dia_to_box];
  have : Γ ⊢ □p ⟷ (□~~p) := by deduct;
  have : Γ ⊢ ((□~~p) ⟷ ~~(□~~p)) := by deduct;
  deduct;

@[tautology]
lemma box_duality! : Γ ⊢! □p ⟷ ~(◇~p) := ⟨box_duality⟩

@[tautology]
def dia_duality : Γ ⊢ ◇p ⟷ ~(□~p) := by
  simp only [ModalDuality.dia_to_box];
  apply neg_iff';
  apply iff_id;

@[tautology]
lemma dia_duality! : Γ ⊢! ◇p ⟷ ~(□~p) := ⟨dia_duality⟩

@[tautology]
def multibox_duality : Γ ⊢ □[n]p ⟷ ~(◇[n](~p)) := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih =>
    simp [ModalDuality.dia_to_box];
    exact iff_trans'
      (show Γ ⊢ □□[n]p ⟷ ~~(□~~(□[n]p)) by
        have : Γ ⊢ □(□[n]p) ⟷ ~(◇~(□[n]p)) := box_duality
        simpa [ModalDuality.dia_to_box];
      )
      (by
        have : ∅ ⊢ ~~(□[n]p) ⟷ □[n]p := by deduct;
        have : ∅ ⊢ (□[n]p ⟷ ~(◇[n](~p))) := by deduct;
        have : ∅ ⊢ ~~(□[n]p) ⟷ ~(◇[n](~p)) := iff_trans' (by assumption) (by assumption);
        have : ∅ ⊢ □~~(□[n]p) ⟷ □~(◇[n](~p)) := box_iff' (by assumption);
        exact weakening' (by simp) $ dn_iff' this;
      )

@[tautology]
lemma multibox_duality! {n Γ p} : Γ ⊢! □[n]p ⟷ ~(◇[n](~p)) := ⟨multibox_duality⟩

@[tautology]
def multidia_duality : Γ ⊢ ◇[n]p ⟷ ~(□[n](~p)) := by
  induction n generalizing Γ with
  | zero => apply dn;
  | succ n ih =>
    simp [ModalDuality.dia_to_box];
    apply neg_iff';
    apply box_iff';
    exact iff_trans' (neg_iff' $ ih) (by deduct);

@[tautology]
lemma multidia_duality! : Γ ⊢! ◇[n]p ⟷ ~(□[n](~p)) := ⟨multidia_duality⟩

@[tautology]
def boxverum : Γ ⊢ □⊤ := by deduct;

@[tautology]
lemma boxverum! : Γ ⊢! □⊤ := ⟨boxverum⟩

@[tautology]
def equiv_dianeg_negbox : Γ ⊢ ◇~p ⟷ ~(□p) := by
  simp only [ModalDuality.dia_to_box];
  apply neg_iff';
  apply box_iff';
  apply iff_symm';
  apply equiv_dn;

@[tautology]
lemma equiv_dianeg_negbox! : Γ ⊢! ◇~p ⟷ ~(□p) := ⟨equiv_dianeg_negbox⟩

@[inference]
def box_imp' (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □p ⟶ □q := by deduct

@[inference]
def distribute_box_conj' (d : Γ ⊢ □(p ⋏ q)) : Γ ⊢ □p ⋏ □q := by
  have dp : ∅ ⊢ □(p ⋏ q) ⟶ □p := by deduct;
  have dq : ∅ ⊢ □(p ⋏ q) ⟶ □q := by deduct;
  have : Γ ⊢ □p := by simpa using dp ⨀ d;
  have : Γ ⊢ □q := by simpa using dq ⨀ d;
  deduct;

@[inference]
lemma distribute_box_conj'! (d : Γ ⊢! □(p ⋏ q)) : Γ ⊢! □p ⋏ □q := ⟨distribute_box_conj' d.some⟩

@[tautology]
def distribute_box_conj : Γ ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := by apply dtr; deduct;

@[tautology]
lemma distribute_box_conj! : Γ ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_conj⟩

@[inference]
def collect_box_conj' (d : Γ ⊢ □p ⋏ □q) : Γ ⊢ □(p ⋏ q) := by
  have : ∅ ⊢ □p ⟶ □(q ⟶ (p ⋏ q)) := by deduct
  have : ∅ ⊢ □p ⟶ (□q ⟶ □(p ⋏ q)) := imp_trans' (by assumption) (by deduct);
  simpa using this ⨀ (conj₁' d) ⨀ (conj₂' d)

@[inference]
lemma collect_box_conj'! (d : Γ ⊢! □p ⋏ □q) : Γ ⊢! □(p ⋏ q) := ⟨collect_box_conj' d.some⟩

@[tautology]
def collect_box_conj : Γ ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := by apply dtr; deduct;

@[tautology]
lemma collect_box_conj! : Γ ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_conj⟩

@[tautology]
def box_conj_iff : Γ ⊢ □(p ⋏ q) ⟷ □p ⋏ □q := by deduct

def pick_box_finset_conj {Γ : Set F} {Δ : Finset F} (h : Γ ⊢ □(Δ.conj)) : ∀ p ∈ Δ, Γ ⊢ □p := by sorry;

lemma pick_box_finset_conj! {Γ : Set F} {Δ : Finset F} (h : Γ ⊢! □(Δ.conj)) : ∀ p ∈ Δ, Γ ⊢! □p := by
  intros p hp;
  have : Γ ⊢ □p := pick_box_finset_conj h.some p hp;
  exact ⟨this⟩

def pick_multibox_finset_conj {Γ : Set F} {Δ : Finset F} (h : Γ ⊢ □[n]Δ.conj) : ∀ p ∈ Δ, Γ ⊢ □[n]p := by sorry;

lemma pick_multibox_finset_conj! {Γ : Set F} {Δ : Finset F} (h : Γ ⊢! □[n]Δ.conj) : ∀ p ∈ Δ, Γ ⊢! □[n]p := by
  intros p hp;
  have : Γ ⊢ □[n]p := pick_multibox_finset_conj h.some p hp;
  exact ⟨this⟩

def collect_box_finset_conj {Γ : Set F} {Δ : Finset F} (h : ∀ p ∈ Δ, Γ ⊢ □p) : Γ ⊢ □(Δ.conj) := by sorry;

lemma collect_box_finset_conj! {Γ : Set F} {Δ : Finset F} (h : ∀ p ∈ Δ, Γ ⊢! □p) : Γ ⊢! □(Δ.conj) := by
  exact ⟨collect_box_finset_conj (by intro p hp; exact h p hp |>.some)⟩

def collect_multibox_finset_conj {Γ : Set F} {Δ : Finset F} (h : ∀ p ∈ Δ, Γ ⊢ □[n]p) : Γ ⊢ □[n]Δ.conj := by sorry;

lemma collect_multibox_finset_conj! {Γ : Set F} {Δ : Finset F} (h : ∀ p ∈ Δ, Γ ⊢! □[n]p) : Γ ⊢! □[n]Δ.conj := by
  exact ⟨collect_multibox_finset_conj (by intro p hp; exact h p hp |>.some)⟩

@[inference]
def collect_box_disj' (d : Γ ⊢ □p ⋎ □q) : Γ ⊢ □(p ⋎ q) := by
  have : Γ ⊢ □p ⟶ □(p ⋎ q) := by deduct;
  have : Γ ⊢ □q ⟶ □(p ⋎ q) := by deduct
  exact disj₃' (by assumption) (by assumption) d;

@[inference]
lemma collect_box_disj'! (d : Γ ⊢! □p ⋎ □q) : Γ ⊢! □(p ⋎ q) := ⟨collect_box_disj' d.some⟩

@[tautology]
def distribute_dia_conj : Γ ⊢ ◇(p ⋏ q) ⟶ (◇p ⋏ ◇q) := by
  simp [ModalDuality.dia_to_box];
  apply contra₂';
  apply dtr;
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ ~(~(□~p) ⋏ ~(□~q)) := by deduct;
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □~p ⋎ □~q := disj_dn_elim' $ neg_conj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) := collect_box_disj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) ⟶ □(~(p ⋏ q)) := box_distribute_nec' disj_neg;
  exact modus_ponens₂ (by assumption) (by assumption);

@[inference]
def distribute_dia_conj' (d : Γ ⊢ ◇(p ⋏ q)) : Γ ⊢ ◇p ⋏ ◇q := distribute_dia_conj ⨀ d

def distribute_multidia_conj' (d : Γ ⊢ ◇[n](p ⋏ q)) : Γ ⊢ ◇[n]p ⋏ ◇[n]q := by
  induction n generalizing Γ with
  | zero => deduct
  | succ n ih => sorry; -- simp_all only [Dia.multidia];

lemma distribute_multidia_finset_conj'! {Γ : Set F} {Δ : Finset F} (d : Γ ⊢! ◇[n]Δ.conj) : Γ ⊢! (Δ.multidia n).conj := by
  sorry;

lemma distribute_multidia_finset_conj! {n : ℕ} {Γ : Set F} {Δ : Finset F} : Γ ⊢! ◇[n]Δ.conj ⟶ (Δ.multidia n).conj := by
  apply dtr!;
  apply distribute_multidia_finset_conj'!;
  apply axm! (by simp);

def collect_dia_disj : Γ ⊢ ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := by
  simp [ModalDuality.dia_to_box];
  apply contra₁';
  apply dtr;
  sorry;

def collect_dia_disj' (d : Γ ⊢ ◇p ⋎ ◇q) : Γ ⊢ ◇(p ⋎ q) := collect_dia_disj ⨀ d

variable [HasAxiom4 Bew]

@[tautology]
def axiom4 : Γ ⊢ (Axiom4 p) := HasAxiom4.A4 Γ p

@[tautology]
lemma axiom4! : Γ ⊢! (Axiom4 p) := ⟨Hilbert.axiom4⟩

@[inference]
def axiom4' (d₁ : Γ ⊢ □p) : Γ ⊢ □□p := (Hilbert.axiom4) ⨀ d₁

@[inference]
lemma axiom4'! (d : Γ ⊢! □p) : Γ ⊢! □□p := ⟨axiom4' d.some⟩


variable [HasAxiomT Bew]

@[tautology]
def axiomT :  Γ ⊢ (AxiomT p) := HasAxiomT.T Γ p

@[tautology]
lemma axiomT! : Γ ⊢! (AxiomT p) := ⟨Hilbert.axiomT⟩

@[inference]
def axiomT' (d₁ : Γ ⊢ □p) : Γ ⊢ p := (Hilbert.axiomT) ⨀ d₁

@[inference]
lemma axiomT'! (d : Γ ⊢! □p) : Γ ⊢! p := ⟨axiomT' d.some⟩

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
