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
variable [HasDT Bew] [Minimal Bew] [HasNecessitation Bew] [HasAxiomK Bew]
variable [Classical Bew]

open HasNecessitation

def necessitation {Γ : Set F} {p} (d : (∅ : Set F) ⊢ p) : Γ ⊢ □p := HasNecessitation.necessitation d

def necessitation! {Γ : Set F} {p} (d : (∅ : Set F) ⊢! p) : Γ ⊢! □p := ⟨necessitation d.some⟩

def multi_necessitation {p} {n : ℕ} (d : (∅ : Set F) ⊢ p) : Γ ⊢ □[n]p := by
  induction n generalizing Γ with
  | zero => simp [-NegDefinition.neg]; exact weakening' (by simp) d;
  | succ n ih => exact necessitation ih;

def multi_necessitation! {p} {n : ℕ} (d : (∅ : Set F) ⊢! p) : Γ ⊢! □[n]p := ⟨multi_necessitation d.some⟩

open HasBoxedNecessitation

variable [HasBoxedNecessitation Bew]

def boxed_necessitation {Γ : Set F} {p} (d : Γ ⊢ p) : Γ.box ⊢ □p := HasBoxedNecessitation.boxed_necessitation d

def boxed_necessitation! {Γ : Set F} {p} (d : Γ ⊢! p) : Γ.box ⊢! □p := ⟨boxed_necessitation d.some⟩

def preboxed_necessitation {Γ : Set F} {p} (d : Γ.prebox ⊢ p) : Γ ⊢ □p := by
  exact Deduction.weakening' Set.prebox_box_subset $ boxed_necessitation d;

def preboxed_necessitation! {Γ : Set F} {p} (d : Γ.prebox ⊢! p) : Γ ⊢! □p := ⟨preboxed_necessitation d.some⟩

open HasAxiomK

def axiomK {Γ p q} : Γ ⊢ (AxiomK p q) := HasAxiomK.K Γ p q

def box_distribute' {Γ : Set F} {p q} (d₁ : Γ ⊢ (□(p ⟶ q))) : Γ ⊢ □p ⟶ □q := Hilbert.axiomK ⨀ d₁

lemma box_distribute'! {Γ : Set F} {p q : F} (d : Γ ⊢! □(p ⟶ q)) : Γ ⊢! □p ⟶ □q := ⟨box_distribute' d.some⟩

def box_distribute_nec' {Γ : Set F} {p q} (d₁ : ∅ ⊢ p ⟶ q) : Γ ⊢ □p ⟶ □q := box_distribute' $ necessitation d₁

lemma box_distribute_nec'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □p ⟶ □q := ⟨box_distribute_nec' d.some⟩

def multiaxiomK {Γ : Set F} {p q} : Γ ⊢ □[n](p ⟶ q) ⟶ (□[n]p ⟶ □[n]q) := by
  induction n generalizing Γ with
  | zero => simp; apply imp_id;
  | succ n ih =>
    have : Γ ⊢ □□[n](p ⟶ q) ⟶ □(□[n]p ⟶ □[n]q) := box_distribute' $ necessitation ih;
    have : Γ ⊢ □(□[n]p ⟶ □[n]q) ⟶ □□[n]p ⟶ □□[n]q := axiomK;
    exact imp_trans' (by assumption) (by assumption);

def multibox_distribute' {Γ : Set F} {p q} (d : Γ ⊢ □[n](p ⟶ q)) :  Γ ⊢ □[n]p ⟶ □[n]q := multiaxiomK ⨀ d

lemma multibox_distribute'! {Γ : Set F} {p q : F} (d : Γ ⊢! □[n](p ⟶ q)) : Γ ⊢! □[n]p ⟶ □[n]q := ⟨multibox_distribute' d.some⟩

def multibox_distribute_nec' {Γ : Set F} {p q} (d : ∅ ⊢ p ⟶ q) : Γ ⊢ □[n]p ⟶ □[n]q := multibox_distribute' $ multi_necessitation d

lemma multibox_distribute_nec'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟶ q) : Γ ⊢! □[n]p ⟶ □[n]q := ⟨multibox_distribute_nec' d.some⟩

def axiomK' {Γ : Set F} {p q} (d₁ : Γ ⊢ (□(p ⟶ q))) (d₂ : Γ ⊢ □p) : Γ ⊢ □q := (Hilbert.axiomK ⨀ d₁) ⨀ d₂

lemma axiomK! (Γ : Set F) (p q) : Γ ⊢! (AxiomK p q) := ⟨Hilbert.axiomK⟩

lemma axiomK'! {Γ : Set F} {p q} (d₁ : Γ ⊢! (□(p ⟶ q))) (d₂ : Γ ⊢! □p) : Γ ⊢! □q := ⟨axiomK' d₁.some d₂.some⟩

def box_distribute_iff (Γ : Set F) (p q : F) : Γ ⊢ □(p ⟷ q) ⟶ (□p ⟷ □q) := by
  have : (Set.box {p ⟷ q}) ⊢ (□p ⟶ □q) := box_distribute' $ boxed_necessitation $ iff_mp' $ axm (by simp);
  have : (Set.box {p ⟷ q}) ⊢ (□q ⟶ □p) := box_distribute' $ boxed_necessitation $ iff_mpr' $ axm (by simp);
  have : (Set.box {p ⟷ q}) ⊢ (□p ⟷ □q) := iff_intro (by assumption) (by assumption);
  have : ({□(p ⟷ q)}) ⊢ (□p ⟷ □q) := by simpa [Set.box] using this;
  have : ∅ ⊢ (□(p ⟷ q) ⟶ (□p ⟷ □q)) := dtr (by simpa);
  exact weakening' (by simp) this

def box_distribute_iff' {Γ : Set F} {p q : F} (h : Γ ⊢ □(p ⟷ q)) : Γ ⊢ (□p ⟷ □q) := by
  exact (box_distribute_iff Γ p q) ⨀ h

def box_iff' {Γ : Set F} {p q : F} (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (□p ⟷ □q) := box_distribute_iff' $ necessitation h

lemma box_iff'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (□p ⟷ □q) := ⟨box_iff' d.some⟩

def dia_iff' {Γ : Set F} {p q : F} (h : ∅ ⊢ p ⟷ q) : Γ ⊢ (◇p ⟷ ◇q) := by
  simp only [ModalDuality.dia_to_box];
  apply neg_iff';
  apply box_iff';
  apply neg_iff';
  assumption

lemma dia_iff'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟷ q) : Γ ⊢! (◇p ⟷ ◇q) := ⟨dia_iff' d.some⟩

def multibox_iff' {Γ : Set F} {p q : F} (h : ∅ ⊢ p ⟷ q) : Γ ⊢ □[n]p ⟷ □[n]q := by
  induction n  generalizing Γ with
  | zero => exact weakening' (by simp) h;
  | succ n ih => exact box_iff' $ ih;

lemma multibox_iff'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟷ q) : Γ ⊢! □[n]p ⟷ □[n]q := ⟨multibox_iff' d.some⟩

def multidia_iff' {Γ : Set F} {p q : F} (h : ∅ ⊢ p ⟷ q) : Γ ⊢ ◇[n]p ⟷ ◇[n]q := by
  induction n  generalizing Γ with
  | zero => exact weakening' (by simp) h;
  | succ n ih => exact dia_iff' $ ih;

lemma multidia_iff'! {Γ : Set F} {p q : F} (d : ∅ ⊢! p ⟷ q) : Γ ⊢! ◇[n]p ⟷ ◇[n]q := ⟨multidia_iff' d.some⟩

def box_duality (Γ : Set F) (p) : Γ ⊢ □p ⟷ ~(◇~p) := by
  simp [-NegDefinition.neg];
  have : Γ ⊢ □p ⟷ (□~~p) := box_iff' $ dn _ _;
  have : Γ ⊢ ((□~~p) ⟷ ~~(□~~p)) := dn _ _;
  exact iff_trans' (by assumption) (by assumption);

lemma box_duality! (Γ : Set F) (p) : Γ ⊢! □p ⟷ ~(◇~p) := ⟨box_duality Γ p⟩

def dia_duality (Γ : Set F) (p) : Γ ⊢ ◇p ⟷ ~(□~p) := by
  simp only [ModalDuality.dia_to_box];
  apply neg_iff';
  apply iff_id;

lemma dia_duality! (Γ : Set F) (p) : Γ ⊢! ◇p ⟷ ~(□~p) := ⟨dia_duality Γ p⟩

def multibox_duality (n : ℕ) (Γ : Set F) (p) : Γ ⊢ □[n]p ⟷ ~(◇[n](~p)) := by
  induction n generalizing Γ with
  | zero => simp [-NegDefinition.neg]; apply dn;
  | succ n ih =>
    simp [-NegDefinition.neg];
    exact iff_trans'
      (show Γ ⊢ □□[n]p ⟷ ~~(□~~(□[n]p)) by simpa [ModalDuality.dia_to_box] using box_duality Γ (□[n]p))
      (by
        have : ∅ ⊢ ~~(□[n]p) ⟷ □[n]p := iff_symm' $ dn _ _;
        have : ∅ ⊢ (□[n]p ⟷ ~(◇[n](~p))) := @ih ∅;
        have : ∅ ⊢ ~~(□[n]p) ⟷ ~(◇[n](~p)) := iff_trans' (by assumption) (by assumption);
        have : ∅ ⊢ □~~(□[n]p) ⟷ □~(◇[n](~p)) := box_iff' (by assumption);
        exact weakening' (by simp) $ dn_iff' this;
      )

lemma multibox_duality! {n Γ p} : Γ ⊢! □[n]p ⟷ ~(◇[n](~p)) := ⟨multibox_duality n Γ p⟩

def multidia_duality (n : ℕ) (Γ : Set F) (p) : Γ ⊢ ◇[n]p ⟷ ~(□[n](~p)) := by
  induction n generalizing Γ with
  | zero => simp [-NegDefinition.neg]; apply dn;
  | succ n ih =>
    simp [-NegDefinition.neg];
    apply neg_iff';
    apply box_iff';
    have : ∅ ⊢ (~(◇[n]p) ⟷ ~~(□[n](~p))):= neg_iff' $ ih _;
    have : ∅ ⊢ (~~(□[n](~p)) ⟷ □[n](~p)) := iff_symm' $ dn _ _
    exact iff_trans' (by assumption) (by assumption);

lemma multidia_duality! {n Γ p} : Γ ⊢! ◇[n]p ⟷ ~(□[n](~p)) := ⟨multidia_duality n Γ p⟩

def boxverum (Γ : Set F) : Γ ⊢ □⊤ := necessitation (verum _)

lemma boxverum! (Γ : Set F) : Γ ⊢! □⊤ := ⟨boxverum Γ⟩

def equiv_dianeg_negbox (Γ p) : Γ ⊢ ◇~p ⟷ ~(□p) := by
  simp only [ModalDuality.dia_to_box];
  apply Hilbert.neg_iff';
  apply box_iff';
  apply iff_symm';
  apply equiv_dn;

lemma equiv_dianeg_negbox! (Γ p) : Γ ⊢! ◇~p ⟷ ~(□p) := ⟨equiv_dianeg_negbox Γ p⟩

def box_imp' {Γ : Set F} {p q : F} (d : ∅ ⊢ p ⟶ q) : Γ ⊢ (□p ⟶ □q) := by
  have d₁ : ∅ ⊢ □(p ⟶ q) ⟶ (□p ⟶ □q) := by apply axiomK;
  have d₂ : ∅ ⊢ □(p ⟶ q) := necessitation d;
  exact weakening' (by simp) $ modus_ponens' d₁ d₂;

def distribute_box_conj' (d : Γ ⊢ □(p ⋏ q)) : Γ ⊢ □p ⋏ □q := by
  have dp : ∅ ⊢ □(p ⋏ q) ⟶ □p := box_distribute_nec' $ by apply conj₁;
  have dq : ∅ ⊢ □(p ⋏ q) ⟶ □q := box_distribute_nec' $ by apply conj₂;
  have : Γ ⊢ □p := by simpa using dp ⨀ d;
  have : Γ ⊢ □q := by simpa using dq ⨀ d;
  exact conj₃' (by assumption) (by assumption);

lemma distribute_box_conj'! (d : Γ ⊢! □(p ⋏ q)) : Γ ⊢! □p ⋏ □q := ⟨distribute_box_conj' d.some⟩

def distribute_box_conj : Γ ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := by
  apply dtr;
  apply distribute_box_conj' $ axm (by simp)

lemma distribute_box_conj! : Γ ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_conj⟩

def collect_box_conj' {Γ : Set F} {p q : F} (d : Γ ⊢ □p ⋏ □q) : Γ ⊢ □(p ⋏ q) := by
  have : ∅ ⊢ p ⟶ (q ⟶ (p ⋏ q)) := by apply conj₃;
  have : ∅ ⊢ □p ⟶ □(q ⟶ (p ⋏ q)) := box_imp' (by assumption)
  have : ∅ ⊢ □p ⟶ (□q ⟶ □(p ⋏ q)) := imp_trans' (by assumption) (by apply axiomK);
  simpa using modus_ponens (modus_ponens this (conj₁' d)) (conj₂' d)

lemma collect_box_conj'! {Γ : Set F} {p q : F} (d : Γ ⊢! □p ⋏ □q) : Γ ⊢! □(p ⋏ q) := ⟨collect_box_conj' d.some⟩

def collect_box_conj {Γ : Set F} {p q : F} : Γ ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := by
  apply dtr;
  apply collect_box_conj' $ axm (by simp)

lemma collect_box_conj! {Γ : Set F} {p q : F} : Γ ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_conj⟩

def box_conj_iff {Γ : Set F} {p q : F} : Γ ⊢ □(p ⋏ q) ⟷ □p ⋏ □q := by
  apply iff_intro;
  . apply distribute_box_conj;
  . apply collect_box_conj;

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

def collect_box_disj' {Γ : Set F} {p q : F} (d : Γ ⊢ □p ⋎ □q) : Γ ⊢ □(p ⋎ q) := by
  have : Γ ⊢ □p ⟶ □(p ⋎ q) := box_imp' (by apply disj₁);
  have : Γ ⊢ □q ⟶ □(p ⋎ q) := box_imp' (by apply disj₂);
  exact disj₃' (by assumption) (by assumption) d;

lemma collect_box_disj'! {Γ : Set F} {p q : F} (d : Γ ⊢! □p ⋎ □q) : Γ ⊢! □(p ⋎ q) := ⟨collect_box_disj' d.some⟩

def distribute_dia_conj {Γ : Set F} {p q : F} : Γ ⊢ ◇(p ⋏ q) ⟶ (◇p ⋏ ◇q) := by
  simp [-NegDefinition.neg];
  apply contra₂';
  apply dtr;
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ ~(~(□~p) ⋏ ~(□~q)) := axm (by simp)
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □~p ⋎ □~q := disj_dn_elim' $ neg_conj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) := collect_box_disj' (by assumption);
  have : (insert (~(~(□~p) ⋏ ~(□~q))) Γ) ⊢ □(~p ⋎ ~q) ⟶ □(~(p ⋏ q)) := box_distribute_nec' disj_neg;
  exact modus_ponens' (by assumption) (by assumption);

def distribute_dia_conj' {Γ : Set F} {p q : F} (d : Γ ⊢ ◇(p ⋏ q)) : Γ ⊢ ◇p ⋏ ◇q := by
  exact distribute_dia_conj ⨀ d

def distribute_multidia_conj' (d : Γ ⊢ ◇[n](p ⋏ q)) : Γ ⊢ ◇[n]p ⋏ ◇[n]q := by
  induction n with
  | zero => trivial;
  | succ n ih => sorry; -- simp_all only [Dia.multidia];

lemma distribute_multidia_finset_conj'! {Γ : Set F} {Δ : Finset F} (d : Γ ⊢! ◇[n]Δ.conj) : Γ ⊢! (Δ.multidia n).conj := by
  sorry;

lemma distribute_multidia_finset_conj! {n : ℕ} {Γ : Set F} {Δ : Finset F} : Γ ⊢! ◇[n]Δ.conj ⟶ (Δ.multidia n).conj := by
  apply dtr!;
  apply distribute_multidia_finset_conj'!;
  apply axm! (by simp);

def collect_dia_disj {Γ : Set F} {p q : F} : Γ ⊢ ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := by
  simp [-NegDefinition.neg];
  apply contra₁';
  apply dtr;
  sorry;

def collect_dia_disj' {Γ : Set F} {p q : F} (d : Γ ⊢ ◇p ⋎ ◇q) : Γ ⊢ ◇(p ⋎ q) := collect_dia_disj ⨀ d

variable [HasAxiom4 Bew]

def axiom4 {Γ : Set F} {p} :  Γ ⊢ (Axiom4 p) := HasAxiom4.A4 Γ p

def axiom4' {Γ : Set F} {p} (d₁ : Γ ⊢ □p) : Γ ⊢ □□p := (Hilbert.axiom4) ⨀ d₁

lemma axiom4! (Γ : Set F) (p) : Γ ⊢! (Axiom4 p) := ⟨Hilbert.axiom4⟩

lemma axiom4'! {Γ : Set F} {p} (d : Γ ⊢! □p) : Γ ⊢! □□p := ⟨axiom4' d.some⟩


variable [HasAxiomT Bew]

def axiomT {Γ : Set F} {p} :  Γ ⊢ (AxiomT p) := HasAxiomT.T Γ p

def axiomT' {Γ : Set F} {p} (d₁ : Γ ⊢ □p) : Γ ⊢ p := (Hilbert.axiomT) ⨀ d₁

lemma axiomT! (Γ : Set F) (p) : Γ ⊢! (AxiomT p) := ⟨Hilbert.axiomT⟩

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
