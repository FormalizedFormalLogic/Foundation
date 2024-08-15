import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

variable {α : Type u} [Inhabited α] [DecidableEq α]


namespace Formula

variable {p q r : Formula α}

@[elab_as_elim]
def cases_neg {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (~p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p
  | ~p      => hneg p
  | p ⟶ q  => if e : q = ⊥ then e ▸ hneg p else himp p q e

@[elab_as_elim]
def rec_neg {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (~p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C p → C q → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_neg hfalsum hatom hneg himp hbox p)
  | ~p      => hneg p (rec_neg hfalsum hatom hneg himp hbox p)
  | p ⟶ q  =>
    if e : q = ⊥
    then e ▸ hneg p (rec_neg hfalsum hatom hneg himp hbox p)
    else himp p q e (rec_neg hfalsum hatom hneg himp hbox p) (rec_neg hfalsum hatom hneg himp hbox q)

section Complement

variable {p q: Formula α}

def negated : Formula α → Bool
  | ~_ => True
  | _  => False

@[simp]
lemma negated_def : (~p).negated := by simp [negated]

@[simp]
lemma negated_imp : (p ⟶ q).negated ↔ (q = ⊥) := by
  simp [negated, Formula.imp_eq];
  split;
  . simp_all [Formula.imp_eq]; rfl;
  . simp_all [Formula.imp_eq]; simpa;

lemma negated_iff : p.negated ↔ ∃ q, p = ~q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp];
  | _ => simp [negated]

lemma not_negated_iff : ¬p.negated ↔ ∀ q, p ≠ ~q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp];
  | _ => simp [negated]



lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

def complement : Formula α → Formula α
  | ~p => p
  | p  => ~p

prefix:80 "-" => complement

namespace complement

@[simp] lemma neg_def : -(~p) = p := by
  induction p using Formula.rec' <;> simp_all [complement]

@[simp] lemma bot_def : -(⊥ : Formula α) = ~(⊥) := by simp only [complement, imp_inj, and_true]; rfl;

@[simp] lemma box_def : -(□p) = ~(□p) := by simp only [complement, imp_inj, and_true]; rfl;

lemma imp_def₁ (hq : q ≠ ⊥) : -(p ⟶ q) = ~(p ⟶ q) := by
  simp only [complement];
  split;
  . rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  . rfl;

lemma imp_def₂ (hq : q = ⊥) : -(p ⟶ q) = p := by
  subst_vars;
  apply neg_def;

lemma resort_box (h : -p = □q) : p = ~□q := by
  simp [complement] at h;
  split at h;
  . subst_vars; rfl;
  . contradiction;

end complement

end Complement


@[elab_as_elim]
def rec_negated {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (~p))
    (himp    : ∀ (p q : Formula α), ¬(p ⟶ q).negated → C p → C q → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_negated hfalsum hatom hneg himp hbox p)
  | ~p      => hneg p (rec_negated hfalsum hatom hneg himp hbox p)
  | p ⟶ q  => by
    by_cases e : q = ⊥
    . exact e ▸ hneg p (rec_negated hfalsum hatom hneg himp hbox p)
    . refine himp p q ?_ (rec_negated hfalsum hatom hneg himp hbox p) (rec_negated hfalsum hatom hneg himp hbox q)
      . simpa [negated_imp]

end Formula

/--/
abbrev Complementary (P : Finset $ Formula α) : Finset (Formula α) := P ∪ (P.image (complement ·))
postfix:80 "⁻" => Formula.Complementary

namespace Complementary

variable {s : Finset $ Formula α}
variable [Theory.SubformulaClosed s.toSet]

end Complementary


abbrev GLComplementary (p : Formula α) : Finset (Formula α) := (𝒮 p)⁻
prefix:70 "𝒮⁻ " => Formula.GLComplementary

namespace GLComplementary


lemma mem_subformula_of_mem_box (h : □q ∈ 𝒮⁻ p) : □q ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨r, _, hr₂⟩;
  . assumption;
  . have := complement_box hr₂; subst this; simpa;

lemma mem_of_mem_box (h : □q ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := by
  simp; left;
  exact Subformulas.mem_box $ mem_subformula_of_mem_box h;

end GLComplementary

end Formula



structure Theory.Complete (T : Theory α) (p : Formula α) : Prop where
  subset_cf : T ⊆ 𝒮⁻ p
  whichone : ∀ q ∈ 𝒮 p, (q ∈ T) ∨ (-q ∈ T)

namespace Theory

variable {p : Formula α} {T : Theory α}
-- variable (T_consis : (Λ)-Consistent T) (T_subset : T ⊆ 𝒮⁻ p)

lemma complete_lindenbaum : ∃ Z, (Λ)-Consistent Z ∧ Z.Complete p ∧ T ⊆ Z := by sorry;

lemma not_mem_of_mem_neg (T_consis : (Λ)-Consistent T) (h : ~p ∈ T) : p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

lemma not_mem_neg_of_mem (T_consis : (Λ)-Consistent T) (h : p ∈ T) : ~p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

lemma Complete.whichone' (self : Theory.Complete T p) : ∀ q ∈ 𝒮 p, (q ∈ T) ∨ (~q ∈ T) := by
  intro q hq;
  have := self.whichone q hq;
  by_cases n : q.negated;
  . rw [Formula.eq_complement_negated n] at *;
    left; simpa;
  . rwa [Formula.eq_complement_not_negated n] at *;

end Theory
-/


abbrev Formulae (α) := Finset $ Formula α

namespace Formulae

def complementary (P : Formulae α) : Formulae α := P ∪ (P.image (Formula.complement))
postfix:80 "⁻" => Formulae.complementary

class ComplementaryClosed (X : Formulae α) (S : Formulae α) : Prop where
  subset : X ⊆ S⁻
  either : ∀ p ∈ S, p ∈ X ∨ -p ∈ X

def SubformulaeComplementaryClosed (X : Formulae α) (p : Formula α) : Prop := X.ComplementaryClosed (𝒮 p)

variable {S : Formulae α}

end Formulae



namespace Theory

variable {p : Formula α} {T : Theory α}

lemma not_mem_of_mem_neg (T_consis : (Λ)-Consistent T) (h : ~p ∈ T) : p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

lemma not_mem_neg_of_mem (T_consis : (Λ)-Consistent T) (h : p ∈ T) : ~p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

end Theory


lemma complement_derive_bot
  {p : Formula α} [System (Formula α) S] {𝓢 : S} [System.ModusPonens 𝓢]
  (hp : 𝓢 ⊢! p) (hcp : 𝓢 ⊢! -p)
  : 𝓢 ⊢! ⊥ := by
  induction p using Formula.cases_neg with
  | hfalsum => assumption;
  | hatom a =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    simp [Formula.complement] at hcp;
    exact hp ⨀ hcp;
  | himp p q h =>
    simp [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox p =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;

lemma complement_derive_bot₂
  {Λ : DeductionParameter α} (hp : Λ ⊢! p) (hcp : Λ ⊢! -p) : Λ ⊢! ⊥ := complement_derive_bot hp hcp

structure ComplementaryClosedConsistentFormulae (Λ) (S : Formulae α) where
  formulae : Formulae α
  consistent : (Λ)-Consistent (formulae.toSet)
  closed : formulae.ComplementaryClosed S
alias CCF := ComplementaryClosedConsistentFormulae

namespace ComplementaryClosedConsistentFormulae

open System
open Formula (atom)
variable {Λ : DeductionParameter α}

lemma lindenbaum
  {X : Formulae α} (consisT : (Λ)-Consistent X)
  (S : Formulae α) : ∃ X' : CCF Λ S, X ⊆ X'.formulae ∧ X'.formulae ⊆ S⁻ := by
  sorry

noncomputable instance [System.Consistent Λ] : Inhabited (CCF Λ S)
  := ⟨lindenbaum (X := ∅) (by sorry) S |>.choose⟩

variable {S} {X : CCF Λ S}

@[simp] lemma unprovable_falsum : X.formulae *⊬[Λ]! ⊥ := X.consistent

lemma mem_compl_of_not_mem (hs : q ∈ S) (h : q ∉ X.formulae) : -q ∈ X.formulae := by
  rcases X.closed.either q (by assumption) with (h | h);
  . contradiction;
  . assumption;

lemma mem_of_not_mem_compl (hs : q ∈ S) (h : -q ∉ X.formulae) : q ∈ X.formulae := by
  rcases X.closed.either q (by assumption) with (h | h);
  . assumption;
  . contradiction;

lemma membership_iff (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (X.formulae *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices -q ∉ X.formulae by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact X.closed.either q hq_sub;
    by_contra hC;
    have hnp : X.formulae *⊢[Λ]! -q := Context.by_axm! hC;
    have := complement_derive_bot hp hnp;
    simpa;

lemma mem_verum (h : ⊤ ∈ S) : ⊤ ∈ X.formulae := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp]
lemma mem_falsum : ⊥ ∉ X.formulae := Theory.not_mem_falsum_of_consistent X.consistent

lemma iff_mem_compl (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (-q ∉ X.formulae) := by
  constructor;
  . intro hq; replace hq := membership_iff hq_sub |>.mp hq;
    by_contra hnq;
    induction q using Formula.cases_neg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(atom a) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hbox q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(□q) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hneg q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! q := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | himp q r h =>
      simp only [Formula.complement.imp_def₁ h] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(q ⟶ r) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := this ⨀ hq;
      simpa;
  . intro h; exact mem_of_not_mem_compl (by assumption) h;

lemma iff_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∈ X.formulae) ↔ (q ∈ X.formulae) → (-r ∉ X.formulae) := by
  constructor;
  . intro hqr hq;
    apply iff_mem_compl hsub_r |>.mp;
    replace hqr := membership_iff hsub_qr |>.mp hqr;
    replace hq := membership_iff hsub_q |>.mp hq;
    exact membership_iff hsub_r |>.mpr $ hqr ⨀ hq;
  . intro hqr; replace hqr := not_or_of_imp hqr
    rcases hqr with (hq | hr);
    . apply membership_iff hsub_qr |>.mpr;
      replace hq := mem_compl_of_not_mem hsub_q hq;
      induction q using Formula.cases_neg with
      | hfalsum => exact efq!;
      | hatom a => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hbox q => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hneg q =>
        simp only [Formula.complement.neg_def] at hq;
        exact efq_of_neg₂! $ Context.by_axm! hq;
      | himp q r h =>
        simp only [Formula.complement.imp_def₁ h] at hq;
        exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
    . apply membership_iff (by assumption) |>.mpr;
      exact dhyp! $ membership_iff (by assumption) |>.mp $ iff_mem_compl (by assumption) |>.mpr hr;

lemma iff_not_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∉ X.formulae) ↔ (q ∈ X.formulae) ∧ (-r ∈ X.formulae) := by
  simpa using @iff_mem_imp α _ Λ S X q r hsub_qr hsub_q hsub_r |>.not;

end ComplementaryClosedConsistentFormulae

namespace Kripke

open Formula

variable {p q : Formula α}

abbrev GLCompleteFrame {p : Formula α} (h : 𝐆𝐋 ⊬! p) : Kripke.FiniteFrame where
  World := CCF 𝐆𝐋 (𝒮 p)
  World_finite := by
    sorry;
  World_nonempty := by
    sorry;
    -- have : (𝐆𝐋)-Consistent {~p} := Theory.unprovable_iff_singleton_neg_consistent.mp h;
    -- obtain ⟨Ω, hΩ⟩ := CompleteConsistentTheory.lindenbaum p this;
    -- exact ⟨Ω⟩;
  Rel X Y :=
    (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.formulae → (q ∈ Y.formulae ∧ □q ∈ Y.formulae)) ∧
    (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.formulae ∧ □r ∈ Y.formulae)

namespace GLCompleteFrame

variable {p : Formula α} {h : 𝐆𝐋 ⊬! p}

lemma irreflexive : Irreflexive (GLCompleteFrame h).Rel := by simp [Irreflexive];

lemma transitive : Transitive (GLCompleteFrame h).Rel := by
  simp;
  rintro X Y Z ⟨RXY, ⟨r, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro q hq₁ hq₂;
    exact RYZ q hq₁ $ RXY q hq₁ hq₂ |>.2;
  . use r;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ r (by assumption) (by assumption) |>.2;

end GLCompleteFrame

abbrev GLCompleteModel (h : 𝐆𝐋 ⊬! p) : Kripke.Model α where
  Frame := GLCompleteFrame h
  Valuation X a := (atom a) ∈ X.formulae

open Formula.Kripke
open ComplementaryClosedConsistentFormulae

open System System.FiniteContext in
private lemma GL_truthlemma.lemma1
  {q : Formula α}
  {X : (GLCompleteModel h).World} (h_sub : □q ∉ X.formulae)
  : (𝐆𝐋)-Consistent (({□q, ~q} ∪ (X.formulae.prebox ∪ X.formulae.prebox.box)).toSet) := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
  have := toₛ! hΓ₂;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⋏ ~q ⟶ ⊥ := imply_left_remove_conj! (p := ~q) this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ ~q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ q := imp_trans''! this $ imp_trans''! (and₂'! neg_equiv!) dne!
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⋏ □q ⟶ q := imply_left_remove_conj! (p := □q) this;
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⟶ (□q ⟶ q) := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □(□q ⟶ q) := imply_box_distribute'! this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □q := imp_trans''! this axiomL!;
  have : 𝐆𝐋 ⊢! ⋀□'(Γ.remove (~q)).remove (□q) ⟶ □q := imp_trans''! collect_box_conj! this;
  have : (□'(Γ.remove (~q)).remove (□q)) ⊢[𝐆𝐋]! □q := provable_iff.mpr this;
  sorry;

open Formula.Subformulas in
macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_self
    | apply mem_imp₁ $ by assumption
    | apply mem_imp₂ $ by assumption
    | apply mem_box  $ by assumption
  )

open Formula MaximalConsistentTheory in
lemma GL_truthlemma₂
  {p : Formula α} (h : 𝐆𝐋 ⊬! p) {X : (GLCompleteModel h).World}
  {q : Formula α} (q_sub : q ∈ 𝒮 p) :
  Satisfies (GLCompleteModel h) X q ↔ q ∈ X.formulae := by
  induction q using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp q r ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      simp [Satisfies];
      constructor;
      . apply ihq (by trivial) |>.mpr;
        exact iff_not_mem_imp q_sub |>.mp h |>.1;
      . apply ihr (by trivial) |>.not.mpr;
        have := iff_not_mem_imp q_sub |>.mp h |>.2;
        exact iff_mem_compl (by trivial) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by trivial) |>.mp hq;
      replace hr := ihr (by trivial) |>.not.mp hr;
      apply iff_not_mem_imp q_sub |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by trivial) |>.not.mp (by simpa using hr);
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      have := GL_truthlemma.lemma1 (X := X) (h_sub := h);
      obtain ⟨Y, hY₁, _⟩ := lindenbaum (S := 𝒮 p) this;
      simp only [Finset.union_subset_iff] at hY₁;
      have hY₁₁ : □q ∈ Y.formulae := by apply hY₁.1; simp;
      have hY₁₂ : ~q ∈ Y.formulae := by apply hY₁.1; simp;
      simp [Satisfies];
      use Y;
      constructor;
      . intro r _ hr_sub;
        constructor;
        . apply hY₁.2.1; simpa;
        . apply hY₁.2.2; simpa;
      . use q;
        refine ⟨q_sub, h, hY₁₁, ?_⟩;
        . apply ih (by trivial) |>.not.mpr;
          exact Theory.not_mem_of_mem_neg Y.consistent (by simp_all);
    . intro h Y RXY;
      apply ih (by trivial) |>.mpr;
      simp [Frame.Rel'] at RXY;
      refine RXY.1 q ?_ h |>.1;
      assumption;

private lemma GL_completeAux : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLCompleteFrame h);
  constructor;
  . exact ⟨GLCompleteFrame.transitive, GLCompleteFrame.irreflexive⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX₁, hX₂⟩ := lindenbaum (Λ := 𝐆𝐋) (X := {~p}) (S := 𝒮 p)
      (by sorry); -- Theory.unprovable_iff_singleton_neg_consistent.mp h
    use (GLCompleteModel h).Valuation, X;
    apply @GL_truthlemma₂ α _ p (by simpa) X p (by trivial) |>.not.mpr;
    apply Theory.not_mem_of_mem_neg X.consistent (by simp_all);

end Kripke

end LO.Modal.Standard
