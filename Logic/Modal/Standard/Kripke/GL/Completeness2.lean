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
    (himp     : ∀ (p q : Formula α), q ≠ ⊥ → C (p ⟶ q))
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

def negated : Formula α → Bool
  | ~_ => true
  | _  => false

lemma negated_iff {p : Formula α} : p.negated ↔ ∃ q, p = ~q := by
  induction p using Formula.cases_neg with
  | himp p q hq =>
    simp [negated];
    split;
    . simp_all [Formula.imp_eq]; contradiction;
    . simpa;
  | _ => simp [negated]

lemma not_negated_iff {p : Formula α} : ¬p.negated ↔ ∀ q, p ≠ ~q := by
  induction p using Formula.cases_neg with
  | himp p q hq =>
    simp [negated];
    split;
    . simp_all [Formula.imp_eq]; contradiction;
    . simpa;
  | _ => simp [negated]

def complement (p : Formula α) : Formula α := if p.negated then p else ~p
prefix:80 "-" => complement

lemma eq_complement_negated {p : Formula α} (hp : p.negated) : -p = p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]

lemma eq_complement_not_negated {p : Formula α} (hp : ¬p.negated) : -p = ~p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]

lemma complement_bot (h : -p = ⊥) : p = ⊥ := by
  by_cases hn : p.negated;
  . rw [eq_complement_negated hn] at h; exact h;
  . rw [eq_complement_not_negated hn] at h; contradiction;

lemma complement_box (h : -p = □q) : p = □q := by
  by_cases hn : p.negated;
  . rw [eq_complement_negated hn] at h; exact h;
  . rw [eq_complement_not_negated hn] at h; contradiction;


/-
lemma complement_imp (h : -p = q ⟶ r) : p = q ⟶ r := by
  by_cases hn : p.negated;
  . rw [eq_complement_negated hn] at h; exact h;
  . rw [eq_complement_not_negated hn] at h; contradiction;
-/


end Complement


@[elab_as_elim]
def rec_negated {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (~p))
    (himp    : ∀ (p q : Formula α), (p ⟶ q).negated = false → C p → C q → C (p ⟶ q))
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
      . simp [negated]
        split;
        . rename_i h;
          simp only [imp_eq, imp_inj] at h;
          have := h.2;
          contradiction;
        . simp;


abbrev Complementary (P : Finset $ Formula α) : Finset (Formula α) := P ∪ (P.image (complement ·))
postfix:80 "⁻" => Formula.Complementary

namespace Complementary

variable {s : Finset $ Formula α}
variable [Theory.SubformulaClosed s.toSet]

end Complementary


abbrev GLComplementary (p : Formula α) : Finset (Formula α) := (𝒮 p)⁻
prefix:70 "𝒮⁻ " => Formula.GLComplementary

namespace GLComplementary

lemma mem_of_mem_box (h : □q ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := by
  simp_all [GLComplementary];
  rcases h with h | ⟨r, _, hr₂⟩;
  . aesop;
  . have := complement_box hr₂; subst this;
    aesop;

lemma mem_subformula_of_mem_box (h : □q ∈ 𝒮⁻ p) : □q ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨r, _, hr₂⟩;
  . assumption;
  . have := complement_box hr₂; subst this; simpa;

/-
lemma mem_of_mem_imp (h : q ⟶ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p ∧ r ∈ 𝒮⁻ p := by
  simp_all [GLComplementary];
  rcases h with h | ⟨s, _, hr₂⟩;
  . aesop;
  . have := complement_imp hr₂; subst this; aesop;

lemma mem_of_mem_imp₁ (h : q ⟶ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := mem_of_mem_imp h |>.1

lemma mem_of_mem_imp₂ (h : q ⟶ r ∈ 𝒮⁻ p) : r ∈ 𝒮⁻ p := mem_of_mem_imp h |>.2

lemma mem_subformula_of_mem_and (h : q ⋏ r ∈ 𝒮⁻ p) : q ⋏ r ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_and hr₂; subst this; simpa;

lemma mem_subformula_of_mem_or (h : q ⋎ r ∈ 𝒮⁻ p) : q ⋎ r ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_or hr₂; subst this; simpa;

lemma mem_subformula_of_mem_imp (h : q ⟶ r ∈ 𝒮⁻ p) : q ⟶ r ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_imp hr₂; subst this; simpa;

lemma mem_subformula_of_mem_top (h : ⊤ ∈ 𝒮⁻ p) : ⊤ ∈ 𝒮 p := by
  simp [GLComplementary] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_top hr₂; subst this; simpa;

attribute [aesop safe 5 forward]
  mem_subformula_of_mem_box
  mem_subformula_of_mem_and
  mem_subformula_of_mem_or
  mem_subformula_of_mem_imp
  mem_subformula_of_mem_top
  -- mem_subformula_of_mem_bot
-/

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



structure CompleteConsistentTheory (Λ : DeductionParameter α) (p : Formula α) where
  theory : Theory α
  consistent : (Λ)-Consistent theory
  complete : theory.Complete p

alias CCT := CompleteConsistentTheory

namespace CompleteConsistentTheory

open System

variable {Λ : DeductionParameter α}

lemma lindenbaum (p : Formula α) (consisT : (Λ)-Consistent T) : ∃ Ω : CCT Λ p, (T ⊆ Ω.theory) := by
  obtain ⟨Z, Z_consis, Z_complete, Z_subset_T⟩ := Theory.complete_lindenbaum (α := α) (Λ := Λ);
  use ⟨Z, Z_consis, Z_complete⟩;

variable {p q : Formula α}
variable {Ω Ω₁ Ω₂ : CCT Λ p}

lemma mem_compl_of_not_mem (hs : q ∈ 𝒮 p) (h : q ∉ Ω.theory) : -q ∈ Ω.theory := by
  have := Ω.complete.whichone q (by assumption);
  aesop;

lemma mem_of_not_mem_compl (hs : q ∈ 𝒮 p) (h : -q ∉ Ω.theory) : q ∈ Ω.theory := by
  have := Ω.complete.whichone q (by assumption);
  aesop;

lemma membership_iff (hq : q ∈ 𝒮 p) : (q ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~q ∉ Ω.theory by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact Ω.complete.whichone' q hq;
    by_contra hC;
    have hnp : Ω.theory *⊢[Λ]! ~q := Context.by_axm! hC;
    have := neg_mdp! hnp hp;
    have := Ω.consistent;
    contradiction;

lemma mem_verum (h : ⊤ ∈ 𝒮 p) : ⊤ ∈ Ω.theory := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp] lemma mem_falsum : ⊥ ∉ Ω.theory := Theory.not_mem_falsum_of_consistent Ω.consistent

lemma unprovable_falsum (h : ⊥ ∈ 𝒮 p) : Ω.theory *⊬[Λ]! ⊥ := by apply membership_iff (by assumption) |>.not.mp; simp

lemma no_both (h : q ∈ 𝒮 p) (hn : ¬q.negated) : ¬((q ∈ Ω.theory) ∧ (-q ∈ Ω.theory)) := by
  by_contra hC;
  obtain ⟨hq, hnq⟩ := hC;
  rw [Formula.eq_complement_not_negated hn] at *;
  replace hq := membership_iff h |>.mp hq;
  replace hnq := membership_iff (by sorry) |>.mp hnq;
  exact unprovable_falsum (by sorry) (hnq ⨀ hq);

lemma iff_mem_compl (hq : q ∈ 𝒮 p) (hn : ¬q.negated) : (q ∈ Ω.theory) ↔ (-q ∉ Ω.theory) := by
  constructor;
  . intro h; have := no_both hq hn (Ω := Ω); simp_all;
  . intro h; exact mem_of_not_mem_compl (by sorry) h;

lemma iff_mem_imp (hsub : (q ⟶ r) ∈ 𝒮 p) : ((q ⟶ r) ∈ Ω.theory) ↔ (q ∈ Ω.theory) → (-r ∉ Ω.theory) := by
  constructor;
  . intro hqr hq;
    apply iff_mem_compl (by sorry) (by sorry) |>.mp;
    replace hqr := membership_iff (by sorry) |>.mp hqr;
    replace hq := membership_iff (by sorry) |>.mp hq;
    exact membership_iff (by sorry) |>.mpr $ hqr ⨀ hq;
  . intro hpq;
    replace hpq := imp_iff_or_not.mp hpq;
    rcases hpq with (hq | hr);
    . replace hq := membership_iff (by sorry) |>.mp $ iff_mem_compl (by sorry) (by sorry) |>.mpr hq;
      apply membership_iff (by sorry) |>.mpr;
      exact dhyp! hq;
    . replace hr := by simpa using iff_mem_compl (by sorry) (by sorry) |>.not.mp hr;
      apply membership_iff (by sorry) |>.mpr;
      sorry;

lemma iff_mem_imp_not (hsub : (q ⟶ r) ∈ 𝒮 p) : ((q ⟶ r) ∉ Ω.theory) ↔ (q ∈ Ω.theory) ⋏ (-r ∈ Ω.theory) := by
  simpa using @iff_mem_imp α _ Λ p q Ω r hsub |>.not;

/-
lemma iff_mem_imp (hsub : (q ⟶ r) ∈ 𝒮 p) : ((q ⟶ r) ∈ Ω.theory) ↔ (q ∈ Ω.theory) → (r ∈ Ω.theory) := by
  constructor;
  . intro hqr hq;
    have dqr := membership_iff (by aesop) |>.mp hqr;
    have dq  := membership_iff (by aesop) |>.mp hq;
    apply membership_iff (by aesop) |>.mpr;
    exact dqr ⨀ dq;
  . rintro hqr;
    replace hqr := not_or_of_imp hqr;
    rcases hqr with (hq | hr);
    . apply membership_iff (by aesop) |>.mpr;
      replace hq := mem_compl_of_not_mem (by aesop) hq;
      sorry;
    . apply membership_iff (by aesop) |>.mpr;
      exact dhyp! $ membership_iff (by aesop) |>.mp hr;
    -- apply membership_iff (by aesop) |>.mpr;
    -- sorry;
-/

end CompleteConsistentTheory

namespace Kripke

open Formula

variable {p q : Formula α}

abbrev GLCompleteFrame {p : Formula α} (h : 𝐆𝐋 ⊬! p) : Kripke.FiniteFrame where
  World := CCT 𝐆𝐋 p
  World_finite := by
    sorry;
  World_nonempty := by
    have : (𝐆𝐋)-Consistent {~p} := Theory.unprovable_iff_singleton_neg_consistent.mp h;
    obtain ⟨Ω, hΩ⟩ := CompleteConsistentTheory.lindenbaum p this;
    exact ⟨Ω⟩;
  Rel X Y :=
    (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.theory → (q ∈ Y.theory ∧ □q ∈ Y.theory)) ∧
    (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.theory ∧ □r ∈ Y.theory)

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
  Valuation X a := (atom a) ∈ X.theory

open Formula.Kripke
open CompleteConsistentTheory

open System System.FiniteContext in
private lemma GL_truthlemma.lemma1
  {q : Formula α}
  {X : Theory α} (X_consistent : (𝐆𝐋)-Consistent X) (h : □q ∉ X) : (𝐆𝐋)-Consistent ({□q, ~q} ∪ (□''⁻¹X ∪ □''□''⁻¹X)) := by
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

open Formula MaximalConsistentTheory in
lemma GL_truthlemma₂
  {p : Formula α} (h : 𝐆𝐋 ⊬! p) {X : (GLCompleteModel h).World}
  {q : Formula α} (h_sub : q ∈ 𝒮⁻ p) :
  Satisfies (GLCompleteModel h) X q ↔ q ∈ X.theory := by
  induction q using Formula.rec_negated generalizing X with
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      have := @GL_truthlemma.lemma1 α _ q X.theory X.consistent h;
      obtain ⟨Y, hY⟩ := CompleteConsistentTheory.lindenbaum p this;
      simp [Set.insert_subset_iff] at hY;
      have ⟨⟨hY₁, hY₂⟩, hY₃, hY₄⟩ := hY;
      simp [Satisfies];
      use Y;
      constructor;
      . intro r hr₁ hr₂;
        constructor;
        . apply hY₃; exact hr₂;
        . apply hY₄; exact hr₂;
      . use q;
        refine ⟨?_, ?_, ?_, ?_⟩;
        . exact GLComplementary.mem_subformula_of_mem_box h_sub;
        . assumption;
        . assumption;
        . apply @ih Y (GLComplementary.mem_of_mem_box h_sub) |>.not.mpr;
          apply Theory.not_mem_of_mem_neg Y.consistent (by aesop);
    . intro h Y RXY;
      apply ih (X := Y) (GLComplementary.mem_of_mem_box h_sub) |>.mpr
      simp [Frame.Rel'] at RXY;
      exact RXY.1 q (GLComplementary.mem_subformula_of_mem_box h_sub) h |>.1;
  | hfalsum => simp [Satisfies];
  | hatom => simp [Satisfies];
  | hneg q ih =>
    sorry;
  | himp q r neg ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      have ⟨hq, hr⟩ := iff_mem_imp_not (by sorry) |>.mp h;
      simp [Satisfies];
      constructor;
      . exact ihq (by sorry) |>.mpr hq;
      . exact ihr (by sorry) |>.not.mpr $ iff_mem_compl (by sorry) (by sorry) |>.not.mpr (by simpa);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      apply iff_mem_imp_not (by sorry) |>.mpr;
      constructor;
      . exact ihq (by sorry) |>.mp hq;
      . simpa using iff_mem_compl (by sorry) (by sorry) |>.not.mp $ ihr (by sorry) |>.not.mp hr;

private lemma GL_completeAux : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLCompleteFrame h);
  constructor;
  . exact ⟨GLCompleteFrame.transitive, GLCompleteFrame.irreflexive⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    have ⟨X, hX⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {~p}) (p := p) (Theory.unprovable_iff_singleton_neg_consistent.mp h);
    use (GLCompleteModel h).Valuation, X;
    apply GL_truthlemma₂ (h := h) (by simp) |>.not.mpr;
    apply Theory.not_mem_of_mem_neg X.consistent (by aesop);

end Kripke

end LO.Modal.Standard
