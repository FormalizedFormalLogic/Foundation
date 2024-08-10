import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

variable {α : Type u} [Inhabited α] [DecidableEq α]


namespace Formula

variable {p q r : Formula α}

/-- Supplemental subformulas finset for completeness of `𝐆𝐋` -/
abbrev GLSubformulas (p : Formula α) : Finset (Formula α) := (𝒮 p) ∪ ((𝒮 p).image (complement ·))
prefix:70 "𝒮⁻ " => Formula.GLSubformulas

namespace GLSubformulas

lemma mem_of_mem_box (h : □q ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := by
  simp_all [GLSubformulas];
  rcases h with h | ⟨r, _, hr₂⟩;
  . aesop;
  . have := complement_box hr₂; subst this;
    aesop;

lemma mem_of_mem_and (h : q ⋏ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p ∧ r ∈ 𝒮⁻ p := by
  simp_all [GLSubformulas];
  rcases h with h | ⟨s, _, hr₂⟩;
  . aesop;
  . have := complement_and hr₂; subst this; aesop;

lemma mem_of_mem_and₁ (h : q ⋏ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := mem_of_mem_and h |>.1

lemma mem_of_mem_and₂ (h : q ⋏ r ∈ 𝒮⁻ p) : r ∈ 𝒮⁻ p := mem_of_mem_and h |>.2

lemma mem_of_mem_or (h : q ⋎ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p ∧ r ∈ 𝒮⁻ p := by
  simp_all [GLSubformulas];
  rcases h with h | ⟨s, _, hr₂⟩;
  . aesop;
  . have := complement_or hr₂; subst this; aesop;

lemma mem_of_mem_or₁ (h : q ⋎ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := mem_of_mem_or h |>.1

lemma mem_of_mem_or₂ (h : q ⋎ r ∈ 𝒮⁻ p) : r ∈ 𝒮⁻ p := mem_of_mem_or h |>.2

lemma mem_of_mem_imp (h : q ⟶ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p ∧ r ∈ 𝒮⁻ p := by
  simp_all [GLSubformulas];
  rcases h with h | ⟨s, _, hr₂⟩;
  . aesop;
  . have := complement_imp hr₂; subst this; aesop;

lemma mem_of_mem_imp₁ (h : q ⟶ r ∈ 𝒮⁻ p) : q ∈ 𝒮⁻ p := mem_of_mem_imp h |>.1

lemma mem_of_mem_imp₂ (h : q ⟶ r ∈ 𝒮⁻ p) : r ∈ 𝒮⁻ p := mem_of_mem_imp h |>.2

lemma mem_subformula_of_mem_box (h : □q ∈ 𝒮⁻ p) : □q ∈ 𝒮 p := by
  simp [GLSubformulas] at h;
  rcases h with h | ⟨r, _, hr₂⟩;
  . assumption;
  . have := complement_box hr₂; subst this; simpa;

lemma mem_subformula_of_mem_and (h : q ⋏ r ∈ 𝒮⁻ p) : q ⋏ r ∈ 𝒮 p := by
  simp [GLSubformulas] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_and hr₂; subst this; simpa;

lemma mem_subformula_of_mem_or (h : q ⋎ r ∈ 𝒮⁻ p) : q ⋎ r ∈ 𝒮 p := by
  simp [GLSubformulas] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_or hr₂; subst this; simpa;

lemma mem_subformula_of_mem_imp (h : q ⟶ r ∈ 𝒮⁻ p) : q ⟶ r ∈ 𝒮 p := by
  simp [GLSubformulas] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_imp hr₂; subst this; simpa;

lemma mem_subformula_of_mem_top (h : ⊤ ∈ 𝒮⁻ p) : ⊤ ∈ 𝒮 p := by
  simp [GLSubformulas] at h;
  rcases h with h | ⟨s, _, hr₂⟩;
  . assumption;
  . have := complement_top hr₂; subst this; simpa;

end GLSubformulas

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

variable {p : Formula α}
variable {Ω Ω₁ Ω₂ : CCT Λ p}

lemma mem_compl_of_not_mem (hs : q ∈ 𝒮 p) (h : q ∉ Ω.theory) : -q ∈ Ω.theory := by
  have := Ω.complete.whichone q (by aesop);
  aesop;

lemma mem_of_not_mem_compl (hs : q ∈ 𝒮 p) (h : -q ∉ Ω.theory) : q ∈ Ω.theory := by
  have := Ω.complete.whichone q (by aesop);
  aesop;

lemma membership_iff (hq : q ∈ 𝒮 p) : (q ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~q ∉ Ω.theory by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      have := Ω.complete.whichone q hq;
      by_cases n : q.negated;
      . rw [Formula.eq_complement_negated n] at this; simp_all;
      . rw [Formula.eq_complement_not_negated n] at this; assumption;
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

lemma iff_mem_neg (hq : ~p ∈ 𝒮 p) : (~q ∈ Ω.theory) ↔ (q ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    sorry;
  . intro hp;
    sorry;

lemma iff_mem_and (hq : (q ⋏ r) ∈ 𝒮 p) : ((q ⋏ r) ∈ Ω.theory) ↔ (q ∈ Ω.theory) ∧ (r ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff (by assumption) |>.mp hpq;
    constructor;
    . apply membership_iff (by aesop) |>.mpr;
      exact and₁'! hpq;
    . apply membership_iff (by aesop) |>.mpr;
      exact and₂'! hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff (by aesop) |>.mpr;
    exact and₃'! (membership_iff (by aesop) |>.mp hp) (membership_iff (by aesop) |>.mp hq);

lemma iff_mem_or (hq : (q ⋎ r) ∈ 𝒮 p) : ((q ⋎ r) ∈ Ω.theory) ↔ (q ∈ Ω.theory) ∨ (r ∈ Ω.theory) := by
  constructor;
  . intro hqr;
    replace hqr := membership_iff (by aesop) |>.mp hqr;
    by_contra hC; push_neg at hC;
    obtain ⟨hq, hr⟩ := hC;
    replace hq := membership_iff (by sorry) |>.mp $ @iff_mem_neg α _ Λ p Ω q (by sorry) |>.mpr hq;
    replace hr := membership_iff (by sorry) |>.mp $ @iff_mem_neg α _ Λ p Ω r (by sorry) |>.mpr hr;
    have : Ω.theory *⊢[Λ]! ⊥ := or₃'''! (neg_equiv'!.mp hq) (neg_equiv'!.mp hr) hqr;
    exact Ω.consistent this;
  . rintro (hp | hq);
    . apply membership_iff (by aesop) |>.mpr;
      exact or₁'! (membership_iff (by aesop) |>.mp hp);
    . apply membership_iff (by aesop) |>.mpr;
      exact or₂'! (membership_iff (by aesop) |>.mp hq);

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
      replace hq := mem_compl_of_not_mem (by sorry) hq;
      by_cases n : q.negated;
      . rw [Formula.eq_complement_negated n] at hq;
        sorry;
      . rw [Formula.eq_complement_not_negated n] at hq;
        exact efq_of_neg! $ membership_iff (by sorry) |>.mp hq;

    . apply membership_iff (by aesop) |>.mpr;
      exact dhyp! $ membership_iff (by aesop) |>.mp hr;
    -- apply membership_iff (by aesop) |>.mpr;
    -- sorry;

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
  induction q using Formula.rec' generalizing X with
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
        . exact GLSubformulas.mem_subformula_of_mem_box h_sub;
        . assumption;
        . assumption;
        . apply @ih Y (GLSubformulas.mem_of_mem_box h_sub) |>.not.mpr;
          apply Theory.not_mem_of_mem_neg Y.consistent (by aesop);
    . intro h Y RXY;
      apply ih (X := Y) (GLSubformulas.mem_of_mem_box h_sub) |>.mpr
      simp [Frame.Rel'] at RXY;
      exact RXY.1 q (GLSubformulas.mem_subformula_of_mem_box h_sub) h |>.1;
  | hverum =>
    simp [Satisfies];
    exact CompleteConsistentTheory.mem_verum (GLSubformulas.mem_subformula_of_mem_top h_sub);
  | hfalsum => simp [Satisfies];
  | hatom => simp [Satisfies];
  | hand q r ihq ihr =>
    constructor;
    . intro h; simp [Satisfies] at h;
      have ⟨hq₁, hq₂⟩ := GLSubformulas.mem_of_mem_and h_sub;
      apply iff_mem_and (GLSubformulas.mem_subformula_of_mem_and h_sub) |>.mpr;
      constructor;
      . apply ihq hq₁ |>.mp h.1;
      . apply ihr hq₂ |>.mp h.2;
    . intro h;
      have ⟨hq₁, hq₂⟩ := GLSubformulas.mem_of_mem_and h_sub;
      constructor;
      . apply ihq hq₁ |>.mpr;
        exact CompleteConsistentTheory.iff_mem_and (GLSubformulas.mem_subformula_of_mem_and h_sub) |>.mp h |>.1;
      . apply ihr hq₂ |>.mpr;
        exact CompleteConsistentTheory.iff_mem_and (GLSubformulas.mem_subformula_of_mem_and h_sub) |>.mp h |>.2;
  | hor q r ihq ihr =>
    constructor;
    . intro h; simp [Satisfies] at h;
      have ⟨hq₁, hq₂⟩ := GLSubformulas.mem_of_mem_or h_sub;
      apply iff_mem_or (GLSubformulas.mem_subformula_of_mem_or h_sub) |>.mpr;
      rcases h with h | h;
      . left; apply ihq (X := X) hq₁ |>.mp h;
      . right; apply ihr (X := X) hq₂ |>.mp h;
    . intro h;
      have ⟨hq₁, hq₂⟩ := GLSubformulas.mem_of_mem_or h_sub;
      rcases CompleteConsistentTheory.iff_mem_or (GLSubformulas.mem_subformula_of_mem_or h_sub) |>.mp h with h | h;
      . left; apply ihq (X := X) hq₁ |>.mpr; exact h;
      . right; apply ihr (X := X) hq₂ |>.mpr; exact h;
  | himp q r ihq ihr =>
    replace h_sub : q ⟶ r ∈ 𝒮 p := GLSubformulas.mem_subformula_of_mem_imp h_sub;
    have : q ∈ 𝒮 p := Subformulas.mem_imp₁ $ h_sub;
    have : r ∈ 𝒮 p := Subformulas.mem_imp₂ $ h_sub;

    constructor;
    . intro h; replace h := not_or_of_imp h;
      rcases h with (hq | hr);
      . replace hq := ihq (by aesop) |>.not.mp hq;
        apply membership_iff h_sub |>.mpr;
        by_cases q.negated;
        . sorry;
        . sorry;

      . replace hr := ihr (by aesop) |>.mp hr;
        apply membership_iff h_sub |>.mpr;
        exact System.dhyp! $ membership_iff (by aesop) |>.mp hr;
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : q ∈ X.theory := ihq (by aesop) |>.mp hq;
      replace hq : X.theory *⊢[𝐆𝐋]! q  := membership_iff (by aesop) |>.mp hq;

      replace hr : r ∉ X.theory := ihr (by aesop) |>.not.mp hr;
      replace hr : X.theory *⊬[𝐆𝐋]! r  := membership_iff (by aesop) |>.not.mp hr;

      by_contra hqr;
      replace hqr : X.theory *⊢[𝐆𝐋]! q ⟶ r := membership_iff h_sub |>.mp hqr;
      have : X.theory *⊢[𝐆𝐋]! r := hqr ⨀ hq;
      contradiction;
  | hneg q ihq =>
    constructor;
    . intro h; simp [Satisfies] at h;
      sorry;
    . intro h hnq;
      sorry;

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
