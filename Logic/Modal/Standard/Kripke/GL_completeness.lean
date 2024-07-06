import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Soundness
import Logic.Modal.Standard.Kripke.GL

namespace LO.Modal.Standard

open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]

section Completeness

variable [DecidableEq α]
variable {Λ : DeductionParameter α}

namespace Formula

def negated : Formula α → Bool
  | ~_ => true
  | _  => false

lemma negated_iff {p : Formula α} : p.negated ↔ ∃ q, p = ~q := by
  induction p using Formula.rec' <;> simp [negated]

lemma not_negated_iff {p : Formula α} : ¬p.negated ↔ ∀ q, p ≠ ~q := by
  induction p using Formula.rec' <;> simp [negated]

def complement (p : Formula α) : Formula α := if p.negated then p else ~p
postfix:80 "⁻" => complement

lemma eq_complement_negated {p : Formula α} (hp : p.negated) : p⁻ = p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]

lemma eq_complement_not_negated {p : Formula α} (hp : ¬p.negated) : p⁻ = ~p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]

/-
@[simp]
lemma eq_complement_complement {p : Formula α} : p⁻⁻ = p := by
  induction p using Formula.rec' with
  | hneg p ih =>
    simp [complement, negated]
  | hverum =>
    simp [complement, negated]
    sorry;
  | hfalsum =>
    simp [complement, negated]
    sorry;
  | hatom a =>
    simp [complement, negated]
    sorry;
  | himp p q ih₁ ih₂ =>
    dsimp [complement, negated]
    sorry;
-/

-- notation "Sub(" p ")" => Formula.Subformulas p
prefix:70 "𝒮 " => Formula.Subformulas

abbrev ComplementSubformula (p : Formula α) : Finset (Formula α) := (𝒮 p) ∪ (Finset.image (·⁻) $ 𝒮 p)
prefix:70 "𝒮⁻ " => Formula.ComplementSubformula

abbrev neg_complete_subformulas (p : Formula α) : Finset (Formula α) := (𝒮 p) ∪ (Finset.image (~·) $ 𝒮 p)
prefix:70 "𝒮ᶜ " => Formula.neg_complete_subformulas

namespace neg_complete_subformulas

variable {p q r : Formula α}

@[simp] lemma mem_self : p ∈ 𝒮ᶜ p := by simp [neg_complete_subformulas]
@[simp] lemma mem_neg_self : ~p ∈ 𝒮ᶜ p := by simp [neg_complete_subformulas]

/-
lemma neg_mem : ~q ∈ 𝒮⁻ p → q ∈ 𝒮⁻ p := by
  simp;
  rintro (hq₁ | ⟨r, hr₁, hr₂⟩);
  . right; use ~q;
    constructor;
    . assumption;
    . sorry;
  . left;
-/


lemma box_mem : □q ∈ 𝒮ᶜ p → q ∈ 𝒮ᶜ p := by
  simp; intro h; replace h := Formula.Subformulas.mem_box h;
  aesop;

lemma and_mem : q ⋏ r ∈ 𝒮ᶜ p → q ∈ 𝒮ᶜ p ∧ r ∈ 𝒮ᶜ p := by
  simp; intro h; replace h := Formula.Subformulas.mem_and h;
  aesop;

lemma or_mem : q ⋎ r ∈ 𝒮ᶜ p → q ∈ 𝒮ᶜ p ∧ r ∈ 𝒮ᶜ p := by
  simp; intro h; replace h := Formula.Subformulas.mem_or h;
  aesop;

lemma imp_mem : q ⟶ r ∈ 𝒮ᶜ p → q ∈ 𝒮ᶜ p ∧ r ∈ 𝒮ᶜ p := by
  simp; intro h; replace h := Formula.Subformulas.mem_imp h;
  aesop;


end neg_complete_subformulas

def atoms: Formula α → Finset (α)
  | ⊤      => ∅
  | ⊥      => ∅
  | atom a => {a}
  | ~p     => atoms p
  | box p  => atoms p
  | p ⟶ q => atoms p ∪ atoms q
  | p ⋏ q  => atoms p ∪ atoms q
  | p ⋎ q  => atoms p ∪ atoms q
prefix:70 "𝒜 " => Formula.atoms

@[simp]
lemma mem_atoms_iff_mem_subformulae {a : α} : a ∈ 𝒜 p ↔ (atom a) ∈ 𝒮 p := by
  induction p using Formula.rec' <;> simp_all [Subformulas, atoms];


end Formula


namespace Theory

variable {T U : Theory α} (T_subset : T ⊆ U) (T_consis : (Λ)-Consistent T)

lemma exists_maximal_consistent_theory₂
  : ∃ Z, ((Λ)-Consistent Z ∧ Z ⊆ U) ∧ T ⊆ Z ∧ ∀ {X}, ((Λ)-Consistent X ∧ X ⊆ U) → Z ⊆ X → X = Z
  := zorn_subset_nonempty { T : Theory α | (Λ)-Consistent T ∧ T ⊆ U } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    refine ⟨⟨?h₁, ?h₂⟩, ?h₃⟩;
    . intro Γ hΓ; by_contra hC;
      obtain ⟨X, hXc, hXs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain (s := ↑Γ.toFinset) (by simp)
        (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hXs;
      have : (Λ)-Consistent X := hc hXc |>.1;
      have : ¬(Λ)-Consistent X := by
        simp [Theory.Consistent];
        use Γ;
        constructor;
        . apply hXs;
        . assumption;
      contradiction;
    . apply Set.sUnion_subset;
      intro T hT;
      apply hc hT |>.2;
    . intro X hX;
      exact Set.subset_sUnion_of_mem hX;
  ) T ⟨T_consis, T_subset⟩
protected alias lindenbaum₂ := exists_maximal_consistent_theory₂

lemma mem_not_either : ¬(p ∈ T ∧ ~p ∈ T) := by
  by_contra hC;
  have : Λ ⊬! p ⋏ ~p ⟶ ⊥ := by simpa using T_consis (Γ := [p, ~p]) (by aesop);
  have : Λ ⊢! p ⋏ ~p ⟶ ⊥ := intro_bot_of_and!;
  contradiction;

lemma not_mem_neg_of_mem : p ∈ T → ~p ∉ T := by
  have := mem_not_either (T_consis := T_consis) (p := p);
  simp_all;

lemma not_mem_of_mem_neg : ~p ∈ T → p ∉ T := by
  contrapose;
  have := mem_not_either (T_consis := T_consis) (p := p);
  simp_all;

end Theory

structure SubsetMaximalConsistentTheory (Λ : DeductionParameter α) (S : Theory α) where
  T : Theory α
  T_consistent : (Λ)-Consistent T
  T_subset : T ⊆ S
  T_maximal : ∀ U ⊆ S, T ⊂ U → ¬(Λ)-Consistent U

notation "(" Λ "," T ")-MCT" => SubsetMaximalConsistentTheory Λ T

instance : CoeSort (Λ, S)-MCT (Theory α) := ⟨λ Ω => Ω.T⟩

namespace SubsetMaximalConsistentTheory

open Theory

lemma exists_theory {T : Theory α} (T_subset : T ⊆ S) (T_consis : (Λ)-Consistent T) : ∃ Ω : (Λ, S)-MCT, (T ⊆ Ω) := by
  have ⟨Ω, ⟨Ω_consis, Ω_subset⟩, _, Ω_maximal⟩ := Theory.lindenbaum₂ T_subset T_consis;
  use {
    T := Ω,
    T_subset := Ω_subset,
    T_consistent := Ω_consis,
    T_maximal := by
      rintro X hXU ⟨hΩX₁, hΩX₂⟩;
      by_contra hC;
      have := Ω_maximal ⟨hC, hXU⟩ hΩX₁; subst this;
      contradiction;
  };
alias lindenbaum := exists_theory

noncomputable instance instInhabitedSMCT (T) [System.Consistent Λ] : Inhabited (Λ, T)-MCT := ⟨lindenbaum (T := ∅) (S := T) (by tauto) Theory.emptyset_consistent |>.choose⟩

end SubsetMaximalConsistentTheory


def Formula.extended_subformulae (p : Formula α) : Finset (Formula α) := 𝒮 p ∪ ((𝒮 p).image (·⁻)) ∪ {⊤, ⊥}
prefix:70 "𝒮* " => Formula.extended_subformulae

namespace Formula.extended_subformulae

variable {p q : Formula α}

@[simp] lemma mem_top : ⊤ ∈ 𝒮* p := by simp [extended_subformulae]
@[simp] lemma mem_bot : ⊥ ∈ 𝒮* p := by simp [extended_subformulae]

@[simp] lemma mem : q ∈ 𝒮 p → q ∈ 𝒮* p := by simp_all [extended_subformulae];

@[simp]
lemma mem_not_negated (hq : ¬q.negated) : q ∈ 𝒮 p → ~q ∈ 𝒮* p := by
  simp [extended_subformulae];
  intro h; right; use q;
  constructor;
  . assumption;
  . exact eq_complement_not_negated hq;

-- @[simp] lemma mem_self : p ∈ 𝒮* p := by simp;
-- @[simp] lemma mem_neg_self : ~p ∈ 𝒮* p := by simp;

-- lemma mem_neg {p q : Formula α} : ~q ∈ 𝒮* p → q ∈ 𝒮* p := by simp [extended_subformulae]

@[simp] lemma mem_complement_self : p⁻ ∈ 𝒮* p := by simp [extended_subformulae]; aesop;

end Formula.extended_subformulae


abbrev ComplementSubsetMaximalConsistentTheory (Λ : DeductionParameter α) (p : Formula α) := (Λ, 𝒮ᶜ p)-MCT
notation "(" Λ "," p ")-CMCT" => ComplementSubsetMaximalConsistentTheory Λ p


namespace ComplementSubsetMaximalConsistentTheory

open Formula (negated extended_subformulae)

lemma lindenbaum {T : Theory α} (T_subset : T ⊆ 𝒮ᶜ p) (T_consis : (Λ)-Consistent T) : ∃ Ω : (Λ, p)-CMCT, T ⊆ Ω.T := SubsetMaximalConsistentTheory.lindenbaum T_subset T_consis

noncomputable instance instInhabitedCMCT (p) [System.Consistent Λ] : Inhabited (Λ, p)-CMCT := ⟨lindenbaum (T := ∅) (p := p) (by tauto) Theory.emptyset_consistent |>.choose⟩



variable {p q : Formula α}
         {Ω : (Λ, p)-CMCT}

variable (q_sub : q ∈ 𝒮 p := by assumption)

lemma subset_mem_self_csubformula : (insert q Ω.T) ⊆ 𝒮ᶜ p := by
  apply Set.insert_subset_iff.mpr;
  constructor;
  . aesop;
  . exact Ω.T_subset;

lemma subset_not_mem_self_csubformula : (insert (~q) Ω.T) ⊆ 𝒮ᶜ p := by
  apply Set.insert_subset_iff.mpr;
  constructor;
  . aesop;
  . exact Ω.T_subset;

lemma either_mem : q ∈ Ω.T ∨ ~q ∈ Ω.T := by
  by_contra hC; push_neg at hC;
  cases Theory.either_consistent Ω.T_consistent q with
  | inl h => have := Ω.T_maximal _ (subset_mem_self_csubformula) (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.T_maximal _ (subset_not_mem_self_csubformula) (Set.ssubset_insert hC.2); contradiction;

lemma membership_iff : (q ∈ Ω.T) ↔ (Ω *⊢[Λ]! q) := by
  constructor;
  . intro hp'; exact Context.by_axm! hp';
  . intro hp';
    suffices ~q ∉ Ω.T by apply or_iff_not_imp_right.mp $ either_mem; assumption;
    by_contra hC;
    have hn_ps : Ω *⊢[Λ]! ~q := Context.by_axm! hC;
    have : Ω *⊢[Λ]! ⊥ := neg_mdp! hn_ps hp';
    have : Ω *⊬[Λ]! ⊥:= unprovable_falsum Ω.T_consistent;
    contradiction;

@[simp]
lemma mem_atom {a : α} : atom a ∈ Ω.T → a ∈ 𝒜 p := by
  intro h;
  have : atom a ∈ 𝒮ᶜ p := Ω.T_subset h;
  have : atom a ∈ 𝒮 p := by simpa [extended_subformulae] using this;
  exact Formula.mem_atoms_iff_mem_subformulae.mpr this;

lemma not_mem_neg_of_mem : q ∈ Ω.T → ~q ∉ Ω.T := by
  have := Theory.mem_not_either (T_consis := Ω.T_consistent) (p := q);
  simp_all;

lemma not_mem_of_mem_neg : ~q ∈ Ω.T → q ∉ Ω.T := by
  contrapose;
  have := Theory.mem_not_either (T_consis := Ω.T_consistent) (p := q);
  simp_all;

lemma iff_mem_and : (q ⋏ r ∈ Ω.T) ↔ (q ∈ Ω.T) ∧ (r ∈ Ω.T) := by
  constructor;
  . have := Ω.T_subset;
    intro hqr;
    have hqr₂ := membership_iff (by sorry) |>.mp hqr;
    constructor;
    . apply membership_iff (by sorry) |>.mpr; exact and₁'! hqr₂;
    . apply membership_iff (by sorry) |>.mpr; exact and₂'! hqr₂;
  . rintro ⟨hp, hq⟩;
    apply membership_iff (by sorry) |>.mpr;
    exact and₃'! (membership_iff (by sorry) |>.mp hp) (membership_iff (by sorry) |>.mp hq);

end ComplementSubsetMaximalConsistentTheory

-- noncomputable instance {p : Formula α} : Inhabited (𝐆𝐋, ↑(Sub(p) : Theory α))-MCT := inferInstance

namespace Kripke

noncomputable def GLCanonicalFrame (p : Formula α) : Kripke.FiniteFrame where
  World := (𝐆𝐋, p)-CMCT
  World_finite := by
    simp;
    -- because `𝓢* p` is finite
    sorry;
  Rel X Y := (∀ q ∈ □''⁻¹X.T, q ∈ Y.T ∧ □q ∈ Y.T) ∧ (∃ q ∈ □''⁻¹Y, ~(□q) ∈ X.T)
    -- (∀ q ∈ □''⁻¹X.T, q ∈ Y.T ∧ □q ∈ Y.T) ∧ (∃ q ∈ □''⁻¹Y, □q ∉ X.T)

lemma GLCanonicalFrame.Rel_def {p : Formula α} {X Y : (GLCanonicalFrame p).World}
  : X ≺ Y ↔ (∀ q ∈ □''⁻¹X.T, q ∈ Y.T ∧ □q ∈ Y.T) ∧ (∃ q ∈ □''⁻¹Y.T, ~(□q) ∈ X.T) := by rfl

noncomputable def GLCanonicalModel (p : Formula α) : Kripke.FiniteModel α where
  Frame := GLCanonicalFrame p
  Valuation X a := a ∈ p.atoms ∧ (atom a) ∈ X.T

open Formula (neg_complete_subformulas)
open ComplementSubsetMaximalConsistentTheory

lemma GLCanonicalModel.truthlemma {q : Formula α} (q_sub : q ∈ 𝒮ᶜ p) : ∀ {X : (GLCanonicalModel p).World}, X ⊧ q ↔ (q ∈ X.T) := by
  intro X;
  induction q using Formula.rec' generalizing X with
  | hbox q ih =>
    constructor;
    . contrapose; intro h;
      simp [Kripke.Satisfies];
      obtain ⟨Y, hY⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {□q, ~q} ∪ (□''⁻¹X.T ∪ □''□''⁻¹X.T)) (p := p)
        (by
          simp only [Set.union_subset_iff, Set.preimage_union, Finset.coe_image];
          refine ⟨?h₁, ?h₂, ?h₃⟩;
          case h₃ => exact Set.Subset.trans (by aesop) X.T_subset;
          case h₂ => exact Set.Subset.trans (by sorry) X.T_subset;
          case h₁ =>
            apply Set.insert_subset_iff.mpr;
            constructor;
            . simp_all;
            . simp_all; right; exact Formula.Subformulas.mem_box q_sub;
        )
        (by
          intro Γ hΓ hC;
          sorry;
          -- simp at hΓ;
        )
      use Y;
      simp only [Set.union_subset_iff, Set.preimage_union] at hY;
      have ⟨hY₁, hY₂, hY₃⟩ := hY; clear hY;
      constructor;
      . apply GLCanonicalFrame.Rel_def.mpr;
        constructor;
        . intro r hr;
          constructor;
          . exact hY₂ hr;
          . apply hY₃; simpa using hr;
        . use q;
          constructor;
          . apply hY₁; tauto;
          . sorry;
      . apply ih (neg_complete_subformulas.box_mem q_sub) |>.not.mpr;
        apply not_mem_of_mem_neg;
        apply hY₁;
        tauto;
    . intro h Y hXY;
      have ⟨h₁, ⟨r, hr₁, hr₂⟩⟩ := GLCanonicalFrame.Rel_def.mp hXY;
      exact ih (neg_complete_subformulas.box_mem q_sub) |>.mpr (h₁ _ h |>.1);
  | hatom a =>
    simp [GLCanonicalModel, Kripke.Satisfies];
    intro ha;
    exact Formula.mem_atoms_iff_mem_subformulae.mp $ mem_atom ha;
  | hverum =>
    simp;
    have := X.T_subset;
    sorry;
  | hfalsum =>
    simp;
    sorry;
  | hneg q ihq =>
    constructor;
    . sorry;
    . sorry;
  | hand q r ihq ihr =>
    replace ⟨q_sub, r_sub⟩ := neg_complete_subformulas.and_mem q_sub;
    replace ihq := @ihq q_sub;
    replace ihr := @ihr r_sub;
    constructor;
    . rintro ⟨hq, hr⟩;
      have hq := ihq.mp hq;
      have hr := ihr.mp hr;
      sorry;
    . intro h;
      constructor;
      . apply ihq.mpr; sorry;
      . apply ihr.mpr; sorry;
  | hor q r ihq ihr =>
    replace ⟨q_sub, r_sub⟩ := neg_complete_subformulas.or_mem q_sub;
    replace ihq := @ihq q_sub;
    replace ihr := @ihr r_sub;
    constructor;
    . rintro (hq | hr);
      . sorry;
      . sorry;
    . intro h;
      sorry;
  | himp q r ihq ihr =>
    replace ⟨q_sub, r_sub⟩ := neg_complete_subformulas.imp_mem q_sub;
    replace ihq := @ihq q_sub;
    replace ihr := @ihr r_sub;
    constructor;
    . rintro hqr; simp at hqr;
      sorry;
    . intro h;
      sorry;

lemma exists_finite_frame : ¬𝔽ꟳ# ⊧ p ↔ ∃ F ∈ 𝔽.toFiniteFrameClass, ¬F# ⊧ p := by
  constructor;
  . simp;
  . rintro ⟨F, hF₁, hF₂⟩;
    simp; use F;
    constructor;
    . simp_all;
    . assumption;

lemma complete_of_mem_canonicalFrame {p : Formula α} : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLCanonicalFrame p);
  constructor;
  . refine ⟨?transtive, ?irreflexive⟩;
    . simp only [Transitive, GLCanonicalFrame];
      rintro X Y Z ⟨hXY, ⟨b, hb₁, hb₂⟩⟩ ⟨hYZ, ⟨c, _, _⟩⟩;
      constructor;
      . intro q hq; exact hYZ q $ (hXY q hq).2;
      . use b;
        constructor;
        . exact hYZ b hb₁ |>.2;
        . exact hb₂;
    . simp only [Irreflexive, GLCanonicalFrame]; push_neg;
      intro X hX q hq;
      have ⟨_, hq⟩ := hX q hq;
      exact not_mem_neg_of_mem hq;
  . simp [Kripke.ValidOnFrame, Kripke.ValidOnModel];
    use (GLCanonicalModel p).Valuation;
    obtain ⟨X, hX⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {~p}) (p := p) (by simp) (Theory.unprovable_iff_singleton_neg_consistent.mp h);
    use X;
    apply GLCanonicalModel.truthlemma (by simp) |>.not.mpr;
    apply not_mem_of_mem_neg;
    tauto;

instance GL_complete : Complete (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClassꟳ# := ⟨complete_of_mem_canonicalFrame⟩

end Kripke

end Completeness

end LO.Modal.Standard
