import Foundation.ProvabilityLogic.Basic
import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot

namespace LO

namespace Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Classical 𝓢]
         {p q r : F}
         {Γ Δ : List F}

lemma conj_disj_demorgan₂'! (h : 𝓢 ⊢! ⋀Γ.map (∼·)) : 𝓢 ⊢! ∼⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q => simp_all;
  | hcons q Γ hΓ ih =>
    replace h : 𝓢 ⊢! ∼q ⋏ (⋀Γ.map (∼·)) := by
      have e := List.conj₂_cons_nonempty (a := ∼q) (as := Γ.map (∼·)) (by simpa using hΓ);
      simpa [←e] using h;
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    apply demorgan₂'!;
    apply and₃'!;
    . exact and₁'! h;
    . exact ih $ and₂'! h

lemma conj_disj_demorgan₂_suppl'! (h : 𝓢 ⊢! p ➝ ⋀Γ.map (∼·)) : 𝓢 ⊢! p ➝ ∼⋁Γ :=
  deduct'! $ conj_disj_demorgan₂'! $ (of'! h) ⨀ by_axm!

omit [DecidableEq F] in
lemma disj_mem! (h : p ∈ Γ) : 𝓢 ⊢! p ➝ ⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp at h;
  | hsingle q =>
    replace h : p = q := by simpa using h;
    subst h;
    simp;
  | hcons q Γ hΓ ih =>
    replace h : p = q ∨ p ∈ Γ := by simpa using h;
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    rcases h with (rfl | h);
    . exact or₁!;
    . exact imply_right_or'! $ ih h

lemma not_imply_prem''! (hpq : 𝓢 ⊢! p ➝ q) (hpnr : 𝓢 ⊢! p ➝ ∼r) : 𝓢 ⊢! p ➝ ∼(q ➝ r) :=
  deduct'! $ (contra₀'! $ not_or_of_imply!) ⨀ (demorgan₂'! $ and₃'! (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

lemma disj_intro! (h : ∀ q ∈ Γ, 𝓢 ⊢! q ➝ p) : 𝓢 ⊢! ⋁Γ ➝ p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q => simp_all;
  | hcons q Γ hΓ ih =>
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    obtain ⟨h₁, h₂⟩ := by simpa using h;
    replace h₂ := ih h₂;
    exact or₃''! h₁ h₂;

lemma disj_intro'! (h : ∀ q ∈ Γ, 𝓢 ⊢! q ➝ p) : 𝓢 ⊢! ⋁Γ ➝ p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q => simp_all;
  | hcons q Γ hΓ ih =>
    simp [List.disj₂_cons_nonempty (a := q) hΓ];
    obtain ⟨h₁, h₂⟩ := by simpa using h;
    replace h₂ := ih h₂;
    exact or₃''! h₁ h₂;

lemma disj_outro! [Entailment.Consistent 𝓢]
  (h₁ : 𝓢 ⊢! ⋁Γ) (h₂ : ∀ q ∈ Γ, 𝓢 ⊢! q ➝ p) : 𝓢 ⊢! p := by
  induction Γ using List.induction_with_singleton with
  | hnil =>
    obtain ⟨f, hf⟩ := Consistent.exists_unprovable (𝓢 := 𝓢) (by assumption);
    have : 𝓢 ⊢! f := efq'! $ by simpa using h₁;
    contradiction;
  | hsingle r =>
    simp_all;
    exact h₂ ⨀ h₁;
  | hcons q Γ hΓ ih =>
    simp_all;
    have ⟨h₂₁, h₂₂⟩ := h₂;
    apply or₃'''! (d₃ := h₁);
    . exact h₂₁;
    . apply disj_intro!;
      exact h₂₂;

lemma cancel_or_left! (hpq : 𝓢 ⊢! p ⋎ q) (hp : 𝓢 ⊢! ∼p) : 𝓢 ⊢! q := by
  apply or₃'''! (𝓢 := 𝓢) (φ := p) (ψ := q) (χ := q);
  . apply imply_of_not_or'!;
    apply or₁'!;
    apply hp;
  . simp;
  . assumption;

lemma cancel_or_right! (hpq : 𝓢 ⊢! p ⋎ q) (hq : 𝓢 ⊢! ∼q) : 𝓢 ⊢! p := by
  apply cancel_or_left! (p := q) (q := p);
  . exact or_comm'! hpq;
  . exact hq;

lemma disj_tail! (Γ_nil : Γ.length > 0) (h₁ : 𝓢 ⊢! ⋁Γ) (h₂ : 𝓢 ⊢! ∼Γ[0]) : 𝓢 ⊢! ⋁(Γ.tail) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp at Γ_nil;
  | hsingle q =>
    simp at h₁ h₂;
    replace h₂ := neg_equiv'!.mp h₂;
    exact efq'! $ h₂ ⨀ h₁
  | hcons q Γ hΓ ih =>
    simp_all;
    exact cancel_or_left! h₁ h₂;

end Entailment

namespace ProvabilityLogic

open Entailment Entailment.FiniteContext
open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

variable {α : Type u}
         {L} [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T T : Theory L} {𝔅 : ProvabilityPredicate T T} [𝔅.HBL]
         {M₁ : Kripke.Model} {r₁ : M₁.World} [M₁.IsFiniteTree r₁]
         {A B : Modal.Formula _}

structure SolovaySentences
  {T U : FirstOrder.Theory L}
  (𝔅 : ProvabilityPredicate T U) [𝔅.HBL]
  (M₁ : Kripke.Model) (r₁ : M₁.World) [M₁.IsFiniteTree r₁]
  where
  σ : (M₁.extendRoot r₁).World → Sentence L
  SC1 : ∀ i j, i ≠ j → T ⊢!. σ i ➝ ∼σ j
  SC2 : ∀ i j, i ≺ j → T ⊢!. σ i ➝ ∼𝔅 (∼(σ j))
  SC3 : ∀ i, (Model.extendRoot.root (M := M₁) (r := r₁)) ≺ i →
    letI ι := { j | i ≺ j };
    T ⊢!. σ i ➝ 𝔅 ((ι.toFinite.toFinset.image σ).disj)
  SC4 : T ⊬. ∼(σ r₁)

instance : CoeFun (SolovaySentences 𝔅 M₁ r₁) (λ _ => (M₁.extendRoot r₁).World → Sentence L) := ⟨λ σ => σ.σ⟩

noncomputable def SolovaySentences.realization (σ : SolovaySentences 𝔅 M₁ r₁) : Realization L :=
  λ a =>
    letI ι := { i : (M₁.extendRoot r₁).World | i ⊧ (.atom a) };
    haveI : Finite ↑ι := by
      apply
        @Subtype.finite (α := (M₁.extendRoot r₁).World)
        $ Frame.extendRoot.instIsFiniteTree (r := r₁) |>.toIsFinite.world_finite;
    (ι.toFinite.toFinset.image σ).disj

variable {σ : SolovaySentences 𝔅 M₁ r₁}

theorem mainlemma {i : (M₁.extendRoot r₁).World} :
  (i ⊧ A → T ⊢!. (σ i) ➝ (σ.realization.interpret 𝔅 A)) ∧
  (¬i ⊧ A → T ⊢!. (σ i) ➝ ∼(σ.realization.interpret 𝔅 A))
  := by
  induction A using Formula.rec' generalizing i with
  | hfalsum => simp [Realization.interpret, Semantics.Realize, Satisfies];
  | hatom a =>
    simp [Realization.interpret, SolovaySentences.realization, Satisfies, SolovaySentences.realization];
    constructor;
    . intro h;
      sorry;
    . intro h;
      sorry;
  | himp A B ihA ihB =>
    simp [Realization.interpret];
    constructor;
    . intro h;
      rcases Satisfies.imp_def₂.mp h with (hA | hB);
      . exact imp_trans''! (ihA.2 hA) efq_imply_not₁!;
      . exact imp_trans''! (ihB.1 hB) imply₁!;
    . intro hA hB;
      exact not_imply_prem''! (ihA.1 hA) (ihB.2 hB);
  | hbox A ihA =>
    simp [Realization.interpret];
    constructor;
    . intro h;
      apply imp_trans''! $ σ.SC3 i (by sorry);
      apply 𝔅.prov_distribute_imply;
      -- apply disj_intro!;
      sorry;
    . intro h;
      have := Satisfies.box_def.not.mp h;
      push_neg at this;
      obtain ⟨j, Rij, hA⟩ := this;
      have : T ⊢!. ∼𝔅 (∼σ.σ j) ➝ ∼𝔅 (σ.realization.interpret 𝔅 A) := contra₀'! $ 𝔅.prov_distribute_imply $ contra₁'! $ ihA.2 hA;
      exact imp_trans''! (σ.SC2 i j Rij) this;

theorem arithmetical_completeness_GL : (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) → A ∈ Logic.GL := by
  contrapose;
  intro hA;
  push_neg;
  obtain ⟨M₁, r₁, _, hA₁⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
  let σ : SolovaySentences 𝔅 M₁ r₁ := by sorry; -- TODO: Sect 2.1
  use σ.realization;

  have : T ⊢!. σ r₁ ➝ σ.realization.interpret 𝔅 (∼A) := mainlemma (σ := σ) (A := ∼A) (i := r₁) |>.1 $ by
    apply Model.extendRoot.modal_equivalence_original_world.mp;
    exact hA₁;
  replace : T ⊢!. σ.realization.interpret 𝔅 A ➝ ∼(σ r₁) := by
    apply contra₁'!;
    apply imp_trans''! this;
    apply and₂'! neg_equiv!;

  by_contra hC;
  have : T ⊢!. ∼(σ r₁) := this ⨀ hC;
  exact σ.SC4 this;

end ProvabilityLogic

end LO
