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
         {φ ψ ξ : F}
         {Γ Δ : List F}
         {ι} [Fintype ι] {Φ : ι → F}

lemma not_imply_prem''! (hpq : 𝓢 ⊢! φ ➝ ψ) (hpnr : 𝓢 ⊢! φ ➝ ∼ξ) : 𝓢 ⊢! φ ➝ ∼(ψ ➝ ξ) :=
  deduct'! $ (contra₀'! $ not_or_of_imply!) ⨀ (demorgan₂'! $ and₃'! (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

end Entailment


namespace Modal.Kripke

def ImmediateSuccessors {F : Kripke.Frame} (x : F.World) := { y // x ≺ y }
postfix:100 "↑ᵢ" => ImmediateSuccessors

end Modal.Kripke



namespace ProvabilityLogic

open Classical
open Entailment Entailment.FiniteContext
open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

variable {L} [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T] (𝔅 : ProvabilityPredicate T₀ T) [𝔅.HBL]
         {A B : Modal.Formula _}

-- TODO: cleanup
noncomputable instance {F₁ : Kripke.Frame} {r₁ : F₁.World} [F₁.IsFiniteTree r₁] : Fintype (F₁.extendRoot r₁).World := @Fintype.ofFinite _ $ Frame.extendRoot.instIsFiniteTree |>.toIsFinite.world_finite
noncomputable instance {M₁ : Kripke.Model} {r₁ : M₁.World} [M₁.IsFiniteTree r₁] : Fintype (M₁.extendRoot r₁).World := @Fintype.ofFinite _ $ Frame.extendRoot.instIsFiniteTree |>.toIsFinite.world_finite

structure SolovaySentences
  (F₁ : Kripke.Frame) (r₁ : F₁.World) [F₁.IsFiniteTree r₁]
  where
  σ : (F₁.extendRoot r₁).World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢!. σ i ➝ ∼σ j
  protected SC2 : ∀ i j, i ≺ j → T₀ ⊢!. σ i ➝ ∼𝔅 (∼(σ j))
  protected SC3 : ∀ i, Frame.extendRoot.root ≺ i → T₀ ⊢!. σ i ➝ 𝔅 (⩖ j ∈ { j : (F₁.extendRoot r₁).World | i ≺ j }, σ j)
  protected SC4 : T ⊬. ∼(σ r₁)

variable {𝔅}

namespace SolovaySentences

instance {F₁ : Kripke.Frame} {r₁ : F₁.World} [F₁.IsFiniteTree r₁] : CoeFun (SolovaySentences 𝔅 F₁ r₁) (λ _ => (F₁.extendRoot r₁) → Sentence L) := ⟨λ σ => σ.σ⟩

variable {M₁ : Model} {r₁ : M₁.World} [M₁.IsFiniteTree r₁] {σ : SolovaySentences 𝔅 M₁.toFrame r₁}

noncomputable def realization (σ : SolovaySentences 𝔅 M₁.toFrame r₁) : Realization L := λ a => ⩖ i ∈ { i : (M₁.extendRoot r₁).World | i ⊧ (.atom a) }, σ i

theorem mainlemma {i : M₁.World} :
  (i ⊧ A → T₀ ⊢!. (σ i) ➝ (σ.realization.interpret 𝔅 A)) ∧
  (¬i ⊧ A → T₀ ⊢!. (σ i) ➝ ∼(σ.realization.interpret 𝔅 A))
  := by
  induction A using Formula.rec' generalizing i with
  | hfalsum => simp [Realization.interpret, Semantics.Realize, Satisfies];
  | hatom a =>
    constructor;
    . intro h;
      apply imply_fdisj;
      simpa using h;
    . intro h;
      apply contra₁'!;
      apply fdisj_imply!;
      intro i hi;
      apply σ.SC1;
      by_contra hC; subst hC;
      apply h;
      simpa using hi;
  | himp A B ihA ihB =>
    simp only [Realization.interpret, Semantics.Imp.realize_imp, Classical.not_imp, and_imp];
    constructor;
    . intro h;
      rcases Satisfies.imp_def₂.mp h with (hA | hB);
      . exact imp_trans''! (ihA.2 hA) efq_imply_not₁!;
      . exact imp_trans''! (ihB.1 hB) imply₁!;
    . intro hA hB;
      exact not_imply_prem''! (ihA.1 hA) (ihB.2 hB);
  | hbox A ihA =>
    simp only [Realization.interpret];
    constructor;
    . intro h;
      apply imp_trans''! $ σ.SC3 i $ Model.extendRoot.rooted_original;
      apply 𝔅.prov_distribute_imply';
      apply fdisj_imply!;
      rintro j Rij;
      match j with
      | Sum.inl j => simp [Frame.Rel', Frame.extendRoot] at Rij
      | Sum.inr j => exact ihA.1 $ h j $ by simpa using Rij;
    . intro h;
      have := Satisfies.box_def.not.mp h;
      push_neg at this;
      obtain ⟨j, Rij, hA⟩ := this;
      have := contra₁'! $ ihA.2 hA;
      have : T₀ ⊢!. ∼𝔅 (∼σ.σ j) ➝ ∼𝔅 (σ.realization.interpret 𝔅 A) := contra₀'! $ 𝔅.prov_distribute_imply' $ contra₁'! $ ihA.2 hA;
      exact imp_trans''! (σ.SC2 i j Rij) this;

end SolovaySentences

theorem arithmetical_completeness_GL : (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) → A ∈ Logic.GL := by
  contrapose;
  intro hA;
  push_neg;
  obtain ⟨M₁, r₁, _, hA₁⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
  let σ : SolovaySentences 𝔅 M₁.toFrame r₁ := by sorry; -- TODO: Sect 2.1
  use σ.realization;

  have : T₀ ⊢!. σ r₁ ➝ σ.realization.interpret 𝔅 (∼A) := σ.mainlemma (A := ∼A) (i := r₁) |>.1 $ hA₁
  replace : T₀ ⊢!. σ.realization.interpret 𝔅 A ➝ ∼(σ r₁) := by
    apply contra₁'!;
    apply imp_trans''! this;
    apply and₂'! neg_equiv!;
  replace : T ⊢!. σ.realization.interpret 𝔅 A ➝ ∼(σ r₁) := WeakerThan.pbl this;

  by_contra hC;
  have : T ⊢!. ∼(σ r₁) := this ⨀ hC;
  exact σ.SC4 this;

end ProvabilityLogic

end LO
