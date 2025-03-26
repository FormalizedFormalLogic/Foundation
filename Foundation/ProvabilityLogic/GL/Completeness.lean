import Foundation.ProvabilityLogic.Basic
import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot

namespace LO

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
    T ⊢!. σ i ➝ 𝔅 ((ι.toFinite.toFinset.image σ).conj)
  SC4 : T ⊬. ∼(σ r₁)

instance : CoeFun (SolovaySentences 𝔅 M₁ r₁) (λ _ => (M₁.extendRoot r₁).World → Sentence L) := ⟨λ σ => σ.σ⟩

noncomputable def SolovaySentences.realization (σ : SolovaySentences 𝔅 M₁ r₁) : Realization L :=
  λ a =>
    letI ι := { i : (M₁.extendRoot r₁).World | i ⊧ (.atom a) };
    haveI : Finite ↑ι := by sorry
    (ι.toFinite.toFinset.image σ).disj

variable {σ : SolovaySentences 𝔅 M₁ r₁}

-- Lemma 2.1
-- TODO: `↔`にするかNNFでやらないと証明がおそらく出来ない（`➝`で帰納法の仮定が通らない）
theorem mainlemma(h : Satisfies (M₁.extendRoot r₁) i A) : T ⊢!. (σ i) ➝ (σ.realization.interpret 𝔅 A) := by
  induction A using Formula.rec' with
  | hfalsum => simp [Satisfies] at h;
  | hatom a =>
    simp [Realization.interpret, SolovaySentences.realization];
    sorry;
  | himp A B ihA ihB =>
    simp [Realization.interpret, SolovaySentences.realization];
    rcases Satisfies.imp_def₂.mp h with (hA | hB);
    . sorry;
    . sorry;
  | hbox A ihA =>
    sorry

theorem arithmetical_completeness_GL : (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) → A ∈ Logic.GL := by
  contrapose;
  intro hA;
  push_neg;
  obtain ⟨M₁, r₁, _, hA₁⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
  let σ : SolovaySentences 𝔅 M₁ r₁ := by sorry; -- TODO: Sect 2.1
  use σ.realization;

  have : T ⊢!. σ r₁ ➝ σ.realization.interpret 𝔅 (∼A) := mainlemma (σ := σ) (A := ∼A) (i := r₁) $ by
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
