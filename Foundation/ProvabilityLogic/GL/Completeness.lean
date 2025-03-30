import Foundation.ProvabilityLogic.Basic
import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot
import Foundation.Incompleteness.Arith.WitnessComparizon

open Classical

noncomputable section

namespace LO.FirstOrder.Arith

namespace SolovaySentence

open LO.Arith

section model

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

/-- Provability predicate for arithmetic stronger than $\mathbf{R_0}$. -/
def NegativeSuccessor (φ ψ : V) : Prop := T.ProvabilityComparisonₐ (⌜ℒₒᵣ⌝.neg φ) (⌜ℒₒᵣ⌝.neg ψ)

lemma NegativeSuccessor.quote_iff_provabilityComparison {φ ψ : Sentence ℒₒᵣ} :
    NegativeSuccessor (V := V) T ⌜φ⌝ ⌜ψ⌝ ↔ T.ProvabilityComparisonₐ (V := V) ⌜∼φ⌝ ⌜∼ψ⌝ := by
  simp [NegativeSuccessor, quote_sentence_eq_quote_emb (∼φ), quote_sentence_eq_quote_emb (∼ψ)]

section

def negativeSuccessorDef : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, ∃ nψ, !(ℒₒᵣ).lDef.negDef nφ φ ∧ !(ℒₒᵣ).lDef.negDef nψ ψ ∧ !T.provabilityComparisonₐDef nφ nψ” (by simp)

lemma negativeSuccessor_defined : 𝚺₁-Relation (NegativeSuccessor T : V → V → Prop) via (negativeSuccessorDef T) := by
  intro v
  simp [negativeSuccessorDef, NegativeSuccessor, ((ℒₒᵣ).codeIn V).neg_defined.df.iff]

@[simp] lemma eval_negativeSuccessorDef (v) :
    Semiformula.Evalbm V v (negativeSuccessorDef T).val ↔ NegativeSuccessor T (v 0) (v 1) := (negativeSuccessor_defined T).df.iff v

instance negativeSuccessor_definable : 𝚺₁-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

/-- instance for definability tactic-/
instance negativeSuccessor_definable' : 𝚺-[0 + 1]-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

end

end model

open Modal ProvabilityLogic Kripke

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

variable {M : Kripke.Model} {r : M.World} [M.IsFiniteTree r] [Fintype M.World]

local notation "𝐖" => M.World

abbrev WChain (i j : 𝐖) := {l : List 𝐖 // l.ChainI (· ≻ ·) i j}

instance (i j : 𝐖) : Finite (WChain i j) :=
  List.ChainI.finite_of_irreflexive_of_transitive
    (by exact IsIrrefl.irrefl (r := (· ≺ ·)))
    (by intro x y z hxy hyz
        exact IsTrans.trans (r := (· ≺ ·)) z y x hyz hxy)
    i j

def twoPoint (i j : 𝐖) : Semisentence ℒₒᵣ (Fintype.card 𝐖) :=
  ⩕ k ∈ { k : 𝐖 | i ≺ k }, (negativeSuccessorDef T)/[#(Fintype.equivFin 𝐖 j), #(Fintype.equivFin 𝐖 k)]

def Φchain {i j : 𝐖} : WChain i j → Semisentence ℒₒᵣ (Fintype.card 𝐖)
  |         ⟨[k], h⟩ => ⊤
  | ⟨k :: l :: ε, h⟩ =>
    have e : i = k := by rcases h; rfl
    have : (l :: ε).ChainI (· ≻ ·) l j := by
      rcases h
      case cons m lt h =>
        rcases h
        case singleton => simp
        case cons n ln h =>
          exact h.cons ln
    Φchain ⟨l :: ε, this⟩ ⋏ twoPoint T l k

def Φ (i : 𝐖) : Semisentence ℒₒᵣ (Fintype.card 𝐖) :=
  haveI := Fintype.ofFinite (WChain r i)
  ⩖ ε : WChain r i, Φchain T ε

end SolovaySentence

end LO.FirstOrder.Arith

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
         (M₁ : Kripke.Model) (r₁ : M₁.World) [M₁.IsFiniteTree r₁]
         {A B : Modal.Formula _}

local notation "𝐖" => Frame.World <| Model.toFrame <| M₁.extendRoot r₁

-- TODO: cleanup
noncomputable instance : Fintype 𝐖 := @Fintype.ofFinite _ $ Frame.extendRoot.instIsFiniteTree |>.toIsFinite.world_finite

structure SolovaySentences where
  σ : (M₁.extendRoot r₁).World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢!. σ i ➝ ∼σ j
  protected SC2 : ∀ i j, i ≺ j → T₀ ⊢!. σ i ➝ ∼𝔅 (∼(σ j))
  protected SC3 : ∀ i, Model.extendRoot.root ≺ i → T₀ ⊢!. σ i ➝ 𝔅 (⩖ j ∈ { j : 𝐖 | i ≺ j }, σ j)
  protected SC4 : T ⊬. ∼(σ r₁)

variable {𝔅 M₁ r₁}

namespace SolovaySentences

instance : CoeFun (SolovaySentences 𝔅 M₁ r₁) (λ _ => 𝐖 → Sentence L) := ⟨λ σ => σ.σ⟩

noncomputable def realization (σ : SolovaySentences 𝔅 M₁ r₁) : Realization L := λ a => ⩖ i ∈ { i : 𝐖 | i ⊧ (.atom a) }, σ i

variable {σ : SolovaySentences 𝔅 M₁ r₁}

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
  let σ : SolovaySentences 𝔅 M₁ r₁ := by sorry; -- TODO: Sect 2.1
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
