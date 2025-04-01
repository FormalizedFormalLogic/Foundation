import Foundation.ProvabilityLogic.Basic
import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot
import Foundation.Incompleteness.Arith.WitnessComparizon
import Foundation.Incompleteness.Arith.FixedPoint
import Foundation.Incompleteness.Arith.ConsistencyPredicate

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

def twoPointAux (t : 𝐖 → Semiterm ℒₒᵣ Empty N) (i j : 𝐖) : Semisentence ℒₒᵣ N :=
  ⩕ k ∈ { k : 𝐖 | i ≺ k }, (negativeSuccessorDef T)/[t j, t k]

def θChainAux (t : 𝐖 → Semiterm ℒₒᵣ Empty N) {i j : 𝐖} : WChain i j → Semisentence ℒₒᵣ N
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
    θChainAux t ⟨l :: ε, this⟩ ⋏ twoPointAux T t l k

def θAux (t : 𝐖 → Semiterm ℒₒᵣ Empty N) (i : 𝐖) : Semisentence ℒₒᵣ N :=
  haveI := Fintype.ofFinite (WChain r i)
  ⩖ ε : WChain r i, θChainAux T t ε

lemma rew_twoPointAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : 𝐖 → Semiterm ℒₒᵣ Empty N) :
    Rew.substs w ▹ twoPointAux T t i j = twoPointAux T (fun i ↦ Rew.substs w (t i)) i j := by
  simp [twoPointAux, Finset.map_conj', Function.comp_def,
    ←TransitiveRewriting.comp_app, Rew.substs_comp_substs]

lemma rew_θChainAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : 𝐖 → Semiterm ℒₒᵣ Empty N) (ε : WChain i j) :
    Rew.substs w ▹ θChainAux T t ε = θChainAux T (fun i ↦ Rew.substs w (t i)) ε := by
  match ε with
  |         ⟨[k], h⟩ => simp [θChainAux]
  | ⟨k :: l :: ε, h⟩ =>
    have : (l :: ε).ChainI (· ≻ ·) l j := by
      rcases h
      case cons m lt h =>
        rcases h
        case singleton => simp
        case cons n ln h =>
          exact h.cons ln
    simp [θChainAux, rew_θChainAux w _ ⟨l :: ε, this⟩, rew_twoPointAux]

lemma rew_θAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : 𝐖 → Semiterm ℒₒᵣ Empty N) (i : 𝐖) :
    Rew.substs w ▹ θAux T t i = θAux T (fun i ↦ Rew.substs w (t i)) i := by
  simp [Finset.map_disj', θAux]
  sorry

def solovay (i : 𝐖) : Sentence ℒₒᵣ := multifixpoint
  (fun j ↦
    let jj := (Fintype.equivFin 𝐖).symm j
    θAux T (fun i ↦ #(Fintype.equivFin 𝐖 i)) jj ⋏ ⩕ k ∈ { k : 𝐖 | jj ≺ k }, T.consistencyₐ/[#(Fintype.equivFin 𝐖 k)])
  (Fintype.equivFin 𝐖 i)

def θChain {i j : 𝐖} (ε : WChain i j) : Sentence ℒₒᵣ := θChainAux T (fun i ↦ ⌜solovay T i⌝) ε

def θ (i : 𝐖) : Sentence ℒₒᵣ := θAux T (fun i ↦ ⌜solovay T i⌝) i

lemma solovay_diag (i : 𝐖) :
    𝐈𝚺₁ ⊢!. solovay T i ⭤ θ T i ⋏ ⩕ k ∈ { k : 𝐖 | i ≺ k }, T.consistencyₐ/[⌜solovay T k⌝] := by
  have : 𝐈𝚺₁ ⊢!. solovay T i ⭤
      (Rew.substs fun j ↦ ⌜solovay T ((Fintype.equivFin 𝐖).symm j)⌝) ▹
        (θAux T (fun i ↦ #(Fintype.equivFin 𝐖 i)) i ⋏ ⩕ k ∈ { k : 𝐖 | i ≺ k }, T.consistencyₐ/[#(Fintype.equivFin 𝐖 k)]) := by
    simpa [solovay] using multidiagonal (T := 𝐈𝚺₁) (i := Fintype.equivFin 𝐖 i)
      (fun j ↦
        let jj := (Fintype.equivFin 𝐖).symm j
        θAux T (fun i ↦ #(Fintype.equivFin 𝐖 i)) jj ⋏ ⩕ k ∈ { k : 𝐖 | jj ≺ k }, T.consistencyₐ/[#(Fintype.equivFin 𝐖 k)])
  simpa [θ, Finset.hom_conj', Function.comp_def, rew_θAux, ←TransitiveRewriting.comp_app, Rew.substs_comp_substs] using this

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
