import Foundation.ProvabilityLogic.Basic
import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot
import Foundation.Incompleteness.Arith.WitnessComparizon
import Foundation.Incompleteness.Arith.FixedPoint
import Foundation.Incompleteness.Arith.ConsistencyPredicate

open Classical

noncomputable section

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

namespace LO.FirstOrder.Arith

namespace SolovaySentence

open LO.Arith

variable (T : Theory ℒₒᵣ) [T.Delta1Definable]

section model

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

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

section stx

open Modal ProvabilityLogic Kripke

variable {F : Kripke.Frame} {r : F} [F.IsFiniteTree r] [Fintype F]

abbrev WChain (i j : F) := {l : List F // l.ChainI (· ≻ ·) j i}

instance (i j : F) : Finite (WChain j i) :=
  List.ChainI.finite_of_irreflexive_of_transitive
    (by exact IsIrrefl.irrefl (r := (· ≺ ·)))
    (by intro x y z hxy hyz
        exact IsTrans.trans (r := (· ≺ ·)) z y x hyz hxy)
    i j

def twoPointAux (t : F → Semiterm ℒₒᵣ Empty N) (i j : F) : Semisentence ℒₒᵣ N :=
  ⩕ k ∈ { k : F | i ≺ k }, (negativeSuccessorDef T)/[t j, t k]

def θChainAux (t : F → Semiterm ℒₒᵣ Empty N) : List F → Semisentence ℒₒᵣ N
  |          [] => ⊥
  |         [_] => ⊤
  | j :: i :: ε => θChainAux t (i :: ε) ⋏ twoPointAux T t i j

def θAux (t : F → Semiterm ℒₒᵣ Empty N) (i : F) : Semisentence ℒₒᵣ N :=
  haveI := Fintype.ofFinite (WChain r i)
  ⩖ ε : WChain r i, θChainAux T t ε

lemma rew_twoPointAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : F → Semiterm ℒₒᵣ Empty N) :
    Rew.substs w ▹ twoPointAux T t i j = twoPointAux T (fun i ↦ Rew.substs w (t i)) i j := by
  simp [twoPointAux, Finset.map_conj', Function.comp_def,
    ←TransitiveRewriting.comp_app, Rew.substs_comp_substs]

lemma rew_θChainAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : F → Semiterm ℒₒᵣ Empty N) (ε : List F) :
    Rew.substs w ▹ θChainAux T t ε = θChainAux T (fun i ↦ Rew.substs w (t i)) ε := by
  match ε with
  |           [] => simp [θChainAux]
  |          [_] => simp [θChainAux]
  | j :: i :: ε => simp [θChainAux, rew_θChainAux w _ (i :: ε), rew_twoPointAux]

lemma rew_θAux (w : Fin N → Semiterm ℒₒᵣ Empty N') (t : F → Semiterm ℒₒᵣ Empty N) (i : F) :
    Rew.substs w ▹ θAux T t i = θAux T (fun i ↦ Rew.substs w (t i)) i := by
  simp [Finset.map_udisj, θAux, rew_θChainAux]

def _root_.LO.FirstOrder.Arith.solovay (i : F) : Sentence ℒₒᵣ := exclusiveMultifixpoint
  (fun j ↦
    let jj := (Fintype.equivFin F).symm j
    θAux T (fun i ↦ #(Fintype.equivFin F i)) jj ⋏ ⩕ k ∈ { k : F | jj ≺ k }, T.consistencyₐ/[#(Fintype.equivFin F k)])
  (Fintype.equivFin F i)

def twoPoint (i j : F) : Sentence ℒₒᵣ := twoPointAux T (fun i ↦ ⌜solovay T i⌝) i j

def θChain (ε : List F) : Sentence ℒₒᵣ := θChainAux T (fun i ↦ ⌜solovay T i⌝) ε

def θ (i : F) : Sentence ℒₒᵣ := θAux T (fun i ↦ ⌜solovay T i⌝) i

lemma solovay_diag (i : F) :
    𝐈𝚺₁ ⊢!. solovay T i ⭤ θ T i ⋏ ⩕ j ∈ { j : F | i ≺ j }, T.consistencyₐ/[⌜solovay T j⌝] := by
  have : 𝐈𝚺₁ ⊢!. solovay T i ⭤
      (Rew.substs fun j ↦ ⌜solovay T ((Fintype.equivFin F).symm j)⌝) ▹
        (θAux T (fun i ↦ #(Fintype.equivFin F i)) i ⋏ ⩕ k ∈ { k : F | i ≺ k }, T.consistencyₐ/[#(Fintype.equivFin F k)]) := by
    simpa [solovay] using exclusiveMultidiagonal (T := 𝐈𝚺₁) (i := Fintype.equivFin F i)
      (fun j ↦
        let jj := (Fintype.equivFin F).symm j
        θAux T (fun i ↦ #(Fintype.equivFin F i)) jj ⋏ ⩕ k ∈ { k : F | jj ≺ k }, T.consistencyₐ/[#(Fintype.equivFin F k)])
  simpa [θ, Finset.map_conj', Function.comp_def, rew_θAux, ←TransitiveRewriting.comp_app, Rew.substs_comp_substs] using this

@[simp] lemma solovay_exclusive {i j : F} : solovay T i = solovay T j ↔ i = j := by simp [solovay]

end stx


section model

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

open Modal ProvabilityLogic Kripke

variable {F : Kripke.Frame} {r : F} [F.IsFiniteTree r] [Fintype F]

@[simp] lemma val_twoPoint (i j : F) :
    V ⊧/![] (twoPoint T i j) ↔ ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜solovay T j⌝ ⌜solovay T k⌝ := by
  simp [twoPoint, twoPointAux]

variable (V)

inductive ΘChain : List F → Prop where
  | singleton (i : F) : ΘChain [i]
  | cons {i j : F} :
    (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜solovay T j⌝ ⌜solovay T k⌝) → ΘChain (i :: ε) → ΘChain (j :: i :: ε)

def Θ (i : F) : Prop := ∃ ε : List F, ε.ChainI (· ≻ ·) i r ∧ ΘChain T V ε

abbrev Solovay (i : F) := Θ T V i ∧ ∀ j, i ≺ j → T.Consistencyₐ (⌜solovay T j⌝ : V)

variable {T V}

attribute [simp] ΘChain.singleton

@[simp] lemma ΘChain.not_nil : ¬ΘChain T V ([] : List F) := by rintro ⟨⟩

lemma ΘChain.doubleton_iff {i j : F} :
    ΘChain T V [j, i] ↔ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜solovay T j⌝ ⌜solovay T k⌝) := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro h; exact .cons h (by simp)

lemma ΘChain.cons_cons_iff {i j : F} {ε} :
    ΘChain T V (j :: i :: ε) ↔
    ΘChain T V (i :: ε) ∧ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜solovay T j⌝ ⌜solovay T k⌝) := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro ⟨ih, h⟩; exact .cons h ih

lemma ΘChain.cons_cons_iff' {i j : F} {ε} :
    ΘChain T V (j :: i :: ε) ↔ ΘChain T V [j, i] ∧ ΘChain T V (i :: ε) := by
  constructor
  · rintro ⟨⟩; simpa [ΘChain.doubleton_iff, *]
  · rintro ⟨ih, h⟩; exact h.cons (by rcases ih; assumption)

lemma ΘChain.cons_of {m i j : F} {ε}
    (hc : List.ChainI (· ≻ ·) i m ε)
    (hΘ : ΘChain T V ε)
    (H : (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜solovay T j⌝ ⌜solovay T k⌝))
    (hij : i ≺ j) :
    ΘChain T V (j :: ε) := by
  rcases hc
  case singleton => exact .cons H hΘ
  case cons => exact .cons H hΘ

section

@[simp] lemma val_θChain (ε : List F) : V ⊧/![] (θChain T ε) ↔ ΘChain T V ε := by
  unfold θChain θChainAux
  match ε with
  |          [] => simp
  |         [i] => simp
  | j :: i :: ε =>
    suffices
      V ⊧/![] (θChain T (i :: ε)) ∧ V ⊧/![] (twoPoint T i j) ↔
      ΘChain T V (j :: i :: ε) by simpa [-val_twoPoint] using this
    simp [ΘChain.cons_cons_iff, val_θChain (i :: ε)]

@[simp] lemma val_θ {i : F} : V ⊧/![] (θ T i) ↔ Θ T V i := by
  suffices (∃ ε, List.ChainI (· ≻ ·) i r ε ∧ V ⊧/![] (θChain T ε)) ↔ Θ T V i by
    simpa [-val_θChain, θ, θAux]
  simp [θ, θAux, Θ]

@[simp] lemma val_solovay {i : F} : V ⊧/![] (solovay T i) ↔ Solovay T V i := by
  simpa [models_iff] using
    consequence_iff.mp (sound! (T := 𝐈𝚺₁) (solovay_diag T i)) V inferInstance

end

lemma Solovay.refute (ne : r ≠ i) : Solovay T V i → T.Provableₐ (⌜∼solovay T i⌝ : V) := by
  intro h
  rcases show Θ T V i from h.1 with ⟨ε, hε, cε⟩
  rcases List.ChainI.prec_exists_of_ne hε (Ne.symm ne) with ⟨ε', i', hii', rfl, hε'⟩
  have : ∀ k, i' ≺ k → NegativeSuccessor T ⌜solovay T i⌝ ⌜solovay T k⌝ := (ΘChain.cons_cons_iff.mp cε).2
  have : T.ProvabilityComparisonₐ (V := V) ⌜∼solovay T i⌝ ⌜∼solovay T i⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using this i hii'
  exact ProvabilityComparisonₐ.refl_iff_provable.mp this

lemma Θ.disjunction (i : F) : Θ T V i → Solovay T V i ∨ ∃ j, i ≺ j ∧ Solovay T V j := by
  have : IsConverseWellFounded F (· ≺ ·) := inferInstance
  apply WellFounded.induction this.cwf i
  intro i ih hΘ
  by_cases hS : Solovay T V i
  · left; exact hS
  · right
    have : ∃ j, i ≺ j ∧ ∀ k, i ≺ k → T.ProvabilityComparisonₐ (V := V) ⌜∼solovay T j⌝ ⌜∼solovay T k⌝ := by
      have : ∃ j, i ≺ j ∧ T.Provableₐ (⌜∼solovay T j⌝ : V) := by
        simp [Theory.Consistencyₐ.quote_iff] at hS; exact hS hΘ
      rcases this with ⟨j', hij', hj'⟩
      have := ProvabilityComparisonₐ.find_minimal_proof_fintype (T := T) (ι := {j : F // i ≺ j}) (i := ⟨j', hij'⟩)
        (fun k ↦ ⌜∼solovay T k.val⌝) (by simpa)
      simpa using this
    rcases this with ⟨j, hij, hj⟩
    have : Θ T V j := by
      rcases hΘ with ⟨ε, hε, cε⟩
      exact ⟨
        j :: ε,
        hε.cons hij,
        cε.cons_of hε (by simpa [NegativeSuccessor.quote_iff_provabilityComparison]) hij⟩
    have : Solovay T V j ∨ ∃ k, j ≺ k ∧ Solovay T V k := ih j hij this
    rcases this with (hSj | ⟨k, hjk, hSk⟩)
    · exact ⟨j, hij, hSj⟩
    · exact ⟨k, Trans.trans hij hjk, hSk⟩

lemma ΘChain.append_iff {ε₁ ε₂ : List F} : ΘChain T V (ε₁ ++ i :: ε₂) ↔ ΘChain T V (ε₁ ++ [i]) ∧ ΘChain T V (i :: ε₂) := by
  match ε₁ with
  |           [] => simp
  |          [x] => simp [ΘChain.cons_cons_iff' (ε := ε₂)]
  | x :: y :: ε₁ =>
    have : ΘChain T V (y :: (ε₁ ++ i :: ε₂)) ↔ ΘChain T V (y :: (ε₁ ++ [i])) ∧ ΘChain T V (i :: ε₂) :=
      append_iff (ε₁ := y :: ε₁) (ε₂ := ε₂) (i := i)
    simp [cons_cons_iff' (ε := ε₁ ++ i :: ε₂), cons_cons_iff' (ε := ε₁ ++ [i]), and_assoc, this]

private lemma Solovay.exclusive.comparable {i₁ i₂ : F} {ε₁ ε₂ : List F}
    (ne : i₁ ≠ i₂)
    (h : ε₁ <:+ ε₂)
    (Hi₁ : ∀ j, i₁ ≺ j → T.Consistencyₐ (⌜solovay T j⌝ : V))
    (cε₁ : List.ChainI (· ≻ ·) i₁ r ε₁)
    (cε₂ : List.ChainI (· ≻ ·) i₂ r ε₂)
    (Θε₂ : ΘChain T V ε₂) : False := by
  have : ∃ a, a :: ε₁ <:+ ε₂ := by
    rcases List.IsSuffix.eq_or_cons_suffix h with (e | h)
    · have : ε₁ ≠ ε₂ := by
        rintro rfl
        have : i₁ = i₂ := (List.ChainI.eq_of cε₁ cε₂).1
        contradiction
      contradiction
    · exact h
  rcases this with ⟨j, hj⟩
  have hji₁ε₂ : [j, i₁] <:+: ε₂ := by
    rcases cε₁.tail_exists with ⟨ε₁', rfl⟩
    exact List.infix_iff_prefix_suffix.mpr ⟨j :: i₁ :: ε₁', by simp, hj⟩
  have hij₁ : i₁ ≺ j := cε₂.rel_of_infix j i₁ hji₁ε₂
  have : ¬T.Provableₐ (⌜∼solovay T j⌝ : V) := by simpa [Theory.Consistencyₐ.quote_iff] using Hi₁ j hij₁
  have : T.Provableₐ (⌜∼solovay T j⌝ : V) := by
    have : ΘChain T V [j, i₁] := by
      rcases hji₁ε₂ with ⟨η₁, η₂, rfl⟩
      have Θε₂ : ΘChain T V (η₁ ++ j :: i₁ :: η₂) := by simpa using Θε₂
      exact ΘChain.cons_cons_iff'.mp (ΘChain.append_iff.mp Θε₂).2 |>.1
    have : ∀ k, i₁ ≺ k → T.ProvabilityComparisonₐ (V := V) ⌜∼solovay T j⌝ ⌜∼solovay T k⌝ := by
      simpa [NegativeSuccessor.quote_iff_provabilityComparison] using ΘChain.cons_cons_iff.mp this
    exact ProvabilityComparisonₐ.refl_iff_provable.mp (this j hij₁)
  contradiction

lemma Solovay.exclusive {i₁ i₂ : F} (ne : i₁ ≠ i₂) : Solovay T V i₁ → ¬Solovay T V i₂ := by
  intro S₁ S₂
  rcases S₁ with ⟨⟨ε₁, cε₁, Θε₁⟩, Hi₁⟩
  rcases S₂ with ⟨⟨ε₂, cε₂, Θε₂⟩, Hi₂⟩
  by_cases hε₁₂ : ε₁ <:+ ε₂
  · exact Solovay.exclusive.comparable ne hε₁₂ Hi₁ cε₁ cε₂ Θε₂
  by_cases hε₂₁ : ε₂ <:+ ε₁
  · exact Solovay.exclusive.comparable (Ne.symm ne) hε₂₁ Hi₂ cε₂ cε₁ Θε₁
  have : ∃ ε k j₁ j₂, j₁ ≠ j₂ ∧ j₁ :: k :: ε <:+ ε₁ ∧ j₂ :: k :: ε <:+ ε₂ := by
    rcases List.suffix_trichotomy hε₁₂ hε₂₁ with ⟨ε', j₁, j₂, nej, h₁, h₂⟩
    match ε' with
    |     [] =>
      rcases show j₁ = r from List.single_suffix_uniq h₁ cε₁.prefix_suffix.2
      rcases show j₂ = r from List.single_suffix_uniq h₂ cε₂.prefix_suffix.2
      contradiction
    | k :: ε =>
      exact ⟨ε, k, j₁, j₂, nej, h₁, h₂⟩
  rcases this with ⟨ε, k, j₁, j₂, nej, hj₁, hj₂⟩
  have C₁ : ΘChain T V [j₁, k] := by
    rcases hj₁ with ⟨_, rfl⟩
    have : ΘChain T V ([j₁] ++ k :: ε) := (ΘChain.append_iff.mp Θε₁).2
    simpa using (ΘChain.append_iff.mp this).1
  have C₂ : ΘChain T V [j₂, k] := by
    rcases hj₂ with ⟨_, rfl⟩
    have : ΘChain T V ([j₂] ++ k :: ε) := (ΘChain.append_iff.mp Θε₂).2
    simpa using (ΘChain.append_iff.mp this).1
  have P₁ : T.ProvabilityComparisonₐ (V := V) ⌜∼solovay T j₁⌝ ⌜∼solovay T j₂⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using
      ΘChain.doubleton_iff.mp C₁ j₂
        (cε₂.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₂ :: k :: ε, by simp, hj₂⟩)
  have P₂ : T.ProvabilityComparisonₐ (V := V) ⌜∼solovay T j₂⌝ ⌜∼solovay T j₁⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using
      ΘChain.doubleton_iff.mp C₂ j₁
        (cε₁.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₁ :: k :: ε, by simp, hj₁⟩)
  have : j₁ = j₂ := by simpa using ProvabilityComparisonₐ.antisymm P₁ P₂
  contradiction

end model

end SolovaySentence

end LO.FirstOrder.Arith
