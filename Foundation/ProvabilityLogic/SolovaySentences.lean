import Foundation.ProvabilityLogic.Interpretation
import Foundation.Modal.Kripke.Logic.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot
import Foundation.FirstOrder.Internal.WitnessComparison
import Foundation.FirstOrder.Internal.FixedPoint
import Foundation.FirstOrder.Internal.Consistency
import Foundation.ProvabilityLogic.GL.Soundness
import Foundation.ProvabilityLogic.Height

/-!
# Basix propaties of Solovay sentences and its existance$
-/

open Classical

noncomputable section

namespace LO.Modal.Kripke

section frame

variable {F : Frame} [Fintype F] {r : F} [F.IsTree r]

def Frame.World.finHeight (i : F) : ℕ := fcwHeight (· ≺ ·) i

variable (F)

def Frame.finHeight : ℕ := Frame.World.finHeight r

variable {F}

lemma Frame.World.finHeight_lt_whole_finHeight {i : F} (hi : r ≺ i) :
    Frame.World.finHeight i < F.finHeight := fcwHeight_gt_of hi

lemma Frame.World.finHeight_le_whole_finHeight (i : F) :
    Frame.World.finHeight i ≤ F.finHeight := by
  by_cases hi : i = r
  · rcases hi; rfl
  · have : r ≺ i := root_genaretes'! i hi
    exact le_of_lt (fcwHeight_gt_of this)

lemma finHeight_lt_iff_relItr {i : F} :
    Frame.World.finHeight i < n ↔ ∀ j, ¬i ≺^[n] j  := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices Frame.World.finHeight i ≤ n ↔ ∀ j : F, i ≺ j → Frame.World.finHeight j < n by
      calc
        Frame.World.finHeight i < n + 1
          ↔ Frame.World.finHeight i ≤ n := Nat.lt_add_one_iff
        _ ↔ ∀ j, i ≺ j → Frame.World.finHeight j < n := this
        _ ↔ ∀ j, i ≺ j → ∀ k, ¬j ≺^[n] k := by simp [finHeight_lt_iff_relItr (n := n)]
        _ ↔ ∀ k j, i ≺ j → ¬j ≺^[n] k    := by grind
        _ ↔ ∀ j, ¬i ≺^[n + 1] j  := by simp
    constructor
    · exact fun h j hij ↦ lt_of_lt_of_le (fcwHeight_gt_of hij) h
    · exact fcwHeight_le

lemma le_finHeight_iff_relItr {i : F} :
    n ≤ Frame.World.finHeight i ↔ ∃ j, i ≺^[n] j := calc
  n ≤ Frame.World.finHeight i ↔ ¬Frame.World.finHeight i < n := Iff.symm Nat.not_lt
  _                           ↔ ∃ j, i ≺^[n] j := by simp [finHeight_lt_iff_relItr]

lemma finHeight_eq_iff_relItr {i : F} :
    Frame.World.finHeight i = n ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := calc
  Frame.World.finHeight i = n
    ↔ Frame.World.finHeight i < n + 1 ∧ n ≤ Frame.World.finHeight i := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge
  _ ↔ (∀ j, ¬i ≺^[n + 1] j) ∧ (∃ j, i ≺^[n] j) := by simp [finHeight_lt_iff_relItr, le_finHeight_iff_relItr]
  _ ↔ (∀ k j, i ≺^[n] j → ¬j ≺ k) ∧ (∃ j, i ≺^[n] j) := by simp only [HRel.Iterate.forward, not_exists, not_and]
  _ ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := by grind

lemma exists_terminal (i : F) : ∃ j, i ≺^[Frame.World.finHeight i] j := le_finHeight_iff_relItr.mp (by simp)

namespace Frame.extendRoot

@[simp] lemma finHeight_pos : 0 < (F.extendRoot 1).finHeight := by
  apply lt_fcwHeight ?_ (by simp)
  · exact Sum.inr r
  trivial

@[simp] lemma finHeight₁ : (F.extendRoot 1).finHeight = F.finHeight + 1 := by
  let l := World.finHeight (extendRoot.root : F.extendRoot 1)
  suffices
      l ≤ Frame.World.finHeight r + 1 ∧
      Frame.World.finHeight r < l by
    simpa using Nat.eq_iff_le_and_ge.mpr this
  constructor
  · suffices l - 1 ≤ World.finHeight r from Nat.le_add_of_sub_le this
    apply le_finHeight_iff_relItr.mpr
    by_cases hl : l - 1 = 0
    · exact ⟨r, by simp [hl]⟩
    have lpos : 0 < l - 1 := Nat.zero_lt_of_ne_zero hl
    have e : l = (l - 1) + 1 := by
      symm; exact Nat.sub_add_cancel Frame.extendRoot.finHeight_pos
    have : ∃ j, extendRoot.root ≺^[l] j := exists_terminal (extendRoot.root : F.extendRoot 1)
    rcases this with ⟨j, hj⟩
    have : ∃ z, extendRoot.root ≺ z ∧ z ≺^[l - 1] j := by
      rw [e] at hj
      simpa using hj
    rcases this with ⟨z, hz, hzj⟩
    have : ∃ x, j = embed x := eq_inr_of_root_rel <| HRel.Iterate.unwrap_of_trans_of_pos finHeight_pos hj
    rcases this with ⟨j, rfl⟩
    rcases not_root_of_from_root'₁ hz with (rfl | ⟨z, rfl, Rrz⟩)
    · exact ⟨j, embed_rel_iterate_embed_iff_rel.mp hzj⟩
    use j
    exact HRel.Iterate.constant_trans_of_pos lpos Rrz (embed_rel_iterate_embed_iff_rel.mp hzj)
  · suffices World.finHeight r + 1 ≤ World.finHeight extendRoot.root from this
    apply le_finHeight_iff_relItr.mpr
    rcases exists_terminal r with ⟨j, hj⟩
    exact ⟨j, r, by trivial, embed_rel_iterate_embed_iff_rel.mpr hj⟩

end Frame.extendRoot

end frame

section model

variable {M : Model} {r : M.World} [M.IsFiniteTree r] [Fintype M]

lemma finHeight_lt_iff_satisfies_boxbot {i : M} :
    Frame.World.finHeight i < n ↔ i ⊧ □^[n] ⊥ := by
  simp only [finHeight_lt_iff_relItr, Formula.Kripke.Satisfies.multibox_def]
  simp

lemma finHeight_pos_of_dia {i : M} (hA : i ⊧ ◇ A) : 0 < Frame.World.finHeight i := by
  have : ∃ j, i ≺ j ∧ j ⊧ A := Formula.Kripke.Satisfies.dia_def.mp hA
  rcases this with ⟨j, hj, _⟩
  apply lt_fcwHeight hj (by simp)

@[simp] lemma Model.extendRoot.finHeight₁ :
    (M.extendRoot 1).finHeight = M.finHeight + 1 := Frame.extendRoot.finHeight₁

end model

end LO.Modal.Kripke

namespace LO.ProvabilityLogic

open Entailment Entailment.FiniteContext
open FirstOrder
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

variable {L : Language} [L.DecidableEq] [L.ReferenceableBy L]
         {T₀ T : Theory L} [T₀ ⪯ T] (𝔅 : Provability T₀ T) [𝔅.HBL]
         {A B : Modal.Formula _}

structure SolovaySentences (F : Kripke.Frame) (r : F) [F.IsFiniteTree r] [Fintype F] where
  σ : F → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢!. σ i ➝ ∼σ j
  protected SC2 : ∀ i j, i ≺ j → T₀ ⊢!. σ i ➝ 𝔅.dia (σ j)
  protected SC3 : ∀ i, r ≠ i → T₀ ⊢!. σ i ➝ 𝔅 (⩖ j ∈ { j : F | i ≺ j }, σ j)
  protected SC4 : T₀ ⊢!. ⩖ j, σ j

attribute [coe] SolovaySentences.σ

variable {𝔅}

namespace SolovaySentences

instance {F : Kripke.Frame} {r : F} [F.IsFiniteTree r] [Fintype F] : CoeFun (SolovaySentences 𝔅 F r) (λ _ => F → Sentence L) := ⟨λ σ => σ.σ⟩

variable {M : Model} {r : M.World} [M.IsFiniteTree r] [Fintype M]

variable (S : SolovaySentences 𝔅 M.toFrame r)

noncomputable def realization :
    Realization 𝔅 := ⟨fun a ↦ ⩖ i ∈ { i : M | i ⊧ (.atom a) }, S i⟩

private lemma mainlemma_aux {i : M} (hri : r ≺ i) :
    (i ⊧ A → T₀ ⊢!. S i ➝ S.realization A) ∧
    (¬i ⊧ A → T₀ ⊢!. S i ➝ ∼S.realization A) := by
  induction A generalizing i with
  | hfalsum => simp [Realization.interpret, Semantics.Realize, Satisfies];
  | hatom a =>
    constructor;
    . intro h;
      apply right_Fdisj'!_intro;
      simpa using h;
    . intro h;
      apply CN!_of_CN!_right;
      apply left_Fdisj'!_intro;
      intro i hi;
      apply S.SC1;
      by_contra hC; subst hC;
      apply h;
      simpa using hi;
  | himp A B ihA ihB =>
    simp only [Realization.interpret, Semantics.Imp.realize_imp, Classical.not_imp, and_imp];
    constructor;
    . intro h;
      rcases Satisfies.imp_def₂.mp h with (hA | hB);
      . exact C!_trans ((ihA hri).2 hA) CNC!;
      . exact C!_trans ((ihB hri).1 hB) imply₁!;
    . intro hA hB;
      exact not_imply_prem''! ((ihA hri).1 hA) ((ihB hri).2 hB);
  | hbox A ihA =>
    simp only [Realization.interpret];
    constructor;
    . intro h;
      apply C!_trans $ S.SC3 i $ (by rintro rfl; exact IsIrrefl.irrefl _ hri);
      apply 𝔅.prov_distribute_imply';
      apply left_Fdisj'!_intro;
      rintro j Rij;
      replace Rij : i ≺ j := by simpa using Rij
      exact (ihA (IsTrans.trans _ _ _ hri Rij)).1 (h j Rij)
    . intro h;
      have := Satisfies.box_def.not.mp h;
      push_neg at this;
      obtain ⟨j, Rij, hA⟩ := this;
      have := CN!_of_CN!_right $ (ihA (IsTrans.trans _ _ _ hri Rij)).2 hA
      have : T₀ ⊢!. ∼𝔅 (∼S.σ j) ➝ ∼𝔅 (S.realization A) :=
        contra! $ 𝔅.prov_distribute_imply' $ CN!_of_CN!_right $ (ihA (IsTrans.trans _ _ _ hri Rij)).2 hA;
      exact C!_trans (S.SC2 i j Rij) this;

theorem mainlemma (S : SolovaySentences 𝔅 M.toFrame r) {i : M} (hri : r ≺ i) :
    i ⊧ A → T₀ ⊢!. S i ➝ S.realization A := (mainlemma_aux S hri).1

theorem mainlemma_neg (S : SolovaySentences 𝔅 M.toFrame r) {i : M} (hri : r ≺ i) :
    ¬i ⊧ A → T₀ ⊢!. S i ➝ ∼S.realization A := (mainlemma_aux S hri).2

lemma root_of_iterated_inconsistency : T₀ ⊢!. ∼𝔅^[M.finHeight] ⊥ ➝ S r := by
  suffices T₀ ⊢!. (⩖ j, S j) ➝ ∼S r ➝ 𝔅^[M.finHeight] ⊥ by
    cl_prover [this, S.SC4]
  apply Entailment.left_Udisj!_intro
  intro i
  by_cases hir : i = r
  · rcases hir
    cl_prover
  · have hri : r ≺ i := Frame.root_genaretes'! i hir
    have : T₀ ⊢!. S.σ i ➝ (↑𝔅)^[M.finHeight] ⊥ := by
      simpa [Realization.interpret_boxItr_def] using
        S.mainlemma hri (A := □^[M.finHeight] ⊥)
          <| finHeight_lt_iff_satisfies_boxbot.mp
          <| Frame.World.finHeight_lt_whole_finHeight hri
    cl_prover [this]

lemma theory_height [𝔅.Sound₀] (h : r ⊧ ◇(∼A)) (b : T ⊢!. S.realization A) :
    𝔅.height < M.finHeight := by
  apply 𝔅.height_lt_pos_of_boxDot (finHeight_pos_of_dia h)
  have : ∃ i, r ≺ i ∧ ¬i ⊧ A := Formula.Kripke.Satisfies.dia_def.mp h
  rcases this with ⟨i, hi, hiA⟩
  have b₀ : T₀ ⊢!. 𝔅 (S.realization A) := 𝔅.D1 b
  have b₁ : T₀ ⊢!. ∼(↑𝔅)^[M.finHeight] ⊥ ➝ S r := S.root_of_iterated_inconsistency
  have b₂ : T₀ ⊢!. S r ➝ 𝔅.dia (S i) := S.SC2 r i hi
  have b₃ : T₀ ⊢!. 𝔅.dia (S i) ➝ ∼𝔅 (S.realization A) := by
    simpa [Provability.dia] using
      𝔅.dia_distribute_imply <| WeakerThan.pbl <| S.mainlemma_neg hi hiA
  cl_prover [b₀, b₁, b₂, b₃]

end SolovaySentences

end LO.ProvabilityLogic

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

namespace SolovaySentences

open Modal ProvabilityLogic Kripke

variable {T : ArithmeticTheory} [T.Δ₁]

section frame

variable {F : Kripke.Frame} {r : F} [F.IsFiniteTree r] [Fintype F]

section model

variable (T) {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def NegativeSuccessor (φ ψ : V) : Prop := T.ProvabilityComparison (neg ℒₒᵣ φ) (neg ℒₒᵣ ψ)

lemma NegativeSuccessor.quote_iff_provabilityComparison {φ ψ : Sentence ℒₒᵣ} :
    NegativeSuccessor (V := V) T ⌜φ⌝ ⌜ψ⌝ ↔ T.ProvabilityComparison (V := V) ⌜∼φ⌝ ⌜∼ψ⌝ := by
  simp [NegativeSuccessor, Semiformula.empty_quote_def, Semiformula.quote_def]

section

def negativeSuccessor : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, ∃ nψ, !(negGraph ℒₒᵣ) nφ φ ∧ !(negGraph ℒₒᵣ) nψ ψ ∧ !T.provabilityComparison nφ nψ”

lemma negativeSuccessor_defined : 𝚺₁-Relation[V] NegativeSuccessor T via (negativeSuccessor T) := by
  intro v
  simp [negativeSuccessor, NegativeSuccessor, (neg.defined (L := ℒₒᵣ)).df.iff]

@[simp] lemma eval_negativeSuccessorDef (v) :
    Semiformula.Evalbm V v (negativeSuccessor T).val ↔ NegativeSuccessor T (v 0) (v 1) := (negativeSuccessor_defined T).df.iff v

instance negativeSuccessor_definable : 𝚺₁-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

/-- instance for definability tactic-/
instance negativeSuccessor_definable' : 𝚺-[0 + 1]-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

end

end model

section stx

variable (T)

abbrev WChain (i j : F) := {l : List F // l.ChainI (· ≻ ·) j i}

instance (i j : F) : Finite (WChain j i) :=
  List.ChainI.finite_of_irreflexive_of_transitive
    (by exact IsIrrefl.irrefl (r := (· ≺ ·)))
    (by intro x y z hxy hyz
        exact IsTrans.trans (r := (· ≺ ·)) z y x hyz hxy)
    i j

def twoPointAux (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) (i j : F) : Semisentence ℒₒᵣ N :=
  ⩕ k ∈ { k : F | i ≺ k }, (negativeSuccessor T)/[t j, t k]

def θChainAux (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) : List F → Semisentence ℒₒᵣ N
  |          [] => ⊥
  |         [_] => ⊤
  | j :: i :: ε => θChainAux t (i :: ε) ⋏ twoPointAux T t i j

def θAux (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) (i : F) : Semisentence ℒₒᵣ N :=
  haveI := Fintype.ofFinite (WChain r i)
  ⩖ ε : WChain r i, θChainAux T t ε

lemma rew_twoPointAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) :
    Rew.substs w ▹ twoPointAux T t i j = twoPointAux T (fun i ↦ Rew.substs w (t i)) i j := by
  simp [twoPointAux, Finset.map_conj', Function.comp_def, ←TransitiveRewriting.comp_app,
    Rew.substs_comp_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma rew_θChainAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) (ε : List F) :
    Rew.substs w ▹ θChainAux T t ε = θChainAux T (fun i ↦ Rew.substs w (t i)) ε := by
  match ε with
  |          [] => simp [θChainAux]
  |         [_] => simp [θChainAux]
  | j :: i :: ε => simp [θChainAux, rew_θChainAux w _ (i :: ε), rew_twoPointAux]

lemma rew_θAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : F → FirstOrder.Semiterm ℒₒᵣ Empty N) (i : F) :
    Rew.substs w ▹ θAux T t i = θAux T (fun i ↦ Rew.substs w (t i)) i := by
  simp [Finset.map_udisj, θAux, rew_θChainAux]

def _root_.LO.FirstOrder.Theory.solovay (i : F) : Sentence ℒₒᵣ := exclusiveMultifixpoint
  (fun j ↦
    let jj := (Fintype.equivFin F).symm j
    θAux T (fun i ↦ #(Fintype.equivFin F i)) jj ⋏ ⩕ k ∈ { k : F | jj ≺ k }, T.consistentWith/[#(Fintype.equivFin F k)])
  (Fintype.equivFin F i)

def twoPoint (i j : F) : Sentence ℒₒᵣ := twoPointAux T (fun i ↦ ⌜T.solovay i⌝) i j

def θChain (ε : List F) : Sentence ℒₒᵣ := θChainAux T (fun i ↦ ⌜T.solovay i⌝) ε

def θ (i : F) : Sentence ℒₒᵣ := θAux T (fun i ↦ ⌜T.solovay i⌝) i

lemma solovay_diag (i : F) :
    𝐈𝚺₁ ⊢!. T.solovay i ⭤ θ T i ⋏ ⩕ j ∈ { j : F | i ≺ j }, T.consistentWith/[⌜T.solovay j⌝] := by
  have : 𝐈𝚺₁ ⊢!. T.solovay i ⭤
      (Rew.substs fun j ↦ ⌜T.solovay ((Fintype.equivFin F).symm j)⌝) ▹
        (θAux T (fun i ↦ #(Fintype.equivFin F i)) i ⋏ ⩕ k ∈ { k : F | i ≺ k }, T.consistentWith/[#(Fintype.equivFin F k)]) := by
    simpa [Theory.solovay, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      exclusiveMultidiagonal (T := 𝐈𝚺₁) (i := Fintype.equivFin F i)
        (fun j ↦
          let jj := (Fintype.equivFin F).symm j
          θAux T (fun i ↦ #(Fintype.equivFin F i)) jj ⋏ ⩕ k ∈ { k : F | jj ≺ k }, T.consistentWith/[#(Fintype.equivFin F k)])
  simpa [θ, Finset.map_conj', Function.comp_def, rew_θAux, ←TransitiveRewriting.comp_app,
    Rew.substs_comp_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using this

@[simp] lemma solovay_exclusive {i j : F} : T.solovay i = T.solovay j ↔ i = j := by simp [Theory.solovay]

private lemma θChainAux_sigma1 (ε : List F) : Hierarchy 𝚺 1 (θChainAux T t ε) := by
  match ε with
  |          [] => simp [θChainAux]
  |         [_] => simp [θChainAux]
  | _ :: i :: ε =>
    simp [θChainAux, twoPointAux, θChainAux_sigma1 (i :: ε)]

@[simp] lemma θ_sigma1 (i : F) : Hierarchy 𝚺 1 (θ T i) := by
  simp [θ, θAux, θChainAux_sigma1]

end stx

section model

variable (T)

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

open Modal ProvabilityLogic Kripke

@[simp] lemma val_twoPoint (i j : F) :
    V ⊧/![] (twoPoint T i j) ↔ ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay j⌝ ⌜T.solovay k⌝ := by
  simp [twoPoint, twoPointAux]

variable (V)

inductive ΘChain : List F → Prop where
  | singleton (i : F) : ΘChain [i]
  | cons {i j : F} :
    (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay j⌝ ⌜T.solovay k⌝) → ΘChain (i :: ε) → ΘChain (j :: i :: ε)

def Θ (i : F) : Prop := ∃ ε : List F, ε.ChainI (· ≻ ·) i r ∧ ΘChain T V ε

def _root_.LO.FirstOrder.Theory.Solovay (i : F) := Θ T V i ∧ ∀ j, i ≺ j → T.ConsistentWith (⌜T.solovay j⌝ : V)

variable {T V}

attribute [simp] ΘChain.singleton

@[simp] lemma ΘChain.not_nil : ¬ΘChain T V ([] : List F) := by rintro ⟨⟩

lemma ΘChain.doubleton_iff {i j : F} :
    ΘChain T V [j, i] ↔ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay j⌝ ⌜T.solovay k⌝) := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro h; exact .cons h (by simp)

lemma ΘChain.cons_cons_iff {i j : F} {ε} :
    ΘChain T V (j :: i :: ε) ↔
    ΘChain T V (i :: ε) ∧ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay j⌝ ⌜T.solovay k⌝) := by
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
    (H : (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay j⌝ ⌜T.solovay k⌝))
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
  simp [Θ]

@[simp] lemma val_solovay {i : F} : V ⊧/![] (T.solovay i) ↔ T.Solovay V i := by
  simpa [models_iff] using
    consequence_iff.mp (sound!₀ (solovay_diag T i)) V inferInstance

end

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
    (Hi₁ : ∀ j, i₁ ≺ j → T.ConsistentWith (⌜T.solovay j⌝ : V))
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
  have : ¬T.Provable (⌜∼T.solovay j⌝ : V) := by simpa [Theory.ConsistentWith.quote_iff] using Hi₁ j hij₁
  have : T.Provable (⌜∼T.solovay j⌝ : V) := by
    have : ΘChain T V [j, i₁] := by
      rcases hji₁ε₂ with ⟨η₁, η₂, rfl⟩
      have Θε₂ : ΘChain T V (η₁ ++ j :: i₁ :: η₂) := by simpa using Θε₂
      exact ΘChain.cons_cons_iff'.mp (ΘChain.append_iff.mp Θε₂).2 |>.1
    have : ∀ k, i₁ ≺ k → T.ProvabilityComparison (V := V) ⌜∼T.solovay j⌝ ⌜∼T.solovay k⌝ := by
      simpa [NegativeSuccessor.quote_iff_provabilityComparison] using ΘChain.cons_cons_iff.mp this
    exact (ProvabilityComparison.refl_iff_provable (L := ℒₒᵣ)).mp (this j hij₁)
  contradiction

/-- Condition 1.-/
lemma Solovay.exclusive {i₁ i₂ : F} (ne : i₁ ≠ i₂) : T.Solovay V i₁ → ¬T.Solovay V i₂ := by
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
  have P₁ : T.ProvabilityComparison (V := V) ⌜∼T.solovay j₁⌝ ⌜∼T.solovay j₂⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using
      ΘChain.doubleton_iff.mp C₁ j₂
        (cε₂.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₂ :: k :: ε, by simp, hj₂⟩)
  have P₂ : T.ProvabilityComparison (V := V) ⌜∼T.solovay j₂⌝ ⌜∼T.solovay j₁⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using
      ΘChain.doubleton_iff.mp C₂ j₁
        (cε₁.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₁ :: k :: ε, by simp, hj₁⟩)
  have : j₁ = j₂ := by simpa using ProvabilityComparison.antisymm (V := V) P₁ P₂
  contradiction

/-- Condition 2.-/
lemma Solovay.consistent {i j : F} (hij : i ≺ j) : T.Solovay V i → ¬T.Provable (⌜∼T.solovay j⌝ : V) := fun h ↦
  (Theory.ConsistentWith.quote_iff T).mp (h.2 j hij)

lemma Solovay.refute (ne : r ≠ i) : T.Solovay V i → T.Provable (⌜∼T.solovay i⌝ : V) := by
  intro h
  rcases show Θ T V i from h.1 with ⟨ε, hε, cε⟩
  rcases List.ChainI.prec_exists_of_ne hε (Ne.symm ne) with ⟨ε', i', hii', rfl, hε'⟩
  have : ∀ k, i' ≺ k → NegativeSuccessor T ⌜T.solovay i⌝ ⌜T.solovay k⌝ := (ΘChain.cons_cons_iff.mp cε).2
  have : T.ProvabilityComparison (V := V) ⌜∼T.solovay i⌝ ⌜∼T.solovay i⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparison] using this i hii'
  exact (ProvabilityComparison.refl_iff_provable (T := T)).mp this

lemma Θ.disjunction (i : F) : Θ T V i → T.Solovay V i ∨ ∃ j, i ≺ j ∧ T.Solovay V j := by
  have : IsConverseWellFounded F (· ≺ ·) := inferInstance
  apply WellFounded.induction this.cwf i
  intro i ih hΘ
  by_cases hS : T.Solovay V i
  · left; exact hS
  · right
    have : ∃ j, i ≺ j ∧ ∀ k, i ≺ k → T.ProvabilityComparison (V := V) ⌜∼T.solovay j⌝ ⌜∼T.solovay k⌝ := by
      have : ∃ j, i ≺ j ∧ T.Provable (⌜∼T.solovay j⌝ : V) := by
        have : Θ T V i → ∃ x, i ≺ x ∧ T.Provable (⌜∼T.solovay x⌝ : V) := by
          simpa [Theory.ConsistentWith.quote_iff, Theory.Solovay] using hS
        exact this hΘ
      rcases this with ⟨j', hij', hj'⟩
      have := ProvabilityComparison.find_minimal_proof_fintype (T := T) (ι := {j : F // i ≺ j}) (i := ⟨j', hij'⟩)
        (fun k ↦ ⌜∼T.solovay k.val⌝) (by simpa)
      simpa using this
    rcases this with ⟨j, hij, hj⟩
    have : Θ T V j := by
      rcases hΘ with ⟨ε, hε, cε⟩
      exact ⟨
        j :: ε,
        hε.cons hij,
        cε.cons_of hε (by simpa [NegativeSuccessor.quote_iff_provabilityComparison]) hij⟩
    have : T.Solovay V j ∨ ∃ k, j ≺ k ∧ T.Solovay V k := ih j hij this
    rcases this with (hSj | ⟨k, hjk, hSk⟩)
    · exact ⟨j, hij, hSj⟩
    · exact ⟨k, Trans.trans hij hjk, hSk⟩

/-- Condition 4.-/
lemma disjunctive : ∃ i : F, T.Solovay V i := by
  have : T.Solovay V r ∨ ∃ j, r ≺ j ∧ T.Solovay V j :=
    Θ.disjunction (V := V) (T := T) r ⟨[r], by simp⟩
  rcases this with  (H | ⟨i, _, H⟩)
  · exact ⟨r, H⟩
  · exact ⟨i, H⟩

/-- Condition 3.-/
lemma Solovay.box_disjunction [𝐈𝚺₁ ⪯ T] {i : F} (ne : r ≠ i) :
    T.Solovay V i → T.Provable (⌜⩖ j ∈ {j : F | i ≺ j}, T.solovay j⌝ : V) := by
  intro hS
  have TP : T.internalize V ⊢! ⌜θ T i ➝ T.solovay i ⋎ ⩖ j ∈ {j : F | i ≺ j}, T.solovay j⌝ :=
    internal_sentence_provable_of_outer_sentence_provable <| by
      have : 𝐈𝚺₁ ⊢!. θ T i ➝ T.solovay i ⋎ ⩖ j ∈ {j : F | i ≺ j}, T.solovay j :=
        oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
          simpa [models_iff] using Θ.disjunction i
      exact Entailment.WeakerThan.pbl this
  have Tθ : T.internalize V ⊢! ⌜θ T i⌝ :=
    InternalArithmetic.sigma_one_provable_of_models T (show Hierarchy 𝚺 1 (θ T i) by simp) (by simpa [models_iff] using hS.1)
  have hP : T.internalize V ⊢! ⌜T.solovay i⌝ ⋎ ⌜⩖ j ∈ {j : F | i ≺ j}, T.solovay j⌝ := (by simpa using TP) ⨀ Tθ
  have : T.internalize V ⊢! ∼⌜T.solovay i⌝ := by simpa using (tprovable_tquote_iff_provable_quote (T := T)).mpr (Solovay.refute ne hS)
  have : T.internalize V ⊢! ⌜⩖ j ∈ {j : F | i ≺ j}, T.solovay j⌝ := Entailment.of_a!_of_n! hP this
  exact (tprovable_tquote_iff_provable_quote (T := T)).mp this

end model

lemma solovay_root_sound [𝐈𝚺₁ ⪯ T] [T.SoundOn (Hierarchy 𝚷 2)] : T.Solovay ℕ r := by
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans inferInstance (inferInstanceAs (𝐈𝚺₁ ⪯ T))
  have NS : ∀ i, r ≠ i → ¬T.Solovay ℕ i := by
    intro i hi H
    have Bi : T ⊢!. ∼T.solovay i := (provable_iff_provable₀ (T := T)).mp (Solovay.refute hi H)
    have : ¬T.Solovay ℕ i := by
      set π := θ T i ⋏ ⩕ j ∈ { j : F | i ≺ j }, T.consistentWith/[⌜T.solovay j⌝]
      have sπ : 𝐈𝚺₁ ⊢!. T.solovay i ⭤ π := solovay_diag T i
      have : T ⊢!. ∼π := by
        have : T ⊢!. T.solovay i ⭤ π := Entailment.WeakerThan.wk (inferInstanceAs (𝐈𝚺₁.toAxiom ⪯ T.toAxiom)) sπ
        exact Entailment.K!_left (Entailment.ENN!_of_E! this) ⨀ Bi
      have : ¬ℕ ⊧/![] π := by
        simpa [models_iff] using
          (inferInstanceAs (T.SoundOn (Hierarchy 𝚷 2))).sound
            (σ := ∼π)
            this
            (by simp [π,
              (show Hierarchy 𝚷 1 T.consistentWith.val by simp).strict_mono 𝚺 (show 1 < 2 by simp),
              (show Hierarchy 𝚺 1 (θ T i) by simp).mono (show 1 ≤ 2 by simp)])
      have : T.Solovay ℕ i ↔ ℕ ⊧/![] π := by
        simpa [models_iff] using consequence_iff.mp (sound!₀ sπ) ℕ inferInstance
      simpa [this]
    contradiction
  have : T.Solovay ℕ r ∨ ∃ j, r ≺ j ∧ T.Solovay ℕ j := Θ.disjunction (V := ℕ) (T := T) r ⟨[r], by simp⟩
  rcases this with (H | ⟨i, hri, Hi⟩)
  · assumption
  · have : ¬T.Solovay ℕ i := NS i (by rintro rfl; exact IsIrrefl.irrefl r hri)
    contradiction

lemma solovay_unprovable [𝐈𝚺₁ ⪯ T] [T.SoundOn (Hierarchy 𝚷 2)] {i : F} (h : r ≠ i) : T ⊬. ∼T.solovay i := by
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans inferInstance (inferInstanceAs (𝐈𝚺₁ ⪯ T))
  have : ∼T.Provable ⌜∼T.solovay i⌝ :=
    Solovay.consistent (V := ℕ) (T := T) (Frame.root_genaretes'! i (Ne.symm h)) solovay_root_sound
  simpa [Theory.ConsistentWith.quote_iff, provable_iff_provable₀, Axiom.unprovable_iff] using this

variable (T F)

def _root_.LO.ProvabilityLogic.SolovaySentences.standard
    [𝐈𝚺₁ ⪯ T] : SolovaySentences T.standardProvability F r where
  σ := T.solovay
  SC1 i j ne :=
    oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using Solovay.exclusive ne
  SC2 i j h :=
    oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using Solovay.consistent h
  SC3 i h :=
    oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using Solovay.box_disjunction h
  SC4 :=
    oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
      simpa [models₀_iff] using disjunctive

lemma _root_.LO.ProvabilityLogic.SolovaySentences.standard_σ_def [𝐈𝚺₁ ⪯ T] :
    (SolovaySentences.standard T F).σ = T.solovay := rfl

end frame

end SolovaySentences

end LO.ISigma1.Metamath
