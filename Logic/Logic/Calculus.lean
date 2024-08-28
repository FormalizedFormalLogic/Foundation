import Logic.Logic.System
import Logic.Logic.HilbertStyle.Supplemental

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
* `LO.Tait`
* `LO.Gentzen`

-/

namespace LO

class OneSided (F : outParam Type*) (K : Type*) where
  Derivation : K → List F → Type*

infix:45 " ⟹ " => OneSided.Derivation

abbrev OneSided.Derivation₁ [OneSided F K] (𝓚 : K) (p : F) : Type _ := 𝓚 ⟹ [p]

infix:45 " ⟹. " => OneSided.Derivation₁

abbrev OneSided.Derivable [OneSided F K] (𝓚 : K) (Δ : List F) : Prop := Nonempty (𝓚 ⟹ Δ)

infix:45 " ⟹! " => OneSided.Derivable

abbrev OneSided.Derivable₁ [OneSided F K] (𝓚 : K) (p : F) : Prop := Nonempty (𝓚 ⟹. p)

infix:45 " ⟹!. " => OneSided.Derivable₁

noncomputable def OneSided.Derivable.get [OneSided F K] (𝓚 : K) (Δ : List F) (h : 𝓚 ⟹! Δ) : 𝓚 ⟹ Δ :=
  Classical.choice h

class Tait (F K : Type*) [LogicalConnective F] [Collection F K] extends OneSided F K where
  verum (𝓚 : K) (Δ : List F)         : 𝓚 ⟹ ⊤ :: Δ
  and {𝓚 : K} {p q : F} {Δ : List F} : 𝓚 ⟹ p :: Δ → 𝓚 ⟹ q :: Δ → 𝓚 ⟹ p ⋏ q :: Δ
  or {𝓚 : K} {p q : F} {Δ : List F}  : 𝓚 ⟹ p :: q :: Δ → 𝓚 ⟹ p ⋎ q :: Δ
  wk {𝓚 : K} {Δ Δ' : List F}         : 𝓚 ⟹ Δ → Δ ⊆ Δ' → 𝓚 ⟹ Δ'
  em {𝓚 : K} {p} {Δ : List F}        : p ∈ Δ → ~p ∈ Δ → 𝓚 ⟹ Δ

class Tait.Cut (F K : Type*) [LogicalConnective F] [Collection F K] [Tait F K] where
  cut {𝓚 : K} {Δ : List F} {p} : 𝓚 ⟹ p :: Δ → 𝓚 ⟹ ~p :: Δ → 𝓚 ⟹ Δ

class Tait.Axiomatized (F K : Type*) [LogicalConnective F] [Collection F K] [Tait F K] where
  root {𝓚 : K} {p}    : p ∈ 𝓚 → 𝓚 ⟹. p
  trans {𝓚 𝓛 : K} {Γ} : ((q : F) → q ∈ 𝓚 → 𝓛 ⟹. q) → 𝓚 ⟹ Γ → 𝓛 ⟹ Γ

variable {F S K : Type*} [LogicalConnective F] [Collection F K]

namespace OneSided

variable [OneSided F K] {𝓚 : K} {Γ Δ : List F}

protected abbrev cast (d : 𝓚 ⟹ Δ) (e : Δ = Γ) : 𝓚 ⟹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

open System

variable [DeMorgan F] [Tait F K]

variable {𝓚 : K} {Γ Δ : List F} {p q p₁ p₂ p₃ p₄ : F}

def ofEq (b : 𝓚 ⟹ Γ) (h : Γ = Δ) : 𝓚 ⟹ Δ := h ▸ b

lemma of_eq (b : 𝓚 ⟹! Γ) (h : Γ = Δ) : 𝓚 ⟹! Δ := h ▸ b

def verum' (h : ⊤ ∈ Γ := by simp) : 𝓚 ⟹ Γ := wk (verum 𝓚 Γ) (by simp [h])

lemma verum! (𝓚 : K) (Γ : List F) : 𝓚 ⟹! ⊤ :: Γ := ⟨verum _ _⟩

lemma verum'! (h : ⊤ ∈ Γ) : 𝓚 ⟹! Γ := ⟨verum' h⟩

lemma and! (hp : 𝓚 ⟹! p :: Γ) (hq : 𝓚 ⟹! q :: Γ) : 𝓚 ⟹! p ⋏ q :: Γ := ⟨and hp.get hq.get⟩

lemma or! (h : 𝓚 ⟹! p :: q :: Γ) : 𝓚 ⟹! p ⋎ q :: Γ := ⟨or h.get⟩

lemma wk! (h : 𝓚 ⟹! Γ) (ss : Γ ⊆ Δ) : 𝓚 ⟹! Δ := ⟨wk h.get ss⟩

lemma em! (hp : p ∈ Γ) (hn : ~p ∈ Γ) : 𝓚 ⟹! Γ := ⟨em hp hn⟩

def close (p : F) (hp : p ∈ Γ := by simp) (hn : ~p ∈ Γ := by simp) : 𝓚 ⟹ Γ := em hp hn

lemma close! (p : F) (hp : p ∈ Γ := by simp) (hn : ~p ∈ Γ := by simp) : 𝓚 ⟹! Γ := em! hp hn

def and' {p q : F} (h : p ⋏ q ∈ Γ) (dp : 𝓚 ⟹ p :: Γ) (dq : 𝓚 ⟹ q :: Γ) : 𝓚 ⟹ Γ :=
  wk (and dp dq) (by simp [h])

def or' {p q : F} (h : p ⋎ q ∈ Γ) (dpq : 𝓚 ⟹ p :: q :: Γ) : 𝓚 ⟹ Γ :=
  wk (or dpq) (by simp [h])

def wkTail (d : 𝓚 ⟹ Γ) : 𝓚 ⟹ p :: Γ := wk d (by simp)

def rotate₁ (d : 𝓚 ⟹ p₂ :: p₁ :: Γ) : 𝓚 ⟹ p₁ :: p₂ :: Γ := wk d (by simp; apply List.subset_cons_of_subset _ (by simp))

def rotate₂ (d : 𝓚 ⟹ p₃ :: p₁ :: p₂ :: Γ) : 𝓚 ⟹ p₁ :: p₂ :: p₃ :: Γ :=
  wk d (by simp; apply List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))

def rotate₃ (d : 𝓚 ⟹ p₄ :: p₁ :: p₂ :: p₃ :: Γ) : 𝓚 ⟹ p₁ :: p₂ :: p₃ :: p₄ :: Γ :=
  wk d (by simp; apply List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| List.subset_cons_of_subset _ <| by simp))

variable [Tait.Cut F K] [Tait.Axiomatized F K] {𝓚 𝓛 : K} {Γ : List F}

alias cut := Tait.Cut.cut

alias root := Tait.Axiomatized.root

lemma cut! (hp : 𝓚 ⟹! p :: Δ) (hn : 𝓚 ⟹! ~p :: Δ) : 𝓚 ⟹! Δ := ⟨cut hp.get hn.get⟩

lemma root! {p} (h : p ∈ 𝓚) : 𝓚 ⟹!. p := ⟨root h⟩


def ofAxiomSubset (h : 𝓚 ⊆ 𝓛) : 𝓚 ⟹ Γ → 𝓛 ⟹ Γ :=
  Tait.Axiomatized.trans fun _ hq ↦ Tait.Axiomatized.root (Collection.subset_iff.mp h _ hq)

lemma of_axiom_subset (h : 𝓚 ⊆ 𝓛) : 𝓚 ⟹! Γ → 𝓛 ⟹! Γ := fun b ↦ ⟨ofAxiomSubset h b.get⟩

instance system : System F K := ⟨(· ⟹. ·)⟩

instance : System.Axiomatized K where
  prfAxm := fun hf ↦ Tait.Axiomatized.root <| hf
  weakening := Tait.ofAxiomSubset

lemma waekerThan_of_subset (h : 𝓚 ⊆ 𝓛) : 𝓚 ≤ₛ 𝓛 := fun _ ↦ System.Axiomatized.weakening! h

instance : System.StrongCut K K where
  cut {_ _ _ bs b} := Tait.Axiomatized.trans (fun _ hq ↦ bs hq) b

lemma provable_bot_iff_derivable_nil : 𝓚 ⟹! [] ↔ 𝓚 ⊢! ⊥ := ⟨fun b ↦ wk! b (by simp), fun b ↦ cut! b (by simpa using verum! _ _)⟩

instance : DeductiveExplosion K where
  dexp {𝓚 b p} := wk (Tait.Cut.cut b (by simpa using verum _ _)) (by simp)

/-
instance : System.Deduction K where
  ofInsert {p q 𝓚 b} := by {  }
  inv {p q 𝓚 b} :=
    let h : cons p 𝓚 ⟹ [~p ⋎ q, q] :=
      wk (show cons p 𝓚 ⟹ [~p ⋎ q] from ofEq (ofAxiomSubset (by simp) b) (by simp [DeMorgan.imply])) (by simp)
    let n : cons p 𝓚 ⟹ [~(~p ⋎ q), q] :=
      let hp : cons p 𝓚 ⟹ [p, q] := wk (show cons p 𝓚 ⊢ p from byAxm (by simp)) (by simp)
      let hq : cons p 𝓚 ⟹ [~q, q] := em (p := q) (by simp) (by simp)
      ofEq (and hp hq) (by simp)
    cut h n
-/

lemma inconsistent_iff_provable :
    Inconsistent 𝓚 ↔ 𝓚 ⟹! [] :=
  ⟨fun b ↦ ⟨cut (inconsistent_iff_provable_bot.mp b).get (by simpa using verum _ _)⟩,
   fun h ↦ inconsistent_iff_provable_bot.mpr (wk! h (by simp))⟩

lemma consistent_iff_unprovable :
    Consistent 𝓚 ↔ IsEmpty (𝓚 ⟹ []) :=
  not_iff_not.mp <| by simp [not_consistent_iff_inconsistent, inconsistent_iff_provable]

/-
lemma provable_iff_inconsistent {p} :
    𝓚 ⊢! p ↔ Inconsistent (cons (~p) 𝓚) := by
  simp [inconsistent_iff_provable, deduction_iff, DeMorgan.imply]
  constructor
  · intro h; exact cut! (of_axiom_subset (by simp) h) (root! <| by simp)
  · rintro ⟨b⟩
    exact ⟨by simpa using Tait.Axiomatized.proofOfContra b⟩

lemma refutable_iff_inconsistent {p} :
    𝓚 ⊢! ~p ↔ Inconsistent (cons p 𝓚) := by simpa using provable_iff_inconsistent (𝓚 := 𝓚) (p := ~p)

lemma consistent_insert_iff_not_refutable {p}  :
    System.Consistent (cons p 𝓚) ↔ 𝓚 ⊬! ~p := by
  simp [System.Unprovable, refutable_iff_inconsistent, System.not_inconsistent_iff_consistent]

lemma inconsistent_of_provable_and_refutable {p} (bp : 𝓚 ⊢! p) (br : 𝓚 ⊢! ~p) : Inconsistent 𝓚 :=
  inconsistent_iff_provable.mpr <| cut! bp br
-/

instance : System.Classical 𝓚 where
  mdp {p q dpq dp} :=
    let dpq : 𝓚 ⟹ [~p ⋎ q, q] := wk dpq (by simp [DeMorgan.imply])
    let dnq : 𝓚 ⟹ [~(~p ⋎ q), q] :=
      let d : 𝓚 ⟹ [p ⋏ ~q, q] := and (wk dp <| by simp) (close q)
      ofEq d (by simp)
    cut dpq dnq
  neg_equiv p := ofEq
    (show 𝓚 ⊢ (p ⋎ ~p ⋎ ⊥) ⋏ (p ⋏ ⊤ ⋎ ~p) from
      and (or <| rotate₁ <| or <| close p) (or <| and (close p) verum'))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := verum _ _
  imply₁ p q :=
    have : 𝓚 ⊢ ~p ⋎ ~q ⋎ p := or <| rotate₁ <| or <| close p
    ofEq this (by simp [DeMorgan.imply])
  imply₂ p q r :=
    have : 𝓚 ⊢ p ⋏ q ⋏ ~ r ⋎ p ⋏ ~q ⋎ ~p ⋎ r :=
      or <| rotate₁ <| or <| rotate₁ <| or <| rotate₃ <| and
        (close p)
        (and (rotate₃ <| and (close p) (close q)) (close r))
    ofEq this (by simp [DeMorgan.imply])
  and₁ p q :=
    have : 𝓚 ⊢ (~p ⋎ ~q) ⋎ p := or <| or <| close p
    ofEq this (by simp [DeMorgan.imply])
  and₂ p q :=
    have : 𝓚 ⊢ (~p ⋎ ~q) ⋎ q := or <| or <| close q
    ofEq this (by simp [DeMorgan.imply])
  and₃ p q :=
    have : 𝓚 ⊢ ~p ⋎ ~q ⋎ p ⋏ q := or <| rotate₁ <| or <| rotate₁ <| and (close p) (close q)
    ofEq this (by simp [DeMorgan.imply])
  or₁ p q :=
    have : 𝓚 ⊢ ~p ⋎ p ⋎ q := or <| rotate₁ <| or <| close p
    ofEq this (by simp [DeMorgan.imply])
  or₂ p q :=
    have : 𝓚 ⊢ ~q ⋎ p ⋎ q := or <| rotate₁ <| or <| close q
    ofEq this (by simp [DeMorgan.imply])
  or₃ p q r :=
    have : 𝓚 ⊢ p ⋏ ~ r ⋎ q ⋏ ~ r ⋎ ~p ⋏ ~q ⋎ r :=
      or <| rotate₁ <| or <| rotate₁ <| or <| and
        (rotate₃ <| and (close p) (close r))
        (rotate₂ <| and (close q) (close r))
    ofEq this (by simp [DeMorgan.imply])
  dne p :=
    have : 𝓚 ⊢ ~p ⋎ p := or <| close p
    ofEq this (by simp [DeMorgan.imply])

end Tait

end LO
