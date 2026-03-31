module

public import Foundation.Propositional.Entailment.Cl.Basic

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
* `LO.Tait`
* `LO.Gentzen`

-/

@[expose]
public section

namespace LO

class OneSided (K : Type*) (F : outParam Type*) where
  Derivation : K → List F → Type*

infix:45 " ⟹ " => OneSided.Derivation

abbrev OneSided.Derivation₁ [OneSided K F] (𝓚 : K) (φ : F) : Type _ := 𝓚 ⟹ [φ]

infix:45 " ⟹. " => OneSided.Derivation₁

abbrev OneSided.Derivable [OneSided K F] (𝓚 : K) (Δ : List F) : Prop := Nonempty (𝓚 ⟹ Δ)

infix:45 " ⟹! " => OneSided.Derivable

abbrev OneSided.Derivable₁ [OneSided K F] (𝓚 : K) (φ : F) : Prop := Nonempty (𝓚 ⟹. φ)

infix:45 " ⟹!. " => OneSided.Derivable₁

noncomputable def OneSided.Derivable.get [OneSided K F] (𝓚 : K) (Δ : List F) (h : 𝓚 ⟹! Δ) : 𝓚 ⟹ Δ :=
  Classical.choice h

class Tait (F K : Type*) [LogicalConnective F] [DeMorgan F] [AdjunctiveSet F K] extends OneSided K F where
  verum (𝓚 : K) (Δ : List F)         : 𝓚 ⟹ ⊤ :: Δ
  and {𝓚 : K} {φ ψ : F} {Δ : List F} : 𝓚 ⟹ φ :: Δ → 𝓚 ⟹ ψ :: Δ → 𝓚 ⟹ φ ⋏ ψ :: Δ
  or {𝓚 : K} {φ ψ : F} {Δ : List F}  : 𝓚 ⟹ φ :: ψ :: Δ → 𝓚 ⟹ φ ⋎ ψ :: Δ
  wk {𝓚 : K} {Δ Δ' : List F}         : 𝓚 ⟹ Δ → Δ ⊆ Δ' → 𝓚 ⟹ Δ'
  em {𝓚 : K} {φ} {Δ : List F}        : φ ∈ Δ → ∼φ ∈ Δ → 𝓚 ⟹ Δ

class Tait.Cut (F K : Type*) [LogicalConnective F] [DeMorgan F] [AdjunctiveSet F K] [Tait F K] where
  cut {𝓚 : K} {Δ : List F} {φ} : 𝓚 ⟹ φ :: Δ → 𝓚 ⟹ ∼φ :: Δ → 𝓚 ⟹ Δ

class Tait.Axiomatized (F K : Type*) [LogicalConnective F] [DeMorgan F] [AdjunctiveSet F K] [Tait F K] where
  axm {𝓚 : K} {φ} : φ ∈ 𝓚 → 𝓚 ⟹. φ
  trans {𝓚 𝓛 : K} {Γ} : ((ψ : F) → ψ ∈ 𝓚 → 𝓛 ⟹. ψ) → 𝓚 ⟹ Γ → 𝓛 ⟹ Γ

variable {F S K : Type*} [LogicalConnective F] [AdjunctiveSet F K]

namespace OneSided

variable [OneSided K F] {𝓚 : K} {Γ Δ : List F}

protected abbrev cast (d : 𝓚 ⟹ Δ) (e : Δ = Γ) : 𝓚 ⟹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

open Entailment

variable [DeMorgan F] [Tait F K]

variable {𝓚 : K} {Γ Δ : List F} {φ ψ φ₁ φ₂ φ₃ φ₄ : F}

def ofEq (b : 𝓚 ⟹ Γ) (h : Γ = Δ) : 𝓚 ⟹ Δ := h ▸ b

lemma of_eq (b : 𝓚 ⟹! Γ) (h : Γ = Δ) : 𝓚 ⟹! Δ := h ▸ b

def em' (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝓚 ⟹ Γ := em hp hn

def verum' (h : ⊤ ∈ Γ := by simp) : 𝓚 ⟹ Γ := wk (verum 𝓚 Γ) (by simp [h])

lemma verum! (𝓚 : K) (Γ : List F) : 𝓚 ⟹! ⊤ :: Γ := ⟨verum _ _⟩

lemma verum'! (h : ⊤ ∈ Γ) : 𝓚 ⟹! Γ := ⟨verum' h⟩

lemma and! (hp : 𝓚 ⟹! φ :: Γ) (hq : 𝓚 ⟹! ψ :: Γ) : 𝓚 ⟹! φ ⋏ ψ :: Γ := ⟨and hp.get hq.get⟩

lemma or! (h : 𝓚 ⟹! φ :: ψ :: Γ) : 𝓚 ⟹! φ ⋎ ψ :: Γ := ⟨or h.get⟩

lemma wk! (h : 𝓚 ⟹! Γ) (ss : Γ ⊆ Δ := by simp) : 𝓚 ⟹! Δ := ⟨wk h.get ss⟩

lemma em! (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) : 𝓚 ⟹! Γ := ⟨em hp hn⟩

def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝓚 ⟹ Γ := em hp hn

lemma close! (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝓚 ⟹! Γ := em! hp hn

def and' {φ ψ : F} (h : φ ⋏ ψ ∈ Γ) (dp : 𝓚 ⟹ φ :: Γ) (dq : 𝓚 ⟹ ψ :: Γ) : 𝓚 ⟹ Γ :=
  wk (and dp dq) (by simp [h])

def or' {φ ψ : F} (h : φ ⋎ ψ ∈ Γ) (dpq : 𝓚 ⟹ φ :: ψ :: Γ) : 𝓚 ⟹ Γ :=
  wk (or dpq) (by simp [h])

def wkTail (d : 𝓚 ⟹ Γ) : 𝓚 ⟹ φ :: Γ := wk d (by simp)

def wkAppendLeft (d : 𝓚 ⟹ Δ) : 𝓚 ⟹ Δ ++ Γ := wk d (by simp)

def wkAppendRight (d : 𝓚 ⟹ Γ) : 𝓚 ⟹ Δ ++ Γ := wk d (by simp)

def rotate₁ (d : 𝓚 ⟹ φ₂ :: φ₁ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: Γ := wk d (by simp)

def rotate₂ (d : 𝓚 ⟹ φ₃ :: φ₁ :: φ₂ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: φ₃ :: Γ :=
  wk d (by simpa using List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))

def rotate₃ (d : 𝓚 ⟹ φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ :=
  wk d (by simpa using
    List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| List.subset_cons_of_subset _ <| by simp))

variable {𝓚 𝓛 : K} {Γ : List F}

alias cut := Tait.Cut.cut

alias axm := Tait.Axiomatized.axm

lemma cut! [Cut F K] (hp : 𝓚 ⟹! φ :: Δ) (hn : 𝓚 ⟹! ∼φ :: Δ) : 𝓚 ⟹! Δ := ⟨cut hp.get hn.get⟩

lemma root! [Tait.Axiomatized F K] {φ} (h : φ ∈ 𝓚) : 𝓚 ⟹!. φ := ⟨axm h⟩

def byAxm [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) : 𝓚 ⟹ Γ := wk (axm h) (by simp_all)

lemma byAxm! [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) : 𝓚 ⟹! Γ := ⟨byAxm φ h hΓ⟩

def ofAxiomSubset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : 𝓚 ⟹ Γ → 𝓛 ⟹ Γ :=
  Tait.Axiomatized.trans fun _ hq ↦ Tait.Axiomatized.axm (AdjunctiveSet.subset_iff.mp h _ hq)

lemma of_axiom_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : 𝓚 ⟹! Γ → 𝓛 ⟹! Γ := fun b ↦ ⟨ofAxiomSubset h b.get⟩

instance system : Entailment K F := ⟨(· ⟹. ·)⟩

instance [Tait.Axiomatized F K] : Entailment.Axiomatized K where
  prfAxm := fun hf ↦ Tait.Axiomatized.axm <| hf
  weakening := Tait.ofAxiomSubset

lemma provable_bot_iff_derivable_nil [Cut F K] : 𝓚 ⟹! [] ↔ 𝓚 ⊢ ⊥ :=
  ⟨fun b ↦ wk! b (by simp), fun b ↦ cut! b (by simpa using verum! _ _)⟩

lemma waekerThan_of_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : 𝓚 ⪯ 𝓛 := ⟨fun _ ↦ Entailment.Axiomatized.weakening! h⟩

instance [Tait.Axiomatized F K] : Entailment.StrongCut K K where
  cut {_ _ _ bs b} := Tait.Axiomatized.trans (fun _ hq ↦ bs hq) b

instance [Cut F K] : DeductiveExplosion K where
  dexp {𝓚 b φ} := wk (Tait.Cut.cut b (by simpa using verum _ _)) (by simp)

/-
instance : Entailment.Deduction K where
  ofInsert {φ ψ 𝓚 b} := by {  }
  inv {φ ψ 𝓚 b} :=
    let h : cons φ 𝓚 ⟹ [∼φ ⋎ ψ, ψ] :=
      wk (show cons φ 𝓚 ⟹ [∼φ ⋎ ψ] from ofEq (ofAxiomSubset (by simp) b) (by simp [DeMorgan.imply])) (by simp)
    let n : cons φ 𝓚 ⟹ [∼(∼φ ⋎ ψ), ψ] :=
      let hp : cons φ 𝓚 ⟹ [φ, ψ] := wk (show cons φ 𝓚 ⊢! φ from byAxm (by simp)) (by simp)
      let hq : cons φ 𝓚 ⟹ [∼ψ, ψ] := em (φ := ψ) (by simp) (by simp)
      ofEq (and hp hq) (by simp)
    cut h n
-/

lemma inconsistent_iff_provable [Cut F K] :
    Inconsistent 𝓚 ↔ 𝓚 ⟹! [] :=
  ⟨fun b ↦ ⟨cut (inconsistent_iff_provable_bot.mp b).get (by simpa using verum _ _)⟩,
   fun h ↦ inconsistent_iff_provable_bot.mpr (wk! h (by simp))⟩

lemma consistent_iff_unprovable [Tait.Axiomatized F K] [Cut F K] :
    Consistent 𝓚 ↔ IsEmpty (𝓚 ⟹ []) :=
  not_iff_not.mp <| by simp [not_consistent_iff_inconsistent, inconsistent_iff_provable]

/-
lemma provable_iff_inconsistent {φ} :
    𝓚 ⊢ φ ↔ Inconsistent (cons (∼φ) 𝓚) := by
  simp [inconsistent_iff_provable, deduction_iff, DeMorgan.imply]
  constructor
  · intro h; exact cut! (of_axiom_subset (by simp) h) (root! <| by simp)
  · rintro ⟨b⟩
    exact ⟨by simpa using Tait.Axiomatized.proofOfContra b⟩

lemma refutable_iff_inconsistent {φ} :
    𝓚 ⊢ ∼φ ↔ Inconsistent (cons φ 𝓚) := by simpa using provable_iff_inconsistent (𝓚 := 𝓚) (φ := ∼φ)

lemma consistent_insert_iff_not_refutable {φ}  :
    Entailment.Consistent (cons φ 𝓚) ↔ 𝓚 ⊬ ∼φ := by
  simp [Entailment.Unprovable, refutable_iff_inconsistent, Entailment.not_inconsistent_iff_consistent]

lemma inconsistent_of_provable_and_refutable {φ} (bp : 𝓚 ⊢ φ) (br : 𝓚 ⊢ ∼φ) : Inconsistent 𝓚 :=
  inconsistent_iff_provable.mpr <| cut! bp br
-/

instance [NegInvolutive F] [Cut F K] : Entailment.Cl 𝓚 where
  mdp {φ ψ dpq dp} :=
    let dpq : 𝓚 ⟹ [∼φ ⋎ ψ, ψ] := wk dpq (by simp [DeMorgan.imply])
    let dnq : 𝓚 ⟹ [∼(∼φ ⋎ ψ), ψ] :=
      let d : 𝓚 ⟹ [φ ⋏ ∼ψ, ψ] := and (wk dp <| by simp) (close ψ)
      ofEq d (by simp)
    cut dpq dnq
  negEquiv {φ} := ofEq
    (show 𝓚 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      and (or <| rotate₁ <| or <| close φ) (or <| and (close φ) verum'))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := verum _ _
  implyK {φ ψ} :=
    have : 𝓚 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓚 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      or <| rotate₁ <| or <| rotate₁ <| or <| rotate₃ <| and
        (close φ)
        (and (rotate₃ <| and (close φ) (close ψ)) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓚 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ := or <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓚 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := or <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓚 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := or <| rotate₁ <| or <| rotate₁ <| and (close φ) (close ψ)
    ofEq this (by simp [DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓚 ⊢! ∼φ ⋎ φ ⋎ ψ := or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓚 ⊢! ∼ψ ⋎ φ ⋎ ψ := or <| rotate₁ <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓚 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      or <| rotate₁ <| or <| rotate₁ <| or <| and
        (rotate₃ <| and (close φ) (close χ))
        (rotate₂ <| and (close ψ) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  dne {φ} :=
    have : 𝓚 ⊢! ∼φ ⋎ φ := or <| close φ
    ofEq this (by simp [DeMorgan.imply])

lemma wkCut [Cut F K] (hp : 𝓚 ⟹! φ :: Δ) (hn : 𝓚 ⟹! ∼φ :: Δ) : 𝓚 ⟹! Δ := ⟨cut hp.get hn.get⟩

def modusPonens [NegInvolutive F] [Cut F K] (b : 𝓚 ⊢! φ 🡒 ψ) : 𝓚 ⟹ φ :: Γ → 𝓚 ⟹ ψ :: Γ := fun d ↦
  cut (φ := φ)
    (wk d <| by simp) <|
    cut (φ := φ 🡒 ψ)
      (wk b <| by simp) <|
      have : 𝓚 ⟹ φ ⋏ ∼ψ :: ∼φ :: ψ :: Γ := and (em' φ) (em' ψ)
      ofEq this <| by simp [DeMorgan.imply]

def modusPonens! [NegInvolutive F] [Cut F K] (b : 𝓚 ⊢ φ 🡒 ψ) : 𝓚 ⟹! φ :: Γ → 𝓚 ⟹! ψ :: Γ := fun d ↦ ⟨modusPonens b.get d.get⟩

def cutFalsum [Cut F K] (d : 𝓚 ⟹ ⊥ :: Γ) : 𝓚 ⟹ Γ := Tait.cut (φ := ⊥) (Tait.wk d <| by simp) (ofEq (verum _ Γ) <| by simp)

def orReversion [Cut F K] (d : 𝓚 ⟹ φ ⋎ ψ :: Γ) : 𝓚 ⟹ φ :: ψ :: Γ :=
  Tait.cut (φ := φ ⋎ ψ)
    (wk d <| List.cons_subset_cons _ <| by simp)
    ( have : 𝓚 ⟹ ∼φ ⋏ ∼ψ :: φ :: ψ :: Γ := and (em' φ) (em' ψ)
      ofEq this (by simp) )

def disjConsOfAppend {Γ Δ} (d : 𝓚 ⟹ Γ ++ Δ) : 𝓚 ⟹ Γ.disj :: Δ :=
  match Γ with
  |     [] => wk d (by simp)
  | φ :: Γ => or <|
    have : 𝓚 ⟹ Γ ++ φ :: Δ := wk d <| by simp
    wk (disjConsOfAppend this) (by simp)

def proofOfDerivation (d : 𝓚 ⟹ Γ) : 𝓚 ⊢! Γ.disj := disjConsOfAppend (Γ := Γ) (Δ := []) (ofEq d (by simp))

def AppendOfDisjCons [Cut F K] {Γ Δ} (d : 𝓚 ⟹ Γ.disj :: Δ) : 𝓚 ⟹ Γ ++ Δ :=
  match Γ with
  |     [] => ofEq (cutFalsum d) (by simp)
  | φ :: Γ =>
    have : 𝓚 ⟹ Γ.disj :: φ :: Δ := wk (orReversion d) (by simp)
    wk (AppendOfDisjCons this) (by simp)

def derivationOfProof [Cut F K] (d : 𝓚 ⊢! Γ.disj) : 𝓚 ⟹ Γ := ofEq (AppendOfDisjCons d) (by simp)

lemma derivable_iff_provable_disj [Cut F K] : 𝓚 ⟹! Γ ↔ 𝓚 ⊢ Γ.disj :=
  ⟨fun h ↦ ⟨proofOfDerivation h.get⟩, fun h ↦ ⟨derivationOfProof h.get⟩⟩

end Tait

end LO

end
