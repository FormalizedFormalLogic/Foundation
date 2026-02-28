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

class OneSidedLK {F : Type*} [LogicalConnective F] [DeMorgan F] (𝔇 : List F → Type*) where
  identity (φ) : 𝔇 [φ, ∼φ]
  wk : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 [⊤]
  and : 𝔇 (φ :: Γ) → 𝔇 (ψ :: Γ) → 𝔇 (φ ⋏ ψ :: Γ)
  or : 𝔇 (φ :: ψ :: Γ) → 𝔇 (φ ⋎ ψ :: Γ)

class OneSidedLK.Cut
    {F : Type*} [LogicalConnective F] [DeMorgan F] (𝔇 : List F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (φ :: Γ) → 𝔇 (∼φ :: Γ) → 𝔇 Γ

class OneSidedLK.EquivEntailment
    {F : Type*} [LogicalConnective F] [DeMorgan F] (𝔇 : outParam (List F → Type*))
    (S : Type*) [Entailment S F] [AdjunctiveSet F S] where
  equiv {𝓢 : S} : (l : {l : List F // ∀ φ ∈ l, φ ∈ 𝓢}) × 𝔇 (φ :: ∼l) ≃ 𝓢 ⊢! φ

variable {F S K : Type*} [LogicalConnective F] [AdjunctiveSet F K]

namespace OneSidedLK

variable {F : Type*} [LogicalConnective F] [DeMorgan F] {𝔇 : List F → Type*} [OneSidedLK 𝔇]

def cast (b : 𝔇 Γ) (h : Γ = Δ := by simp) : 𝔇 Δ := h ▸ b

def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ := wk (identity φ) (by simp_all)

def verum' (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ := wk verum (by simp [h])

def and' {φ ψ : F} (h : φ ⋏ ψ ∈ Γ) (dp : 𝔇 (φ :: Γ)) (dq : 𝔇 (ψ :: Γ)) : 𝔇 Γ :=
  wk (and dp dq) (by simp [h])

def or' {φ ψ : F} (h : φ ⋎ ψ ∈ Γ) (dpq : 𝔇 (φ :: ψ :: Γ)) : 𝔇 Γ :=
  wk (or dpq) (by simp [h])

def wkTail (d : 𝔇 Γ) : 𝔇 (φ :: Γ) := wk d (by simp)

def wkAppendLeft (d : 𝔇 Δ) : 𝔇 (Δ ++ Γ) := wk d (by simp)

def wkAppendRight (d : 𝔇 Γ) : 𝔇 (Δ ++ Γ) := wk d (by simp)

def rotate₁ (d : 𝔇 (φ₂ :: φ₁ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: Γ) := wk d (by simp)

def rotate₂ (d : 𝔇 (φ₃ :: φ₁ :: φ₂ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: Γ) :=
  wk d (by simpa using List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))

def rotate₃ (d : 𝔇 (φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ) :=
  wk d (by simpa using
    List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| List.subset_cons_of_subset _ <| by simp))

alias cut := OneSidedLK.Cut.cut

open Entailment

variable {S : Type*} [Entailment S F] [AdjunctiveSet F S]

def ofAxiom [OneSidedLK.EquivEntailment 𝔇 S] {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ :=
  OneSidedLK.EquivEntailment.equiv ⟨⟨[φ], by simp_all⟩, identity φ⟩

def ofAxiomSubset [OneSidedLK.EquivEntailment 𝔇 S] {𝓢 𝓤 : S} : 𝓢 ⊢! φ → 𝓢 ⊆ 𝓤 → 𝓤 ⊢! φ := fun b h ↦
  have ⟨l, d⟩ := OneSidedLK.EquivEntailment.equiv.symm b
  OneSidedLK.EquivEntailment.equiv
    ⟨⟨l, fun φ hφ ↦ AdjunctiveSet.subset_iff.mp h _ (l.prop φ hφ)⟩, d⟩

instance [OneSidedLK.EquivEntailment 𝔇 S] : Entailment.Axiomatized S where
  prfAxm h := ofAxiom h
  weakening h d := ofAxiomSubset d h

lemma waekerThan_of_subset [OneSidedLK.EquivEntailment 𝔇 S] {𝓢 𝓤 : S} (h : 𝓢 ⊆ 𝓤) : 𝓢 ⪯ 𝓤 :=
  ⟨fun _ ↦ Entailment.Axiomatized.weakening! h⟩

instance [OneSidedLK.EquivEntailment 𝔇 S] : Entailment.StrongCut S S where
  cut {T U φ bs b} := by {  }
/--/
lemma of_axiom_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : 𝔇! Γ → 𝓛 ⟹! Γ := fun b ↦ ⟨ofAxiomSubset h b.get⟩

instance system : Entailment K F := ⟨(· ⟹. ·)⟩



lemma provable_bot_iff_derivable_nil [Cut F K] : 𝔇! [] ↔ 𝓚 ⊢ ⊥ :=
  ⟨fun b ↦ wk! b (by simp), fun b ↦ cut! b (by simpa using verum! _ _)⟩





instance [Cut F K] : DeductiveExplosion K where
  dexp {𝓚 b φ} := wk (Tait.Cut.cut b (by simpa using verum _ _)) (by simp)

/-
instance : Entailment.Deduction K where
  ofInsert {φ ψ 𝓚 b} := by {  }
  inv {φ ψ 𝓚 b} :=
    let h : cons φ 𝔇 [∼φ ⋎ ψ, ψ] :=
      wk (show cons φ 𝔇 [∼φ ⋎ ψ] from ofEq (ofAxiomSubset (by simp) b) (by simp [DeMorgan.imply])) (by simp)
    let n : cons φ 𝔇 [∼(∼φ ⋎ ψ), ψ] :=
      let hp : cons φ 𝔇 [φ, ψ] := wk (show cons φ 𝓚 ⊢! φ from byAxm (by simp)) (by simp)
      let hq : cons φ 𝔇 [∼ψ, ψ] := em (φ := ψ) (by simp) (by simp)
      ofEq (and hp hq) (by simp)
    cut h n
-/

lemma inconsistent_iff_provable [Cut F K] :
    Inconsistent 𝓚 ↔ 𝔇! [] :=
  ⟨fun b ↦ ⟨cut (inconsistent_iff_provable_bot.mp b).get (by simpa using verum _ _)⟩,
   fun h ↦ inconsistent_iff_provable_bot.mpr (wk! h (by simp))⟩

lemma consistent_iff_unprovable [Tait.Axiomatized F K] [Cut F K] :
    Consistent 𝓚 ↔ IsEmpty (𝔇 []) :=
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
    let dpq : 𝔇 [∼φ ⋎ ψ, ψ] := wk dpq (by simp [DeMorgan.imply])
    let dnq : 𝔇 [∼(∼φ ⋎ ψ), ψ] :=
      let d : 𝔇 [φ ⋏ ∼ψ, ψ] := and (wk dp <| by simp) (close ψ)
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

lemma wkCut [Cut F K] (hp : 𝔇! φ :: Δ) (hn : 𝔇! ∼φ :: Δ) : 𝔇! Δ := ⟨cut hp.get hn.get⟩

def modusPonens [NegInvolutive F] [Cut F K] (b : 𝓚 ⊢! φ ➝ ψ) : 𝔇 φ :: Γ → 𝔇 ψ :: Γ := fun d ↦
  cut (φ := φ)
    (wk d <| by simp) <|
    cut (φ := φ ➝ ψ)
      (wk b <| by simp) <|
      have : 𝔇 φ ⋏ ∼ψ :: ∼φ :: ψ :: Γ := and (em' φ) (em' ψ)
      ofEq this <| by simp [DeMorgan.imply]

def modusPonens! [NegInvolutive F] [Cut F K] (b : 𝓚 ⊢ φ ➝ ψ) : 𝔇! φ :: Γ → 𝔇! ψ :: Γ := fun d ↦ ⟨modusPonens b.get d.get⟩

def cutFalsum [Cut F K] (d : 𝔇 ⊥ :: Γ) : 𝔇 Γ := Tait.cut (φ := ⊥) (Tait.wk d <| by simp) (ofEq (verum _ Γ) <| by simp)

def orReversion [Cut F K] (d : 𝔇 φ ⋎ ψ :: Γ) : 𝔇 φ :: ψ :: Γ :=
  Tait.cut (φ := φ ⋎ ψ)
    (wk d <| List.cons_subset_cons _ <| by simp)
    ( have : 𝔇 ∼φ ⋏ ∼ψ :: φ :: ψ :: Γ := and (em' φ) (em' ψ)
      ofEq this (by simp) )

def disjConsOfAppend {Γ Δ} (d : 𝔇 Γ ++ Δ) : 𝔇 Γ.disj :: Δ :=
  match Γ with
  |     [] => wk d (by simp)
  | φ :: Γ => or <|
    have : 𝔇 Γ ++ φ :: Δ := wk d <| by simp
    wk (disjConsOfAppend this) (by simp)

def proofOfDerivation (d : 𝔇 Γ) : 𝓚 ⊢! Γ.disj := disjConsOfAppend (Γ := Γ) (Δ := []) (ofEq d (by simp))

def AppendOfDisjCons [Cut F K] {Γ Δ} (d : 𝔇 Γ.disj :: Δ) : 𝔇 Γ ++ Δ :=
  match Γ with
  |     [] => ofEq (cutFalsum d) (by simp)
  | φ :: Γ =>
    have : 𝔇 Γ.disj :: φ :: Δ := wk (orReversion d) (by simp)
    wk (AppendOfDisjCons this) (by simp)

def derivationOfProof [Cut F K] (d : 𝓚 ⊢! Γ.disj) : 𝔇 Γ := ofEq (AppendOfDisjCons d) (by simp)

lemma derivable_iff_provable_disj [Cut F K] : 𝔇! Γ ↔ 𝓚 ⊢ Γ.disj :=
  ⟨fun h ↦ ⟨proofOfDerivation h.get⟩, fun h ↦ ⟨derivationOfProof h.get⟩⟩

end Tait

end LO

end
