module

public import Foundation.Propositional.Entailment.Cl.Basic

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
- `LO.OneSidedLK`
-/

@[expose]
public section

namespace LO

/-! ## One-sided $\mathbf{LK}$ -/

class OneSidedLK {F : Type*} [LogicalConnective F] [DeMorgan F] [NegInvolutive F] (𝔇 : List F → Type*) where
  identity (φ) : 𝔇 [φ, ∼φ]
  wk : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 [⊤]
  and : 𝔇 (φ :: Γ) → 𝔇 (ψ :: Γ) → 𝔇 (φ ⋏ ψ :: Γ)
  or : 𝔇 (φ :: ψ :: Γ) → 𝔇 (φ ⋎ ψ :: Γ)

class OneSidedLK.Cut
    {F : Type*} [LogicalConnective F] [DeMorgan F] [NegInvolutive F] (𝔇 : List F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (φ :: Γ) → 𝔇 (∼φ :: Δ) → 𝔇 (Γ ++ Δ)

namespace OneSidedLK

variable {F : Type*} [LogicalConnective F] [DeMorgan F] [NegInvolutive F] {𝔇 : List F → Type*} [OneSidedLK 𝔇]

def cast (b : 𝔇 Γ) (h : Γ = Δ := by simp) : 𝔇 Δ := h ▸ b

def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ := wk (identity φ) (by simp_all)

def verum' (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ := wk verum (by simp [h])

def tensor {φ ψ : F} (dφ : 𝔇 (φ :: Γ)) (dψ : 𝔇 (ψ :: Δ)) : 𝔇 (φ ⋏ ψ :: Γ ++ Δ) :=
  and (wk dφ (by simp)) (wk dψ (by simp))

def rotate₁ (d : 𝔇 (φ₂ :: φ₁ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: Γ) := wk d (by simp)

def rotate₂ (d : 𝔇 (φ₃ :: φ₁ :: φ₂ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: Γ) :=
  wk d (by simpa using List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))

def rotate₃ (d : 𝔇 (φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ) :=
  wk d (by simpa using
    List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| List.subset_cons_of_subset _ <| by simp))

alias cut := OneSidedLK.Cut.cut

protected class Entailment (𝔇 : outParam (List F → Type*)) (S : Type*) [Entailment S F] [AdjunctiveSet F S] where
  equiv {𝓢 : S} {φ} : 𝓢 ⊢! φ ≃ (l : {l : List F // ∀ φ ∈ l, φ ∈ 𝓢}) × 𝔇 (φ :: ∼l)

open Entailment

variable {S : Type*} [Entailment S F] [AdjunctiveSet F S] [OneSidedLK.Entailment 𝔇 S]

omit [DeMorgan F] [NegInvolutive F] [OneSidedLK 𝔇] in
lemma provable_iff {𝓢 : S} :
    𝓢 ⊢ φ ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (φ :: ∼Γ)) := by
  simpa using OneSidedLK.Entailment.equiv.nonempty_congr

def toProof (𝓢 : S) (d : 𝔇 [φ]) : 𝓢 ⊢! φ := OneSidedLK.Entailment.equiv.symm ⟨⟨[], by simp⟩, d⟩

def ofAxiom {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ :=
  OneSidedLK.Entailment.equiv.symm ⟨⟨[φ], by simp_all⟩, identity φ⟩

def ofAxiomSubset {𝓢 𝓤 : S} : 𝓢 ⊢! φ → 𝓢 ⊆ 𝓤 → 𝓤 ⊢! φ := fun b h ↦
  have ⟨l, d⟩ := OneSidedLK.Entailment.equiv b
  OneSidedLK.Entailment.equiv.symm
    ⟨⟨l, fun φ hφ ↦ AdjunctiveSet.subset_iff.mp h _ (l.prop φ hφ)⟩, d⟩

instance : Entailment.Axiomatized S where
  prfAxm h := ofAxiom h
  weakening h d := ofAxiomSubset d h

variable [OneSidedLK.Cut 𝔇]

instance (𝓢 : S) : Entailment.ModusPonens 𝓢 where
  mdp {φ ψ} b₁ b₂ :=
    let ⟨Γ₁, b₁⟩ := OneSidedLK.Entailment.equiv b₁
    let ⟨Γ₂, b₂⟩ := OneSidedLK.Entailment.equiv b₂
    have : 𝔇 [∼(φ ➝ ψ), ∼φ, ψ] := cast (tensor (𝔇 := 𝔇) (identity φ) (identity (∼ψ))) (by simp [DeMorgan.imply])
    have : 𝔇 (∼φ :: ψ :: ∼↑Γ₁) := wk (cut b₁ this) (by simp)
    have : 𝔇 (ψ :: ∼↑Γ₁ ++ ∼↑Γ₂) := wk (cut b₂ this) (by simp)
    OneSidedLK.Entailment.equiv.symm ⟨⟨Γ₁ ++ Γ₂, by simp; grind⟩, cast this⟩

instance : Entailment.StrongCut S S where
  cut {T U φ bs b} :=
  let rec bl (l : List F) (hl : ∀ ψ ∈ l, ψ ∈ U) (χ) (d : 𝔇 (χ :: ∼l)) : T ⊢! χ :=
    match l with
    |     [] => OneSidedLK.Entailment.equiv.symm ⟨⟨[], by simp⟩, d⟩
    | ψ :: l =>
      have bχ : T ⊢! ψ ➝ χ :=
        Entailment.cast (bl l (by simp at hl; grind) (∼ψ ⋎ χ) (OneSidedLK.or <| OneSidedLK.rotate₁ d))
        (by simp [DeMorgan.imply])
      have bψ : T ⊢! ψ := bs (show ψ ∈ U by simp at hl; grind)
      Entailment.mdp bχ bψ
  have ⟨l, hl⟩ := OneSidedLK.Entailment.equiv b
  bl l l.prop φ hl

instance : Entailment.DeductiveExplosion S where
  dexp b φ :=
    have ⟨Γ, b⟩ := OneSidedLK.Entailment.equiv b
    OneSidedLK.Entailment.equiv.symm
    ⟨ Γ,
      have : 𝔇 [∼⊥] := cast verum (by simp)
      wk (cut b this) (by simp) ⟩

lemma inconsistent_iff {𝓢 : S} :
    Entailment.Inconsistent 𝓢 ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (∼Γ)) := calc
  _ ↔ 𝓢 ⊢ ⊥ := Entailment.inconsistent_iff_provable_bot
  _ ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (⊥ :: ∼Γ)) := by simp [provable_iff]
  _ ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (∼Γ)) := by
    constructor
    · rintro ⟨Γ, hΓ, ⟨d⟩⟩
      have : 𝔇 [(∼⊥ : F)] := cast verum
      exact ⟨Γ, hΓ, ⟨cast (cut d this)⟩⟩
    · rintro ⟨Γ, hΓ, ⟨d⟩⟩
      exact ⟨Γ, hΓ, ⟨wk d (by simp)⟩⟩

instance (𝓢 : S) : Entailment.Cl 𝓢 where
  negEquiv {φ} := Entailment.cast
    (show 𝓢 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      toProof _ <| and (or <| rotate₁ <| or <| close φ) (or <| and (identity φ) verum'))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := toProof _ <| verum
  implyK {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := toProof _ <| or <| rotate₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      toProof _ <| or <| rotate₁ <| or <| rotate₁ <| or <| rotate₃ <| and
        (close φ)
        (and (rotate₃ <| and (close φ) (close ψ)) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ :=  toProof _ <|or <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := toProof _ <| or <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := toProof _ <| or <| rotate₁ <| or <| rotate₁ <| and (close φ) (close ψ)
    Entailment.cast this (by simp [DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ ⋎ ψ := toProof _ <| or <| rotate₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓢 ⊢! ∼ψ ⋎ φ ⋎ ψ := toProof _ <| or <| rotate₁ <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      toProof _ <| or <| rotate₁ <| or <| rotate₁ <| or <| and
        (rotate₃ <| and (close φ) (close χ))
        (rotate₂ <| and (close ψ) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  dne {φ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ := toProof _ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])

end OneSidedLK

end LO

end
