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

def weakening (d : 𝔇 Γ) (h : Γ ⊆ Δ := by simp) : 𝔇 Δ := wk d (by simp [h])

def rotate (d : 𝔇 (φ :: Γ)) : 𝔇 (Γ ++ [φ]) := weakening d

def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ := wk (identity φ) (by simp_all)

def top (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ := wk verum (by simp [h])

def tensor {φ ψ : F} (dφ : 𝔇 (φ :: Γ)) (dψ : 𝔇 (ψ :: Δ)) : 𝔇 (φ ⋏ ψ :: Γ ++ Δ) :=
  and (wk dφ (by simp)) (wk dψ (by simp))

def swap₁ (d : 𝔇 (φ₂ :: φ₁ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: Γ) := wk d (by simp)

def swap₂ (d : 𝔇 (φ₃ :: φ₁ :: φ₂ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: Γ) :=
  wk d (by grind)

def swap₃ (d : 𝔇 (φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ) :=
  wk d (by grind)

alias cut := OneSidedLK.Cut.cut

def eCut [Cut 𝔇] (d₁ : 𝔇 (φ :: Γ)) (d₂ : 𝔇 (ψ :: Δ)) (e : ∼φ = ψ := by simp) : 𝔇 (Γ ++ Δ) := cut d₁ (cast d₂ (by simp [e]))

def disj₂ {Γ Δ : List F} [Cut 𝔇] : 𝔇 (Γ ++ Δ) → 𝔇 (⋁Γ :: Δ) := fun d ↦
  match Γ with
  |               [] => weakening d
  |              [φ] => d
  |           [φ, ψ] => or d
  | φ :: ψ :: χ :: Γ => by
    let Φ := ⋁(χ :: Γ)
    have : 𝔇 ((φ ⋎ ψ :: χ :: Γ) ++ Δ) := or d
    have d₁ : 𝔇 ((φ ⋎ ψ) ⋎ Φ :: Δ) := disj₂ this
    have d₂ : 𝔇 [(∼φ ⋏ ∼ψ) ⋏ ∼Φ, φ ⋎ ψ ⋎ Φ] :=
      have : 𝔇 [φ, ψ ⋎ Φ, (∼φ ⋏ ∼ψ) ⋏ ∼Φ] :=
        weakening <| or <| rotate <| rotate <|
          tensor (tensor (rotate (identity (𝔇 := 𝔇) φ)) (rotate (identity  ψ))) (rotate (identity Φ))
      rotate <| or <| this
    exact eCut d₂ d₁
  termination_by _ => Γ.length

def conj₂ {Γ Δ : List F} (d : (φ : F) → φ ∈ Γ → 𝔇 (φ :: Δ)) : 𝔇 (⋀Γ :: Δ) :=
  match Γ with
  |          [] => weakening verum
  |         [φ] => d φ (by simp)
  | φ :: ψ :: Γ =>
    have : 𝔇 (⋀(ψ :: Γ) :: Δ) := conj₂ (Γ := ψ :: Γ) (fun χ h ↦ d χ (by simp_all))
    and (d φ (by simp)) this

open Entailment

/-- An entailment relation which is determined solely by derivability. -/
class PrincipalEntailment (𝔇 : outParam (List F → Type*)) {P : Type*} [Entailment P F] (𝓟 : P) where
  equiv {φ} : 𝓟 ⊢! φ ≃ 𝔇 [φ]

namespace PrincipalEntailment

variable {P : Type*} [Entailment P F] {𝓟 : P} [PrincipalEntailment 𝔇 𝓟]

omit [LogicalConnective F] [DeMorgan F] [NegInvolutive F] [OneSidedLK 𝔇] in
lemma provable_iff :
    𝓟 ⊢ φ ↔ Nonempty (𝔇 [φ]) := by
  simpa using OneSidedLK.PrincipalEntailment.equiv.nonempty_congr

variable [OneSidedLK.Cut 𝔇] (𝓟)

instance : Entailment.ModusPonens 𝓟 where
  mdp {φ ψ} b₁ b₂ :=
    let b₁ := equiv b₁
    let b₂ := equiv b₂
    have : 𝔇 [∼(φ 🡒 ψ), ∼φ, ψ] := cast (tensor (𝔇 := 𝔇) (identity φ) (identity (∼ψ))) (by simp [DeMorgan.imply])
    have : 𝔇 [∼φ, ψ] := wk (cut b₁ this) (by simp)
    have : 𝔇 [ψ] := wk (cut b₂ this) (by simp)
    equiv.symm <| cast this

instance : Entailment.Cl 𝓟 where
  negEquiv {φ} := Entailment.cast
    (show 𝓟 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      equiv.symm <| and (or <| swap₁ <| or <| close φ) (or <| and (identity φ) top))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := equiv.symm <| verum
  implyK {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := equiv.symm <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓟 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      equiv.symm <| or <| swap₁ <| or <| swap₁ <| or <| swap₃ <| and
        (close φ)
        (and (swap₃ <| and (close φ) (close ψ)) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓟 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ :=  equiv.symm <|or <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓟 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := equiv.symm <| or <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := equiv.symm <| or <| swap₁ <| or <| swap₁ <| and (close φ) (close ψ)
    Entailment.cast this (by simp [DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ φ ⋎ ψ := equiv.symm <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓟 ⊢! ∼ψ ⋎ φ ⋎ ψ := equiv.symm <| or <| swap₁ <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓟 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      equiv.symm <| or <| swap₁ <| or <| swap₁ <| or <| and
        (swap₃ <| and (close φ) (close χ))
        (swap₂ <| and (close ψ) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  dne {φ} :=
    have : 𝓟 ⊢! ∼φ ⋎ φ := equiv.symm <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])

variable {𝓟}

lemma derivable_iff_provable_disj : Nonempty (𝔇 Γ) ↔ 𝓟 ⊢ ⋁Γ := by
  constructor
  · rintro ⟨d⟩
    have : 𝔇 (Γ ++ []) := cast d
    exact provable_iff.mpr ⟨disj₂ this⟩
  · rintro h
    have d₁ : 𝔇 [⋁Γ] := (provable_iff.mp h).some
    have d₂ : 𝔇 (⋀(∼Γ) :: Γ) := conj₂ fun φ h ↦ close φ (by simp) (by simp_all)
    exact ⟨eCut d₁ d₂⟩

end PrincipalEntailment

abbrev Pullback (𝔇 : List F → Type*) {G : Type*} [LogicalConnective G] (f : G →ˡᶜ F) : List G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)

namespace Pullback

variable {G : Type*} [LogicalConnective G] [DeMorgan G] [NegInvolutive G] {f : G →ˡᶜ F}

def cast (d : 𝔇 Δ) (h : Δ = Γ.map f := by simp) : Pullback 𝔇 f Γ := by
  unfold Pullback
  exact h ▸ d

def uncast (d : Pullback 𝔇 f Γ) (h : Δ = Γ.map f := by simp) : 𝔇 Δ := h ▸ d

instance oneSidedLK [OneSidedLK 𝔇] : OneSidedLK (Pullback 𝔇 f) where
  identity φ := cast <| identity (f φ)
  wk {Δ Γ} d h := cast (wk d (List.map_subset f h) : 𝔇 (Γ.map f)) (by simp)
  verum := cast verum
  and d₁ d₂ := cast <| and d₁ d₂
  or d := cast <| or d

instance cut [Cut 𝔇] : Cut (Pullback 𝔇 f) where
  cut {φ Γ Δ} bp bn :=
    have bp : 𝔇 (f φ :: Γ.map f) := uncast bp
    have bn : 𝔇 (∼f φ :: Δ.map f) := uncast bn
    cast (Cut.cut bp bn)

instance {P : Type*} [Entailment P F] (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] :
    PrincipalEntailment (Pullback 𝔇 f) (Entailment.pullback 𝓟 f) where
  equiv {φ} := PrincipalEntailment.equiv (φ := f φ)

omit [DeMorgan F] [NegInvolutive F] [OneSidedLK 𝔇] [DeMorgan G] [NegInvolutive G] in
@[simp] lemma nonempty_iff {Γ} : Nonempty (Pullback 𝔇 f Γ) ↔ Nonempty (𝔇 (Γ.map f)) := by simp [Pullback]

omit [DeMorgan F] [NegInvolutive F] [OneSidedLK 𝔇] [DeMorgan G] [NegInvolutive G] in
@[simp] lemma isEmpty_iff {Γ} : IsEmpty (Pullback 𝔇 f Γ) ↔ IsEmpty (𝔇 (Γ.map f)) := by simp [Pullback]

end Pullback

/-- An entailment relation which is determined by a context and derivability. -/
class ContextualEntailment (𝔇 : outParam (List F → Type*)) (S : Type*) [Entailment S F] [AdjunctiveSet F S] where
  equiv {𝓢 : S} {φ} : 𝓢 ⊢! φ ≃ (l : {l : List F // ∀ φ ∈ l, φ ∈ 𝓢}) × 𝔇 (φ :: ∼l)

namespace ContextualEntailment

variable {S : Type*} [Entailment S F] [AdjunctiveSet F S] [ContextualEntailment 𝔇 S]

omit [DeMorgan F] [NegInvolutive F] [OneSidedLK 𝔇] in
lemma provable_iff {𝓢 : S} :
    𝓢 ⊢ φ ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (φ :: ∼Γ)) := by
  simpa using equiv.nonempty_congr

def toProof (𝓢 : S) (d : 𝔇 [φ]) : 𝓢 ⊢! φ := equiv.symm ⟨⟨[], by simp⟩, d⟩

def ofAxiom {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ :=
  equiv.symm ⟨⟨[φ], by simp_all⟩, identity φ⟩

def ofAxiomSubset {𝓢 𝓤 : S} : 𝓢 ⊢! φ → 𝓢 ⊆ 𝓤 → 𝓤 ⊢! φ := fun b h ↦
  have ⟨l, d⟩ := equiv b
  equiv.symm
    ⟨⟨l, fun φ hφ ↦ AdjunctiveSet.subset_iff.mp h _ (l.prop φ hφ)⟩, d⟩

instance : Entailment.Axiomatized S where
  prfAxm h := ofAxiom h
  weakening h d := ofAxiomSubset d h

variable [OneSidedLK.Cut 𝔇]

instance (𝓢 : S) : Entailment.ModusPonens 𝓢 where
  mdp {φ ψ} b₁ b₂ :=
    let ⟨Γ₁, b₁⟩ := equiv b₁
    let ⟨Γ₂, b₂⟩ := equiv b₂
    have : 𝔇 [∼(φ 🡒 ψ), ∼φ, ψ] := cast (tensor (𝔇 := 𝔇) (identity φ) (identity (∼ψ))) (by simp [DeMorgan.imply])
    have : 𝔇 (∼φ :: ψ :: ∼↑Γ₁) := wk (cut b₁ this) (by simp)
    have : 𝔇 (ψ :: ∼↑Γ₁ ++ ∼↑Γ₂) := wk (cut b₂ this) (by simp)
    equiv.symm ⟨⟨Γ₁ ++ Γ₂, by simp; grind⟩, cast this⟩

instance : Entailment.StrongCut S S where
  cut {T U φ bs b} :=
  let rec bl (l : List F) (hl : ∀ ψ ∈ l, ψ ∈ U) (χ) (d : 𝔇 (χ :: ∼l)) : T ⊢! χ :=
    match l with
    |     [] => equiv.symm ⟨⟨[], by simp⟩, d⟩
    | ψ :: l =>
      have bχ : T ⊢! ψ 🡒 χ :=
        Entailment.cast (bl l (by simp at hl; grind) (∼ψ ⋎ χ) (OneSidedLK.or <| OneSidedLK.swap₁ d))
        (by simp [DeMorgan.imply])
      have bψ : T ⊢! ψ := bs (show ψ ∈ U by simp at hl; grind)
      Entailment.mdp bχ bψ
  have ⟨l, hl⟩ := equiv b
  bl l l.prop φ hl

instance : Entailment.DeductiveExplosion S where
  dexp b φ :=
    have ⟨Γ, b⟩ := equiv b
    equiv.symm
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

instance cl (𝓢 : S) : Entailment.Cl 𝓢 where
  negEquiv {φ} := Entailment.cast
    (show 𝓢 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      toProof _ <| and (or <| swap₁ <| or <| close φ) (or <| and (identity φ) top))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := toProof _ <| verum
  implyK {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := toProof _ <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      toProof _ <| or <| swap₁ <| or <| swap₁ <| or <| swap₃ <| and
        (close φ)
        (and (swap₃ <| and (close φ) (close ψ)) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ :=  toProof _ <|or <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := toProof _ <| or <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := toProof _ <| or <| swap₁ <| or <| swap₁ <| and (close φ) (close ψ)
    Entailment.cast this (by simp [DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ ⋎ ψ := toProof _ <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓢 ⊢! ∼ψ ⋎ φ ⋎ ψ := toProof _ <| or <| swap₁ <| or <| close ψ
    Entailment.cast this (by simp [DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      toProof _ <| or <| swap₁ <| or <| swap₁ <| or <| and
        (swap₃ <| and (close φ) (close χ))
        (swap₂ <| and (close ψ) (close χ))
    Entailment.cast this (by simp [DeMorgan.imply])
  dne {φ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ := toProof _ <| or <| close φ
    Entailment.cast this (by simp [DeMorgan.imply])

variable {P : Type*} [Entailment P F]

omit [DeMorgan F] [OneSidedLK 𝔇] [Cut 𝔇] in
lemma empty_provable_iff_eprovable {𝓟 : P} [PrincipalEntailment 𝔇 𝓟] :
    (∅ : S) ⊢ φ ↔ 𝓟 ⊢ φ := by
  constructor
  · rintro ⟨d⟩
    let ⟨l, d⟩ := equiv d
    have : 𝓟 ⊢! φ := PrincipalEntailment.equiv.symm <| cast d <| by
      have : ∀ φ, φ ∉ (l : List F) := by simpa using l.prop
      simp [List.eq_nil_iff_forall_not_mem]; grind
    exact ⟨this⟩
  · rintro ⟨b⟩
    have : 𝔇 [φ] := PrincipalEntailment.equiv b
    exact ⟨equiv.symm ⟨⟨[], by simp⟩, this⟩⟩

lemma iff_context {𝓢 : S} {𝓟 : P} [PrincipalEntailment 𝔇 𝓟] :
    𝓢 ⊢ φ ↔ AdjunctiveSet.set 𝓢 *⊢[𝓟] φ := by
  constructor
  · rintro h
    have ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
    have : 𝓟 ⊢ ⋀Γ 🡒 φ := by
      have : 𝔇 (∼Γ ++ [φ]) := weakening d
      have : Nonempty (𝔇 [⋀Γ 🡒 φ]) := by simpa [DeMorgan.imply] using Nonempty.intro (or <| disj₂ this)
      exact PrincipalEntailment.provable_iff.mpr this
    refine ⟨⟨Γ, by simpa using hΓ, this.some⟩⟩
  · rintro ⟨Γ, h, d⟩
    have : 𝓟 ⊢! ⋀Γ 🡒 φ := d
    have d : 𝔇 [⋁(∼Γ) ⋎ φ] := cast (PrincipalEntailment.equiv this) (by simp [DeMorgan.imply])
    have : 𝔇 (⋀Γ ⋏ ∼φ :: φ :: ∼Γ) :=
      have : 𝔇 (⋀Γ :: ∼Γ) := conj₂ fun φ h ↦ close φ (by simp) (by simp [h])
      weakening <| tensor this (rotate <| identity φ)
    have : 𝔇 (φ :: ∼Γ) := eCut d this
    refine provable_iff.mpr ⟨Γ, h, ⟨this⟩⟩

lemma of_principal_provable {𝓟 : P} [PrincipalEntailment 𝔇 𝓟] {𝓢 : S} : 𝓟 ⊢ φ → 𝓢 ⊢ φ := fun h ↦
  iff_context.mpr (Entailment.Context.of! h)

open Classical in
noncomputable abbrev deduction (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] : Entailment.Deduction S where
  ofInsert {φ ψ 𝓢 b} :=
    have : AdjunctiveSet.set (Adjoin.adjoin φ 𝓢) *⊢[𝓟] ψ := iff_context.mp ⟨b⟩
    have : AdjunctiveSet.set 𝓢 *⊢[𝓟] φ 🡒 ψ := Context.deduct! <| by simpa using this
    (iff_context.mpr this).get
  inv {φ ψ 𝓢 b} :=
    have : AdjunctiveSet.set (Adjoin.adjoin φ 𝓢) *⊢[𝓟] ψ := by simpa using Context.deductInv! (iff_context.mp ⟨b⟩)
    (iff_context.mpr this).get

end ContextualEntailment

end OneSidedLK

end LO

end
