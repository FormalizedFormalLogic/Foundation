module

public import Foundation.Propositional.Entailment.Cl
public import Foundation.Vorspiel.Multiset

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
- `LO.OneSidedLK`
-/

@[expose]
public section

namespace LO

namespace Multiset

variable {α : Type*} [Tilde α]

instance : Tilde (Multiset α) := ⟨fun Γ ↦ Γ.map (∼·)⟩

lemma tilde_def (Γ : Multiset α) : ∼Γ = Γ.map (∼·) := rfl

@[simp] lemma tilde_zero : ∼(0 : Multiset α) = 0 := rfl

@[simp] lemma tilde_add (Γ Δ : Multiset α) : ∼(Γ + Δ) = ∼Γ + ∼Δ := by
  simp [tilde_def]

@[simp] lemma tilde_atom (φ : α) : ∼(⦃φ⦄ : Multiset α) = ⦃∼φ⦄ := by
  simp [tilde_def]

@[simp] lemma mem_tilde_iff [TildeInvolutive α] {φ : α} {Γ : Multiset α} : φ ∈ ∼Γ ↔ ∼φ ∈ Γ := by
  rw [tilde_def]
  constructor
  · intro h
    rcases Multiset.mem_map.mp h with ⟨ψ, hψ, rfl⟩
    simpa using hψ
  · intro hφ
    simpa using Multiset.mem_map_of_mem (fun ψ ↦ ∼ψ) hφ

instance [TildeInvolutive α] : TildeInvolutive (Multiset α) where
  tilde_involutive Γ := by simp [tilde_def, Multiset.map_map]

end Multiset

/-! ## One-sided $\mathbf{LK}$ -/

class OneSidedLK {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] (𝔇 : Multiset F → Type*) where
  identity (φ) : 𝔇 ⦃φ, ∼φ⦄
  contraction : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 ⦃⊤⦄
  and : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Γ + ⦃ψ⦄) → 𝔇 (Γ + ⦃φ ⋏ ψ⦄)
  or : 𝔇 (Γ + ⦃φ, ψ⦄) → 𝔇 (Γ + ⦃φ ⋎ ψ⦄)

class OneSidedLK.Cut
    {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
    (𝔇 : Multiset F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Δ + ⦃∼φ⦄) → 𝔇 (Γ + Δ)

namespace OneSidedLK

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
  [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] {𝔇 : Multiset F → Type*}

def cast (b : 𝔇 Γ) (h : Γ = Δ := by abel) : 𝔇 Δ := h ▸ b

def contra [OneSidedLK 𝔇] (d : 𝔇 Γ) (h : Γ ⊆ Δ := by simp) : 𝔇 Δ := contraction d h

def rotate [OneSidedLK 𝔇] (d : 𝔇 (Γ + ⦃φ⦄)) : 𝔇 (Γ + ⦃φ⦄) := d

def close [OneSidedLK 𝔇] (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ :=
  contraction (identity φ) (by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all)

def top [OneSidedLK 𝔇] (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ :=
  contraction verum (by
    intro φ hφ
    have : φ = ⊤ := by simpa using hφ
    simpa [this] using h)

def tensor [OneSidedLK 𝔇] {φ ψ : F} (dφ : 𝔇 (Γ + ⦃φ⦄)) (dψ : 𝔇 (Δ + ⦃ψ⦄)) :
    𝔇 (Γ + Δ + ⦃φ ⋏ ψ⦄) :=
  and
    (contraction dφ (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))
    (contraction dψ (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))

def swap₁ [OneSidedLK 𝔇] (d : 𝔇 (Γ + ⦃φ₂, φ₁⦄)) : 𝔇 (Γ + ⦃φ₁, φ₂⦄) := cast d

def swap₂ [OneSidedLK 𝔇] (d : 𝔇 (Γ + ⦃φ₃, φ₁, φ₂⦄)) :
    𝔇 (Γ + ⦃φ₁, φ₂, φ₃⦄) := cast d

def swap₃ [OneSidedLK 𝔇] (d : 𝔇 (Γ + ⦃φ₄, φ₁, φ₂, φ₃⦄)) :
    𝔇 (Γ + ⦃φ₁, φ₂, φ₃, φ₄⦄) := cast d

alias cut := OneSidedLK.Cut.cut

def eCut [Cut 𝔇] (d₁ : 𝔇 (Γ + ⦃φ⦄)) (d₂ : 𝔇 (Δ + ⦃ψ⦄))
    (e : ∼φ = ψ := by simp) : 𝔇 (Γ + Δ) :=
  cut d₁ (cast d₂ (by simp [e]))

/-- Eliminating falsum is the routine cut against the verum rule. -/
def removeBot [Cut 𝔇] (d : 𝔇 (Γ + ⦃⊥⦄)) : 𝔇 Γ :=
  have dt : 𝔇 ((0 : Multiset F) + ⦃∼⊥⦄) := cast verum (by simp)
  cast <| cut (φ := ⊥) (Γ := Γ) (Δ := 0) d dt

/-- Modus ponens with independent side contexts. This is the routine cut derivation. -/
def modusPonens [Cut 𝔇] (di : 𝔇 (Γ + ⦃φ 🡒 ψ⦄)) (dp : 𝔇 (Δ + ⦃φ⦄)) :
    𝔇 (Γ + Δ + ⦃ψ⦄) :=
  have h₁ : 𝔇 ⦃∼(φ 🡒 ψ), ∼φ, ψ⦄ := cast
    (tensor (𝔇 := 𝔇) (Γ := ⦃∼φ⦄) (Δ := ⦃ψ⦄) (φ := φ) (ψ := ∼ψ)
      (cast (identity φ) (by abel)) (cast (identity (∼ψ)) (by simp; abel)))
    (by simp [LogicalConnective.DeMorgan.imply]; abel)
  have h₂ : 𝔇 (Γ + ⦃∼φ, ψ⦄) := cast <|
    cut (φ := φ 🡒 ψ) (Γ := Γ) (Δ := ⦃∼φ, ψ⦄) di (cast h₁)
  cast <| cut (φ := φ) (Γ := Δ) (Δ := Γ + ⦃ψ⦄) dp (cast h₂)

def disj₂ {Γ : List F} {Δ : Multiset F} [OneSidedLK 𝔇] :
    𝔇 ((Γ : Multiset F) + Δ) → 𝔇 (Δ + ⦃⋁Γ⦄) := fun d ↦
  match Γ with
  | [] => contra d (by intro φ hφ; simp_all)
  | [φ] => cast d (by
    change φ ::ₘ Δ = Δ + ⦃φ⦄
    exact (Multiset.add_atom_eq_cons φ Δ).symm)
  | φ :: ψ :: Γ => by
    have dt : 𝔇 ((Δ + ⦃φ⦄) + ⦃⋁(ψ :: Γ)⦄) :=
      disj₂ (cast d (by
        change (φ ::ₘ (↑(ψ :: Γ) : Multiset F)) + Δ = (↑(ψ :: Γ) : Multiset F) + (Δ + ⦃φ⦄)
        rw [← Multiset.add_atom_eq_cons]
        abel))
    exact or (Γ := Δ) (φ := φ) (ψ := ⋁(ψ :: Γ)) (cast dt (by abel))
  termination_by _ => Γ.length

def conj₂ [OneSidedLK 𝔇] {Γ : List F} {Δ : Multiset F}
    (d : (φ : F) → φ ∈ Γ → 𝔇 (Δ + ⦃φ⦄)) : 𝔇 (Δ + ⦃⋀Γ⦄) :=
  match Γ with
  |          [] => contra verum (by intro φ hφ; simp_all)
  |         [φ] => d φ (by simp)
  | φ :: ψ :: Γ =>
    have : 𝔇 (Δ + ⦃⋀(ψ :: Γ)⦄) := conj₂ (Γ := ψ :: Γ) (fun χ h ↦ d χ (by simp_all))
    and (Γ := Δ) (φ := φ) (ψ := ⋀(ψ :: Γ)) (d φ (by simp)) this

namespace AxiomDerivation

variable [OneSidedLK 𝔇]

def introOr (d : 𝔇 ⦃φ, ψ⦄) : 𝔇 ⦃φ ⋎ ψ⦄ :=
  cast (or (Γ := 0) (φ := φ) (ψ := ψ) (cast d (by abel))) (by simp)

def introDisj {Γ : List F} (d : 𝔇 (Γ : Multiset F)) : 𝔇 ⦃⋁Γ⦄ :=
  cast <| disj₂ (Γ := Γ) (Δ := 0) (cast d)

/-- The rule expansion of the classical negation equivalence axiom. This is a routine syntactic derivation. -/
def negEquiv (φ : F) : 𝔇 ⦃(φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ)⦄ :=
  have d₁ : 𝔇 ⦃φ ⋎ ∼φ ⋎ ⊥⦄ := introDisj <| close φ (Γ := ⦃φ, ∼φ, ⊥⦄)
  have dp : 𝔇 ⦃∼φ, φ⦄ := close φ (Γ := ⦃∼φ, φ⦄)
  have dt : 𝔇 ⦃∼φ, ⊤⦄ := top (Γ := ⦃∼φ, ⊤⦄)
  have dc : 𝔇 ⦃∼φ, φ ⋏ ⊤⦄ := cast <| and (Γ := ⦃∼φ⦄) (φ := φ) (ψ := ⊤) (cast dp) (cast dt)
  cast <| and (Γ := 0) (φ := φ ⋎ ∼φ ⋎ ⊥) (ψ := φ ⋏ ⊤ ⋎ ∼φ)
    (cast d₁) (cast <| introOr (φ := φ ⋏ ⊤) (ψ := ∼φ) <| cast dc (by abel))

/-- The rule expansion of the K axiom. This is a routine syntactic derivation. -/
def implyK (φ ψ : F) : 𝔇 ⦃∼φ ⋎ ∼ψ ⋎ φ⦄ :=
  introDisj <| close φ (Γ := ⦃∼φ, ∼ψ, φ⦄)

/-- The rule expansion of the S axiom. This is a routine syntactic derivation. -/
def implyS (φ ψ χ : F) : 𝔇 ⦃φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ⦄ :=
  let A := φ ⋏ ψ ⋏ ∼χ
  let B := φ ⋏ ∼ψ
  let C := ∼φ
  let D := χ
  have dφ : 𝔇 (⦃B, C, D⦄ + ⦃φ⦄) := close φ (Γ := ⦃B, C, D⦄ + ⦃φ⦄)
    (by simp) (by simp [C])
  have dbp : 𝔇 (⦃C, D, ψ⦄ + ⦃φ⦄) := close φ (Γ := ⦃C, D, ψ⦄ + ⦃φ⦄)
    (by simp) (by simp [C])
  have dbn : 𝔇 (⦃C, D, ψ⦄ + ⦃∼ψ⦄) := close ψ (Γ := ⦃C, D, ψ⦄ + ⦃∼ψ⦄)
  have dψ : 𝔇 (⦃B, C, D⦄ + ⦃ψ⦄) := cast <|
    and (Γ := ⦃C, D, ψ⦄) (φ := φ) (ψ := ∼ψ) dbp dbn
  have dnχ : 𝔇 (⦃B, C, D⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃B, C, D⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dr : 𝔇 (⦃B, C, D⦄ + ⦃ψ ⋏ ∼χ⦄) := and (φ := ψ) (ψ := ∼χ) dψ dnχ
  have da : 𝔇 ⦃A, B, C, D⦄ := cast <| and (φ := φ) (ψ := ψ ⋏ ∼χ) dφ dr
  introDisj da

/-- The rule expansion of the first conjunction axiom. This is a routine syntactic derivation. -/
def and₁ (φ ψ : F) : 𝔇 ⦃(∼φ ⋎ ∼ψ) ⋎ φ⦄ :=
  introOr <| cast <| or (Γ := ⦃φ⦄) (φ := ∼φ) (ψ := ∼ψ)
    (cast <| close φ (Γ := ⦃φ, ∼φ, ∼ψ⦄))

/-- The rule expansion of the second conjunction axiom. This is a routine syntactic derivation. -/
def and₂ (φ ψ : F) : 𝔇 ⦃(∼φ ⋎ ∼ψ) ⋎ ψ⦄ :=
  introOr <| cast <| or (Γ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
    (cast <| close ψ (Γ := ⦃ψ, ∼φ, ∼ψ⦄))

/-- The rule expansion of conjunction introduction. This is a routine syntactic derivation. -/
def and₃ (φ ψ : F) : 𝔇 ⦃∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ⦄ :=
  have dp : 𝔇 ⦃∼φ, ∼ψ, φ⦄ := close φ (Γ := ⦃∼φ, ∼ψ, φ⦄)
  have dq : 𝔇 ⦃∼φ, ∼ψ, ψ⦄ := close ψ (Γ := ⦃∼φ, ∼ψ, ψ⦄)
  introDisj (Γ := [∼φ, ∼ψ, φ ⋏ ψ]) <| cast <|
    and (Γ := ⦃∼φ, ∼ψ⦄) (φ := φ) (ψ := ψ)
    (cast dp (by abel)) (cast dq (by abel))

/-- The rule expansion of the first disjunction axiom. This is a routine syntactic derivation. -/
def or₁ (φ ψ : F) : 𝔇 ⦃∼φ ⋎ φ ⋎ ψ⦄ :=
  introDisj <| close φ (Γ := ⦃∼φ, φ, ψ⦄)

/-- The rule expansion of the second disjunction axiom. This is a routine syntactic derivation. -/
def or₂ (φ ψ : F) : 𝔇 ⦃∼ψ ⋎ φ ⋎ ψ⦄ :=
  introDisj <| close ψ (Γ := ⦃∼ψ, φ, ψ⦄)

/-- The rule expansion of disjunction elimination. This is a routine syntactic derivation. -/
def or₃ (φ ψ χ : F) : 𝔇 ⦃φ ⋏ ∼χ ⋎ ψ ⋏ ∼χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ⦄ :=
  let A := φ ⋏ ∼χ
  let B := ψ ⋏ ∼χ
  let C := ∼φ ⋏ ∼ψ
  let D := χ
  have dap : 𝔇 (⦃B, D, ∼φ⦄ + ⦃φ⦄) := close φ (Γ := ⦃B, D, ∼φ⦄ + ⦃φ⦄)
  have dan : 𝔇 (⦃B, D, ∼φ⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃B, D, ∼φ⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dnp : 𝔇 (⦃A, B, D⦄ + ⦃∼φ⦄) := cast <| and (φ := φ) (ψ := ∼χ) dap dan
  have dbp : 𝔇 (⦃A, D, ∼ψ⦄ + ⦃ψ⦄) := close ψ (Γ := ⦃A, D, ∼ψ⦄ + ⦃ψ⦄)
  have dbn : 𝔇 (⦃A, D, ∼ψ⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃A, D, ∼ψ⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dnn : 𝔇 (⦃A, B, D⦄ + ⦃∼ψ⦄) := cast <| and (φ := ψ) (ψ := ∼χ) dbp dbn
  have dc : 𝔇 ⦃A, B, C, D⦄ := cast <| and (φ := ∼φ) (ψ := ∼ψ) dnp dnn
  introDisj dc

/-- The rule expansion of double-negation elimination. This is a routine syntactic derivation. -/
def dne (φ : F) : 𝔇 ⦃∼φ ⋎ φ⦄ :=
  introOr <| close φ (Γ := ⦃∼φ, φ⦄)

end AxiomDerivation

open Entailment

/-- A one-sided classical calculus induces classical entailment whenever singleton
derivations can be embedded as proofs. This is the routine translation of the
Hilbert axioms into one-sided sequent rules. -/
abbrev AxiomDerivation.cl {P : Type*} [Entailment P F] (𝓟 : P)
    [Entailment.ModusPonens 𝓟] [OneSidedLK 𝔇]
    (lift : ∀ {φ}, 𝔇 ⦃φ⦄ → 𝓟 ⊢! φ) : Entailment.Cl 𝓟 where
  negEquiv {φ} := Entailment.cast
    (show 𝓟 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      lift <| AxiomDerivation.negEquiv φ)
    (by simp [Axioms.NegEquiv, LogicalConnective.DeMorgan.imply, LogicalConnective.iff])
  verum := lift verum
  implyK {φ ψ} := Entailment.cast (lift <| AxiomDerivation.implyK φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  implyS {φ ψ χ} := Entailment.cast (lift <| AxiomDerivation.implyS φ ψ χ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₁ {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₁ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₂ {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₂ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₃ {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₃ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₁ {φ ψ} := Entailment.cast (lift <| AxiomDerivation.or₁ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₂ {φ ψ} := Entailment.cast (lift <| AxiomDerivation.or₂ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₃ {φ ψ χ} := Entailment.cast (lift <| AxiomDerivation.or₃ φ ψ χ)
    (by simp [LogicalConnective.DeMorgan.imply])
  dne {φ} := Entailment.cast (lift <| AxiomDerivation.dne φ)
    (by simp [LogicalConnective.DeMorgan.imply])

/-- An entailment relation which is determined solely by derivability. -/
class PrincipalEntailment (𝔇 : outParam (Multiset F → Type*)) {P : Type*} [Entailment P F] (𝓟 : P) where
  equiv {φ} : 𝓟 ⊢! φ ≃ 𝔇 ⦃φ⦄

namespace PrincipalEntailment

variable {P : Type*} [Entailment P F] {𝓟 : P} [PrincipalEntailment 𝔇 𝓟]

omit [LogicalConnective F] [LogicalNeutral F]
  [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] in
lemma provable_iff :
    𝓟 ⊢ φ ↔ Nonempty (𝔇 ⦃φ⦄) := by
  simpa using! OneSidedLK.PrincipalEntailment.equiv.nonempty_congr

variable [OneSidedLK.Cut 𝔇] (𝓟)

instance : Entailment.ModusPonens 𝓟 where
  mdp {φ ψ} b₁ b₂ :=
    equiv.symm <| cast <| modusPonens (Γ := 0) (Δ := 0) (equiv b₁) (equiv b₂)

instance : Entailment.Cl 𝓟 := AxiomDerivation.cl 𝓟 PrincipalEntailment.equiv.symm

variable {𝓟}

lemma derivable_iff_provable_disj {Γ : List F} : Nonempty (𝔇 (Γ : Multiset F)) ↔ 𝓟 ⊢ ⋁Γ := by
  constructor
  · rintro ⟨d⟩
    have : 𝔇 ((Γ : Multiset F) + 0) := cast d
    exact provable_iff.mpr ⟨disj₂ this⟩
  · rintro h
    have d₁ : 𝔇 ⦃⋁Γ⦄ := (provable_iff.mp h).some
    have d₂ : 𝔇 ((Γ : Multiset F) + ⦃⋀(∼Γ)⦄) := conj₂ fun φ h ↦ close φ (by simp) (by simp_all)
    exact ⟨cast (eCut (Γ := 0) (Δ := (Γ : Multiset F)) d₁ d₂)⟩

end PrincipalEntailment

abbrev Pullback (𝔇 : Multiset F → Type*) {G : Type*} [LogicalConnective G]
    [LogicalNeutral G] (f : G →ˡᶜ F) : Multiset G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)

namespace Pullback

variable {G : Type*} [LogicalConnective G] [LogicalNeutral G]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] {f : G →ˡᶜ F}

def cast (d : 𝔇 Δ) (h : Δ = Γ.map f := by simp) : Pullback 𝔇 f Γ := by
  unfold Pullback
  exact h ▸ d

def uncast (d : Pullback 𝔇 f Γ) (h : Δ = Γ.map f := by simp) : 𝔇 Δ := h ▸ d

instance oneSidedLK [OneSidedLK 𝔇] : OneSidedLK (Pullback 𝔇 f) where
  identity φ := cast <| identity (𝔇 := 𝔇) (f φ)
  contraction {Δ Γ} d h := cast (contraction d (Multiset.map_subset_map h) : 𝔇 (Γ.map f)) (by simp)
  verum := cast verum
  and {Γ φ ψ} d₁ d₂ := cast <| and (Γ := Γ.map f) (φ := f φ) (ψ := f ψ)
    (uncast d₁ (by simp)) (uncast d₂ (by simp))
  or {Γ φ ψ} d := cast <| or (Γ := Γ.map f) (φ := f φ) (ψ := f ψ) (uncast d (by simp))

instance cut [Cut 𝔇] : Cut (Pullback 𝔇 f) where
  cut {Γ φ Δ} bp bn :=
    have bp : 𝔇 (Γ.map f + ⦃f φ⦄) := uncast bp
    have bn : 𝔇 (Δ.map f + ⦃∼f φ⦄) := uncast bn
    cast (Cut.cut (φ := f φ) bp bn)

instance {P : Type*} [Entailment P F] (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] :
    PrincipalEntailment (Pullback 𝔇 f) (Entailment.pullback 𝓟 f) where
  equiv {φ} := PrincipalEntailment.equiv (φ := f φ)

omit [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] in
@[simp] lemma nonempty_iff {Γ} : Nonempty (Pullback 𝔇 f Γ) ↔ Nonempty (𝔇 (Γ.map f)) := by simp [Pullback]

omit [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] in
@[simp] lemma isEmpty_iff {Γ} : IsEmpty (Pullback 𝔇 f Γ) ↔ IsEmpty (𝔇 (Γ.map f)) := by simp [Pullback]

end Pullback

end OneSidedLK

end LO

end
