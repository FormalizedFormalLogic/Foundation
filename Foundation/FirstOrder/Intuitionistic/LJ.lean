module

public import Foundation.Vorspiel.Multiset
public import Foundation.Vorspiel.Option
public import Foundation.FirstOrder.Intuitionistic.Rew

/-! # First-order $\mathbf{LJ}$ -/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language.{u}}

open Semiformulaᵢ

abbrev Theoryᵢ (L : Language.{u}) := Set (Sentenceᵢ L)

namespace LJ

abbrev Sequent (L : Language.{u}) := Multiset (Propositionᵢ L)

abbrev Head (L : Language.{u}) := Option (Propositionᵢ L)

namespace Head

def shift (Ξ : Head L) : Head L := Ξ.map Rewriting.shift

def rewrite (f : ℕ → SyntacticTerm L) (Ξ : Head L) : Head L :=
  Ξ.map (Rew.rewrite f ▹ ·)

@[simp] lemma shift_none : shift (none : Head L) = none := rfl

@[simp] lemma shift_some (φ : Propositionᵢ L) : shift φ = some (Rewriting.shift φ) := rfl

@[simp] lemma rewrite_none (f : ℕ → SyntacticTerm L) : rewrite f (none : Head L) = none := rfl

@[simp] lemma rewrite_some (f : ℕ → SyntacticTerm L) (φ : Propositionᵢ L) :
    rewrite f φ = some (Rew.rewrite f ▹ φ) := rfl

end Head

inductive Derivation : Sequent L → Head L → Type _
/-- Identity rule -/
| identity (R : L.Rel k) (v) : Derivation ⦃rel R v⦄ (rel R v)
/-- Cut rule -/
| cut {φ : Propositionᵢ L} {Γ Δ Ξ} :
  Derivation Γ φ → Derivation (Δ + ⦃φ⦄) Ξ → Derivation (Γ + Δ) Ξ
/-- Structural rule -/
| contraction {Γ Γ' : Multiset (Propositionᵢ L)} {Ξ Ξ' : Option (Propositionᵢ L)} :
  Derivation Γ Ξ → Γ ⊆ Γ' → Ξ ⊆ Ξ' → Derivation Γ' Ξ'
/-- Positive introduction of verum -/
| verum : Derivation 0 (some ⊤)
/-- Negative introduction of falsum -/
| falsum : Derivation ⦃⊥⦄ none
/-- Positive introduction of implication -/
| positiveImply {φ ψ : Propositionᵢ L} :
  Derivation (Γ + ⦃φ⦄) ψ → Derivation Γ (φ 🡒 ψ)
/-- Negative introduction of implication -/
| negativeImply {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation (Δ + ⦃ψ⦄) Ξ → Derivation (Γ + Δ + ⦃φ 🡒 ψ⦄) Ξ
/-- Positive introduction of conjunction -/
| positiveAnd {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation Γ ψ → Derivation Γ (φ ⋏ ψ)
/-- Negative introduction of conjunction -/
| negativeAnd {φ ψ : Propositionᵢ L} :
  Derivation (Γ + ⦃φ, ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋏ ψ⦄) Ξ
/-- Positive introduction of disjunction (left) -/
| positiveOrLeft {φ ψ : Propositionᵢ L} :
  Derivation Γ φ → Derivation Γ (φ ⋎ ψ)
/-- Positive introduction of disjunction (right) -/
| positiveOrRight {φ ψ : Propositionᵢ L} :
  Derivation Γ ψ → Derivation Γ (φ ⋎ ψ)
/-- Negative introduction of disjunction -/
| negativeOr :
  Derivation (Γ + ⦃φ⦄) Ξ → Derivation (Γ + ⦃ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋎ ψ⦄) Ξ
/-- Positive introduction of universal quantifier -/
| positiveForall {φ : Semipropositionᵢ L 1} :
  Derivation Γ⁺ᵐ (Rewriting.free φ) → Derivation Γ (∀¹ φ)
/-- Negative introduction of universal quantifier -/
| negativeForall {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
  Derivation (Γ + ⦃φ/[t]⦄) Ξ → Derivation (Γ + ⦃∀¹ φ⦄) Ξ
/-- Positive introduction of existential quantifier -/
| positiveExists {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
  Derivation Γ (φ/[t]) → Derivation Γ (∃¹ φ)
/-- Negative introduction of existential quantifier -/
| negativeExists {φ : Semipropositionᵢ L 1} :
  Derivation (Γ⁺ᵐ + ⦃Rewriting.free φ⦄) Ξ.shift → Derivation (Γ + ⦃∃¹ φ⦄) Ξ

infix:45 " ⊢ᴸᴶ¹ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L} {Ξ Λ : Head L}

open Rewriting LawfulSyntacticRewriting

def cast (d : Γ ⊢ᴸᴶ¹ Ξ) (seq : Γ = Δ := by abel) (heq : Ξ = Λ := by simp) :
    Δ ⊢ᴸᴶ¹ Λ := seq ▸ heq ▸ d

def eta : (φ : Propositionᵢ L) → ⦃φ⦄ ⊢ᴸᴶ¹ φ
  | .rel R v => identity R v
  |        ⊥ => contraction falsum (by simp) (by simp)
  |    φ ⋏ ψ => positiveAnd
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
        contraction (eta φ) (by simp) (by simp)))
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
        contraction (eta ψ) (by simp) (by simp)))
  |    φ ⋎ ψ => negativeOr (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ ⋎ ψ)
      (cast (positiveOrLeft (ψ := ψ) (eta φ)))
      (cast (positiveOrRight (φ := φ) (eta ψ)))
  |    φ 🡒 ψ => positiveImply <|
      cast (negativeImply (φ := φ) (ψ := ψ) (Δ := 0) (Ξ := ψ)
        (eta φ)
        (cast (eta ψ) (by simp) (by simp)))
  |     ∀¹ φ => positiveForall (Γ := ⦃∀¹ φ⦄) <|
      cast (negativeForall (Γ := 0) (Ξ := Rewriting.free φ) (φ := Rewriting.shift φ) (t := &0) <|
        cast (eta (Rewriting.free φ)) (by simp) (by simp)) (by simp)
  |     ∃¹ φ => negativeExists (Γ := 0) (Ξ := ∃¹ φ) <|
      cast (positiveExists (Γ := ⦃Rewriting.free φ⦄) (φ := Rewriting.shift φ) (t := &0) <|
        cast (eta (Rewriting.free φ)) (by simp) (by simp))
  termination_by φ => φ.complexity

def assumption {φ : Propositionᵢ L} (h : φ ∈ Γ) : Γ ⊢ᴸᴶ¹ φ :=
  contraction (eta φ) (by simpa using h) (by simp)

def positiveNeg {φ : Propositionᵢ L} (d : Γ + ⦃φ⦄ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)) :
    Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L) :=
  positiveImply d

def negativeNeg {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ) :
    Γ + ⦃(∼φ : Propositionᵢ L)⦄ ⊢ᴸᴶ¹ none :=
  cast (seq := by rw [add_zero]; rfl) <| negativeImply (φ := φ) (ψ := ⊥) (Γ := Γ) (Δ := 0) (Ξ := none) d <|
    cast falsum (by simp) (by rfl)

def modusPonens {φ ψ : Propositionᵢ L} (di : Γ ⊢ᴸᴶ¹ φ 🡒 ψ) (dφ : Γ ⊢ᴸᴶ¹ φ) :
    Γ ⊢ᴸᴶ¹ ψ :=
  contraction
    (cut (φ := φ 🡒 ψ) (Γ := Γ) (Δ := Γ) (Ξ := ψ) di <| cast (seq := by simp) <|
      negativeImply (φ := φ) (ψ := ψ) (Γ := Γ) (Δ := 0) (Ξ := ψ)
        dφ (cast (eta ψ) (by simp) (by simp)))
    (by intro θ hθ; simp_all) (by simp)

def negElim {φ : Propositionᵢ L} (dn : Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L))
    (dφ : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L) :=
  modusPonens dn dφ

def cutOne {φ : Propositionᵢ L} (dφ : Γ ⊢ᴸᴶ¹ φ) (d : ⦃φ⦄ ⊢ᴸᴶ¹ Ξ) : Γ ⊢ᴸᴶ¹ Ξ :=
  cast (seq := by simp) <| cut (Γ := Γ) (Δ := 0) (Ξ := Ξ) dφ <| cast d (by simp)

def andLeft {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ φ :=
  cutOne d <| cast <| negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
    assumption (by simp)

def andRight {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ ψ :=
  cutOne d <| cast <| negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
    assumption (by simp)

def specialize {φ : Semipropositionᵢ L 1} (d : Γ ⊢ᴸᴶ¹ ∀¹ φ) (t : Term L ℕ) : Γ ⊢ᴸᴶ¹ φ/[t] :=
  cutOne d <| cast <| negativeForall (Γ := 0) (Ξ := φ/[t]) (φ := φ) (t := t) <|
    assumption (by simp)

def rewrite (f : ℕ → SyntacticTerm L) {Γ : Sequent L} {Ξ : Head L} : Γ ⊢ᴸᴶ¹ Ξ →
    Γ.map (Rew.rewrite f ▹ ·) ⊢ᴸᴶ¹ Head.rewrite f Ξ
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) dφ d =>
    (cut (φ := Rew.rewrite f ▹ φ)
      (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Δ := Δ.map (Rew.rewrite f ▹ ·))
      (Ξ := Head.rewrite f Ξ)
      ((rewrite f dφ).cast) ((rewrite f d).cast (by simp))).cast (by simp)
  | contraction d hΓ hΞ =>
    (rewrite f d).contraction (Multiset.map_subset_map hΓ) (by
      cases hΞ <;> simp [Head.rewrite])
  | verum => verum
  | falsum => falsum
  | positiveImply (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (positiveImply (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((rewrite f d).cast (by simp))).cast (by simp)
  | negativeImply (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := ψ) dφ dψ =>
    (negativeImply (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (Δ := Δ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ)
      (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      (rewrite f dφ).cast ((rewrite f dψ).cast (by simp))).cast (by simp)
  | positiveAnd dφ dψ => positiveAnd (rewrite f dφ) (rewrite f dψ)
  | negativeAnd (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (negativeAnd (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ)
      (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((rewrite f d).cast (by simp))).cast (by simp)
  | positiveOrLeft d => positiveOrLeft (rewrite f d)
  | positiveOrRight d => positiveOrRight (rewrite f d)
  | negativeOr (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ =>
    (negativeOr (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (Ξ := Head.rewrite f Ξ) (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((rewrite f dφ).cast (by simp)) ((rewrite f dψ).cast (by simp))).cast (by simp)
  | positiveForall (Γ := Γ) (φ := φ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    (positiveForall (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) <|
      (rewrite g d).cast
        (by simp [g, Rewriting.shiftsM, shift_rewrite_eq])
        (by simp [g, Head.rewrite, free_rewrite_eq, Function.comp_def]))
      |>.cast (by simp) (by simp [Head.rewrite, Rew.q_rewrite])
  | negativeForall (Γ := Γ) (φ := φ) (t := t) d =>
    (negativeForall (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (Ξ := Head.rewrite f Ξ) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (t := Rew.rewrite f t)
      ((rewrite f d).cast (by simp [rewrite_subst_eq]))).cast (by simp [Rew.q_rewrite])
  | positiveExists (φ := φ) (t := t) d =>
    (positiveExists (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) (t := Rew.rewrite f t)
      ((rewrite f d).cast (heq := by simp [rewrite_subst_eq]))).cast
        (heq := by simp [Head.rewrite, Rew.q_rewrite])
  | negativeExists (Γ := Γ) (Ξ := Ξ) (φ := φ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    (negativeExists (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (Ξ := Head.rewrite f Ξ) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) <|
      (rewrite g d).cast
        (by simp [g, Rewriting.shiftsM, free_rewrite_eq, shift_rewrite_eq, Function.comp_def])
        (by cases Ξ <;> simp [g, Head.rewrite, Head.shift, shift_rewrite_eq]))
      |>.cast (by simp [Rew.q_rewrite])

/-- Height of an LJ derivation, with initial rules at height zero (standard definition). -/
def height : {Γ : Sequent L} → {Ξ : Head L} → Γ ⊢ᴸᴶ¹ Ξ → ℕ
  | _, _, .identity _ _ => 0
  | _, _, .cut d₁ d₂ => max (height d₁) (height d₂) + 1
  | _, _, .contraction d _ _ => height d + 1
  | _, _, .verum => 0
  | _, _, .falsum => 0
  | _, _, .positiveImply d => height d + 1
  | _, _, .negativeImply d₁ d₂ => max (height d₁) (height d₂) + 1
  | _, _, .positiveAnd d₁ d₂ => max (height d₁) (height d₂) + 1
  | _, _, .negativeAnd d => height d + 1
  | _, _, .positiveOrLeft d => height d + 1
  | _, _, .positiveOrRight d => height d + 1
  | _, _, .negativeOr d₁ d₂ => max (height d₁) (height d₂) + 1
  | _, _, .positiveForall d => height d + 1
  | _, _, .negativeForall d => height d + 1
  | _, _, .positiveExists d => height d + 1
  | _, _, .negativeExists d => height d + 1

/-- Transport along sequent equalities preserves height (routine). -/
@[simp] lemma height_cast {Γ Δ : Sequent L} {Ξ Λ : Head L}
    (d : Γ ⊢ᴸᴶ¹ Ξ) (hΓ : Γ = Δ) (hΞ : Ξ = Λ) :
    height (d.cast hΓ hΞ) = height d := by
  subst Δ
  subst Λ
  rfl

/-- Term substitution preserves derivation height (standard syntactic property). -/
@[simp] lemma height_rewrite (f : ℕ → SyntacticTerm L) {Γ : Sequent L}
    {Ξ : Head L} (d : Γ ⊢ᴸᴶ¹ Ξ) : height (d.rewrite f) = height d := by
  induction d generalizing f <;>
    simp only [LJ.Derivation.rewrite, height, height_cast]
  case positiveAnd a b iha ihb =>
    exact congrArg (· + 1) <| congrArg₂ max (iha f) (ihb f)
  all_goals aesop

protected def map (d : Γ ⊢ᴸᴶ¹ Ξ) (f : ℕ → ℕ) :
    Γ.map (Rew.rewriteMap f ▹ ·) ⊢ᴸᴶ¹ Ξ.map (Rew.rewriteMap f ▹ ·) :=
  d.rewrite fun x ↦ &(f x)

protected def shift (d : Γ ⊢ᴸᴶ¹ Ξ) : Γ⁺ᵐ ⊢ᴸᴶ¹ Ξ.shift :=
  cast (d.map Nat.succ) (by rfl) (by cases Ξ <;> rfl)

def weakening (d : Γ ⊢ᴸᴶ¹ Ξ) (hΓ : Γ ⊆ Δ) : Δ ⊢ᴸᴶ¹ Ξ :=
  contraction d hΓ (by cases Ξ <;> simp)

def dni {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ (∼∼φ : Propositionᵢ L) :=
  positiveNeg <| contraction d.negativeNeg (by simp) (by simp)

/-- Contraposition for singleton derivations (standard intuitionistic reasoning). -/
def contrapose {φ ψ : Propositionᵢ L} (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) :
    ⦃∼ψ⦄ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L) :=
  positiveNeg <| negElim (assumption (by simp [Semiformulaᵢ.neg_def])) <|
    cutOne (assumption (by simp)) d

/-- Double negation preserves derivability, by twice applying contraposition (folklore). -/
def doubleNegationMap {φ ψ : Propositionᵢ L} (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) :
    ⦃∼∼φ⦄ ⊢ᴸᴶ¹ (∼∼ψ : Propositionᵢ L) := d.contrapose.contrapose

def dneOfNegative [L.DecidableEq] : {φ : Propositionᵢ L} → φ.IsNegative → ⦃∼∼φ⦄ ⊢ᴸᴶ¹ φ
  | ⊥, _ => negElim (eta _) <| contraction
      (positiveNeg (Γ := 0) (φ := ⊥) (assumption (by simp))) (by simp) (by simp)
  | φ ⋏ ψ, h =>
    have hn : φ.IsNegative ∧ ψ.IsNegative := by simpa using h
    positiveAnd
      (cutOne (doubleNegationMap (andLeft (eta _))) (dneOfNegative hn.1))
      (cutOne (doubleNegationMap (andRight (eta _))) (dneOfNegative hn.2))
  | φ 🡒 ψ, h => by
    have hnψ : ψ.IsNegative := by simpa using h
    have ihψ := dneOfNegative hnψ
    let N : Sequent L := ⦃∼∼(φ 🡒 ψ)⦄
    apply positiveImply (Γ := N) (φ := φ) (ψ := ψ)
    let C : Sequent L := N + ⦃φ⦄
    have dnnψ : C ⊢ᴸᴶ¹ ↑(∼∼ψ) := positiveNeg (Γ := C) <| by
      let D : Sequent L := C + ⦃∼ψ⦄
      have dnImp : D ⊢ᴸᴶ¹ ∼(φ 🡒 ψ) := positiveNeg (Γ := D) <| by
        let E : Sequent L := D + ⦃φ 🡒 ψ⦄
        have dψ : E ⊢ᴸᴶ¹ ψ := modusPonens
          (assumption (φ := φ 🡒 ψ) (by simp [E]))
          (assumption (φ := φ) (by simp [E, D, C]))
        exact negElim
          (assumption (φ := ∼ψ) (by simp [D, Semiformulaᵢ.neg_def])) dψ
      exact negElim
        (assumption (φ := ∼∼(φ 🡒 ψ)) (by simp [C, N, Semiformulaᵢ.neg_def])) dnImp
    exact cutOne dnnψ ihψ
  | ∀¹ φ, h => positiveForall <| cutOne
      (cast (doubleNegationMap (specialize (eta (∀¹ Rewriting.shift φ)) &0))
        (by simp [Semiformulaᵢ.neg_def]) (by simp))
      (dneOfNegative (by simpa using h))
  termination_by φ _ => φ.complexity

def ofDNOfNegative [L.DecidableEq] {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ (∼∼φ : Propositionᵢ L))
    (h : φ.IsNegative) : Γ ⊢ᴸᴶ¹ φ := cutOne d (dneOfNegative h)

/-- Mutual LJ derivability from singleton antecedents. -/
abbrev InterDerivation (L : Language.{u}) (φ ψ : Propositionᵢ L) :=
  (⦃φ⦄ ⊢ᴸᴶ¹ ψ) × (⦃ψ⦄ ⊢ᴸᴶ¹ φ)

namespace InterDerivation

variable {φ ψ χ φ₁ φ₂ ψ₁ ψ₂ : Propositionᵢ L}

protected def refl (φ : Propositionᵢ L) : InterDerivation L φ φ := ⟨eta φ, eta φ⟩

def symm (d : InterDerivation L φ ψ) : InterDerivation L ψ φ := ⟨d.2, d.1⟩

def trans (d₁ : InterDerivation L φ ψ) (d₂ : InterDerivation L ψ χ) :
    InterDerivation L φ χ := ⟨cutOne d₁.1 d₂.1, cutOne d₂.2 d₁.2⟩
def neg (d : InterDerivation L φ ψ) : InterDerivation L (∼φ) (∼ψ) :=
  ⟨contrapose d.2, contrapose d.1⟩

def and (dφ : InterDerivation L φ₁ φ₂) (dψ : InterDerivation L ψ₁ ψ₂) :
    InterDerivation L (φ₁ ⋏ ψ₁) (φ₂ ⋏ ψ₂) := by
  constructor
  · exact positiveAnd (cutOne (andLeft (eta _)) dφ.1) (cutOne (andRight (eta _)) dψ.1)
  · exact positiveAnd (cutOne (andLeft (eta _)) dφ.2) (cutOne (andRight (eta _)) dψ.2)

def all {φ ψ : Semipropositionᵢ L 1}
    (d : InterDerivation L (Rewriting.free φ) (Rewriting.free ψ)) :
    InterDerivation L (∀¹ φ) (∀¹ ψ) := by
  let lift : ∀ {φ ψ : Semipropositionᵢ L 1},
      (⦃Rewriting.free φ⦄ ⊢ᴸᴶ¹ Rewriting.free ψ) → ⦃∀¹ φ⦄ ⊢ᴸᴶ¹ ∀¹ ψ :=
    fun {φ ψ} d ↦ positiveForall <| cutOne
      (cast (specialize (eta (∀¹ Rewriting.shift φ)) &0) (by simp) (by simp)) d
  exact ⟨lift d.1, lift d.2⟩

def dne [L.DecidableEq] (h : φ.IsNegative) : InterDerivation L (∼∼φ) φ :=
  ⟨dneOfNegative h, dni (eta φ)⟩

def iffnegOfNegIff [L.DecidableEq] (h : φ.IsNegative)
    (d : InterDerivation L (∼φ) ψ) : InterDerivation L φ (∼ψ) :=
  (dne h).symm.trans d.neg

end InterDerivation

end Derivation

end LJ

inductive LJ (L : Language.{u})
  | symbol

notation "𝐋𝐉¹" => LJ.symbol

notation "𝐋𝐉¹[" L "]" => LJ.symbol (L := L)

abbrev LJ.Proof (φ : Propositionᵢ L) := 0 ⊢ᴸᴶ¹ some φ

instance : Entailment (LJ L) (Propositionᵢ L) where
  Prf _ := LJ.Proof

namespace LJ

namespace Proof

lemma def_eq (φ : Propositionᵢ L) : (𝐋𝐉¹ ⊢! φ) = (0 ⊢ᴸᴶ¹ some φ) := rfl

end Proof

end LJ

structure Theoryᵢ.Proof (T : Theoryᵢ L) (σ : Sentenceᵢ L) where
  axioms : Multiset (Sentenceᵢ L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : axioms.map Rewriting.emb ⊢ᴸᴶ¹ ↑σ

instance : Entailment (Theoryᵢ L) (Sentenceᵢ L) := ⟨Theoryᵢ.Proof⟩

namespace Theoryᵢ.Proof

variable {T U : Theoryᵢ L} [L.DecidableEq]

def weakening (ss : T ⊆ U) : T ⊢! σ → U ⊢! σ
  | ⟨Γ, hΓ, d⟩ => ⟨Γ, fun ψ hψ ↦ ss (hΓ ψ hψ), d⟩

instance : Entailment.Axiomatized (Theoryᵢ L) where
  prfAxm {T} φ h := ⟨⦃φ⦄, by simpa using AdjunctiveSet.mem_set_iff.mp h,
    LJ.Derivation.cast (LJ.Derivation.eta (φ : Propositionᵢ L)) (by simp)⟩
  weakening := weakening

def deduct : adjoin φ T ⊢! ψ → T ⊢! φ 🡒 ψ
  | ⟨Γ, hΓ, d⟩ =>
    ⟨Γ.filter (· ≠ φ), by
      intro θ hθ
      have hθΓ : θ ∈ Γ := (Multiset.mem_filter.mp hθ).1
      have hθφ : θ ≠ φ := (Multiset.mem_filter.mp hθ).2
      simpa [hθφ] using hΓ θ hθΓ,
    LJ.Derivation.cast (heq := by rfl) <|
      LJ.Derivation.positiveImply (φ := (φ : Propositionᵢ L)) (ψ := (ψ : Propositionᵢ L)) <|
      LJ.Derivation.contraction (Ξ' := (ψ : Propositionᵢ L)) d (by
        intro θ hθ
        rcases Multiset.mem_map.mp hθ with ⟨χ, hχ, rfl⟩
        by_cases h : χ = φ
        · subst χ
          simp
        · exact Multiset.mem_add.mpr <| Or.inl <|
            Multiset.mem_map_of_mem Rewriting.emb <| Multiset.mem_filter_of_mem hχ h) (by simp)⟩

def deductInv : T ⊢! φ 🡒 ψ → adjoin φ T ⊢! ψ
  | ⟨Γ, hΓ, d⟩ =>
    ⟨Γ + ⦃φ⦄, by
      intro θ hθ
      rcases Multiset.mem_add.mp hθ with hθ | hθ
      · exact Set.mem_insert_of_mem φ (hΓ θ hθ)
      · exact Or.inl (by simpa using hθ),
    LJ.Derivation.cast (seq := by simp) (heq := by rfl) <| LJ.Derivation.cut
      (φ := ((φ : Propositionᵢ L) 🡒 (ψ : Propositionᵢ L)))
      (Γ := Γ.map Rewriting.emb) (Δ := ⦃(φ : Propositionᵢ L)⦄) (Ξ := (ψ : Propositionᵢ L))
      (LJ.Derivation.cast d (heq := by rfl))
      (LJ.Derivation.cast (heq := rfl) <| LJ.Derivation.negativeImply
        (φ := (φ : Propositionᵢ L)) (ψ := (ψ : Propositionᵢ L))
        (Γ := ⦃(φ : Propositionᵢ L)⦄) (Δ := 0) (Ξ := (ψ : Propositionᵢ L))
        (LJ.Derivation.eta (φ : Propositionᵢ L))
        (LJ.Derivation.cast (LJ.Derivation.eta (ψ : Propositionᵢ L)) (by simp) (by simp)))⟩

instance : Entailment.Deduction (Theoryᵢ L) where
  ofInsert := deduct
  inv := deductInv

end Theoryᵢ.Proof

end FFL.FirstOrder
