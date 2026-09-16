module

public import Foundation.SecondOrder.Syntax.Rew
public import Foundation.Logic.Calculus

/-!
# Second-order one-sided $\mathbf{LK}$

The structural rules are the standard local weakening and contraction rules.
-/

@[expose] public section

namespace FFL.SecondOrder

open FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := Multiset (Proposition L)

namespace Sequent

def shift₀ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₀

@[simp] lemma shift₀_zero : shift₀ (0 : Sequent L) = 0 := rfl

@[simp] lemma shift₀_add (Γ Δ : Sequent L) :
    shift₀ (Γ + Δ) = shift₀ Γ + shift₀ Δ := Multiset.map_add _ _ _

@[simp] lemma shift₀_atom (φ : Proposition L) : shift₀ ⦃φ⦄ = ⦃Semiproposition.shift₀ φ⦄ := Multiset.map_atom _ _

def shift₁ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₁

@[simp] lemma shift₁_zero : shift₁ (0 : Sequent L) = 0 := rfl

@[simp] lemma shift₁_add (Γ Δ : Sequent L) :
    shift₁ (Γ + Δ) = shift₁ Γ + shift₁ Δ := Multiset.map_add _ _ _

@[simp] lemma shift₁_atom (φ : Proposition L) : shift₁ ⦃φ⦄ = ⦃Semiproposition.shift₁ φ⦄ := Multiset.map_atom _ _

instance : Tilde (Sequent L) := ⟨Multiset.map (∼·)⟩

@[simp] lemma tilde_zero : ∼(0 : Sequent L) = 0 := rfl

@[simp] lemma tilde_add (Γ Δ : Sequent L) : ∼(Γ + Δ) = ∼Γ + ∼Δ := Multiset.map_add _ _ _

@[simp] lemma tilde_atom (φ : Proposition L) : ∼⦃φ⦄ = ⦃∼φ⦄ := Multiset.map_atom _ _

end Sequent

/-- Second-order one-sided $\mathbf{LK}$-derivation -/
inductive Derivation : Sequent L → Type _
| identity : Derivation ⦃φ, ∼φ⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction : Derivation (Γ + ⦃φ, φ⦄) → Derivation (Γ + ⦃φ⦄)
| weakening : Derivation Γ → Derivation (Γ + ⦃φ⦄)
| verum : Derivation ⦃⊤⦄
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) → Derivation (Γ + ⦃φ ⋏ ψ⦄)
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| all₁ {φ : Semiproposition L 0 1} : Derivation (Sequent.shift₀ Γ + ⦃φ.free₀⦄) → Derivation (Γ + ⦃∀¹ φ⦄)
| exs₁ {φ : Semiproposition L 0 1} : Derivation (Γ + ⦃φ/[t]⦄) → Derivation (Γ + ⦃∃¹ φ⦄)
| all₂ {φ : Semiproposition L 1 0} : Derivation (Sequent.shift₁ Γ + ⦃φ.free₁⦄) → Derivation (Γ + ⦃∀² φ⦄)
| exs₂ {φ : Semiproposition L 1 0} : Derivation (Γ + ⦃φ/⟦ψ⟧⦄) → Derivation (Γ + ⦃∃² φ⦄)

prefix:45 "⊢ᴸᴷ² " => Derivation

namespace Derivation

def cast {Γ Δ : Sequent L} (d : ⊢ᴸᴷ² Γ) (h : Γ = Δ := by abel) : ⊢ᴸᴷ² Δ := h ▸ d

instance : OneSidedLK (Derivation (L := L)) where
  weakening d := d.weakening
  contraction d := d.contraction
  identity _ := .identity
  verum := .verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or

instance : OneSidedLK.Cut (Derivation (L := L)) where
  cut d₁ d₂ := d₁.cut d₂

private lemma unshift₁_shift₁ {N n : ℕ} (φ : Semiproposition L N n) :
    (Rew.rewrite Nat.pred).app (Semiproposition.shift₁ φ) = φ := by
  induction φ using Semiformula.rec' <;>
    simp_all [Semiproposition.shift₁, Rew.shift];

def traversal [L.DecidableEq] {Γ : Sequent L} : ⊢ᴸᴷ² Γ → Γ.Traversal
  | identity (φ := φ) => (Multiset.Traversal.atom φ).succ (∼φ)
  | cut d dn => d.traversal.remove.add dn.traversal.remove
  | contraction (φ := φ) d => (d.traversal.cast (by abel)).remove (a := φ)
  | weakening (φ := φ) d => d.traversal.succ φ
  | verum => .atom ⊤
  | and (φ := φ) (ψ := ψ) d _ => d.traversal.remove.succ (φ ⋏ ψ)
  | or (φ := φ) (ψ := ψ) d =>
      ((d.traversal.cast (by abel)).remove (a := ψ)).remove (a := φ) |>.succ (φ ⋎ ψ)
  | all₁ (φ := φ) d =>
      ((d.traversal.remove.map (FirstOrder.Rew.rewriteMap Nat.pred ▹ ·)).cast (by
        simp [Sequent.shift₀, Multiset.map_map, Rewriting.rewriteMap_pred_shift])).succ (∀¹ φ)
  | exs₁ (φ := φ) d => d.traversal.remove.succ (∃¹ φ)
  | all₂ (φ := φ) d =>
      ((d.traversal.remove.map (Rew.rewrite Nat.pred).app).cast (by
        simp [Sequent.shift₁, Multiset.map_map, unshift₁_shift₁])).succ (∀² φ)
  | exs₂ (φ := φ) d => d.traversal.remove.succ (∃² φ)

/-- Applies structural rules along supplied traversals (a routine derived rule). -/
def contra [L.DecidableEq] {Γ Δ : Sequent L}
    (d : ⊢ᴸᴷ² Γ) (tΔ : Δ.Traversal) (h : Γ ⊆ Δ := by simp) : ⊢ᴸᴷ² Δ :=
  Structural.ofSubset d.traversal tΔ d h

end Derivation

abbrev Proof (φ : Sentence L) := ⊢ᴸᴷ² ⦃(φ : Proposition L)⦄

inductive Proof.Symbol (L : Language) : Type
| symbol

notation "𝐋𝐊²" => Proof.Symbol.symbol

instance : Entailment (Proof.Symbol L) (Sentence L) := ⟨fun _ ↦ Proof⟩

/-! ## Proof system with axioms -/

abbrev Theory (L : Language) := Set (Sentence L)

/-- A theory proof uses finitely many sentence axioms, as in first-order LK. -/
structure Theory.Proof (T : Theory L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation (Rew.emb.app.comp FirstOrder.Rewriting.emb)
    (⦃σ⦄ + ∼axioms)

namespace Theory.Proof

instance : Entailment (Theory L) (Sentence L) where
  Prf := Theory.Proof

attribute [simp] Theory.Proof.axioms_mem

/-- A singleton derivation gives a theory proof without using any axioms. -/
def ofDerivation {T : Theory L} {φ : Sentence L}
    (d : ⊢ᴸᴷ² ⦃(φ : Proposition L)⦄) : T ⊢! φ :=
  ⟨0, by simp, by simpa [OneSidedLK.Pullback] using d⟩

instance : Entailment.Compact (Theory L) where
  core b := {φ | φ ∈ b.axioms}
  corePrf b := ⟨b.axioms, by simp, b.derivation⟩
  core_finite b := by simp [AdjunctiveSet.Finite, AdjunctiveSet.set];
  core_subset b := by simpa [AdjunctiveSet.subset_iff] using b.axioms_mem;

instance : Entailment.Axiomatized (Theory L) where
  prfAxm {𝓢 φ} h :=
    ⟨⦃φ⦄, by simpa using h, by
      simpa [OneSidedLK.Pullback, Multiset.tilde_def] using
        (Derivation.identity (φ := (φ : Proposition L)))⟩
  weakening h b :=
    ⟨b.axioms, fun ψ hψ ↦ h (b.axioms_mem ψ hψ), b.derivation⟩

end Theory.Proof

end FFL.SecondOrder

end
