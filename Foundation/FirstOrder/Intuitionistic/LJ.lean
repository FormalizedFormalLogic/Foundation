module

public import Foundation.Vorspiel.Multiset
public import Foundation.Vorspiel.Option
public import Foundation.FirstOrder.Intuitionistic.Rew

/-! # First-order $\mathbf{LJ}$ -/

@[expose] public section

namespace LO.FirstOrder

variable {L : Language}

open Semiformulaᵢ

abbrev Theoryᵢ (L : Language) := Set (Sentenceᵢ L)

namespace LJ

abbrev Sequent (L : Language) := Multiset (Propositionᵢ L)

abbrev Head (L : Language) := Option (Propositionᵢ L)

namespace Head

def shift (Ξ : Head L) : Head L := Ξ.map Rewriting.shift

@[simp] lemma shift_none : shift (none : Head L) = none := rfl

@[simp] lemma shift_some (φ : Propositionᵢ L) : shift φ = some (Rewriting.shift φ) := rfl

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

def cast (d : Γ ⊢ᴸᴶ¹ Ξ) (seq : Γ = Δ := by abel) (heq : Ξ = Λ := by simp) : Δ ⊢ᴸᴶ¹ Λ := seq ▸ heq ▸ d

def eta : (φ : Propositionᵢ L) → ⦃φ⦄ ⊢ᴸᴶ¹ φ
  | .rel R v => identity R v
  |        ⊥ => contraction falsum (by simp) (by simp)
  |    φ ⋏ ψ => positiveAnd
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
        contraction (eta φ) (by simpa using Multiset.subset_add_left) (by simp)))
      (cast (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
        contraction (eta ψ) (by simpa using Multiset.subset_add_right) (by simp)))
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
  contraction (eta φ) (by
    intro θ hθ
    have : θ = φ := by simpa only [Multiset.mem_atom_iff] using hθ
    simpa [this] using h) (by simp)

def positiveNeg {φ : Propositionᵢ L} (d : Γ + ⦃φ⦄ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)) : Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L) :=
  positiveImply d

def negativeNeg {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ) : Γ + ⦃(∼φ : Propositionᵢ L)⦄ ⊢ᴸᴶ¹ none :=
  cast (seq := by rw [add_zero]; rfl) <| negativeImply (φ := φ) (ψ := ⊥) (Γ := Γ) (Δ := 0) (Ξ := none) d <|
    cast falsum (by simp) (by rfl)

def modusPonens {φ ψ : Propositionᵢ L} (di : Γ ⊢ᴸᴶ¹ φ 🡒 ψ) (dφ : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ ψ :=
  contraction
    (cut (φ := φ 🡒 ψ) (Γ := Γ) (Δ := Γ) (Ξ := ψ) di <| cast (seq := by simp) <|
      negativeImply (φ := φ) (ψ := ψ) (Γ := Γ) (Δ := 0) (Ξ := ψ)
        dφ (cast (eta ψ) (by simp) (by simp)))
    (by intro θ hθ; simp_all) (by simp)

def negElim {φ : Propositionᵢ L} (dn : Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L)) (dφ : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L) :=
  modusPonens dn dφ

def cutOne {φ : Propositionᵢ L} (dφ : Γ ⊢ᴸᴶ¹ φ) (d : ⦃φ⦄ ⊢ᴸᴶ¹ Ξ) : Γ ⊢ᴸᴶ¹ Ξ :=
  cast (seq := by simp) <| cut (Γ := Γ) (Δ := 0) (Ξ := Ξ) dφ <| cast d (by simp)

def andLeft {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ φ :=
  cutOne d <| cast <| negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
    cast (contraction (Γ' := ⦃φ, ψ⦄) (eta φ) (by intro θ hθ; simp_all) (Option.IsSubsetOf.some φ)) (by simp) (by rfl)

def andRight {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ ψ :=
  cutOne d <| cast <| negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
    cast (contraction (Γ' := ⦃φ, ψ⦄) (eta ψ) (by intro θ hθ; simp_all) (Option.IsSubsetOf.some ψ)) (by simp) (by rfl)

def specialize {φ : Semipropositionᵢ L 1} (d : Γ ⊢ᴸᴶ¹ ∀¹ φ) (t : Term L ℕ) : Γ ⊢ᴸᴶ¹ φ/[t] :=
  cutOne d <| cast <| negativeForall (Γ := 0) (Ξ := φ/[t]) (φ := φ) (t := t) <|
    cast (eta (φ/[t])) (by simp) (by simp)

def dneOfNegative [L.DecidableEq] : {φ : Propositionᵢ L} → φ.IsNegative → ⦃∼∼φ⦄ ⊢ᴸᴶ¹ φ
  | ⊥, _ => by
    have dn : ⦃(∼∼⊥ : Propositionᵢ L)⦄ ⊢ᴸᴶ¹ (∼⊥ : Propositionᵢ L) := contraction
      (positiveNeg (Γ := 0) <| cast (eta ⊥) (by simp) (by rfl))
      (by intro θ hθ; simp_all) (Option.IsSubsetOf.some _)
    exact negElim (assumption (φ := (∼∼⊥ : Propositionᵢ L)) (by simp)) dn
  | φ ⋏ ψ, h => by
    have hn : φ.IsNegative ∧ ψ.IsNegative := by simpa using h
    have ihφ := dneOfNegative hn.1
    have ihψ := dneOfNegative hn.2
    let N : Sequent L := ⦃∼∼(φ ⋏ ψ)⦄
    have dφ : N ⊢ᴸᴶ¹ φ := by
      have dnnφ : N ⊢ᴸᴶ¹ ↑(∼∼φ) := positiveNeg (Γ := N) <| by
        let C : Sequent L := N + ⦃∼φ⦄
        have dnAnd : C ⊢ᴸᴶ¹ ∼(φ ⋏ ψ) := positiveNeg (Γ := C) <| by
          have dAnd : C + ⦃φ ⋏ ψ⦄ ⊢ᴸᴶ¹ φ ⋏ ψ := assumption (by simp [C])
          exact negElim (assumption (φ := ∼φ) (by simp [C, Semiformulaᵢ.neg_def])) (andLeft dAnd)
        exact negElim (assumption (φ := ∼∼(φ ⋏ ψ)) (by simp [N, Semiformulaᵢ.neg_def])) dnAnd
      exact cutOne dnnφ ihφ
    have dψ : N ⊢ᴸᴶ¹ ψ := by
      have dnnψ : N ⊢ᴸᴶ¹ ↑(∼∼ψ) := positiveNeg (Γ := N) <| by
        let C : Sequent L := N + ⦃∼ψ⦄
        have dnAnd : C ⊢ᴸᴶ¹ ∼(φ ⋏ ψ) := positiveNeg (Γ := C) <| by
          have dAnd : C + ⦃φ ⋏ ψ⦄ ⊢ᴸᴶ¹ φ ⋏ ψ := assumption (by simp [C])
          exact negElim (assumption (φ := ∼ψ) (by simp [C, Semiformulaᵢ.neg_def])) (andRight dAnd)
        exact negElim (assumption (φ := ∼∼(φ ⋏ ψ)) (by simp [N, Semiformulaᵢ.neg_def])) dnAnd
      exact cutOne dnnψ ihψ
    exact positiveAnd dφ dψ
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
  | ∀¹ φ, h => by
    have hnFree : (Rewriting.free φ).IsNegative := by simpa using h
    have ihFree := dneOfNegative hnFree
    let N : Sequent L := ⦃∼∼(∀¹ φ)⦄
    apply positiveForall (Γ := N)
    let S : Sequent L := N⁺ᵐ
    have dnnFree : S ⊢ᴸᴶ¹ ↑(∼∼(Rewriting.free φ)) :=
      positiveNeg (Γ := S) <| by
        let C : Sequent L := S + ⦃∼(Rewriting.free φ)⦄
        have dnAll : C ⊢ᴸᴶ¹ ↑(∼(∀¹ Rewriting.shift φ)) :=
          positiveNeg (Γ := C) <| by
            let D : Sequent L := C + ⦃∀¹ Rewriting.shift φ⦄
            have dAll : D ⊢ᴸᴶ¹ ∀¹ Rewriting.shift φ := assumption (by simp [D])
            have dFree : D ⊢ᴸᴶ¹ Rewriting.free φ := cast (specialize dAll &0) (by rfl) (by simp)
            exact negElim
              (assumption (φ := ∼(Rewriting.free φ)) (by simp [C, Semiformulaᵢ.neg_def])) dFree
        exact negElim
          (assumption (φ := ∼∼(∀¹ Rewriting.shift φ))
            (by simp [S, N, Semiformulaᵢ.neg_def])) dnAll
    exact cutOne dnnFree ihFree
  termination_by φ _ => φ.complexity

def ofDNOfNegative [L.DecidableEq] {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ (∼∼φ : Propositionᵢ L))
    (h : φ.IsNegative) : Γ ⊢ᴸᴶ¹ φ := cutOne d (dneOfNegative h)

end Derivation

end LJ

inductive LJ (L : Language)
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

end LO.FirstOrder
