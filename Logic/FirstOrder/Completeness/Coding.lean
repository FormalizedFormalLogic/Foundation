import Logic.FirstOrder.Basic
import Logic.FirstOrder.Computability.Coding

namespace LO

namespace FirstOrder

open Subformula
variable {L : Language.{u}}
  [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]

def newVar (Γ : Sequent L) : ℕ := Γ.sup Subformula.upper

lemma not_fvar?_newVar {p : SyntacticFormula L} {Γ : Sequent L} (h : p ∈ Γ) : ¬fvar? p (newVar Γ) :=
  not_fvar?_of_lt_upper p (by simpa[newVar] using Finset.le_sup h)

namespace DerivationWA

open Subformula
variable {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L}

protected def all_nvar {p} (h : ∀' p ∈ Δ)
  (b : T ⊢ᵀ (insert ([→ &(newVar Δ)].hom p) Δ)) : T ⊢ᵀ Δ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let d₁ : ⊢ᵀ (insert ([→ &(newVar Δ)].hom p) (Δ ∪ b.leftHand.image Rew.emb.hom)) := by simpa using b.derivation
    let d₂ : ⊢ᵀ insert (∀' p) (Δ ∪ b.leftHand.image Rew.emb.hom) :=
      d₁.genelalizeByNewver₀ (by simpa[fvar?] using not_fvar?_newVar h)
        (by simp; rintro q (hq | ⟨σ, _, rfl⟩); { exact not_fvar?_newVar hq }; { simp[fvar?] })
    d₂.cast (Finset.insert_eq_of_mem $ by simp[h])

end DerivationWA

namespace DerivationWA

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSubformula L 1 → Code L
  | ex : SyntacticSubformula L 1 → SyntacticTerm L → Code L
  | id : Sentence L → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSubformula L 1) ⊕
    (SyntacticSubformula L 1 × SyntacticTerm L) ⊕
    (Sentence L) where
  toFun := fun c =>
    match c with
    | (Code.axL r v) => Sum.inl ⟨_, r, v⟩
    | Code.verum     => Sum.inr $ Sum.inl ()
    | (Code.and p q) => Sum.inr $ Sum.inr $ Sum.inl (p, q)
    | (Code.or p q)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, q)
    | (Code.all p)   => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl p
    | (Code.ex p t)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, t)
    | (Code.id σ)    => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr σ
  invFun := fun x =>
    match x with
    | (Sum.inl ⟨_, r, v⟩)                                                => Code.axL r v
    | (Sum.inr $ Sum.inl ())                                             => Code.verum
    | (Sum.inr $ Sum.inr $ Sum.inl (p, q))                               => Code.and p q
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, q))                     => Code.or p q
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl p)                => Code.all p
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, t)) => Code.ex p t
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr σ)      => Code.id σ
  left_inv := fun c => by cases c <;> simp
  right_inv := fun x => by
    rcases x with (⟨_, _, _⟩ | ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _) <;> simp

attribute [local instance] Subterm.encodable Subformula.encodable in
instance : Encodable (Code L) := Encodable.ofEquiv _ (Code.equiv L)

end DerivationWA

end FirstOrder

end LO
