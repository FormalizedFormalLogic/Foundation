import Logic.FirstOrder.Basic
import Logic.FirstOrder.Computability.Coding

namespace LO

namespace FirstOrder

open Semiformula
variable {L : Language.{u}}
  [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]
  [∀ k, Encodable (L.Func k)] [∀ k, Encodable (L.Rel k)]

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.upper).foldr max 0

lemma not_fvar?_newVar {p : SyntacticFormula L} {Γ : Sequent L} (h : p ∈ Γ) : ¬fvar? p (newVar Γ) :=
  not_fvar?_of_lt_upper p (by simpa[newVar] using List.le_max_of_le (List.mem_map_of_mem _ h) (by simp))

namespace System

open Semiformula
variable {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L}

def allNvar {p} (h : ∀' p ∈ Δ) :
    T ⊢'' p/[&(newVar Δ)] :: Δ → T ⊢'' Δ := fun b ↦
  let b : T ⊢'' (∀' p) :: Δ :=
    genelalizeByNewver (by simpa[fvar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Gentzen.Disjconseq.wk b (by simp[h])

protected def id {σ} (hσ : σ ∈ T) :
    T ⊢'' ~Rew.emb.hom σ :: Δ → T ⊢'' Δ := fun b ↦ by
  have := Gentzen.negLeft b.derivation
  exact Gentzen.toDisjconseq this
    (by simp only [List.mem_cons, DeMorgan.neg]; rintro p (rfl | hp)
        · exact Set.mem_image_of_mem _ hσ
        · exact b.subset p hp )

end System

namespace System

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.Rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSemiformula L 1 → Code L
  | ex : SyntacticSemiformula L 1 → SyntacticTerm L → Code L
  | id : Sentence L → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.Rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSemiformula L 1) ⊕
    (SyntacticSemiformula L 1 × SyntacticTerm L) ⊕
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

attribute [local instance] Semiterm.encodable Semiformula.encodable in
instance : Encodable (Code L) := Encodable.ofEquiv _ (Code.equiv L)

end System

end FirstOrder

end LO
