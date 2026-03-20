module

public import Foundation.SecondOrder.Syntax.Rew

@[expose] public section

/-!
# A set-theoretic semantics of second-order logic

- TODO: Align with https://github.com/FormalizedFormalLogic/Foundation/pull/794
-/

namespace LO.SecondOrder

open FirstOrder

variable {L : Language}

structure Struc₂ (L : Language) extends FirstOrder.Struc L where
  sets : Set (Set Dom)

abbrev SmallStruc (L : Language.{u}) := Struc.{u, u} L

namespace Struc₂

instance (s : Struc₂ L) : Nonempty s.Dom := s.nonempty

instance (s : Struc₂ L) : Structure L s.Dom := inferInstance

end Struc₂

namespace Semiformula

variable {M : Type w} [s : Structure L M]

def EvalAux
    (𝕊 : Set (Set M))
    (F : Ξ → Set M) (f : ξ → M) (E : Fin N → Set M) (e : Fin n → M) : Semiformula L Ξ ξ N n → Prop
  |  rel R v => s.rel R (Semiterm.val s e f ∘ v)
  | nrel R v => ¬s.rel R (Semiterm.val s e f ∘ v)
  |   t ∈& X => t.val s e f ∈ F X
  |   t ∉& X => t.val s e f ∉ F X
  |   t ∈# X => t.val s e f ∈ E X
  |   t ∉# X => t.val s e f ∉ E X
  |        ⊤ => True
  |        ⊥ => False
  |    φ ⋏ ψ => φ.EvalAux 𝕊 F f E e ∧ ψ.EvalAux 𝕊 F f E e
  |    φ ⋎ ψ => φ.EvalAux 𝕊 F f E e ∨ ψ.EvalAux 𝕊 F f E e
  |     ∀⁰ φ => ∀ x, φ.EvalAux 𝕊 F f E (x :> e)
  |     ∃⁰ φ => ∃ x, φ.EvalAux 𝕊 F f E (x :> e)
  |     ∀¹ φ => ∀ X ∈ 𝕊, φ.EvalAux 𝕊 F f (X :> E) e
  |     ∃¹ φ => ∃ X ∈ 𝕊, φ.EvalAux 𝕊 F f (X :> E) e

variable {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M} {E : Fin N → Set M} {e : Fin n → M}

@[simp] lemma EvalAux_neg (φ : Semiformula L Ξ ξ N n) :
    EvalAux 𝕊 F f E e (∼φ) ↔ ¬EvalAux 𝕊 F f E e φ := by
  induction φ using rec' <;> simp [*, EvalAux, or_iff_not_imp_left]

def Eval (𝕊 : Set (Set M)) (F : Ξ → Set M) (f : ξ → M) (E : Fin N → Set M) (e : Fin n → M) : Semiformula L Ξ ξ N n →ˡᶜ Prop where
  toTr := EvalAux 𝕊 F f E e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [EvalAux_neg, EvalAux, imp_iff_not_or]

@[simp] lemma eval_rel {k} {R : L.Rel k} {v} :
    (rel R v).Eval 𝕊 F f E e ↔ s.rel R (Semiterm.val s e f ∘ v) := by rfl

@[simp] lemma eval_nrel {k} {R : L.Rel k} {v} :
    (nrel R v).Eval 𝕊 F f E e ↔ ¬s.rel R (Semiterm.val s e f ∘ v) := by rfl

@[simp] lemma eval_fvar {X : Ξ} {t} :
    (t ∈& X).Eval 𝕊 F f E e ↔ t.val s e f ∈ F X := by rfl

@[simp] lemma eval_nfvar {X : Ξ} {t} :
    (t ∉& X).Eval 𝕊 F f E e ↔ t.val s e f ∉ F X := by rfl

@[simp] lemma eval_bvar {X : Fin N} {t} :
    (t ∈# X).Eval 𝕊 F f E e ↔ t.val s e f ∈ E X := by rfl

@[simp] lemma eval_nbvar {X : Fin N} {t} :
    (t ∉# X).Eval 𝕊 F f E e ↔ t.val s e f ∉ E X := by rfl

@[simp] lemma eval_fal₀ {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∀⁰ φ).Eval 𝕊 F f E e ↔ ∀ x, φ.Eval 𝕊 F f E (x :> e) := by rfl

@[simp] lemma eval_exs₀ {φ : Semiformula L Ξ ξ N (n + 1)} :
    (∃⁰ φ).Eval 𝕊 F f E e ↔ ∃ x, φ.Eval 𝕊 F f E (x :> e) := by rfl

@[simp] lemma eval_fal₁ {φ : Semiformula L Ξ ξ (N + 1) n} :
    (∀¹ φ).Eval 𝕊 F f E e ↔ ∀ X ∈ 𝕊, φ.Eval 𝕊 F f (X :> E) e := by rfl

@[simp] lemma eval_exs₁ {φ : Semiformula L Ξ ξ (N + 1) n} :
    (∃¹ φ).Eval 𝕊 F f E e ↔ ∃ X ∈ 𝕊, φ.Eval 𝕊 F f (X :> E) e := by rfl

end Semiformula

def Struc₂.of {M : Type*} [Nonempty M] (𝕊 : Set (Set M)) (L : Language) [s : Structure L M] : Struc₂ L := ⟨s.toStruc, 𝕊⟩

notation:max 𝕊 "↓[" L "]" => Struc₂.of 𝕊 L

instance : Semantics (Struc₂ L) (Sentence L) where
  Models 𝓈 σ := σ.Eval 𝓈.sets Empty.elim Empty.elim ![] ![]

lemma models_def {𝓈 : Struc₂ L} {σ : Sentence L} :
    𝓈 ⊧ σ ↔ σ.Eval 𝓈.sets Empty.elim Empty.elim ![] ![] := by rfl

lemma models_iff [Nonempty M] [Structure L M] {𝕊 : Set (Set M)} {σ : Sentence L} :
    𝕊↓[L] ⊧ σ ↔ σ.Eval 𝕊 Empty.elim Empty.elim ![] ![] := by rfl

instance : Semantics.Tarski (Struc₂ L) where
  models_verum _ := by simp [models_def]
  models_falsum _ := by simp [models_def]
  models_and := by simp [models_def]
  models_or := by simp [models_def]
  models_imply := by simp [models_def]
  models_not := by simp [models_def]

end LO.SecondOrder
