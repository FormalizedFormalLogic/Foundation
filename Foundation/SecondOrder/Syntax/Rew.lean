module

public import Foundation.SecondOrder.Syntax.Formula

@[expose] public section

namespace LO.SecondOrder

open FirstOrder

namespace Semiformula

variable {L : Language} {Ξ ξ₁ ξ₂ : Type*}

def rewAux (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L Ξ ξ₁ N n₁ → Semiformula L Ξ ξ₂ N n₂
  |  rel R v => rel R (ω ∘ v)
  | nrel R v => nrel R (ω ∘ v)
  |   t ∈# X => ω t ∈# X
  |   t ∉# X => ω t ∉# X
  |   t ∈& X => ω t ∈& X
  |   t ∉& X => ω t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => rewAux ω φ ⋏ rewAux ω ψ
  |    φ ⋎ ψ => rewAux ω φ ⋎ rewAux ω ψ
  |     ∀⁰ φ => ∀⁰ rewAux ω.q φ
  |     ∃⁰ φ => ∃⁰ rewAux ω.q φ
  |     ∀¹ φ => ∀¹ rewAux ω φ
  |     ∃¹ φ => ∃¹ rewAux ω φ

lemma rewAux_neg (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    rewAux ω (∼φ) = ∼rewAux ω φ := by
  induction φ using rec' generalizing n₂ <;> simp [rewAux, *]

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L Ξ ξ₁ N n₁ →ˡᶜ Semiformula L Ξ ξ₂ N n₂ where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' φ := rewAux_neg _ _
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [DeMorgan.imply, rewAux, rewAux_neg]

instance : Rewriting L ξ₁ (Semiformula L Ξ ξ₁ N) ξ₂ (Semiformula L Ξ ξ₂ N) where
  app := rew
  app_all (_ _) := rfl
  app_exs (_ _) := rfl

@[coe] abbrev emb [IsEmpty o] (φ : Semiformula L Ξ o N n) : Semiformula L Ξ ξ N n := Rewriting.emb φ

abbrev free₀ (φ : Semistatement L N (n + 1)) : Semistatement L N n := Rewriting.free φ

abbrev shift₀ (φ : Semistatement L N n) : Semistatement L N n := Rewriting.shift φ

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ (rel r v : Semiformula L Ξ ξ₁ N n₁) = rel r fun i ↦ ω (v i) := rfl

lemma rew_rel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ (rel r v : Semiformula L Ξ ξ₁ N n₁) = rel r (ω ∘ v) := rfl

lemma rew_nrel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ (nrel r v : Semiformula L Ξ ξ₁ N n₁) = nrel r fun i ↦ ω (v i) := rfl

@[simp] lemma rew_all₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∀⁰ φ) = ∀⁰ (ω.q ▹ φ) := rfl

@[simp] lemma rew_exs₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∃⁰ φ) = ∃⁰ (ω.q ▹ φ) := rfl

@[simp] lemma rew_all₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∀¹ φ) = ∀¹ (ω ▹ φ) := rfl

@[simp] lemma rew_exs₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∃¹ φ) = ∃¹ (ω ▹ φ) := rfl

def b₁Shift : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ (N + 1) n
  |  rel R v => rel R v
  | nrel R v => nrel R v
  |   t ∈# X => t ∈# X.succ
  |   t ∉# X => t ∉# X.succ
  |   t ∈& X => t ∈& X
  |   t ∉& X => t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.b₁Shift ⋏ ψ.b₁Shift
  |    φ ⋎ ψ => φ.b₁Shift ⋎ ψ.b₁Shift
  |     ∀⁰ φ => ∀⁰ φ.b₁Shift
  |     ∃⁰ φ => ∃⁰ φ.b₁Shift
  |     ∀¹ φ => ∀¹ φ.b₁Shift
  |     ∃¹ φ => ∃¹ φ.b₁Shift

end Semiformula

structure Rew (L : Language) (Ξ₁ : Type*) (N₁ : ℕ) (Ξ₂ : Type*) (N₂ : ℕ) (ξ : Type*) where
  bv : Fin N₁ → Semiformula L Ξ₂ ξ N₂ 1
  fv : Ξ₁ → Semiformula L Ξ₂ ξ N₂ 1

namespace Rew

open Semiformula

variable {L : Language} {Ξ₁ Ξ₂ ξ : Type*}

def q (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ (N₁ + 1) Ξ₂ (N₂ + 1) ξ where
  bv := (#0 ∈# 0) :> fun X ↦ (Ω.bv X).b₁Shift
  fv X := (Ω.fv X).b₁Shift

def appAux (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Semiformula L Ξ₁ ξ N₁ n → Semiformula L Ξ₂ ξ N₂ n
  |  .rel R v => .rel R v
  | .nrel R v => .nrel R v
  |   t ∈# X => (Ω.bv X)/[t]
  |   t ∉# X => ∼(Ω.bv X)/[t]
  |   t ∈& X => (Ω.fv X)/[t]
  |   t ∉& X => ∼(Ω.fv X)/[t]
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => Ω.appAux φ ⋏ Ω.appAux ψ
  |    φ ⋎ ψ => Ω.appAux φ ⋎ Ω.appAux ψ
  |     ∀⁰ φ => ∀⁰ Ω.appAux φ
  |     ∃⁰ φ => ∃⁰ Ω.appAux φ
  |     ∀¹ φ => ∀¹ Ω.q.appAux φ
  |     ∃¹ φ => ∃¹ Ω.q.appAux φ

lemma appAux_neg (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    Ω.appAux (∼φ) = ∼Ω.appAux φ := by
  induction φ using Semiformula.rec' generalizing N₂ <;> simp [appAux, *]

def app (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Semiformula L Ξ₁ ξ N₁ n →ˡᶜ Semiformula L Ξ₂ ξ N₂ n where
  toTr := Ω.appAux
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [appAux_neg]
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [DeMorgan.imply, appAux_neg, appAux]

variable (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ)

@[simp] lemma app_rel (r : L.Rel k) (v) :
    Ω.app (.rel r v : Semiformula L Ξ₁ ξ N₁ n) = .rel r v := rfl

@[simp] lemma app_nrel (r : L.Rel k) (v) :
    Ω.app (.nrel r v : Semiformula L Ξ₁ ξ N₁ n) = .nrel r v := rfl

@[simp] lemma app_bvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω.app (t ∈# X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.bv X)/[t] := rfl

@[simp] lemma app_nbvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω.app (t ∉# X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.bv X)/[t] := rfl

@[simp] lemma app_fvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω.app (t ∈& X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.fv X)/[t] := rfl

@[simp] lemma app_nfvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω.app (t ∉& X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.fv X)/[t] := rfl

@[simp] lemma app_all₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω.app (∀⁰ φ) = ∀⁰ Ω.app φ := rfl

@[simp] lemma app_exs₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω.app (∃⁰ φ) = ∃⁰ Ω.app φ := rfl

@[simp] lemma app_all₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω.app (∀¹ φ) = ∀¹ Ω.q.app φ := rfl

@[simp] lemma app_exs₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω.app (∃¹ φ) = ∃¹ Ω.q.app φ := rfl

end Rew

open Semiformula

end LO.SecondOrder
