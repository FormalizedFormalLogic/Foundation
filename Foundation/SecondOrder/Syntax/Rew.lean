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

@[simp] lemma rew_bvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Fin N) :
    ω ▹ (t ∈# X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∈# X := rfl

@[simp] lemma rew_nbvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Fin N) :
    ω ▹ (t ∉# X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∉# X := rfl

@[simp] lemma rew_fvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Ξ) :
    ω ▹ (t ∈& X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∈& X := rfl

@[simp] lemma rew_nfvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Ξ) :
    ω ▹ (t ∉& X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∉& X := rfl

@[simp] lemma rew_all₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∀⁰ φ) = ∀⁰ (ω.q ▹ φ) := rfl

@[simp] lemma rew_exs₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∃⁰ φ) = ∃⁰ (ω.q ▹ φ) := rfl

@[simp] lemma rew_all₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∀¹ φ) = ∀¹ (ω ▹ φ) := rfl

@[simp] lemma rew_exs₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∃¹ φ) = ∃¹ (ω ▹ φ) := rfl

instance : ReflectiveRewriting L ξ (Semiformula L Ξ ξ N) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, rew_nrel, *]

instance : TransitiveRewriting L ξ₁ (Semiformula L Ξ ξ₁ N) ξ₂ (Semiformula L Ξ ξ₂ N) ξ₃ (Semiformula L Ξ ξ₃ N) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, rew_nrel, Rew.comp_app, Rew.q_comp, *]

def b₁ShiftAux : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ (N + 1) n
  |  rel R v => rel R v
  | nrel R v => nrel R v
  |   t ∈# X => t ∈# X.succ
  |   t ∉# X => t ∉# X.succ
  |   t ∈& X => t ∈& X
  |   t ∉& X => t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.b₁ShiftAux ⋏ ψ.b₁ShiftAux
  |    φ ⋎ ψ => φ.b₁ShiftAux ⋎ ψ.b₁ShiftAux
  |     ∀⁰ φ => ∀⁰ φ.b₁ShiftAux
  |     ∃⁰ φ => ∃⁰ φ.b₁ShiftAux
  |     ∀¹ φ => ∀¹ φ.b₁ShiftAux
  |     ∃¹ φ => ∃¹ φ.b₁ShiftAux

lemma b₁ShiftAux_neg (φ : Semiformula L Ξ ξ N n) :
    (∼φ).b₁ShiftAux = ∼(φ.b₁ShiftAux) := by
  induction φ using rec' <;> simp [b₁ShiftAux, *]

def b₁Shift : Semiformula L Ξ ξ N n →ˡᶜ Semiformula L Ξ ξ (N + 1) n where
  toTr := b₁ShiftAux
  map_top' := rfl
  map_bot' := rfl
  map_neg' φ := b₁ShiftAux_neg _
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [DeMorgan.imply, b₁ShiftAux_neg, b₁ShiftAux]

/--/
@[simp] lemma b₁Shift_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v : Semiformula L Ξ ξ N n).b₁Shift = rel r v := rfl

@[simp] lemma b₁Shift_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v : Semiformula L Ξ ξ N n).b₁Shift = nrel r v := rfl

@[simp] lemma b₁Shift_bvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∈# X : Semiformula L Ξ ξ N n).b₁Shift = t ∈# X.succ := rfl

@[simp] lemma b₁Shift_nbvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∉# X : Semiformula L Ξ ξ N n).b₁Shift = t ∉# X.succ := rfl

@[simp] lemma b₁Shift_fvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∈& X : Semiformula L Ξ ξ N n).b₁Shift = t ∈& X := rfl

@[simp] lemma b₁Shift_nfvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∉& X : Semiformula L Ξ ξ N n).b₁Shift = t ∉& X := rfl

@[simp] lemma b₁Shift_all₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀⁰ φ).b₁Shift = ∀⁰ (φ.b₁Shift) := rfl

@[simp] lemma b₁Shift_exs₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃⁰ φ).b₁Shift = ∃⁰ (φ.b₁Shift) := rfl

@[simp] lemma b₁Shift_all₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀¹ φ).b₁Shift = ∀¹ (φ.b₁Shift) := rfl

@[simp] lemma b₁Shift_exs₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃¹ φ).b₁Shift = ∃¹ (φ.b₁Shift) := rfl

lemma b₁Shift_comm (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    (ω ▹ φ).b₁Shift = ω ▹ φ.b₁Shift := by
  match φ with
  | .rel R v | .nrel R v | t ∈# X | t ∉# X | t ∈& X | t ∉& X | ⊤ | ⊥ => rfl
  | φ ⋏ ψ | φ ⋎ ψ => simp [b₁Shift_comm ω φ, b₁Shift_comm ω ψ]
  | ∀⁰ φ | ∃⁰ φ => simp [b₁Shift_comm ω.q φ]
  | ∀¹ φ | ∃¹ φ => simp [b₁Shift_comm ω φ]

end Semiformula

@[ext]
structure Rew (L : Language) (Ξ₁ : Type*) (N₁ : ℕ) (Ξ₂ : Type*) (N₂ : ℕ) (ξ : Type*) where
  bv : Fin N₁ → Semiformula L Ξ₂ ξ N₂ 1
  fv : Ξ₁ → Semiformula L Ξ₂ ξ N₂ 1

namespace Rew

open Semiformula

variable {L : Language} {Ξ₁ Ξ₂ ξ : Type*}

def map (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₂ where
  bv X := ω ▹ Ω.bv X
  fv X := ω ▹ Ω.fv X

@[simp] lemma map_bv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) (X : Fin N₁) :
    (Ω.map ω).bv X = ω ▹ Ω.bv X := by rfl

@[simp] lemma map_fv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) (X : Ξ₁) :
    (Ω.map ω).fv X = ω ▹ Ω.fv X := by rfl

def q (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ (N₁ + 1) Ξ₂ (N₂ + 1) ξ where
  bv := (#0 ∈# 0) :> fun X ↦ (Ω.bv X).b₁Shift
  fv X := (Ω.fv X).b₁Shift

local postfix:max "𐞥" => q

@[simp] lemma q_bv_zero (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω𐞥.bv 0 = #0 ∈# 0 := by rfl

@[simp] lemma q_bv_succ (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    Ω𐞥.bv X.succ = (Ω.bv X).b₁Shift := by rfl

@[simp] lemma q_fv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    Ω𐞥.fv X = (Ω.fv X).b₁Shift := by rfl

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
  |     ∀¹ φ => ∀¹ Ω𐞥.appAux φ
  |     ∃¹ φ => ∃¹ Ω𐞥.appAux φ

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

local infix:73 " • " => app

section

variable (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ)

@[simp] lemma app_rel (r : L.Rel k) (v) :
    Ω • (.rel r v : Semiformula L Ξ₁ ξ N₁ n) = .rel r v := rfl

@[simp] lemma app_nrel (r : L.Rel k) (v) :
    Ω • (.nrel r v : Semiformula L Ξ₁ ξ N₁ n) = .nrel r v := rfl

@[simp] lemma app_bvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω • (t ∈# X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.bv X)/[t] := rfl

@[simp] lemma app_nbvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω • (t ∉# X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.bv X)/[t] := rfl

@[simp] lemma app_fvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω • (t ∈& X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.fv X)/[t] := rfl

@[simp] lemma app_nfvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω • (t ∉& X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.fv X)/[t] := rfl

@[simp] lemma app_all₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω • (∀⁰ φ) = ∀⁰ Ω • φ := rfl

@[simp] lemma app_exs₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω • (∃⁰ φ) = ∃⁰ Ω • φ := rfl

@[simp] lemma app_all₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω • (∀¹ φ) = ∀¹ Ω𐞥 • φ := rfl

@[simp] lemma app_exs₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω • (∃¹ φ) = ∃¹ Ω𐞥 • φ := rfl

end

lemma app_comm_subst {N₁ N₂} (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (v : Fin n₁ → Semiterm L ξ n₂) (φ : Semiformula L Ξ₁ ξ N₁ n₁) :
    Ω • (FirstOrder.Rew.subst v ▹ φ) = FirstOrder.Rew.subst v ▹ (Ω • φ) := by
  induction φ using Semiformula.rec' generalizing N₂ n₂ <;>
    simp [*, ←FirstOrder.TransitiveRewriting.comp_app, FirstOrder.Rew.subst_comp_subst, FirstOrder.Rew.q_subst,
      Semiformula.rew_rel, Semiformula.rew_nrel]

protected def id : Rew L Ξ N Ξ N ξ where
  bv X := #0 ∈# X
  fv X := #0 ∈& X

@[simp] lemma id_bv (X : Fin N) :
    (Rew.id : Rew L Ξ N Ξ N ξ).bv X = #0 ∈# X := by rfl

@[simp] lemma id_fv (X : Ξ) :
    (Rew.id : Rew L Ξ N Ξ N ξ).fv X = #0 ∈& X := by rfl

@[simp] lemma q_id :
    (Rew.id : Rew L Ξ N Ξ N ξ)𐞥 = Rew.id := by
  ext X
  · cases X using Fin.cases <;> simp
  · simp

@[simp] lemma app_id (φ : Semiformula L Ξ ξ N n) :
    Rew.id • φ = φ := by
  induction φ using Semiformula.rec' <;> simp [*]

def comp (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₁ Ξ₃ N₃ ξ where
  bv X := Ω₂₃ • Ω₁₂.bv X
  fv X := Ω₂₃ • Ω₁₂.fv X

@[simp] lemma comp_bv (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    (Ω₂₃.comp Ω₁₂).bv X = Ω₂₃ • Ω₁₂.bv X := rfl

@[simp] lemma comp_fv (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω₂₃.comp Ω₁₂).fv X = Ω₂₃ • Ω₁₂.fv X := rfl

lemma app_b₁Shift_eq_q_app_b₁Shift (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω • φ).b₁Shift = Ω𐞥 • φ.b₁Shift := by
  induction φ using Semiformula.rec' generalizing N₂ <;> simp [*, b₁Shift_comm]

@[simp] lemma q_comp_eq (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    (Ω₂₃.comp Ω₁₂)𐞥 = Ω₂₃𐞥.comp Ω₁₂𐞥 := by
  ext X
  · cases X using Fin.cases
    · simp [comp, Semiformula.b₁Shift]
    · simp [comp, app_b₁Shift_eq_q_app_b₁Shift]
  · simp [comp, app_b₁Shift_eq_q_app_b₁Shift]

lemma app_comp (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω₂₃.comp Ω₁₂) • φ = Ω₂₃ • (Ω₁₂ • φ) := by
  induction φ using Semiformula.rec' generalizing N₂ N₃ <;> simp [*, app_comm_subst]

@[simp] lemma one_comp (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Rew.id.comp Ω = Ω := by ext X <;> simp

@[simp] lemma comp_one (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω.comp Rew.id = Ω := by ext X <;> simp

def b₁shift : Rew L Ξ N Ξ (N + 1) ξ where
  bv X := #0 ∈# X.succ
  fv X := #0 ∈& X

@[simp] lemma b₁shift_bv (X : Fin N) :
    (Rew.b₁shift : Rew L Ξ N Ξ (N + 1) ξ).bv X = #0 ∈# X.succ := rfl

@[simp] lemma b₁shift_fv (X : Ξ) :
    (Rew.b₁shift : Rew L Ξ N Ξ (N + 1) ξ).fv X = #0 ∈& X := rfl

@[simp] lemma q_b₁shift :
    (Rew.b₁shift : Rew L Ξ N Ξ (N + 1) ξ)𐞥 = Rew.b₁shift := by
  ext X
  · cases X using Fin.cases <;> simp
  · simp

@[simp] lemma app_b₁shift (φ : Semiformula L Ξ ξ N n) :
    Rew.b₁shift • φ = φ.b₁Shift := by
  induction φ using Semiformula.rec' <;> simp [*]

end Rew

open Semiformula

end LO.SecondOrder
