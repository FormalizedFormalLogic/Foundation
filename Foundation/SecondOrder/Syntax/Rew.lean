module

public import Foundation.SecondOrder.Syntax.Formula

@[expose] public section

namespace Fin

def retrusion (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) := 0 :> fun i ↦ (f i).succ

@[simp] lemma retrusion_zero (f : Fin n → Fin m) : retrusion f 0 = 0 := rfl

@[simp] lemma retrusion_succ (f : Fin n → Fin m) (i : Fin n) :
    retrusion f i.succ = (f i).succ := rfl

@[simp] lemma retrusion_comp_succ (f : Fin n → Fin m) :
    retrusion f ∘ Fin.succ = Fin.succ ∘ f := by ext i; simp

@[simp] lemma retrusion_id : retrusion (id : Fin n → Fin n) = id := by
  ext i; cases i using Fin.cases <;> simp

@[simp] lemma retrusion_comp_retrusion (f : Fin n → Fin m) (g : Fin m → Fin p) :
    retrusion g ∘ retrusion f = retrusion (g ∘ f) := by
  ext i; cases i using Fin.cases <;> simp

end Fin

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

def bmapAux (f : Fin N → Fin M) : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ M n
  |  rel R v => rel R v
  | nrel R v => nrel R v
  |   t ∈# X => t ∈# f X
  |   t ∉# X => t ∉# f X
  |   t ∈& X => t ∈& X
  |   t ∉& X => t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.bmapAux f ⋏ ψ.bmapAux f
  |    φ ⋎ ψ => φ.bmapAux f ⋎ ψ.bmapAux f
  |     ∀⁰ φ => ∀⁰ φ.bmapAux f
  |     ∃⁰ φ => ∃⁰ φ.bmapAux f
  |     ∀¹ φ => ∀¹ φ.bmapAux (Fin.retrusion f)
  |     ∃¹ φ => ∃¹ φ.bmapAux (Fin.retrusion f)

lemma bmapAux_neg {f : Fin N → Fin M} (φ : Semiformula L Ξ ξ N n) :
    (∼φ).bmapAux f = ∼(φ.bmapAux f) := by
  induction φ using rec' generalizing M <;> simp [bmapAux, *]

def bmap (f : Fin N → Fin M) : Semiformula L Ξ ξ N n →ˡᶜ Semiformula L Ξ ξ M n where
  toTr := bmapAux f
  map_top' := rfl
  map_bot' := rfl
  map_neg' φ := bmapAux_neg _
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [DeMorgan.imply, bmapAux_neg, bmapAux]

section bmap

variable {f : Fin N → Fin M}

@[simp] lemma bmap_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v : Semiformula L Ξ ξ N n).bmap f = rel r v := rfl

@[simp] lemma bmap_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v : Semiformula L Ξ ξ N n).bmap f = nrel r v := rfl

@[simp] lemma bmap_bvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∈# X : Semiformula L Ξ ξ N n).bmap f = t ∈# f X := rfl

@[simp] lemma bmap_nbvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∉# X : Semiformula L Ξ ξ N n).bmap f = t ∉# f X := rfl

@[simp] lemma bmap_fvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∈& X : Semiformula L Ξ ξ N n).bmap f = t ∈& X := rfl

@[simp] lemma bmap_nfvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∉& X : Semiformula L Ξ ξ N n).bmap f = t ∉& X := rfl

@[simp] lemma bmap_all₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀⁰ φ).bmap f = ∀⁰ (φ.bmap f) := rfl

@[simp] lemma bmap_exs₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃⁰ φ).bmap f = ∃⁰ (φ.bmap f) := rfl

@[simp] lemma bmap_all₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀¹ φ).bmap f = ∀¹ (φ.bmap (Fin.retrusion f)) := rfl

@[simp] lemma bmap_exs₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃¹ φ).bmap f = ∃¹ (φ.bmap (Fin.retrusion f)) := rfl

lemma bmap_comp {M N n} (f : Fin N → Fin M) (g : Fin M → Fin P) (φ : Semiformula L Ξ ξ N n) :
    (φ.bmap f).bmap g = φ.bmap (g ∘ f) := by
  induction φ using Semiformula.rec' generalizing M P <;> simp [*]

end bmap

lemma bmap_comm (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) (f : Fin N → Fin M) :
    (ω ▹ φ).bmap f = ω ▹ φ.bmap f := by
  match φ with
  | .rel R v | .nrel R v | t ∈# X | t ∉# X | t ∈& X | t ∉& X | ⊤ | ⊥ => rfl
  | φ ⋏ ψ | φ ⋎ ψ => simp [bmap_comm ω φ, bmap_comm ω ψ]
  | ∀⁰ φ | ∃⁰ φ => simp [bmap_comm ω.q φ]
  | ∀¹ φ | ∃¹ φ => simp [bmap_comm ω φ]

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
  bv := (#0 ∈# 0) :> fun X ↦ (Ω.bv X).bmap Fin.succ
  fv X := (Ω.fv X).bmap Fin.succ

local postfix:max "𐞥" => q

@[simp] lemma q_bv_zero (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω𐞥.bv 0 = #0 ∈# 0 := by rfl

@[simp] lemma q_bv_succ (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    Ω𐞥.bv X.succ = (Ω.bv X).bmap Fin.succ := by rfl

@[simp] lemma q_fv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    Ω𐞥.fv X = (Ω.fv X).bmap Fin.succ := by rfl

def appAux (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Semiformula L Ξ₁ ξ N₁ n → Semiformula L Ξ₂ ξ N₂ n
  |  .rel R v => .rel R v
  | .nrel R v => .nrel R v
  |    t ∈# X => (Ω.bv X)/[t]
  |    t ∉# X => ∼(Ω.bv X)/[t]
  |    t ∈& X => (Ω.fv X)/[t]
  |    t ∉& X => ∼(Ω.fv X)/[t]
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => Ω.appAux φ ⋏ Ω.appAux ψ
  |     φ ⋎ ψ => Ω.appAux φ ⋎ Ω.appAux ψ
  |      ∀⁰ φ => ∀⁰ Ω.appAux φ
  |      ∃⁰ φ => ∃⁰ Ω.appAux φ
  |      ∀¹ φ => ∀¹ Ω𐞥.appAux φ
  |      ∃¹ φ => ∃¹ Ω𐞥.appAux φ

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

def bLeft (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₁ Ξ₂ N₃ ξ where
  bv X := (Ω.bv X).bmap f
  fv X := (Ω.fv X).bmap f

@[simp] lemma bLeft_bv (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    (Ω.bLeft f).bv X = (Ω.bv X).bmap f := rfl

@[simp] lemma bLeft_fv (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω.bLeft f).fv X = (Ω.fv X).bmap f := rfl

lemma bLeft_q (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (f : Fin N₂ → Fin N₃) :
    (Ω.bLeft f)𐞥 = Ω𐞥.bLeft (Fin.retrusion f) := by
  ext X
  · cases X using Fin.cases <;> simp [q_bv_succ, bLeft_bv, bmap_comp]
  · simp [q_fv, bLeft_fv, bmap_comp]

lemma app_bmap_eq_bLeft (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω • φ).bmap f = Ω.bLeft f • φ := by
  induction φ using Semiformula.rec' generalizing N₂ N₃ <;> simp [*, bmap_comm, bLeft_q]

def bRight (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₀ Ξ₂ N₂ ξ where
  bv X := Ω.bv (f X)
  fv X := Ω.fv X

@[simp] lemma bRight_bv (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₀) :
    (Ω.bRight f).bv X = Ω.bv (f X) := rfl

@[simp] lemma bRight_fv (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω.bRight f).fv X = Ω.fv X := rfl

lemma bRight_q (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    (Ω.bRight f)𐞥 = Ω𐞥.bRight (Fin.retrusion f) := by
  ext X
  · cases X using Fin.cases <;> simp [bRight_bv]
  · simp [bRight_fv]

lemma bmap_app_eq (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₀ n) :
    Ω • φ.bmap f = Ω.bRight f • φ := by
  induction φ using Semiformula.rec' generalizing N₁ N₂ <;> simp [*, bRight_q]

@[simp] lemma q_bRight_succ (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω𐞥.bRight Fin.succ = Ω.bLeft Fin.succ := by rfl

@[simp] lemma q_comp_eq (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    (Ω₂₃.comp Ω₁₂)𐞥 = Ω₂₃𐞥.comp Ω₁₂𐞥 := by
  ext X
  · cases X using Fin.cases <;> simp [comp, app_bmap_eq_bLeft, bmap_app_eq]
  · simp [comp, app_bmap_eq_bLeft, bmap_app_eq]

lemma app_comp (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω₂₃.comp Ω₁₂) • φ = Ω₂₃ • (Ω₁₂ • φ) := by
  induction φ using Semiformula.rec' generalizing N₂ N₃ <;> simp [*, app_comm_subst]

@[simp] lemma one_comp (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Rew.id.comp Ω = Ω := by ext X <;> simp

@[simp] lemma comp_one (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω.comp Rew.id = Ω := by ext X <;> simp

def free : Rew L ℕ (N + 1) ℕ N ξ where
  bv := (#0 ∈# ·) <: #0 ∈& 0
  fv X := #0 ∈& (X + 1)

section free

@[simp] lemma free_bvar_castSucc_eq (X : Fin N) :
    (free (L := L) (ξ := ξ)).bv (Fin.castSucc X) = #0 ∈# X := by simp [free]

@[simp] lemma free_bvar_last (N : ℕ) :
    (free (L := L) (ξ := ξ)).bv (Fin.last N) = #0 ∈& 0 := by simp [free]

@[simp] lemma free_fvar (X : ℕ) :
    (free (L := L) (ξ := ξ) (N := N)).fv X = #0 ∈& (X + 1) := rfl

@[simp] lemma q_free : (free (L := L) (ξ := ξ) (N := N))𐞥 = free := by
  ext X
  · cases X using Fin.cases
    · simp [free]
    case succ X =>
      simp
      cases X using Fin.lastCases <;> simp [-Fin.castSucc_succ, Fin.succ_castSucc]
  · simp [free]

end free

def rewrite (f : Ξ₁ → Ξ₂) : Rew L Ξ₁ N Ξ₂ N ξ where
  bv X := #0 ∈# X
  fv X := #0 ∈& f X

section rewrite

@[simp] lemma rewrite_bv (f : Ξ₁ → Ξ₂) (X : Fin N) :
    (rewrite (L := L) (ξ := ξ) f).bv X = #0 ∈# X := rfl

@[simp] lemma rewrite_fv (f : Ξ₁ → Ξ₂) (X : Ξ₁) :
    (rewrite (L := L) (ξ := ξ) (N := N) f).fv X = #0 ∈& f X := rfl

@[simp] lemma q_rewrite (f : Ξ₁ → Ξ₂) :
    (rewrite (L := L) (ξ := ξ) (N := N) f)𐞥 = rewrite f := by
  ext X
  · cases X using Fin.cases <;> simp [rewrite]
  · simp [rewrite]

end rewrite

def shift : Rew L ℕ N ℕ N ξ := rewrite (· + 1)

section shift

@[simp] lemma shift_bv (X : Fin N) :
    (shift (L := L) (ξ := ξ)).bv X = #0 ∈# X := rfl

@[simp] lemma shift_fv (X : ℕ) :
    (shift (L := L) (ξ := ξ) (N := N)).fv X = #0 ∈& (X + 1) := rfl

@[simp] lemma q_shift :
    (shift (L := L) (ξ := ξ) (N := N))𐞥 = shift := q_rewrite _

end shift

def emb {ο : Type*} [IsEmpty ο] : Rew L ο N Ξ N ξ := rewrite (IsEmpty.elim' inferInstance)

section emb

variable {ο : Type*} [IsEmpty ο]

@[simp] lemma emb_bv (X : Fin N) :
    (emb (L := L) (ξ := ξ) (Ξ := Ξ) (ο := ο)).bv X = #0 ∈# X := rfl

@[simp] lemma q_emb :
    (emb (L := L) (ξ := ξ) (Ξ := Ξ) (ο := ο) (N := N))𐞥 = emb := q_rewrite _

end emb

def subst (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) : Rew L Ξ₁ N₁ Ξ₁ N₂ ξ where
  bv := Φ
  fv X := #0 ∈& X

section subst

@[simp] lemma subst_bv (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) (X : Fin N₁) :
    (subst Φ).bv X = Φ X := rfl

@[simp] lemma subst_fv (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) (X : Ξ₁) :
    (subst Φ).fv X = #0 ∈& X := rfl

lemma q_subst (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) :
    (subst Φ)𐞥 = subst ((#0 ∈# 0) :> fun X ↦ (Φ X).bmap .succ) := by
  ext X
  · cases X using Fin.cases <;> simp [subst]
  · simp [subst]

end subst

end Rew

namespace Semistatement

abbrev free₀ (φ : Semistatement L N (n + 1)) : Semistatement L N n := FirstOrder.Rewriting.free φ

abbrev shift₀ (φ : Semistatement L N n) : Semistatement L N n := FirstOrder.Rewriting.shift φ

abbrev free₁ (φ : Semistatement L (N + 1) n) : Semistatement L N n := Rew.free.app φ

abbrev shift₁ (φ : Semistatement L N n) : Semistatement L N n := Rew.shift.app φ

abbrev subst₁ (φ : Semiformula L Ξ₁ ξ N₁ n) (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) :
    Semiformula L Ξ₁ ξ N₂ n := (Rew.subst Φ).app φ

section Notation

open Lean PrettyPrinter Delaborator

syntax (name := substNotation) term:max "/⟦" term,* "⟧" : term

macro_rules (kind := substNotation)
  | `($φ:term /⟦$terms:term,*⟧) => `(subst₁ $φ ![$terms,*])

@[app_unexpander subst₁]
meta def unexpsnderSubst : Unexpander
  | `($_ $φ:term ![$ts:term,*]) => `($φ /⟦ $ts,* ⟧)
  | _                           => throw ()

end Notation

end Semistatement

namespace Semisentence

@[coe] abbrev emb (φ : Semisentence L N n) : Semiformula L Ξ ξ N n := Rew.emb.app (FirstOrder.Rewriting.emb φ)

instance : Coe (Semisentence L N n) (Semiformula L Ξ ξ N n) := ⟨emb⟩

end Semisentence

end LO.SecondOrder
