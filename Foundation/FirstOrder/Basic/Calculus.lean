import Foundation.Logic.Calculus
import Foundation.FirstOrder.Basic.Syntax.Theory

namespace LO

namespace FirstOrder

open Semiformula

abbrev Sequent (L : Language) := List (SyntacticFormula L)

variable {L : Language} {𝔖 : SyntacticFormulas L}

inductive Derivation (𝔖 : SyntacticFormulas L) : Sequent L → Type _
| axL : rel r v ∈ Γ → nrel r v ∈ Γ → Derivation 𝔖 Γ
| verum : ⊤ ∈ Γ → Derivation 𝔖 Γ
| or : Derivation 𝔖 (φ :: ψ :: Γ) → φ ⋎ ψ ∈ Γ → Derivation 𝔖 Γ
| and : Derivation 𝔖 (φ :: Γ) → Derivation 𝔖 (ψ :: Γ) → φ ⋏ ψ ∈ Γ → Derivation 𝔖 Γ
| all : Derivation 𝔖 (φ.free :: Γ⁺) → ∀' φ ∈ Γ → Derivation 𝔖 Γ
| ex (t) : Derivation 𝔖 (φ/[t] :: Γ) → ∃' φ ∈ Γ → Derivation 𝔖 Γ
| cut : Derivation 𝔖 (φ :: Γ) → Derivation 𝔖 (∼φ :: Γ) → Derivation 𝔖 Γ
| axm : φ ∈ 𝔖 → φ ∈ Γ → Derivation 𝔖 Γ

instance : OneSided (SyntacticFormulas L) (SyntacticFormula L) := ⟨Derivation⟩

abbrev Derivation₀ (Γ : Sequent L) : Type _ := (∅ : SyntacticFormulas L) ⟹ Γ

abbrev Derivable₀ (Γ : Sequent L) : Prop := (∅ : SyntacticFormulas L) ⟹! Γ

prefix:45 "⊢ᵀ " => Derivation₀

namespace Derivation

variable {𝔖 U : SyntacticFormulas L} {Δ Δ₁ Δ₂ Γ : Sequent L} {φ ψ r : SyntacticFormula L}

open Rewriting LawfulSyntacticRewriting

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected def repr {Δ : Sequent L} : 𝔖 ⟹ Δ → String
  | axL (Γ := Γ) _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | verum (Γ := Γ) _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d _      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((φ ⋎ ψ) :: Γ) ++ "$}\n\n"
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq _ =>
      Derivation.repr dp ++
      Derivation.repr dq ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((φ ⋏ ψ) :: Γ) ++ "$}\n\n"
  | all (Γ := Γ) (φ := φ) d _       =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀' φ) :: Γ) ++ "$}\n\n"
  | ex (Γ := Γ) (φ := φ) _ d _      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃' φ) :: Γ) ++ "$}\n\n"
  | cut (Γ := Γ) dp dn =>
      Derivation.repr dp ++
      Derivation.repr dn ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | axm (φ := φ) _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(ROOT)}\n" ++
      "\\UnaryInfC{$" ++ reprStr φ ++ ", " ++ reprStr (∼φ) ++ "$}\n\n"

instance : Repr (𝔖 ⟹ Δ) where reprPrec d _ := Derivation.repr d

end Repr

def height {Δ : Sequent L} : 𝔖 ⟹ Δ → ℕ
  |     axL _ _ => 0
  |     verum _ => 0
  |      or d _ => d.height + 1
  | and dp dq _ => max (height dp) (height dq) + 1
  |     all d _ => d.height + 1
  |    ex _ d _ => d.height + 1
  |   cut dp dn => max (height dp) (height dn) + 1
  |     axm _ _ => 0

scoped notation "‖" d "‖" => height d

section height

@[simp] lemma height_axL {k} {r : L.Rel k} {v} (hr : rel r v ∈ Γ) (hn : nrel r v ∈ Γ) :
    ‖axL (𝔖 := 𝔖) hr hn‖ = 0 := rfl

@[simp] lemma height_verum (h : ⊤ ∈ Γ) : ‖verum (𝔖 := 𝔖) h‖ = 0 := rfl

@[simp] lemma height_and {φ ψ} (h : φ ⋏ ψ ∈ Γ) (dp : 𝔖 ⟹ φ :: Γ) (dq : 𝔖 ⟹ ψ :: Γ) :
    ‖and dp dq h‖ = (max (‖dp‖) ‖dq‖).succ := rfl

@[simp] lemma height_or {φ ψ} (h : φ ⋎ ψ ∈ Γ) (d : 𝔖 ⟹ φ :: ψ :: Γ) :
    ‖or d h‖ = ‖d‖ + 1 := rfl

@[simp] lemma height_all {φ} (h : ∀' φ ∈ Γ) (d : 𝔖 ⟹ φ.free :: Γ⁺) : ‖all d h‖ = ‖d‖ + 1 := rfl

@[simp] lemma height_ex {t} {φ}  (h : ∃' φ ∈ Γ) (d : 𝔖 ⟹ φ/[t] :: Γ) : ‖ex t d h‖ = ‖d‖ + 1 := rfl

@[simp] lemma height_cut {φ} (dp : 𝔖 ⟹ φ :: Δ) (dn : 𝔖 ⟹ ∼φ :: Δ) :
  ‖cut dp dn‖ = max ‖dp‖ ‖dn‖ + 1 := rfl

@[simp] lemma height_axm (h₁ : φ ∈ 𝔖) (h₂ : φ ∈ Γ) : ‖axm h₁ h₂‖ = 0 := rfl

end height

protected abbrev cast (d : 𝔖 ⟹ Δ) (e : Δ = Γ) : 𝔖 ⟹ Γ := e ▸ d

@[simp] lemma cast_eq (d : 𝔖 ⟹ Δ) (e : Δ = Δ) : Derivation.cast d e = d := rfl

@[simp] lemma height_cast (d : 𝔖 ⟹ Δ) (e : Δ = Γ) :
    ‖Derivation.cast d e‖ = ‖d‖ := by rcases e with rfl; simp [Derivation.cast]

@[simp] lemma height_cast' (d : 𝔖 ⟹ Δ) (e : Δ = Γ) :
    ‖e ▸ d‖ = ‖d‖ := by rcases e with rfl; simp

def wk {Γ Δ} (d : 𝔖 ⟹ Γ) (ss : Γ ⊆ Δ) : 𝔖 ⟹ Δ :=
  match d with
  |          axL hr hn => axL (ss hr) (ss hn)
  |            verum h => verum (ss h)
  |             or d h => or (d.wk <| by simp [ss]) (ss h)
  |        and dp dq h => and (dp.wk <| by simp [ss]) (dq.wk <| by simp [ss]) (ss h)
  |            all d h => all (d.wk <| by simp [ss]) (ss h)
  |           ex t d h => ex t (d.wk <| by simp [ss]) (ss h)
  | cut (φ := φ) dp dn => cut (dp.wk (Δ := φ :: Δ) <| by simp [ss]) (dn.wk <| by simp [ss])
  |          axm h₁ h₂ => axm h₁ (ss h₂)

alias weakening := wk

@[simp] lemma height_wk {Γ Δ} (d : 𝔖 ⟹ Γ) (ss : Γ ⊆ Δ) : ‖d.wk ss‖ = ‖d‖ :=
  match d with
  |     axL _ _ => rfl
  |     verum _ => rfl
  |      or d _ => by simp [wk, height_wk d]
  | and dp dq _ => by simp [wk, height_wk dp, height_wk dq]
  |     all d _ => by simp [wk, height_wk d]
  |    ex _ d _ => by simp [wk, height_wk d]
  |   cut dp dn => by simp [wk, height_wk dp, height_wk dn]
  |     axm _ _ => rfl

private lemma neg_ne_and {φ ψ : SyntacticFormula L} : ∼φ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

def em {Γ φ} (hpos : φ ∈ Γ) (hneg : ∼φ ∈ Γ) : 𝔖 ⟹ Γ :=
  match φ with
  |        ⊤ => verum hpos
  |        ⊥ => verum hneg
  |  rel R v => axL hpos hneg
  | nrel R v => axL hneg hpos
  |    φ ⋏ ψ =>
    have ihp : 𝔖 ⟹ φ :: ∼φ :: ∼ψ :: Γ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝔖 ⟹ ψ :: ∼φ :: ∼ψ :: Γ := em (φ := ψ) (by simp) (by simp)
    have : 𝔖 ⟹ ∼φ :: ∼ψ :: Γ := ihp.and ihq (by simp [hpos])
    this.or (by simpa using hneg)
  |    φ ⋎ ψ =>
    have hneg : ∼φ ⋏ ∼ψ ∈ Γ := by simpa using hneg
    have ihp : 𝔖 ⟹ ∼φ :: φ :: ψ :: Γ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝔖 ⟹ ∼ψ :: φ :: ψ :: Γ := em (φ := ψ) (by simp) (by simp)
    have : 𝔖 ⟹ φ :: ψ :: Γ := ihp.and ihq (by simp [hneg])
    this.or (by simp [hpos])
  |     ∀' φ =>
    have : 𝔖 ⟹ ∼φ.free :: φ.free :: Γ⁺ := em (φ := φ.free) (by simp) (by simp)
    have : 𝔖 ⟹ (∼φ.shift)/[&0] :: φ.free :: Γ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝔖 ⟹ φ.free :: Γ⁺ := this.ex &0 <| List.mem_cons_of_mem _ <| by simpa using mem_shifts_iff.mpr hneg
    this.all (by simp [hpos])
  |     ∃' φ =>
    have : 𝔖 ⟹ φ.free :: ∼φ.free :: Γ⁺ := em (φ := φ.free) (by simp) (by simp)
    have : 𝔖 ⟹ φ.shift/[&0] :: (∼φ).free :: Γ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝔖 ⟹ (∼φ).free :: Γ⁺ := this.ex &0 <| List.mem_cons_of_mem _ <| by simpa using mem_shifts_iff.mpr hpos
    this.all (by simpa using hneg)
termination_by φ.complexity

@[simp] lemma height_em {Γ φ} (hpos : φ ∈ Γ) (hneg : ∼φ ∈ Γ) :
    ‖(em hpos hneg : 𝔖 ⟹ Γ)‖ = 2 * φ.complexity :=
  match φ with
  |        ⊤ => by simp [em]
  |        ⊥ => by simp [em]
  |  rel R v => by simp [em]
  | nrel R v => by simp [em]
  |    φ ⋏ ψ => by simp [em, height_em (φ := φ), height_em (φ := ψ)]; grind
  |    φ ⋎ ψ => by simp [em, height_em (φ := φ), height_em (φ := ψ)]; grind
  |     ∀' φ => by simp [em, height_em (φ := φ.free)]; grind
  |     ∃' φ => by simp [em, height_em (φ := φ.free)]; grind
termination_by φ.complexity

def rewrite (f : ℕ → SyntacticTerm L) : 𝔖 ⟹ Γ → 𝔖 ⟹ Γ.map (Rew.rewrite f ▹ ·) := by {  }

/--/
def all' {Γ : Sequent L} {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) (d : 𝔖 ⟹ φ.free :: Γ) :
    𝔖 ⟹ (∀' φ) :: Γ :=
  let b : 𝔖 ⟹ φ.free :: (∀' φ) :: Γ := wk d (by simp)
  by { apply all (φ := φ) }

def ex' {Γ : Sequent L} {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) (d : 𝔖 ⟹ φ/[t] :: Γ) :
    𝔖 ⟹ (∃' φ) :: Γ :=
  let b : 𝔖 ⟹ φ/[t] :: (∃' φ) :: Γ := wk d (by simp)
  b.ex t (by simp)

instance : Tait (SyntacticFormula L) (SyntacticFormulas L) where
  verum _ Δ := verum (by simp)
  and {Γ φ ψ} Δ dφ dψ :=
    let bφ : Γ ⟹ φ :: φ ⋏ ψ :: Δ := wk dφ (by simp)
    let bψ : Γ ⟹ ψ :: φ ⋏ ψ :: Δ := wk dψ (by simp)
    bφ.and bψ (by simp)
  or {Γ φ ψ} Δ d :=
    let b : Γ ⟹ φ :: ψ :: (φ ⋎ ψ) :: Δ := wk d (by simp; grind)
    b.or (by simp)
  wk d ss := d.wk ss
  em hp hn := em hp hn

instance : Tait.Cut (SyntacticFormula L) (SyntacticFormulas L) where
  cut {_ _ _ dp dn} := cut dp dn

protected def id {φ} (hφ : φ ∈ 𝔖) : 𝔖 ⟹ ∼φ :: Δ → 𝔖 ⟹ Δ := fun b ↦ cut (axm hφ (by simp)) b

def provableOfDerivable {φ} (b : 𝔖 ⟹. φ) : 𝔖 ⊢! φ := b

def specialize {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    𝔖 ⟹ (∀' φ) :: Γ → 𝔖 ⟹ φ/[t] :: Γ := fun d ↦
  have dn : 𝔖 ⟹ ∼(∀' φ) :: φ/[t] :: Γ := by
    simp only [neg_all, Nat.reduceAdd]
    apply Derivation.ex t (φ := ∼φ) ?_ (by simp)
    apply em (φ := φ/[t]) (by simp) (by simp)
  have dp : 𝔖 ⟹ (∀' φ) :: φ/[t] :: Γ :=
    Derivation.wk d (List.cons_subset_cons _ <| by simp)
  Derivation.cut dp dn

def specializes : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → (v : Fin k → SyntacticTerm L) →
    𝔖 ⟹ (∀* φ) :: Γ → 𝔖 ⟹ (φ ⇜ v) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝔖 ⟹ (∀' (Rew.subst (v ·.succ)).q ▹ φ) :: Γ := by simpa using specializes (φ := ∀' φ) (v ·.succ) b
    Derivation.cast (specialize (v 0) this) (by
      simp only [Nat.reduceAdd, ← TransitiveRewriting.comp_app, List.cons.injEq, and_true]; congr 2
      ext x <;> simp [Rew.comp_app]
      cases x using Fin.cases <;> simp)

def instances : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → {v : Fin k → SyntacticTerm L} →
    𝔖 ⟹ (φ ⇜ v) :: Γ → 𝔖 ⟹ (∃* φ) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝔖 ⟹ (∃' (Rew.subst (v ·.succ)).q ▹ φ) :: Γ :=
      ex (v 0) <| Derivation.cast b <| by
        unfold Rewriting.subst; rw [←TransitiveRewriting.comp_app]; congr 3
        ext x <;> simp [Rew.comp_app]
        cases x using Fin.cases <;> simp
    instances (k := k) (v := (v ·.succ)) (Derivation.cast this (by simp))

def allClosureFixitr {φ : SyntacticFormula L} (dp : 𝔖 ⊢! φ) : (m : ℕ) → 𝔖 ⊢! ∀* Rew.fixitr 0 m ▹ φ
  | 0     => by simpa
  | m + 1 => by
    simp only [allClosure_fixitr, Nat.reduceAdd]
    apply all; simpa using allClosureFixitr dp m

def toClose (b : 𝔖 ⊢! φ) : 𝔖 ⊢! φ.univCl' := allClosureFixitr b φ.fvSup

def toClose! (b : 𝔖 ⊢ φ) : 𝔖 ⊢ φ.univCl' := ⟨toClose b.get⟩

def rewrite₁ (b : 𝔖 ⊢! φ) (f : ℕ → SyntacticTerm L) : 𝔖 ⊢! (Rew.rewrite f) ▹ φ :=
  Derivation.cast (specializes (fun x ↦ f x) (allClosureFixitr b φ.fvSup)) (by simp)

def rewrite {Δ} : 𝔖 ⟹ Δ → ∀ (f : ℕ → SyntacticTerm L), 𝔖 ⟹ Δ.map fun φ ↦ Rew.rewrite f ▹ φ
  | axL Δ r v,            f =>
    Derivation.cast (axL (Δ.map fun φ ↦ Rew.rewrite f ▹ φ) r (fun i ↦ Rew.rewrite f (v i))) (by simp [rew_rel, rew_nrel])
  | verum Δ,              f => Derivation.cast (verum (Δ.map fun φ ↦ Rew.rewrite f ▹ φ)) (by simp)
  | @or _ _ Δ φ ψ d,      f =>
    have : 𝔖 ⟹ Rew.rewrite f ▹ φ ⋎ Rew.rewrite f ▹ ψ :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq, f =>
    have : 𝔖 ⟹ Rew.rewrite f ▹ φ ⋏ Rew.rewrite f ▹ ψ :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d,       f =>
    have : 𝔖 ⟹ ((free φ) :: Δ⁺).map fun φ ↦ Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) ▹ φ :=
      rewrite d (&0 :>ₙ fun x => Rew.shift (f x))
    have : 𝔖 ⟹ (∀' Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      all (Derivation.cast this (by simp [free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @ex _ _ Δ φ t d,      f =>
    have : 𝔖 ⟹ (φ/[t] :: Δ).map fun φ ↦ Rew.rewrite f ▹ φ := rewrite d f
    have : 𝔖 ⟹ (∃' Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      ex (Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @wk _ _ Δ Γ d ss,     f => (rewrite d f).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn,    f =>
    have dΔ : 𝔖 ⟹ (Rew.rewrite f ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite d f) (by simp)
    have dΓ : 𝔖 ⟹ ∼(Rew.rewrite f ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΔ dΓ) (by simp)
  | axm h,               f => rewrite₁ (axm h) f

/--/
protected def map {Δ : Sequent L} (d : 𝔖 ⟹ Δ) (f : ℕ → ℕ) :
    𝔖 ⟹ Δ.map fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 f ▹ φ := rewrite d (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : 𝔖 ⟹ Δ) : 𝔖 ⟹ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by simp only [Rewriting.shifts, List.map_inj_left]; intro _ _; rfl)

def trans (F : U ⊢!* 𝔖) {Γ : Sequent L} : 𝔖 ⟹ Γ → U ⟹ Γ
  | axL Γ R v => axL Γ R v
  | verum Γ   => verum Γ
  | and d₁ d₂ => and (trans F d₁) (trans F d₂)
  | or d      => or (trans F d)
  | all d     => all (trans F d)
  | ex t d    => ex t (trans F d)
  | wk d ss   => wk (trans F d) ss
  | cut d₁ d₂ => cut (trans F d₁) (trans F d₂)
  | axm h    => F h

instance : Tait.Axiomatized (SyntacticFormula L) (SyntacticFormulas L) where
  axm {_ _ h} := axm h
  trans {_ _ _ F d} := trans (fun h ↦ F _ h) d

variable [L.DecidableEq]

private def not_close' (φ) : 𝔖 ⟹ [∼(φ.univCl'), φ] :=
  have : 𝔖 ⟹ [∃* ∼(@Rew.fixitr L 0 (fvSup φ) ▹ φ), φ] := instances (v := fun x ↦ &x) (em (φ := φ) (by simp) (by simp))
  Derivation.cast this (by simp [univCl'])

def invClose (b : 𝔖 ⊢! φ.univCl') : 𝔖 ⊢! φ := cut (wk b (by simp)) (not_close' φ)

def invClose! (b : 𝔖 ⊢ φ.univCl') : 𝔖 ⊢ φ := ⟨invClose b.get⟩

def compact {Γ : Sequent L} : 𝔖 ⟹ Γ → (s : { s : Finset (SyntacticFormula L) // ↑s ⊆ 𝔖}) × (s : SyntacticFormulas L) ⟹ Γ
  | axL Γ R v   => ⟨⟨∅, by simp⟩, axL Γ R v⟩
  | verum Γ   => ⟨⟨∅, by simp⟩, verum Γ⟩
  | and d₁ d₂ =>
    let ⟨s₁, d₁⟩ := compact d₁
    let ⟨s₂, d₂⟩ := compact d₂
    ⟨⟨(s₁ ∪ s₂ : Finset (SyntacticFormula L)), by simp [s₁.prop, s₂.prop]⟩,
      and (Tait.ofAxiomSubset (by simp) d₁) (Tait.ofAxiomSubset (by simp) d₂)⟩
  | or d      =>
    let ⟨s, d⟩ := compact d
    ⟨s, or d⟩
  | wk d ss   =>
    let ⟨s, d⟩ := compact d
    ⟨s, wk d ss⟩
  | cut d₁ d₂ =>
    let ⟨s₁, d₁⟩ := compact d₁
    let ⟨s₂, d₂⟩ := compact d₂
    ⟨⟨(s₁ ∪ s₂ : Finset (SyntacticFormula L)), by simp [s₁.prop, s₂.prop]⟩,
      cut (Tait.ofAxiomSubset (by simp) d₁) (Tait.ofAxiomSubset (by simp) d₂)⟩
  | axm (φ := φ) h =>
    ⟨⟨{φ}, by simp [h]⟩, axm (by simp)⟩
  | all d          =>
    let ⟨s, d⟩ := compact d
    ⟨s, all d⟩
  | ex t d =>
    let ⟨s, d⟩ := compact d
    ⟨s, ex t d⟩

instance : Entailment.Compact (SyntacticFormulas L) where
  Γ b := (compact b).1
  ΓPrf b := (compact b).2
  Γ_subset b := by simpa using (compact b).1.prop
  Γ_finite b := by simp

private def deductionAux {Γ : Sequent L} : 𝔖 ⟹ Γ → 𝔖 \ {φ} ⟹ ∼(φ.univCl') :: Γ
  | axL Γ R v       => Tait.wkTail <| axL Γ R v
  | verum Γ         => Tait.wkTail <| verum Γ
  | and d₁ d₂       => Tait.rotate₁ <| and (Tait.rotate₁ (deductionAux d₁)) (Tait.rotate₁ (deductionAux d₂))
  | or d            => Tait.rotate₁ <| or (Tait.rotate₂ (deductionAux d))
  | all d           => Tait.rotate₁ <| all (Derivation.cast (Tait.rotate₁ (deductionAux d)) (by simp))
  | ex t d          => Tait.rotate₁ <| ex t <| Tait.rotate₁ (deductionAux d)
  | wk d ss         => wk (deductionAux d) (by simp [List.subset_cons_of_subset _ ss])
  | cut d₁ d₂       => (Tait.rotate₁ <| deductionAux d₁).cut (Tait.rotate₁ <| deductionAux d₂)
  | axm (φ := ψ) h => if hq : φ = ψ then Derivation.cast (not_close' φ) (by simp [hq]) else
    have : 𝔖 \ {φ} ⟹. ψ := axm (by simp [h, Ne.symm hq])
    wk this (by simp)

def deduction (d : insert φ 𝔖 ⟹ Γ) : 𝔖 ⟹ ∼(φ.univCl') :: Γ := Tait.ofAxiomSubset (by intro x; simp; tauto) (deductionAux d (φ := φ))

def provable_iff_inconsistent : 𝔖 ⊢ φ ↔ Entailment.Inconsistent (insert (∼φ.univCl') 𝔖) := by
  constructor
  · rintro b
    exact Entailment.inconsistent_of_provable_of_unprovable
      (Entailment.wk! (by simp) (toClose! b)) (Entailment.by_axm _ (by simp))
  · intro h
    rcases Tait.inconsistent_iff_provable.mp h with ⟨d⟩
    have : 𝔖 ⊢! φ.univCl' :=  Derivation.cast (deduction d) (by rw [univCl'_eq_self_of (∼(φ.univCl')) (by simp)]; simp)
    exact ⟨invClose this⟩

def unprovable_iff_consistent : 𝔖 ⊬ φ ↔ Entailment.Consistent (insert (∼φ.univCl') 𝔖) := by
  simp [←Entailment.not_inconsistent_iff_consistent, ←provable_iff_inconsistent]

section Hom

variable {L₁ : Language} {L₂ : Language} {𝔖₁ : SyntacticFormulas L₁} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Δ} : 𝔖₁ ⟹ Δ → 𝔖₁.lMap Φ ⟹ Δ.map (.lMap Φ)
  | axL Δ r v            =>
    .cast (axL (Δ.map (.lMap Φ)) (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Semiformula.lMap_rel, Semiformula.lMap_nrel])
  | verum Δ              => by simpa using verum _
  | @or _ _ Δ φ ψ d      => by
    have : 𝔖₁.lMap Φ ⟹ (.lMap Φ φ ⋎ .lMap Φ ψ :: Δ.map (.lMap Φ) : Sequent L₂) :=
      or (by simpa using lMap Φ d)
    exact Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq =>
    have : 𝔖₁.lMap Φ ⟹ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d       =>
    have : 𝔖₁.lMap Φ ⟹ ((∀' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [←Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | @ex _ _ Δ φ t d      =>
    have : 𝔖₁.lMap Φ ⟹ ((∃' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      ex (Semiterm.lMap Φ t)
        (Derivation.cast (lMap Φ d) (by simp [Semiformula.lMap_subst]))
    Derivation.cast this (by simp)
  | @wk _ _ Δ Γ d ss     => (lMap Φ d).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn    =>
    have : 𝔖₁.lMap Φ ⟹ (Δ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp)
  | axm h               => axm (Set.mem_image_of_mem _ h)

lemma inconsistent'_lMap (Φ : L₁ →ᵥ L₂) : Entailment.Inconsistent 𝔖₁ → Entailment.Inconsistent (𝔖₁.lMap Φ) := by
  simp only [Entailment.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨by simpa using lMap Φ b⟩

end Hom

omit [L.DecidableEq]

private lemma map_subst_eq_free (φ : SyntacticSemiformula L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) ▹ (φ/[&m] : SyntacticFormula L) = free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Δ⁺ := by
  apply List.map_congr_left
  intro φ hp; exact rew_eq_of_funEqOn₀
    (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])

def genelalizeByNewver {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : 𝔖 ⟹ φ/[&m] :: Δ) : 𝔖 ⟹ (∀' φ) :: Δ := by
  have : 𝔖 ⟹ (free φ) :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝔖 ⟹ v.map (φ/[·]) ++ Γ) : 𝔖 ⟹ (∃' φ) :: Γ := by
  induction' v with t v ih generalizing Γ
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃' φ) :: Γ) ((ex t h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝔖 ⟹ (∃' φ) :: v.map (φ/[·]) ++ Γ) : 𝔖 ⟹ (∃' φ) :: Γ :=
  (exOfInstances (Γ := (∃' φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

end Derivation

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : SyntacticFormula L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ (newVar Γ) :=
  not_fvar?_of_lt_fvSup φ (by simpa [newVar] using List.le_max_of_le (List.mem_map_of_mem h) (by simp))

namespace Derivation

open Semiformula
variable {P : SyntacticFormula L → Prop} {𝔖 : SyntacticFormulas L} {Δ : Sequent L}

def allNvar {φ} (h : ∀' φ ∈ Δ) : 𝔖 ⟹ φ/[&(newVar Δ)] :: Δ → 𝔖 ⟹ Δ := fun b ↦
  let b : 𝔖 ⟹ (∀' φ) :: Δ :=
    genelalizeByNewver (by simpa [FVar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Tait.wk b (by simp [h])

def id_univClosure {φ} (hp : φ ∈ 𝔖) : 𝔖 ⟹ ∼φ.univCl' :: Δ → 𝔖 ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (toClose (axm hp)) (by simp)) b

end Derivation

namespace SyntacticFormulas

instance {𝔖 U : SyntacticFormulas L} : 𝔖 ⪯ 𝔖 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

instance {𝔖 U : SyntacticFormulas L} : U ⪯ 𝔖 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

def deduction [L.DecidableEq] {𝔖 : SyntacticFormulas L} {φ ψ} (b : insert φ 𝔖 ⊢! ψ) : 𝔖 ⊢! φ.univCl' ➝ ψ :=
  have : 𝔖 ⟹ [∼φ.univCl', ψ] := Derivation.deduction b
  (Tait.or this).cast (by simp; rfl)

theorem deduction! [L.DecidableEq] {𝔖 : SyntacticFormulas L} {φ ψ} (b : insert φ 𝔖 ⊢ ψ) : 𝔖 ⊢ φ.univCl' ➝ ψ :=
  ⟨deduction b.get⟩

lemma close!_iff [L.DecidableEq] {𝔖 : SyntacticFormulas L} {φ} : 𝔖 ⊢ φ.univCl' ↔ 𝔖 ⊢ φ := by
  constructor
  · intro h
    apply deduction! (Entailment.Axiomatized.adjoin! _ _) ⨀ h
  · intro h
    exact Derivation.toClose! h

end SyntacticFormulas

/-!
  ### Theory (a set of sentences)
-/

instance : Entailment (Theory L) (Sentence L) := ⟨fun T σ ↦ (T : SyntacticFormulas L) ⊢! ↑σ⟩

instance (T : Theory L) : Entailment.Cl T := Entailment.Cl.ofEquiv (T : SyntacticFormulas L) T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

def toSyntacticProof {T : Theory L} {σ} : T ⊢! σ → (T : SyntacticFormulas L) ⊢! ↑σ := fun b ↦ b

def ofSyntacticProof {T : Theory L} {σ} : (T : SyntacticFormulas L) ⊢! ↑σ → T ⊢! σ := fun b ↦ b

lemma provable_def {T : Theory L} {σ} : T ⊢ σ ↔ (T : SyntacticFormulas L) ⊢ ↑σ := by rfl

def Proof.cast {T : Theory L} {σ} : T ⊢ σ ↔ (T : SyntacticFormulas L) ⊢ ↑σ := by rfl

namespace Theory

open Entailment

instance : Axiomatized (Theory L) where
  prfAxm {T} σ h := ofSyntacticProof <| Axiomatized.prfAxm (by simpa using h)
  weakening {σ T B} h b := ofSyntacticProof <| Axiomatized.weakening (by simpa using h) b

def deduction [L.DecidableEq] {T : Theory L} {σ τ} (b : insert σ T ⊢! τ) : T ⊢! σ ➝ τ :=
  have : insert ↑σ T.toSyntacticFormulas ⊢! ↑τ := by simpa using toSyntacticProof b
  (SyntacticFormulas.deduction this).cast (by simp)

instance [L.DecidableEq] : Entailment.Deduction (Theory L) where
  ofInsert := Theory.deduction
  inv {σ τ T} b :=
    have : adjoin σ T ⊢! σ ➝ τ := Axiomatized.weakening (by simp) b
    this ⨀ (Axiomatized.adjoin _ _)

def compact! [L.DecidableEq] {T : Theory L} {φ : Sentence L} :
    T ⊢! φ → (s : { s : Finset (Sentence L) // ↑s ⊆ T}) × (s : Theory L) ⊢! φ :=
  fun b ↦
    let ⟨s, b⟩ := Derivation.compact b
    ⟨⟨s.val.image Semiformula.toEmpty', fun φ ↦ by
      suffices ∀ φ' ∈ s.val, φ'.toEmpty' = φ → φ ∈ T by simpa
      intro φ hφ e
      have : ∃ σ ∈ T, ↑σ = φ := by
        simpa [Theory.toSyntacticFormulas] using s.prop hφ
      rcases this with ⟨σ, hσ, rfl⟩
      have : σ = φ := by simpa [Semiformula.toEmpty'] using e
      simp_all⟩, ofSyntacticProof <|
        Axiomatized.weakening (by
          simp only [Finset.coe_image]
          intro φ hφ
          have : ∃ σ ∈ T, ↑σ = φ := by
            simpa [Theory.toSyntacticFormulas] using s.prop hφ
          rcases this with ⟨σ, _, rfl⟩
          simpa using ⟨σ, hφ, by simp⟩) b⟩

instance [L.DecidableEq] : Entailment.Compact (Theory L) where
  Γ b := (compact! b).1
  ΓPrf b := (compact! b).2
  Γ_subset b := by simpa using (compact! b).1.prop
  Γ_finite b := by simp

theorem compact [L.DecidableEq] {T : Theory L} {φ : Sentence L} (b : T ⊢ φ) :
    ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T}), (s : Theory L) ⊢ φ :=
  let ⟨s, b⟩ := compact! b.get
  ⟨s, ⟨b⟩⟩

instance : Entailment.StrongCut (Theory L) (Theory L) where
  cut {T U φ} b d :=
    Tait.Axiomatized.trans (𝓛 := (↑T : SyntacticFormulas L)) (𝓚 := (↑U : SyntacticFormulas L))
      (fun ψ hψ ↦
        let b := @b ψ.toEmpty' (by
          have : ∃ ψ₀ ∈ U, ↑ψ₀ = ψ := by simpa [toSyntacticFormulas] using hψ
          rcases this with ⟨ψ₀, hψ₀U, rfl⟩
          simpa using hψ)
        (toSyntacticProof b).cast <| by
          have : ∃ ψ₀ ∈ U, ↑ψ₀ = ψ := by simpa [toSyntacticFormulas] using hψ
          rcases this with⟨_, _, rfl⟩
          simp)
      (toSyntacticProof d)

lemma compact' [L.DecidableEq] {T : Theory L} {φ : Sentence L}
    (b : T ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T}), (∅ : Theory L) ⊢ s.val.conj ➝ φ := by
  let ⟨s, b⟩ := compact b
  let bc : ({s.val.conj} : Theory L) ⊢ s.val.conj := Axiomatized.provable_axm _ (by simp)
  have : {s.val.conj} ⊢ φ := StrongCut.cut! (fun {ψ} hψ ↦ Entailment.left_Fconj!_intro (by simpa) ⨀ bc) b
  have : (insert s.val.conj ∅ : Theory L) ⊢ φ := by simpa using this
  exact ⟨s, ⟨deduction this.get⟩⟩

instance (T : Theory L) : Entailment.Cl T := Entailment.Cl.ofEquiv (T : SyntacticFormulas L) T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

instance : DeductiveExplosion (Theory L) where
  dexp b _ := ofSyntacticProof <| DeductiveExplosion.dexp (toSyntacticProof b) _

lemma inconsistent_iff {T : Theory L} :
    Inconsistent T ↔ Inconsistent (T : SyntacticFormulas L) := calc
  Inconsistent T ↔ T ⊢ ⊥                                 := inconsistent_iff_provable_bot
  _              ↔ (T : SyntacticFormulas L) ⊢ ⊥         := by simp [provable_def]
  _              ↔ Inconsistent (T : SyntacticFormulas L) := inconsistent_iff_provable_bot.symm

lemma inconsistent_lMap {T : Theory L₁} (Φ : L₁ →ᵥ L₂) :
    Entailment.Inconsistent T → Entailment.Inconsistent (T.lMap Φ) := by
  intro h
  have : SyntacticFormulas.lMap Φ ↑T ⊢ ⊥ := ⟨Derivation.lMap Φ (provable_def.mp <| inconsistent_iff_provable_bot.mp h).get⟩
  refine inconsistent_iff_provable_bot.mpr <| provable_def.mpr ?_
  suffices ↑(lMap Φ T) ⊢ ⊥ by simpa
  apply Axiomatized.weakening! ?_ this
  simp only [SyntacticFormulas.lMap, toSyntacticFormulas, Set.image_subset_iff]
  intro φ hφ
  simpa using ⟨(Semiformula.lMap Φ) φ, Set.mem_image_of_mem _ hφ, Eq.symm (lMap_emb φ)⟩

instance {T U : Theory L} : T ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

instance {T U : Theory L} : U ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

end Theory

namespace SyntacticFormulas

open Entailment

variable [L.DecidableEq] {𝔖 : SyntacticFormulas L}

def coe_provable_iff_provable_coe {σ : Sentence L} :
    (𝔖 : Theory L) ⊢ σ ↔ 𝔖 ⊢ ↑σ := by
  constructor
  · intro b
    have : 𝔖.toTheory.toSyntacticFormulas ⊢ ↑σ := b
    apply Entailment.StrongCut.cut! ?_ this
    intro τ hτ
    have : ∃ τ' ∈ 𝔖, τ'.univCl' = τ := by simpa [SyntacticFormulas.toTheory, Theory.toSyntacticFormulas] using hτ
    rcases this with ⟨τ, h, rfl⟩
    exact Derivation.toClose! <| by_axm _ <| by simpa
  · intro b
    apply provable_def.mpr
    apply Entailment.StrongCut.cut! ?_ b
    intro φ hφ
    have : 𝔖.toTheory.toSyntacticFormulas ⊢ φ.univCl' :=
      by_axm _ <| by simpa [SyntacticFormulas.toTheory, Theory.toSyntacticFormulas] using ⟨φ, by simpa, rfl⟩
    exact SyntacticFormulas.close!_iff.mp this

def coe_unprovable_iff_unprovable_coe {σ} :
    (𝔖 : Theory L) ⊬ σ ↔ 𝔖 ⊬ ↑σ := coe_provable_iff_provable_coe.not

def provable_univCl_iff {φ : SyntacticFormula L} :
    (𝔖 : Theory L) ⊢ φ.univCl ↔ 𝔖 ⊢ φ := Iff.trans coe_provable_iff_provable_coe (by simp [SyntacticFormulas.close!_iff])

def unprovable_univCl_iff {φ : SyntacticFormula L} :
    (𝔖 : Theory L) ⊬ φ.univCl ↔ 𝔖 ⊬ φ := provable_univCl_iff.not

instance (𝔖 𝓣 : SyntacticFormulas L) [𝔖 ⪯ 𝓣] : 𝔖.toTheory ⪯ 𝓣.toTheory :=
  ⟨fun _ b ↦ coe_provable_iff_provable_coe.mpr <| (inferInstanceAs (𝔖 ⪯ 𝓣)).pbl (coe_provable_iff_provable_coe.mp b)⟩

@[simp] lemma coe_consistent_iff :
    Consistent (𝔖 : Theory L) ↔ Consistent 𝔖 := calc
  Consistent (𝔖 : Theory L) ↔ (𝔖 : Theory L) ⊬ ⊥ := consistent_iff_unprovable_bot
  _                        ↔ 𝔖 ⊬ ⊥             := by simp [coe_unprovable_iff_unprovable_coe]
  _                        ↔ Consistent 𝔖      := consistent_iff_unprovable_bot.symm

instance [Consistent 𝔖] : Consistent (𝔖 : Theory L) := by simp_all

end SyntacticFormulas

end FirstOrder

end LO
