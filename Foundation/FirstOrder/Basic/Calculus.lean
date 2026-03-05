module
/- public import Foundation.Logic.Calculus -/
public import Foundation.FirstOrder.Basic.Syntax.Theory
public import Mathlib.Data.List.MinMax

/-! # One-sided sequent calculus for first-order classical logic -/

@[expose] public section

namespace LO

namespace FirstOrder

abbrev Sequent (L : Language) := List (SyntacticFormula L)

open Semiformula

variable {L : Language} {𝓢 : Schema L}

inductive Derivation (𝓢 : Schema L) : Sequent L → Type _
| axm : φ ∈ 𝓢 → Derivation 𝓢 [φ]
| axL (r : L.Rel k) (v) : Derivation 𝓢 [rel r v, nrel r v]
| verum : Derivation 𝓢 [⊤]
| or : Derivation 𝓢 (φ :: ψ :: Γ) → Derivation 𝓢 (φ ⋎ ψ :: Γ)
| and : Derivation 𝓢 (φ :: Γ) → Derivation 𝓢 (ψ :: Γ) → Derivation 𝓢 (φ ⋏ ψ :: Γ)
| all : Derivation 𝓢 (φ.free :: Γ⁺) → Derivation 𝓢 ((∀⁰ φ) :: Γ)
| exs (t) : Derivation 𝓢 (φ/[t] :: Γ) → Derivation 𝓢 ((∃⁰ φ) :: Γ)
| wk : Derivation 𝓢 Δ → Δ ⊆ Γ → Derivation 𝓢 Γ
| cut : Derivation 𝓢 (φ :: Γ) → Derivation 𝓢 (∼φ :: Γ) → Derivation 𝓢 Γ

/--/
instance : OneSided (Schema L) (SyntacticFormula L) := ⟨Derivation⟩

abbrev Schema.pureLK : Schema L := ∅

notation "𝐋𝐊₀" => Schema.pureLK

abbrev Derivation₀ (Γ : Sequent L) : Type _ := 𝐋𝐊₀ ⟹ Γ

abbrev Derivable₀ (Γ : Sequent L) : Prop := 𝐋𝐊₀ ⟹! Γ

prefix:45 "⊢ᵀ " => Derivation₀

abbrev Theory.pureLK : Theory L := ∅

notation "𝐋𝐊" => Theory.pureLK

namespace Derivation

variable {𝓢 U : Schema L} {Δ Δ₁ Δ₂ Γ : Sequent L} {φ ψ r : SyntacticFormula L}

open Rewriting LawfulSyntacticRewriting

def height {Δ : Sequent L} : 𝓢 ⟹ Δ → ℕ
  |   axL _ _ => 0
  |     verum => 0
  |      or d => d.height.succ
  | and dp dq => (max (height dp) (height dq)).succ
  |     all d => d.height.succ
  |   exs _ d => d.height.succ
  |    wk d _ => d.height.succ
  | cut dp dn => (max (height dp) (height dn)).succ
  |     axm _ => 0

section height

@[simp] lemma height_axL {k} {r : L.Rel k} {v} :
  height (axL (𝓢 := 𝓢) r v) = 0 := rfl

@[simp] lemma height_verum : height (verum : Derivation 𝓢 [⊤]) = 0 := rfl

@[simp] lemma height_and {φ ψ} (dp : 𝓢 ⟹ φ :: Δ) (dq : 𝓢 ⟹ ψ :: Δ) :
    height (and dp dq) = (max (height dp) (height dq)).succ := rfl

@[simp] lemma height_or {φ ψ} (d : 𝓢 ⟹ φ :: ψ :: Δ) : height (or d) = d.height.succ := rfl

@[simp] lemma height_all {φ} (d : 𝓢 ⟹ Rewriting.free φ :: Δ⁺) : height (all d) = d.height.succ := rfl

@[simp] lemma height_exs {t} {φ} (d : 𝓢 ⟹ φ/[t] :: Δ) : height (exs t d) = d.height.succ := rfl

@[simp] lemma height_wk (d : 𝓢 ⟹ Δ) (h : Δ ⊆ Γ) : height (wk d h) = d.height.succ := rfl

@[simp] lemma height_cut {φ} (dp : 𝓢 ⟹ φ :: Δ) (dn : 𝓢 ⟹ (∼φ) :: Δ) :
  height (cut dp dn) = (max (height dp) (height dn)).succ := rfl

end height

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected unsafe def repr {Δ : Sequent L} : 𝓢 ⟹ Δ → String
  | axL r v =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr [Semiformula.rel r v, Semiformula.nrel r v] ++ "$}\n\n"
  | verum =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | or (Γ := Δ) (φ := φ) (ψ := ψ) d =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((φ ⋎ ψ) :: Δ) ++ "$}\n\n"
  | and (Γ := Δ) (φ := φ) (ψ := ψ) dp dq =>
      Derivation.repr dp ++
      Derivation.repr dq ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((φ ⋏ ψ) :: Δ) ++ "$}\n\n"
  | all (Γ := Δ) (φ := φ) d =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀⁰ φ) :: Δ) ++ "$}\n\n"
  | exs (Γ := Δ) (φ := φ) _ d =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃⁰ φ) :: Δ) ++ "$}\n\n"
  | wk (𝓢 := 𝓢) (Γ := Γ) d _ =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize(wk)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | @cut _ _ Δ _ dp dn =>
      Derivation.repr dp ++
      Derivation.repr dn ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | axm (φ := φ) _ =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(ROOT)}\n" ++
      "\\UnaryInfC{$" ++ reprStr φ ++ ", " ++ reprStr (∼φ) ++ "$}\n\n"

unsafe instance : Repr (𝓢 ⟹ Δ) where reprPrec d _ := Derivation.repr d

end Repr

protected abbrev cast (d : 𝓢 ⟹ Δ) (e : Δ = Γ) : 𝓢 ⟹ Γ := e ▸ d

@[simp] lemma cast_eq (d : 𝓢 ⟹ Δ) (e : Δ = Δ) : Derivation.cast d e = d := rfl

@[simp] lemma height_cast (d : 𝓢 ⟹ Δ) (e : Δ = Γ) :
    height (Derivation.cast d e) = height d := by rcases e with rfl; simp [Derivation.cast]

@[simp] lemma height_cast' (d : 𝓢 ⟹ Δ) (e : Δ = Γ) :
    height (e ▸ d) = height d := by rcases e with rfl; simp

alias weakening := wk

def verum' (h : ⊤ ∈ Δ) : 𝓢 ⟹ Δ := verum.wk (by simp [h])

def axL' {k} (r : L.Rel k) (v)
    (h : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) : 𝓢 ⟹ Δ := (axL r v).wk (by simp [h, hn])

def all' {φ} (h : ∀⁰ φ ∈ Δ) (d : 𝓢 ⟹ Rewriting.free φ :: Δ⁺) : 𝓢 ⟹ Δ := d.all.wk (by simp [h])

def exs' {φ} (h : ∃⁰ φ ∈ Δ) (t) (d : 𝓢 ⟹ φ/[t] :: Δ) : 𝓢 ⟹ Δ := (d.exs t).wk (by simp [h])

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {φ ψ : SyntacticFormula L} : ¬∼φ = φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

def em {Δ : Sequent L} : {φ : SyntacticFormula L} → (hpos : φ ∈ Δ) → (hneg : ∼φ ∈ Δ) → 𝓢 ⟹ Δ
  | ⊤, hpos, hneg => verum' hpos
  | ⊥, hpos, hneg => verum' hneg
  | .rel R v, hpos, hneg => axL' R v hpos hneg
  | .nrel R v, hpos, hneg => axL' R v hneg hpos
  | φ ⋏ ψ, hpos, hneg =>
    have ihp : 𝓢 ⟹ φ :: ∼φ :: ∼ψ :: Δ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝓢 ⟹ ψ :: ∼φ :: ∼ψ :: Δ := em (φ := ψ) (by simp) (by simp)
    have : 𝓢 ⟹ ∼φ :: ∼ψ :: Δ := (ihp.and ihq).wk (by simp [hpos])
    this.or.wk (by simpa using hneg)
  | φ ⋎ ψ, hpos, hneg =>
    have ihp : 𝓢 ⟹ ∼φ :: φ :: ψ :: Δ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝓢 ⟹ ∼ψ :: φ :: ψ :: Δ := em (φ := ψ) (by simp) (by simp)
    have : 𝓢 ⟹ φ :: ψ :: Δ := (ihp.and ihq).wk (by simp [by simpa using hneg])
    this.or.wk (by simp [hpos])
  | ∀⁰ φ, hpos, hneg =>
    have : 𝓢 ⟹ ∼φ.free :: φ.free :: Δ⁺ := em (φ := φ.free) (by simp) (by simp)
    have : 𝓢 ⟹ (∼φ.shift)/[&0] :: φ.free :: Δ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝓢 ⟹ φ.free :: Δ⁺ := (exs &0 this).wk
      (List.cons_subset_of_subset_of_mem
        (List.mem_cons_of_mem φ.free <| by simpa using mem_shifts_iff.mpr hneg) (by rfl))
    this.all.wk (by simp [hpos])
  | ∃⁰ φ, hpos, hneg =>
    have : 𝓢 ⟹ φ.free :: ∼φ.free :: Δ⁺ := em (φ := φ.free) (by simp) (by simp)
    have : 𝓢 ⟹ (φ.shift)/[&0] :: ∼φ.free :: Δ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝓢 ⟹ (∼φ).free :: Δ⁺ := (exs &0 this).wk
      (List.cons_subset_of_subset_of_mem
        (List.mem_cons_of_mem (∼φ).free <| by simpa using mem_shifts_iff.mpr hpos) (by simp))
    this.all.wk (by simpa using hneg)
  termination_by φ => φ.complexity

instance : Tait (SyntacticFormula L) (Schema L) where
  verum := fun _ Δ => verum' (by simp)
  and := fun dp dq => dp.and dq
  or := fun d => d.or
  wk := fun d ss => d.wk ss
  em := fun hp hn => em hp hn

instance : Tait.Cut (SyntacticFormula L) (Schema L) where
  cut {_ _ _ dp dn} := cut dp dn

protected def id {φ} (hφ : φ ∈ 𝓢) : 𝓢 ⟹ ∼φ :: Δ → 𝓢 ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (axm hφ) (by simp)) b

def provableOfDerivable {φ} (b : 𝓢 ⟹. φ) : 𝓢 ⊢! φ := b

def specialize {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    𝓢 ⟹ (∀⁰ φ) :: Γ → 𝓢 ⟹ φ/[t] :: Γ := fun d ↦
  have : 𝓢 ⟹ ∼φ/[t] :: φ/[t] :: Γ := Tait.em (φ := φ/[t]) (by simp) (by simp)
  have dn : 𝓢 ⟹ ∼(∀⁰ φ) :: φ/[t] :: Γ := by
    simp only [neg_all, Nat.reduceAdd]
    exact Derivation.exs t (by simpa using this)
  have dp : 𝓢 ⟹ (∀⁰ φ) :: φ/[t] :: Γ :=
    Derivation.wk d (List.cons_subset_cons _ <| by simp)
  Derivation.cut dp dn

def specializes : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → (v : Fin k → SyntacticTerm L) →
    𝓢 ⟹ (∀⁰* φ) :: Γ → 𝓢 ⟹ (φ ⇜ v) :: Γ
  |     0, φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝓢 ⟹ (∀⁰ (Rew.subst (v ·.succ)).q ▹ φ) :: Γ := by simpa using specializes (φ := ∀⁰ φ) (v ·.succ) b
    Derivation.cast (specialize (v 0) this) (by
      simp only [Nat.reduceAdd, ← TransitiveRewriting.comp_app, List.cons.injEq, and_true]; congr 2
      ext x <;> simp [Rew.comp_app]
      cases x using Fin.cases <;> simp)

def instances : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → {v : Fin k → SyntacticTerm L} →
    𝓢 ⟹ (φ ⇜ v) :: Γ → 𝓢 ⟹ (∃⁰* φ) :: Γ
  |     0, φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝓢 ⟹ (∃⁰ (Rew.subst (v ·.succ)).q ▹ φ) :: Γ :=
      exs (v 0) <| Derivation.cast b <| by
        unfold Rewriting.subst; rw [←TransitiveRewriting.comp_app]; congr 3
        ext x <;> simp [Rew.comp_app]
        cases x using Fin.cases <;> simp
    instances (k := k) (v := (v ·.succ)) (Derivation.cast this (by simp))

def allClosureFixitr {φ : SyntacticFormula L} (dp : 𝓢 ⊢! φ) : (m : ℕ) → 𝓢 ⊢! ∀⁰* Rew.fixitr 0 m ▹ φ
  | 0     => by simpa
  | m + 1 => by
    simp only [allClosure_fixitr, Nat.reduceAdd]
    apply all; simpa using allClosureFixitr dp m

def toClose (b : 𝓢 ⊢! φ) : 𝓢 ⊢! φ.univCl' := allClosureFixitr b φ.fvSup

def toClose! (b : 𝓢 ⊢ φ) : 𝓢 ⊢ φ.univCl' := ⟨toClose b.get⟩

def rewrite₁ (b : 𝓢 ⊢! φ) (f : ℕ → SyntacticTerm L) : 𝓢 ⊢! (Rew.rewrite f) ▹ φ :=
  Derivation.cast (specializes (fun x ↦ f x) (allClosureFixitr b φ.fvSup)) (by simp)

def rewrite {Γ} : 𝓢 ⟹ Γ → ∀ (f : ℕ → SyntacticTerm L), 𝓢 ⟹ Γ.map fun φ ↦ Rew.rewrite f ▹ φ
  | axL r v, f =>
    Derivation.cast (axL r (fun i ↦ Rew.rewrite f (v i))) (by simp [rew_rel, rew_nrel])
  | verum, f => Derivation.cast verum (by simp)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d,      f =>
    have : 𝓢 ⟹ Rew.rewrite f ▹ φ ⋎ Rew.rewrite f ▹ ψ :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq, f =>
    have : 𝓢 ⟹ Rew.rewrite f ▹ φ ⋏ Rew.rewrite f ▹ ψ :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | all (Γ := Γ) (φ := φ) d, f =>
    have : 𝓢 ⟹ ((Rewriting.free φ) :: Γ⁺).map fun φ ↦ Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) ▹ φ :=
      rewrite d (&0 :>ₙ fun x => Rew.shift (f x))
    have : 𝓢 ⟹ (∀⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      all (Derivation.cast this (by simp [free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | exs (Γ := Γ) (φ := φ) (t := t) d, f =>
    have : 𝓢 ⟹ (φ/[t] :: Γ).map fun φ ↦ Rew.rewrite f ▹ φ := rewrite d f
    have : 𝓢 ⟹ (∃⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      exs (Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | wk (𝓢 := 𝓢) (Γ := Γ) d ss, f => (rewrite d f).wk (List.map_subset _ ss)
  | cut (Γ := Γ) (φ := φ) d dn, f =>
    have dΓ : 𝓢 ⟹ (Rew.rewrite f ▹ φ) :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite d f) (by simp)
    have dΔ : 𝓢 ⟹ ∼(Rew.rewrite f ▹ φ) :: Γ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΓ dΔ) (by simp)
  | axm h, f => rewrite₁ (axm h) f

protected def map {Δ : Sequent L} (d : 𝓢 ⟹ Δ) (f : ℕ → ℕ) :
    𝓢 ⟹ Δ.map fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 f ▹ φ := rewrite d (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : 𝓢 ⟹ Δ) : 𝓢 ⟹ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by simp only [Rewriting.shifts, List.map_inj_left]; intro _ _; rfl)

def trans (F : U ⊢!* 𝓢) {Γ : Sequent L} : 𝓢 ⟹ Γ → U ⟹ Γ
  |   axL r v => axL r v
  |     verum => verum
  | and d₁ d₂ => and (trans F d₁) (trans F d₂)
  |      or d => or (trans F d)
  |     all d => all (trans F d)
  |   exs t d => exs t (trans F d)
  |   wk d ss => wk (trans F d) ss
  | cut d₁ d₂ => cut (trans F d₁) (trans F d₂)
  |     axm h => F h

instance : Tait.Axiomatized (SyntacticFormula L) (Schema L) where
  axm {_ _ h} := axm h
  trans {_ _ _ F d} := trans (fun h ↦ F _ h) d

variable [L.DecidableEq]

def not_close' (φ) : 𝓢 ⟹ [∼(φ.univCl'), φ] :=
  have : 𝓢 ⟹ [∃⁰* ∼(@Rew.fixitr L 0 (fvSup φ) ▹ φ), φ] := instances (v := fun x ↦ &x) (em (φ := φ) (by simp) (by simp))
  Derivation.cast this (by simp [univCl'])

def invClose (b : 𝓢 ⊢! φ.univCl') : 𝓢 ⊢! φ := cut (wk b (by simp)) (not_close' φ)

def invClose! (b : 𝓢 ⊢ φ.univCl') : 𝓢 ⊢ φ := ⟨invClose b.get⟩

def compact {Γ : Sequent L} : 𝓢 ⟹ Γ → (s : { s : Finset (SyntacticFormula L) // ↑s ⊆ 𝓢}) × (s : Schema L) ⟹ Γ
  | axL r v => ⟨⟨∅, by simp⟩, axL r v⟩
  | verum => ⟨⟨∅, by simp⟩, verum⟩
  | and d₁ d₂ =>
    let ⟨s₁, d₁⟩ := compact d₁
    let ⟨s₂, d₂⟩ := compact d₂
    ⟨⟨(s₁ ∪ s₂ : Finset (SyntacticFormula L)), by simp [s₁.prop, s₂.prop]⟩,
      and (Tait.ofAxiomSubset (by simp) d₁) (Tait.ofAxiomSubset (by simp) d₂)⟩
  | or d =>
    let ⟨s, d⟩ := compact d
    ⟨s, or d⟩
  | wk d ss =>
    let ⟨s, d⟩ := compact d
    ⟨s, wk d ss⟩
  | cut d₁ d₂ =>
    let ⟨s₁, d₁⟩ := compact d₁
    let ⟨s₂, d₂⟩ := compact d₂
    ⟨⟨(s₁ ∪ s₂ : Finset (SyntacticFormula L)), by simp [s₁.prop, s₂.prop]⟩,
      cut (Tait.ofAxiomSubset (by simp) d₁) (Tait.ofAxiomSubset (by simp) d₂)⟩
  | axm (φ := φ) h =>
    ⟨⟨{φ}, by simp [h]⟩, axm (by simp)⟩
  | all d =>
    let ⟨s, d⟩ := compact d
    ⟨s, all d⟩
  | exs t d =>
    let ⟨s, d⟩ := compact d
    ⟨s, exs t d⟩

instance : Entailment.Compact (Schema L) where
  Γ b := (compact b).1
  ΓPrf b := (compact b).2
  Γ_subset b := by simpa using (compact b).1.prop
  Γ_finite b := by simp

def deductionAux {Γ : Sequent L} : 𝓢 ⟹ Γ → 𝓢 \ {φ} ⟹ ∼(φ.univCl') :: Γ
  |        axL r v => Tait.wkTail <| axL r v
  |          verum => Tait.wkTail <| verum
  |      and d₁ d₂ => Tait.rotate₁ <| and (Tait.rotate₁ (deductionAux d₁)) (Tait.rotate₁ (deductionAux d₂))
  |           or d => Tait.rotate₁ <| or (Tait.rotate₂ (deductionAux d))
  |          all d => Tait.rotate₁ <| all (Derivation.cast (Tait.rotate₁ (deductionAux d)) (by simp))
  |        exs t d => Tait.rotate₁ <| exs t <| Tait.rotate₁ (deductionAux d)
  |        wk d ss => wk (deductionAux d) (by simp [List.subset_cons_of_subset _ ss])
  |      cut d₁ d₂ => (Tait.rotate₁ <| deductionAux d₁).cut (Tait.rotate₁ <| deductionAux d₂)
  | axm (φ := ψ) h => if hq : φ = ψ then Derivation.cast (not_close' φ) (by simp [hq]) else
    have : 𝓢 \ {φ} ⟹. ψ := axm (by simp [h, Ne.symm hq])
    wk this (by simp)

def deduction (d : insert φ 𝓢 ⟹ Γ) : 𝓢 ⟹ ∼(φ.univCl') :: Γ := Tait.ofAxiomSubset (by intro x; simp; tauto) (deductionAux d (φ := φ))

def provable_iff_inconsistent : 𝓢 ⊢ φ ↔ Entailment.Inconsistent (insert (∼φ.univCl') 𝓢) := by
  constructor
  · rintro b
    exact Entailment.inconsistent_of_provable_of_unprovable
      (Entailment.wk! (by simp) (toClose! b)) (Entailment.by_axm _ (by simp))
  · intro h
    rcases Tait.inconsistent_iff_provable.mp h with ⟨d⟩
    have : 𝓢 ⊢! φ.univCl' :=  Derivation.cast (deduction d) (by rw [univCl'_eq_self_of (∼(φ.univCl')) (by simp)]; simp)
    exact ⟨invClose this⟩

def unprovable_iff_consistent : 𝓢 ⊬ φ ↔ Entailment.Consistent (insert (∼φ.univCl') 𝓢) := by
  simp [←Entailment.not_inconsistent_iff_consistent, ←provable_iff_inconsistent]

section Hom

variable {L₁ : Language} {L₂ : Language} {𝓢₁ : Schema L₁} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Γ} : 𝓢₁ ⟹ Γ → 𝓢₁.lMap Φ ⟹ Γ.map (.lMap Φ)
  | axL r v =>
    .cast (axL (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Semiformula.lMap_rel, Semiformula.lMap_nrel])
  | verum => by simpa using verum
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    have : 𝓢₁.lMap Φ ⟹ (.lMap Φ φ ⋎ .lMap Φ ψ :: Γ.map (.lMap Φ) : Sequent L₂) :=
      or (by simpa using lMap Φ d)
    exact Derivation.cast this (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    have : 𝓢₁.lMap Φ ⟹ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    have : 𝓢₁.lMap Φ ⟹ ((∀⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [←Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    have : 𝓢₁.lMap Φ ⟹ ((∃⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      exs (Semiterm.lMap Φ t)
        (Derivation.cast (lMap Φ d) (by simp [Semiformula.lMap_subst]))
    Derivation.cast this (by simp)
  | wk (Δ := Δ) (Γ := Γ) d ss => (lMap Φ d).wk (List.map_subset _ ss)
  | cut (Γ := Γ) (φ := φ) d dn =>
    have : 𝓢₁.lMap Φ ⟹ (Γ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp)
  | axm h => axm (Set.mem_image_of_mem _ h)

lemma inconsistent'_lMap (Φ : L₁ →ᵥ L₂) : Entailment.Inconsistent 𝓢₁ → Entailment.Inconsistent (𝓢₁.lMap Φ) := by
  simp only [Entailment.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨by simpa using lMap Φ b⟩

end Hom

omit [L.DecidableEq]

private lemma map_subst_eq_free (φ : SyntacticSemiformula L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) ▹ (φ/[&m] : SyntacticFormula L) = Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app])
    (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Δ⁺ := by
  apply List.map_congr_left
  intro φ hp; exact rew_eq_of_funEqOn₀
    (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])

def genelalizeByNewver {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : 𝓢 ⟹ φ/[&m] :: Δ) : 𝓢 ⟹ (∀⁰ φ) :: Δ := by
  have : 𝓢 ⟹ (Rewriting.free φ) :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝓢 ⟹ v.map (φ/[·]) ++ Γ) : 𝓢 ⟹ (∃⁰ φ) :: Γ := by
  induction' v with t v ih generalizing Γ
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃⁰ φ) :: Γ) ((exs t h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝓢 ⟹ (∃⁰ φ) :: v.map (φ/[·]) ++ Γ) : 𝓢 ⟹ (∃⁰ φ) :: Γ :=
  (exOfInstances (Γ := (∃⁰ φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

end Derivation

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : SyntacticFormula L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ (newVar Γ) :=
  not_fvar?_of_lt_fvSup φ (by simpa [newVar] using List.le_max_of_le (List.mem_map_of_mem h) (by simp))

namespace Derivation

open Semiformula
variable {P : SyntacticFormula L → Prop} {𝓢 : Schema L} {Δ : Sequent L}

def allNvar {φ} (h : ∀⁰ φ ∈ Δ) : 𝓢 ⟹ φ/[&(newVar Δ)] :: Δ → 𝓢 ⟹ Δ := fun b ↦
  let b : 𝓢 ⟹ (∀⁰ φ) :: Δ :=
    genelalizeByNewver (by simpa [FVar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Tait.wk b (by simp [h])

def id_allClosure {φ} (hp : φ ∈ 𝓢) : 𝓢 ⟹ ∼φ.univCl' :: Δ → 𝓢 ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (toClose (axm hp)) (by simp)) b

end Derivation

namespace Schema

instance {𝓢 U : Schema L} : 𝓢 ⪯ 𝓢 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

instance {𝓢 U : Schema L} : U ⪯ 𝓢 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

def deduction [L.DecidableEq] {𝓢 : Schema L} {φ ψ} (b : insert φ 𝓢 ⊢! ψ) : 𝓢 ⊢! φ.univCl' ➝ ψ :=
  have : 𝓢 ⟹ [∼φ.univCl', ψ] := Derivation.deduction b
  (Tait.or this).cast (by simp; rfl)

theorem deduction! [L.DecidableEq] {𝓢 : Schema L} {φ ψ} (b : insert φ 𝓢 ⊢ ψ) : 𝓢 ⊢ φ.univCl' ➝ ψ :=
  ⟨deduction b.get⟩

lemma close!_iff [L.DecidableEq] {𝓢 : Schema L} {φ} : 𝓢 ⊢ φ.univCl' ↔ 𝓢 ⊢ φ := by
  constructor
  · intro h
    apply deduction! (Entailment.Axiomatized.adjoin! _ _) ⨀ h
  · intro h
    exact Derivation.toClose! h

end Schema

/-!
  ### Theory (T set of sentences)
-/

instance : Entailment (Theory L) (Sentence L) := ⟨fun T σ ↦ (T : Schema L) ⊢! ↑σ⟩

instance (T : Theory L) : Entailment.Cl T := Entailment.Cl.ofEquiv (T : Schema L) T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

def toSyntacticProof {T : Theory L} {σ} : T ⊢! σ → (T : Schema L) ⊢! ↑σ := fun b ↦ b

def ofSyntacticProof {T : Theory L} {σ} : (T : Schema L) ⊢! ↑σ → T ⊢! σ := fun b ↦ b

lemma provable_def {T : Theory L} {σ} : T ⊢ σ ↔ (T : Schema L) ⊢ ↑σ := by rfl

def Proof.cast {T : Theory L} {σ} : T ⊢ σ ↔ (T : Schema L) ⊢ ↑σ := by rfl

namespace Theory

open Entailment

instance : Axiomatized (Theory L) where
  prfAxm {T} σ h := ofSyntacticProof <| Axiomatized.prfAxm (by simpa using h)
  weakening {σ T B} h b := ofSyntacticProof <| Axiomatized.weakening (by simpa using h) b

def deduction [L.DecidableEq] {T : Theory L} {σ τ} (b : insert σ T ⊢! τ) : T ⊢! σ ➝ τ :=
  have : insert ↑σ T.toSchema ⊢! ↑τ := by simpa using toSyntacticProof b
  (Schema.deduction this).cast (by simp)

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
        simpa [Theory.toSchema] using s.prop hφ
      rcases this with ⟨σ, hσ, rfl⟩
      have : σ = φ := by simpa [Semiformula.toEmpty'] using e
      simp_all⟩, ofSyntacticProof <|
        Axiomatized.weakening (by
          simp only [Finset.coe_image]
          intro φ hφ
          have : ∃ σ ∈ T, ↑σ = φ := by
            simpa [Theory.toSchema] using s.prop hφ
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
    Tait.Axiomatized.trans (𝓛 := (↑T : Schema L)) (𝓚 := (↑U : Schema L))
      (fun ψ hψ ↦
        let b := @b ψ.toEmpty' (by
          have : ∃ ψ₀ ∈ U, ↑ψ₀ = ψ := by simpa [toSchema] using hψ
          rcases this with ⟨ψ₀, hψ₀U, rfl⟩
          simpa using hψ)
        (toSyntacticProof b).cast <| by
          have : ∃ ψ₀ ∈ U, ↑ψ₀ = ψ := by simpa [toSchema] using hψ
          rcases this with⟨_, _, rfl⟩
          simp)
      (toSyntacticProof d)

lemma compact' [L.DecidableEq] {T : Theory L} {φ : Sentence L}
    (b : T ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T}), (∅ : Theory L) ⊢ s.val.conj ➝ φ := by
  let ⟨s, b⟩ := compact b
  let bc : ({s.val.conj} : Theory L) ⊢ s.val.conj := Axiomatized.provable_refl _ (by simp)
  have : {s.val.conj} ⊢ φ := StrongCut.cut! (fun {ψ} hψ ↦ Entailment.left_Fconj!_intro (by simpa) ⨀ bc) b
  have : (insert s.val.conj ∅ : Theory L) ⊢ φ := by simpa using this
  exact ⟨s, ⟨deduction this.get⟩⟩

instance (T : Theory L) : Entailment.Cl T := Entailment.Cl.ofEquiv (T : Schema L) T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

instance : DeductiveExplosion (Theory L) where
  dexp b _ := ofSyntacticProof <| DeductiveExplosion.dexp (toSyntacticProof b) _

lemma inconsistent_iff {T : Theory L} :
    Inconsistent T ↔ Inconsistent (T : Schema L) := calc
  Inconsistent T ↔ T ⊢ ⊥                                 := inconsistent_iff_provable_bot
  _              ↔ (T : Schema L) ⊢ ⊥         := by simp [provable_def]
  _              ↔ Inconsistent (T : Schema L) := inconsistent_iff_provable_bot.symm

lemma inconsistent_lMap {T : Theory L₁} (Φ : L₁ →ᵥ L₂) :
    Entailment.Inconsistent T → Entailment.Inconsistent (T.lMap Φ) := by
  intro h
  have : Schema.lMap Φ ↑T ⊢ ⊥ := ⟨Derivation.lMap Φ (provable_def.mp <| inconsistent_iff_provable_bot.mp h).get⟩
  refine inconsistent_iff_provable_bot.mpr <| provable_def.mpr ?_
  suffices ↑(lMap Φ T) ⊢ ⊥ by simpa
  apply Axiomatized.weakening! ?_ this
  simp only [Schema.lMap, toSchema, Set.image_subset_iff]
  intro φ hφ
  simpa using ⟨(Semiformula.lMap Φ) φ, Set.mem_image_of_mem _ hφ, Eq.symm (lMap_emb φ)⟩

instance {T U : Theory L} : T ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

instance {T U : Theory L} : U ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

end Theory

namespace Schema

open Entailment

variable [L.DecidableEq] {𝓢 : Schema L}

def coe_provable_iff_provable_coe {σ : Sentence L} :
    (𝓢 : Theory L) ⊢ σ ↔ 𝓢 ⊢ ↑σ := by
  constructor
  · intro b
    have : 𝓢.toTheory.toSchema ⊢ ↑σ := b
    apply Entailment.StrongCut.cut! ?_ this
    intro τ hτ
    have : ∃ τ' ∈ 𝓢, τ'.univCl' = τ := by simpa [Schema.toTheory, Theory.toSchema] using hτ
    rcases this with ⟨τ, h, rfl⟩
    exact Derivation.toClose! <| by_axm _ <| by simpa
  · intro b
    apply provable_def.mpr
    apply Entailment.StrongCut.cut! ?_ b
    intro φ hφ
    have : 𝓢.toTheory.toSchema ⊢ φ.univCl' :=
      by_axm _ <| by simpa [Schema.toTheory, Theory.toSchema] using ⟨φ, by simpa, rfl⟩
    exact Schema.close!_iff.mp this

def coe_unprovable_iff_unprovable_coe {σ} :
    (𝓢 : Theory L) ⊬ σ ↔ 𝓢 ⊬ ↑σ := coe_provable_iff_provable_coe.not

def provable_univCl_iff {φ : SyntacticFormula L} :
    (𝓢 : Theory L) ⊢ φ.univCl ↔ 𝓢 ⊢ φ := Iff.trans coe_provable_iff_provable_coe (by simp [Schema.close!_iff])

def unprovable_univCl_iff {φ : SyntacticFormula L} :
    (𝓢 : Theory L) ⊬ φ.univCl ↔ 𝓢 ⊬ φ := provable_univCl_iff.not

instance (𝓢 𝓣 : Schema L) [𝓢 ⪯ 𝓣] : 𝓢.toTheory ⪯ 𝓣.toTheory :=
  ⟨fun _ b ↦ coe_provable_iff_provable_coe.mpr <| (inferInstanceAs (𝓢 ⪯ 𝓣)).pbl (coe_provable_iff_provable_coe.mp b)⟩

@[simp] lemma coe_consistent_iff :
    Consistent (𝓢 : Theory L) ↔ Consistent 𝓢 := calc
  Consistent (𝓢 : Theory L) ↔ (𝓢 : Theory L) ⊬ ⊥ := consistent_iff_unprovable_bot
  _                        ↔ 𝓢 ⊬ ⊥             := by simp [coe_unprovable_iff_unprovable_coe]
  _                        ↔ Consistent 𝓢      := consistent_iff_unprovable_bot.symm

instance [Consistent 𝓢] : Consistent (𝓢 : Theory L) := by simp_all

end Schema

namespace Schema

variable {𝓢 : Schema L}

def specialize! (φ : SyntacticSemiformula L 1) (t : SyntacticTerm L) : 𝓢 ⊢! ∀⁰ φ ➝ φ/[t] :=
  have : 𝓢 ⟹ [(∼φ)/[t], φ/[t]] := Derivation.em (φ := φ/[t]) (by simp) (by simp)
  have : 𝓢 ⟹ [∃⁰ ∼φ, φ/[t]] := this.exs t
  this.or.cast (by simp [Semiformula.imp_eq])

lemma specialize (φ : SyntacticSemiformula L 1) (t : SyntacticTerm L) : 𝓢 ⊢ ∀⁰ φ ➝ φ/[t] := ⟨specialize! φ t⟩

end Schema

namespace Theory

variable {T : Theory L}

def specialize! (φ : Semisentence L 1) (t) : T ⊢! ∀⁰ φ ➝ φ/[t] := ofSyntacticProof <| by
  simpa [Semiformula.coe_subst_eq_subst_coe₁] using (Schema.specialize! (𝓢 := T) φ (t : SyntacticTerm L))

lemma specialize (φ : Semisentence L 1) (t) : T ⊢ ∀⁰ φ ➝ φ/[t] := ⟨specialize! φ t⟩

end Theory

end FirstOrder

end LO

end
