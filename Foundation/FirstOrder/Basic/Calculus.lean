import Foundation.Logic.Calculus
import Foundation.FirstOrder.Basic.Syntax.Theory

namespace LO

namespace FirstOrder

abbrev Sequent (L : Language) := List (SyntacticFormula L)

open Semiformula
variable {L : Language} {𝓢 : SyntacticFormulas L}

inductive Derivation (𝓢 : SyntacticFormulas L) : Sequent L → Type _
| axL (Γ) {k} (r : L.Rel k) (v) : Derivation 𝓢 (rel r v :: nrel r v :: Γ)
| verum (Γ)    : Derivation 𝓢 (⊤ :: Γ)
| or {Γ φ ψ}   : Derivation 𝓢 (φ :: ψ :: Γ) → Derivation 𝓢 (φ ⋎ ψ :: Γ)
| and {Γ φ ψ}  : Derivation 𝓢 (φ :: Γ) → Derivation 𝓢 (ψ :: Γ) → Derivation 𝓢 (φ ⋏ ψ :: Γ)
| all {Γ φ}    : Derivation 𝓢 (Rewriting.free φ :: Γ⁺) → Derivation 𝓢 ((∀' φ) :: Γ)
| ex {Γ φ} (t) : Derivation 𝓢 (φ/[t] :: Γ) → Derivation 𝓢 ((∃' φ) :: Γ)
| wk {Γ Δ}     : Derivation 𝓢 Δ → Δ ⊆ Γ → Derivation 𝓢 Γ
| cut {Γ φ}    : Derivation 𝓢 (φ :: Γ) → Derivation 𝓢 (∼φ :: Γ) → Derivation 𝓢 Γ
| axm {φ}     : φ ∈ 𝓢 → Derivation 𝓢 [φ]

instance : OneSided (SyntacticFormula L) (SyntacticFormulas L) := ⟨Derivation⟩

abbrev Derivation₀ (Γ : Sequent L) : Type _ := (∅ : SyntacticFormulas L) ⟹ Γ

abbrev Derivable₀ (Γ : Sequent L) : Prop := (∅ : SyntacticFormulas L) ⟹! Γ

prefix:45 "⊢ᵀ " => Derivation₀

namespace Derivation

variable {𝓢 U : SyntacticFormulas L} {Δ Δ₁ Δ₂ Γ : Sequent L} {φ ψ r : SyntacticFormula L}

open Rewriting LawfulSyntacticRewriting

def length {Δ : Sequent L} : 𝓢 ⟹ Δ → ℕ
  | axL _ _ _   => 0
  | verum _     => 0
  | or d        => d.length.succ
  | and dp dq   => (max (length dp) (length dq)).succ
  | all d       => d.length.succ
  | ex _ d      => d.length.succ
  | wk d _      => d.length.succ
  | cut dp dn   => (max (length dp) (length dn)).succ
  | axm _      => 0

section length

@[simp] lemma length_axL {k} {r : L.Rel k} {v} :
  length (axL (𝓢 := 𝓢) Δ r v) = 0 := rfl

@[simp] lemma length_verum : length (verum (𝓢 := 𝓢) Δ) = 0 := rfl

@[simp] lemma length_and {φ ψ} (dp : 𝓢 ⟹ φ :: Δ) (dq : 𝓢 ⟹ ψ :: Δ) :
    length (and dp dq) = (max (length dp) (length dq)).succ := rfl

@[simp] lemma length_or {φ ψ} (d : 𝓢 ⟹ φ :: ψ :: Δ) : length (or d) = d.length.succ := rfl

@[simp] lemma length_all {φ} (d : 𝓢 ⟹ Rewriting.free φ :: Δ⁺) : length (all d) = d.length.succ := rfl

@[simp] lemma length_ex {t} {φ} (d : 𝓢 ⟹ φ/[t] :: Δ) : length (ex t d) = d.length.succ := rfl

@[simp] lemma length_wk (d : 𝓢 ⟹ Δ) (h : Δ ⊆ Γ) : length (wk d h) = d.length.succ := rfl

@[simp] lemma length_cut {φ} (dp : 𝓢 ⟹ φ :: Δ) (dn : 𝓢 ⟹ (∼φ) :: Δ) :
  length (cut dp dn) = (max (length dp) (length dn)).succ := rfl

end length

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected unsafe def repr {Δ : Sequent L} : 𝓢 ⟹ Δ → String
  | axL Δ _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | verum Δ       =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | @or _ _ Δ φ ψ d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((φ ⋎ ψ) :: Δ) ++ "$}\n\n"
  | @and _ _ Δ φ ψ dp dq =>
      Derivation.repr dp ++
      Derivation.repr dq ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((φ ⋏ ψ) :: Δ) ++ "$}\n\n"
  | @all _ _ Δ φ d       =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀' φ) :: Δ) ++ "$}\n\n"
  | @ex _ _ Δ φ _ d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃' φ) :: Δ) ++ "$}\n\n"
  | @wk _ _ _ Γ d _      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize(wk)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | @cut _ _ Δ _ dp dn =>
      Derivation.repr dp ++
      Derivation.repr dn ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | axm (φ := φ) _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(ROOT)}\n" ++
      "\\UnaryInfC{$" ++ reprStr φ ++ ", " ++ reprStr (∼φ) ++ "$}\n\n"

unsafe instance : Repr (𝓢 ⟹ Δ) where reprPrec d _ := Derivation.repr d

end Repr

protected abbrev cast (d : 𝓢 ⟹ Δ) (e : Δ = Γ) : 𝓢 ⟹ Γ := e ▸ d

@[simp] lemma cast_eq (d : 𝓢 ⟹ Δ) (e : Δ = Δ) : Derivation.cast d e = d := rfl

@[simp] lemma length_cast (d : 𝓢 ⟹ Δ) (e : Δ = Γ) :
    length (Derivation.cast d e) = length d := by rcases e with rfl; simp [Derivation.cast]

@[simp] lemma length_cast' (d : 𝓢 ⟹ Δ) (e : Δ = Γ) :
    length (e ▸ d) = length d := by rcases e with rfl; simp

alias weakening := wk

def verum' (h : ⊤ ∈ Δ) : 𝓢 ⟹ Δ := (verum Δ).wk (by simp [h])

def axL' {k} (r : L.Rel k) (v)
    (h : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) : 𝓢 ⟹ Δ := (axL Δ r v).wk (by simp [h, hn])

def all' {φ} (h : ∀' φ ∈ Δ) (d : 𝓢 ⟹ Rewriting.free φ :: Δ⁺) : 𝓢 ⟹ Δ := d.all.wk (by simp [h])

def ex' {φ} (h : ∃' φ ∈ Δ) (t) (d : 𝓢 ⟹ φ/[t] :: Δ) : 𝓢 ⟹ Δ := (d.ex t).wk (by simp [h])

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {φ ψ : SyntacticFormula L} : ¬∼φ = φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

def em {Δ : Sequent L} : {φ : SyntacticFormula L} → (hpos : φ ∈ Δ) → (hneg : ∼φ ∈ Δ) → 𝓢 ⟹ Δ
  | ⊤,         hpos, hneg => verum' hpos
  | ⊥,         hpos, hneg => verum' hneg
  | .rel R v,  hpos, hneg => axL' R v hpos hneg
  | .nrel R v, hpos, hneg => axL' R v hneg hpos
  | φ ⋏ ψ,     hpos, hneg =>
    have ihp : 𝓢 ⟹ φ :: ∼φ :: ∼ψ :: Δ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝓢 ⟹ ψ :: ∼φ :: ∼ψ :: Δ := em (φ := ψ) (by simp) (by simp)
    have : 𝓢 ⟹ ∼φ :: ∼ψ :: Δ := (ihp.and ihq).wk (by simp [hpos])
    this.or.wk (by simpa using hneg)
  | φ ⋎ ψ,     hpos, hneg =>
    have ihp : 𝓢 ⟹ ∼φ :: φ :: ψ :: Δ := em (φ := φ) (by simp) (by simp)
    have ihq : 𝓢 ⟹ ∼ψ :: φ :: ψ :: Δ := em (φ := ψ) (by simp) (by simp)
    have : 𝓢 ⟹ φ :: ψ :: Δ := (ihp.and ihq).wk (by simp [by simpa using hneg])
    this.or.wk (by simp [hpos])
  | ∀' φ,      hpos, hneg =>
    have : 𝓢 ⟹ ∼Rewriting.free φ :: Rewriting.free φ :: Δ⁺ := em (φ := Rewriting.free φ) (by simp) (by simp)
    have : 𝓢 ⟹ (∼Rewriting.shift φ)/[&0] :: Rewriting.free φ :: Δ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝓢 ⟹ Rewriting.free φ :: Δ⁺ := (ex &0 this).wk
      (List.cons_subset_of_subset_of_mem
        (List.mem_cons_of_mem (free φ) <| by simpa using mem_shifts_iff.mpr hneg) (by rfl))
    this.all.wk (by simp [hpos])
  | ∃' φ,      hpos, hneg =>
    have : 𝓢 ⟹ Rewriting.free φ :: ∼Rewriting.free φ :: Δ⁺ := em (φ := Rewriting.free φ) (by simp) (by simp)
    have : 𝓢 ⟹ (Rewriting.shift φ)/[&0] :: ∼Rewriting.free φ :: Δ⁺ :=
      Derivation.cast this (by simp [←TransitiveRewriting.comp_app])
    have : 𝓢 ⟹ Rewriting.free (∼φ) :: Δ⁺ := (ex &0 this).wk
      (List.cons_subset_of_subset_of_mem
        (List.mem_cons_of_mem (free (∼φ)) <| by simpa using mem_shifts_iff.mpr hpos) (by simp))
    this.all.wk (by simpa using hneg)
  termination_by φ => φ.complexity

instance : Tait (SyntacticFormula L) (SyntacticFormulas L) where
  verum := fun _ Δ => verum Δ
  and := fun dp dq => dp.and dq
  or := fun d => d.or
  wk := fun d ss => d.wk ss
  em := fun hp hn => em hp hn

instance : Tait.Cut (SyntacticFormula L) (SyntacticFormulas L) where
  cut {_ _ _ dp dn} := cut dp dn

protected def id {φ} (hφ : φ ∈ 𝓢) : 𝓢 ⟹ ∼φ :: Δ → 𝓢 ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (axm hφ) (by simp)) b

def provableOfDerivable {φ} (b : 𝓢 ⟹. φ) : 𝓢 ⊢! φ := b

def specialize {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    𝓢 ⟹ (∀' φ) :: Γ → 𝓢 ⟹ φ/[t] :: Γ := fun d ↦
  have : 𝓢 ⟹ ∼φ/[t] :: φ/[t] :: Γ := Tait.em (φ := φ/[t]) (by simp) (by simp)
  have dn : 𝓢 ⟹ ∼(∀' φ) :: φ/[t] :: Γ := by
    simp only [neg_all, Nat.reduceAdd]
    exact Derivation.ex t (by simpa using this)
  have dp : 𝓢 ⟹ (∀' φ) :: φ/[t] :: Γ :=
    Derivation.wk d (List.cons_subset_cons _ <| by simp)
  Derivation.cut dp dn

def specializes : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → (v : Fin k → SyntacticTerm L) →
    𝓢 ⟹ (∀* φ) :: Γ → 𝓢 ⟹ (φ ⇜ v) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝓢 ⟹ (∀' (Rew.subst (v ·.succ)).q ▹ φ) :: Γ := by simpa using specializes (φ := ∀' φ) (v ·.succ) b
    Derivation.cast (specialize (v 0) this) (by
      simp only [Nat.reduceAdd, ← TransitiveRewriting.comp_app, List.cons.injEq, and_true]; congr 2
      ext x <;> simp [Rew.comp_app]
      cases x using Fin.cases <;> simp)

def instances : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → {v : Fin k → SyntacticTerm L} →
    𝓢 ⟹ (φ ⇜ v) :: Γ → 𝓢 ⟹ (∃* φ) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : 𝓢 ⟹ (∃' (Rew.subst (v ·.succ)).q ▹ φ) :: Γ :=
      ex (v 0) <| Derivation.cast b <| by
        unfold Rewriting.subst; rw [←TransitiveRewriting.comp_app]; congr 3
        ext x <;> simp [Rew.comp_app]
        cases x using Fin.cases <;> simp
    instances (k := k) (v := (v ·.succ)) (Derivation.cast this (by simp))

def allClosureFixitr {φ : SyntacticFormula L} (dp : 𝓢 ⊢! φ) : (m : ℕ) → 𝓢 ⊢! ∀* Rew.fixitr 0 m ▹ φ
  | 0     => by simpa
  | m + 1 => by
    simp only [allClosure_fixitr, Nat.reduceAdd]
    apply all; simpa using allClosureFixitr dp m

def toClose (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∀∀φ := allClosureFixitr b φ.fvSup

def toClose! (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∀∀φ := ⟨toClose b.get⟩

def rewrite₁ (b : 𝓢 ⊢! φ) (f : ℕ → SyntacticTerm L) : 𝓢 ⊢! (Rew.rewrite f) ▹ φ :=
  Derivation.cast (specializes (fun x ↦ f x) (allClosureFixitr b φ.fvSup)) (by simp)

def rewrite {Δ} : 𝓢 ⟹ Δ → ∀ (f : ℕ → SyntacticTerm L), 𝓢 ⟹ Δ.map fun φ ↦ Rew.rewrite f ▹ φ
  | axL Δ r v,            f =>
    Derivation.cast (axL (Δ.map fun φ ↦ Rew.rewrite f ▹ φ) r (fun i ↦ Rew.rewrite f (v i))) (by simp [rew_rel, rew_nrel])
  | verum Δ,              f => Derivation.cast (verum (Δ.map fun φ ↦ Rew.rewrite f ▹ φ)) (by simp)
  | @or _ _ Δ φ ψ d,      f =>
    have : 𝓢 ⟹ Rew.rewrite f ▹ φ ⋎ Rew.rewrite f ▹ ψ :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq, f =>
    have : 𝓢 ⟹ Rew.rewrite f ▹ φ ⋏ Rew.rewrite f ▹ ψ :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d,       f =>
    have : 𝓢 ⟹ ((Rewriting.free φ) :: Δ⁺).map fun φ ↦ Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) ▹ φ :=
      rewrite d (&0 :>ₙ fun x => Rew.shift (f x))
    have : 𝓢 ⟹ (∀' Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      all (Derivation.cast this (by simp [free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @ex _ _ Δ φ t d,      f =>
    have : 𝓢 ⟹ (φ/[t] :: Δ).map fun φ ↦ Rew.rewrite f ▹ φ := rewrite d f
    have : 𝓢 ⟹ (∃' Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ :=
      ex (Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @wk _ _ Δ Γ d ss,     f => (rewrite d f).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn,    f =>
    have dΔ : 𝓢 ⟹ (Rew.rewrite f ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite d f) (by simp)
    have dΓ : 𝓢 ⟹ ∼(Rew.rewrite f ▹ φ) :: Δ.map fun φ ↦ Rew.rewrite f ▹ φ := Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΔ dΓ) (by simp)
  | axm h,               f => rewrite₁ (axm h) f

protected def map {Δ : Sequent L} (d : 𝓢 ⟹ Δ) (f : ℕ → ℕ) :
    𝓢 ⟹ Δ.map fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 f ▹ φ := rewrite d (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : 𝓢 ⟹ Δ) : 𝓢 ⟹ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by simp only [Rewriting.shifts, List.map_inj_left]; intro _ _; rfl)

def trans (F : U ⊢!* 𝓢) {Γ : Sequent L} : 𝓢 ⟹ Γ → U ⟹ Γ
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

variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

private def not_close' (φ) : 𝓢 ⟹ [∼(∀∀φ), φ] :=
  have : 𝓢 ⟹ [∃* ∼(@Rew.fixitr L 0 (fvSup φ) ▹ φ), φ] := instances (v := fun x ↦ &x) (em (φ := φ) (by simp) (by simp))
  Derivation.cast this (by simp [close])

def invClose (b : 𝓢 ⊢! ∀∀φ) : 𝓢 ⊢! φ := cut (wk b (by simp)) (not_close' φ)

def invClose! (b : 𝓢 ⊢ ∀∀φ) : 𝓢 ⊢ φ := ⟨invClose b.get⟩

private def deductionAux {Γ : Sequent L} : 𝓢 ⟹ Γ → 𝓢 \ {φ} ⟹ ∼(∀∀φ) :: Γ
  | axL Γ R v       => Tait.wkTail <| axL Γ R v
  | verum Γ         => Tait.wkTail <| verum Γ
  | and d₁ d₂       => Tait.rotate₁ <| and (Tait.rotate₁ (deductionAux d₁)) (Tait.rotate₁ (deductionAux d₂))
  | or d            => Tait.rotate₁ <| or (Tait.rotate₂ (deductionAux d))
  | all d           => Tait.rotate₁ <| all (Derivation.cast (Tait.rotate₁ (deductionAux d)) (by simp))
  | ex t d          => Tait.rotate₁ <| ex t <| Tait.rotate₁ (deductionAux d)
  | wk d ss         => wk (deductionAux d) (by simp [List.subset_cons_of_subset _ ss])
  | cut d₁ d₂       => (Tait.rotate₁ <| deductionAux d₁).cut (Tait.rotate₁ <| deductionAux d₂)
  | axm (φ := ψ) h => if hq : φ = ψ then Derivation.cast (not_close' φ) (by simp [hq]) else
    have : 𝓢 \ {φ} ⟹. ψ := axm (by simp [h, Ne.symm hq])
    wk this (by simp)

def deduction (d : insert φ 𝓢 ⟹ Γ) : 𝓢 ⟹ ∼(∀∀φ) :: Γ := Tait.ofAxiomSubset (by intro x; simp; tauto) (deductionAux d (φ := φ))

def provable_iff_inconsistent : 𝓢 ⊢ φ ↔ Entailment.Inconsistent (insert (∼∀∀φ) 𝓢) := by
  constructor
  · rintro b
    exact Entailment.inconsistent_of_provable_of_unprovable
      (Entailment.wk! (by simp) (toClose! b)) (Entailment.by_axm _ (by simp))
  · intro h
    rcases Tait.inconsistent_iff_provable.mp h with ⟨d⟩
    have : 𝓢 ⊢! ∀∀φ :=  Derivation.cast (deduction d) (by rw [close_eq_self_of (∼∀∀φ) (by simp)]; simp)
    exact ⟨invClose this⟩

def unprovable_iff_consistent : 𝓢 ⊬ φ ↔ Entailment.Consistent (insert (∼∀∀φ) 𝓢) := by
  simp [←Entailment.not_inconsistent_iff_consistent, ←provable_iff_inconsistent]

section Hom

variable {L₁ : Language} {L₂ : Language} {𝓢₁ : SyntacticFormulas L₁} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Δ} : 𝓢₁ ⟹ Δ → 𝓢₁.lMap Φ ⟹ Δ.map (.lMap Φ)
  | axL Δ r v            =>
    .cast (axL (Δ.map (.lMap Φ)) (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Semiformula.lMap_rel, Semiformula.lMap_nrel])
  | verum Δ              => by simpa using verum _
  | @or _ _ Δ φ ψ d      => by
    have : 𝓢₁.lMap Φ ⟹ (.lMap Φ φ ⋎ .lMap Φ ψ :: Δ.map (.lMap Φ) : Sequent L₂) :=
      or (by simpa using lMap Φ d)
    exact Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq =>
    have : 𝓢₁.lMap Φ ⟹ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d       =>
    have : 𝓢₁.lMap Φ ⟹ ((∀' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [←Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | @ex _ _ Δ φ t d      =>
    have : 𝓢₁.lMap Φ ⟹ ((∃' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      ex (Semiterm.lMap Φ t)
        (Derivation.cast (lMap Φ d) (by simp [Semiformula.lMap_substs]))
    Derivation.cast this (by simp)
  | @wk _ _ Δ Γ d ss     => (lMap Φ d).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn    =>
    have : 𝓢₁.lMap Φ ⟹ (Δ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp)
  | axm h               => axm (Set.mem_image_of_mem _ h)

lemma inconsistent'_lMap (Φ : L₁ →ᵥ L₂) : Entailment.Inconsistent 𝓢₁ → Entailment.Inconsistent (𝓢₁.lMap Φ) := by
  simp only [Entailment.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨by simpa using lMap Φ b⟩

end Hom

omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

private lemma map_subst_eq_free (φ : SyntacticSemiformula L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) ▹ (φ/[&m] : SyntacticFormula L) = Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Δ⁺ := by
  apply List.map_congr_left
  intro φ hp; exact rew_eq_of_funEqOn₀
    (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])

def genelalizeByNewver {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : 𝓢 ⟹ φ/[&m] :: Δ) : 𝓢 ⟹ (∀' φ) :: Δ := by
  have : 𝓢 ⟹ (Rewriting.free φ) :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝓢 ⟹ v.map (φ/[·]) ++ Γ) : 𝓢 ⟹ (∃' φ) :: Γ := by
  induction' v with t v ih generalizing Γ
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃' φ) :: Γ) ((ex t h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : 𝓢 ⟹ (∃' φ) :: v.map (φ/[·]) ++ Γ) : 𝓢 ⟹ (∃' φ) :: Γ :=
  (exOfInstances (Γ := (∃' φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

end Derivation

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : SyntacticFormula L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ (newVar Γ) :=
  not_fvar?_of_lt_fvSup φ (by simpa [newVar] using List.le_max_of_le (List.mem_map_of_mem h) (by simp))

namespace Derivation

open Semiformula
variable {P : SyntacticFormula L → Prop} {𝓢 : SyntacticFormulas L} {Δ : Sequent L}

def allNvar {φ} (h : ∀' φ ∈ Δ) : 𝓢 ⟹ φ/[&(newVar Δ)] :: Δ → 𝓢 ⟹ Δ := fun b ↦
  let b : 𝓢 ⟹ (∀' φ) :: Δ :=
    genelalizeByNewver (by simpa [FVar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Tait.wk b (by simp [h])

def id_univClosure {φ} (hp : φ ∈ 𝓢) : 𝓢 ⟹ ∼∀∀ φ :: Δ → 𝓢 ⟹ Δ := fun b ↦ Tait.cut (Tait.wk (toClose (axm hp)) (by simp)) b

end Derivation

namespace SyntacticFormulas

instance {𝓢 U : SyntacticFormulas L} : 𝓢 ⪯ 𝓢 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

instance {𝓢 U : SyntacticFormulas L} : U ⪯ 𝓢 ∪ U := Entailment.Axiomatized.weakerThanOfSubset (by simp)

def deduction [L.DecidableEq] {𝓢 : SyntacticFormulas L} {φ ψ} (b : insert φ 𝓢 ⊢! ψ) : 𝓢 ⊢! ∀∀φ ➝ ψ :=
  have : 𝓢 ⟹ [∼∀∀φ, ψ] := Derivation.deduction b
  (Tait.or this).cast (by simp; rfl)

theorem deduction! [L.DecidableEq] {𝓢 : SyntacticFormulas L} {φ ψ} (b : insert φ 𝓢 ⊢ ψ) : 𝓢 ⊢ ∀∀φ ➝ ψ :=
  ⟨deduction b.get⟩

lemma close!_iff [L.DecidableEq] {𝓢 : SyntacticFormulas L} {φ} : 𝓢 ⊢ ∀∀φ ↔ 𝓢 ⊢ φ := by
  constructor
  · intro h
    apply deduction! (Entailment.Axiomatized.adjoin! _ _) ⨀ h
  · intro h
    exact Derivation.toClose! h

end SyntacticFormulas

/-!
  ### Theory (T set of sentences)
-/

instance : Entailment (Sentence L) (Theory L) := ⟨fun T σ ↦ (T : SyntacticFormulas L) ⊢! ↑σ⟩

instance (T : Theory L) : Entailment.Cl T := Entailment.Cl.ofEquiv (T : SyntacticFormulas L) T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

def toSyntacticProof {T : Theory L} {σ} : T ⊢! σ → (T : SyntacticFormulas L) ⊢! ↑σ := fun b ↦ b

def  ofSyntacticProof {T : Theory L} {σ} : (T : SyntacticFormulas L) ⊢! ↑σ → T ⊢! σ := fun b ↦ b

lemma provable_def {T : Theory L} {σ} : T ⊢ σ ↔ (T : SyntacticFormulas L) ⊢ ↑σ := by rfl

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
  simp
  apply Axiomatized.weakening! ?_ this
  simp [SyntacticFormulas.lMap, Theory.toSyntacticFormulas]
  intro φ hφ
  simp
  exact ⟨(Semiformula.lMap Φ) φ, Set.mem_image_of_mem _ hφ, Eq.symm (lMap_emb φ)⟩

instance {T U : Theory L} : T ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

instance {T U : Theory L} : U ⪯ T + U := Entailment.Axiomatized.weakerThanOfSubset (by simp [add_def])

end Theory

namespace SyntacticFormulas

open Entailment

variable [L.DecidableEq] {𝓢 : SyntacticFormulas L}

def coe_provable_iff_provable_coe {σ : Sentence L} :
    (𝓢 : Theory L) ⊢ σ ↔ 𝓢 ⊢ ↑σ := by
  constructor
  · intro b
    have : 𝓢.toTheory.toSyntacticFormulas ⊢ ↑σ := b
    apply Entailment.StrongCut.cut! ?_ this
    intro τ hτ
    have : ∃ τ' ∈ 𝓢, ∀∀ τ' = τ := by simpa [SyntacticFormulas.toTheory, Theory.toSyntacticFormulas] using hτ
    rcases this with ⟨τ, h, rfl⟩
    exact Derivation.toClose! <| by_axm _ <| by simpa
  · intro b
    apply provable_def.mpr
    apply Entailment.StrongCut.cut! ?_ b
    intro φ hφ
    have : 𝓢.toTheory.toSyntacticFormulas ⊢ ∀∀φ :=
      by_axm _ <| by simpa [SyntacticFormulas.toTheory, Theory.toSyntacticFormulas] using ⟨φ, by simpa, rfl⟩
    exact SyntacticFormulas.close!_iff.mp this

def coe_unprovable_iff_unprovable_coe {σ} :
    (𝓢 : Theory L) ⊬ σ ↔ 𝓢 ⊬ ↑σ := coe_provable_iff_provable_coe.not

def provable_univCl_iff {φ : SyntacticFormula L} :
    (𝓢 : Theory L) ⊢ ∀∀₀ φ ↔ 𝓢 ⊢ φ := Iff.trans coe_provable_iff_provable_coe (by simp [SyntacticFormulas.close!_iff])

def unprovable_univCl_iff {φ : SyntacticFormula L} :
    (𝓢 : Theory L) ⊬ ∀∀₀ φ ↔ 𝓢 ⊬ φ := provable_univCl_iff.not

instance (𝓢 𝓣 : SyntacticFormulas L) [𝓢 ⪯ 𝓣] : 𝓢.toTheory ⪯ 𝓣.toTheory :=
  ⟨fun _ b ↦ coe_provable_iff_provable_coe.mpr <| (inferInstanceAs (𝓢 ⪯ 𝓣)).pbl (coe_provable_iff_provable_coe.mp b)⟩

@[simp] lemma coe_consistent_iff :
    Consistent (𝓢 : Theory L) ↔ Consistent 𝓢 := calc
  Consistent (𝓢 : Theory L) ↔ (𝓢 : Theory L) ⊬ ⊥ := consistent_iff_unprovable_bot
  _                        ↔ 𝓢 ⊬ ⊥             := by simp [coe_unprovable_iff_unprovable_coe]
  _                        ↔ Consistent 𝓢      := consistent_iff_unprovable_bot.symm

instance [Consistent 𝓢] : Consistent (𝓢 : Theory L) := by simp_all

end SyntacticFormulas

end FirstOrder

end LO
