import Foundation.Logic.Calculus
import Foundation.FirstOrder.Basic.Syntax.Rew

namespace LO

namespace FirstOrder

abbrev Sequent (L : Language) := List (SyntacticFormula L)

open Semiformula
variable {L : Language} {T : Theory L}

inductive Derivation (T : Theory L) : Sequent L → Type _
| axL (Γ) {k} (r : L.Rel k) (v) : Derivation T (rel r v :: nrel r v :: Γ)
| verum (Γ)    : Derivation T (⊤ :: Γ)
| or {Γ φ ψ}   : Derivation T (φ :: ψ :: Γ) → Derivation T (φ ⋎ ψ :: Γ)
| and {Γ φ ψ}  : Derivation T (φ :: Γ) → Derivation T (ψ :: Γ) → Derivation T (φ ⋏ ψ :: Γ)
| all {Γ φ}    : Derivation T (Rewriting.free φ :: Γ⁺) → Derivation T ((∀' φ) :: Γ)
| ex {Γ φ} (t) : Derivation T (φ/[t] :: Γ) → Derivation T ((∃' φ) :: Γ)
| wk {Γ Δ}     : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
| cut {Γ φ}    : Derivation T (φ :: Γ) → Derivation T (∼φ :: Γ) → Derivation T Γ
| root {φ}     : φ ∈ T → Derivation T [φ]

instance : OneSided (SyntacticFormula L) (Theory L) := ⟨Derivation⟩

abbrev Derivation₀ (Γ : Sequent L) : Type _ := (∅ : Theory L) ⟹ Γ

abbrev Derivable₀ (Γ : Sequent L) : Prop := (∅ : Theory L) ⟹! Γ

prefix:45 "⊢ᵀ " => Derivation₀

prefix:45 "⊢ᵀ! " => Derivable₀

namespace Derivation

variable {T U : Theory L} {Δ Δ₁ Δ₂ Γ : Sequent L} {φ ψ r : SyntacticFormula L}

open LawfulRewriting
/-
inductive CutRestricted (C : Set (SyntacticFormula L)) : {Δ : Sequent L} → ⊢ᵀ Δ → Prop
| axL (Δ) {k} (r : L.Rel k) (v)                 : CutRestricted C (axL Δ r v)
| verum (Δ)                                     : CutRestricted C (verum Δ)
| or {Δ φ ψ} {d : ⊢ᵀ φ :: ψ :: Δ}               : CutRestricted C d → CutRestricted C d.or
| and {Δ φ ψ} {dp : ⊢ᵀ φ :: Δ} {dq : ⊢ᵀ ψ :: Δ} : CutRestricted C dp → CutRestricted C dq → CutRestricted C (dp.and dq)
| all {Δ φ} {d : ⊢ᵀ Rewriting.free φ :: Δ⁺}       : CutRestricted C d → CutRestricted C d.all
| ex {Δ φ} (t) {d : ⊢ᵀ φ/[t] :: Δ}              : CutRestricted C d → CutRestricted C d.ex
| wk {Δ Γ} {d : ⊢ᵀ Δ} (ss : Δ ⊆ Γ)              : CutRestricted C d → CutRestricted C (d.wk ss)
| cut {Δ φ} {dp : ⊢ᵀ φ :: Δ} {dn : ⊢ᵀ ∼φ :: Δ}  : CutRestricted C dp → CutRestricted C dn → φ ∈ C → CutRestricted C (dp.cut dn)

def CutFree {Δ : Sequent L} (d : ⊢ᵀ Δ) : Prop := CutRestricted ∅ d

namespace CutRestricted
variable {C C' : Set (SyntacticFormula L)} {Δ Γ : Sequent L} {φ ψ : SyntacticFormula L}

attribute [simp] CutRestricted.axL CutRestricted.verum

@[simp] lemma or' {d : ⊢ᵀ φ :: ψ :: Δ} : CutRestricted C (Derivation.or d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.or⟩

@[simp] lemma and' {dp : ⊢ᵀ φ :: Δ} {dq : ⊢ᵀ ψ :: Δ} :
    CutRestricted C (Derivation.and dp dq) ↔ CutRestricted C dp ∧ CutRestricted C dq :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by rintro ⟨dp, dq⟩; exact CutRestricted.and dp dq⟩

@[simp] lemma all' {φ} {d : ⊢ᵀ Rewriting.free φ :: Δ⁺} : CutRestricted C (Derivation.all d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.all⟩

@[simp] lemma ex' {φ} (t) {d : ⊢ᵀ φ/[t] :: Δ} : CutRestricted C (Derivation.ex t d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.ex t⟩

@[simp] lemma wk' {d : ⊢ᵀ Δ} {ss : Δ ⊆ Γ} : CutRestricted C (Derivation.wk d ss) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.wk ss⟩

@[simp] lemma cut' {dp : ⊢ᵀ φ :: Δ} {dn : ⊢ᵀ ∼φ :: Δ} :
    CutRestricted C (Derivation.cut dp dn) ↔ φ ∈ C ∧ CutRestricted C dp ∧ CutRestricted C dn :=
  ⟨by { rintro ⟨⟩; constructor; { assumption }; constructor <;> assumption },
   by rintro ⟨h, dp, dq⟩; exact CutRestricted.cut dp dq h⟩

lemma of_subset (d : ⊢ᵀ Δ) (ss : C ⊆ C') : CutRestricted C d → CutRestricted C' d := by
  induction d <;> try simp [*]
  case and _ _ _ _ ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩
  case or _ _ _ _ ih => exact ih
  case all _ _ _ _ ih => exact ih
  case ex _ _ _ _ ih => exact ih
  case wk _ _ _ _ ih => exact ih
  case cut _ _ _ ihp ihn =>
    intro h hp hn; exact ⟨ss h, ihp hp, ihn hn⟩
  case root h => simp at h

end CutRestricted
-/

def length : {Δ : Sequent L} → T ⟹ Δ → ℕ
  | _, axL _ _ _   => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max (length dp) (length dq)).succ
  | _, all d       => d.length.succ
  | _, ex _ d      => d.length.succ
  | _, wk d _      => d.length.succ
  | _, cut dp dn   => (max (length dp) (length dn)).succ
  | _, root _      => 0

section length

@[simp] lemma length_axL {k} {r : L.Rel k} {v} :
  length (axL (T := T) Δ r v) = 0 := rfl

@[simp] lemma length_verum : length (verum (T := T) Δ) = 0 := rfl

@[simp] lemma length_and {φ ψ} (dp : T ⟹ φ :: Δ) (dq : T ⟹ ψ :: Δ) :
    length (and dp dq) = (max (length dp) (length dq)).succ := rfl

@[simp] lemma length_or {φ ψ} (d : T ⟹ φ :: ψ :: Δ) : length (or d) = d.length.succ := rfl

@[simp] lemma length_all {φ} (d : T ⟹ Rew.free • φ :: Δ⁺) : length (all d) = d.length.succ := rfl

@[simp] lemma length_ex {t} {φ} (d : T ⟹ φ/[t] :: Δ) : length (ex t d) = d.length.succ := rfl

@[simp] lemma length_wk (d : T ⟹ Δ) (h : Δ ⊆ Γ) : length (wk d h) = d.length.succ := rfl

@[simp] lemma length_cut {φ} (dp : T ⟹ φ :: Δ) (dn : T ⟹ (∼φ) :: Δ) :
  length (cut dp dn) = (max (length dp) (length dn)).succ := rfl

end length

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected unsafe def repr : {Δ : Sequent L} → T ⟹ Δ → String
  | _, axL Δ _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, verum Δ       =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, @or _ _ Δ φ ψ d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((φ ⋎ ψ) :: Δ) ++ "$}\n\n"
  | _, @and _ _ Δ φ ψ dp dq =>
      Derivation.repr dp ++
      Derivation.repr dq ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((φ ⋏ ψ) :: Δ) ++ "$}\n\n"
  | _, @all _ _ Δ φ d       =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀' φ) :: Δ) ++ "$}\n\n"
  | _, @ex _ _ Δ φ _ d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃' φ) :: Δ) ++ "$}\n\n"
  | _, @wk _ _ _ Γ d _      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize(wk)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | _, @cut _ _ Δ _ dp dn =>
      Derivation.repr dp ++
      Derivation.repr dn ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, root (φ := φ) _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(ROOT)}\n" ++
      "\\UnaryInfC{$" ++ reprStr φ ++ ", " ++ reprStr (∼φ) ++ "$}\n\n"

unsafe instance : Repr (T ⟹ Δ) where reprPrec d _ := Derivation.repr d

end Repr

protected abbrev cast (d : T ⟹ Δ) (e : Δ = Γ) : T ⟹ Γ := e ▸ d

@[simp] lemma cast_eq (d : T ⟹ Δ) (e : Δ = Δ) : Derivation.cast d e = d := rfl

@[simp] lemma length_cast (d : T ⟹ Δ) (e : Δ = Γ) :
    length (Derivation.cast d e) = length d := by rcases e with rfl; simp[Derivation.cast]

@[simp] lemma length_cast' (d : T ⟹ Δ) (e : Δ = Γ) :
    length (e ▸ d) = length d := by rcases e with rfl; simp[Derivation.cast]

/-
@[simp] lemma CutRestricted.cast {C : Set (SyntacticFormula L)} {Δ Γ : Sequent L} {e : Δ = Γ} {d : ⊢ᵀ Δ} :
    CutRestricted C (Derivation.cast d e) ↔ CutRestricted C d := by rcases e with ⟨rfl⟩; simp

@[simp] lemma CutFree.cast {Δ Γ : Sequent L} {e : Δ = Γ} {d : ⊢ᵀ Δ} :
    CutFree (Derivation.cast d e) ↔ CutFree d := by rcases e with ⟨rfl⟩; simp
-/

alias weakening := wk

def verum' (h : ⊤ ∈ Δ) : T ⟹ Δ := (verum Δ).wk (by simp[h])

def axL' {k} (r : L.Rel k) (v)
    (h : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) : T ⟹ Δ := (axL Δ r v).wk (by simp[h, hn])

def all' {φ} (h : ∀' φ ∈ Δ) (d : T ⟹ Rewriting.free φ :: Δ⁺) : T ⟹ Δ := d.all.wk (by simp [h])

def ex' {φ} (h : ∃' φ ∈ Δ) (t) (d : T ⟹ φ/[t] :: Δ) : T ⟹ Δ := (d.ex t).wk (by simp [h])

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {φ ψ : SyntacticFormula L} : ¬∼φ = φ ⋏ ψ :=
ne_of_ne_complexity (by simp)

def em {φ : SyntacticFormula L} {Δ : Sequent L} (hpos : φ ∈ Δ) (hneg : ∼φ ∈ Δ) : T ⟹ Δ := by
  induction φ using Semiformula.formulaRec generalizing Δ <;> simp at hneg
  case verum           => exact verum' hpos
  case falsum          => exact verum' hneg
  case rel r v         => exact axL' r v hpos hneg
  case nrel r v        => exact axL' r v hneg hpos
  case all φ ih        =>
    have : T ⟹ ∼Rewriting.free φ :: Rewriting.free φ :: Δ⁺ := ih (by simp) (by simp)
    have : T ⟹ (∼Rewriting.shift φ)/[&0] :: Rewriting.free φ :: Δ⁺ :=
      Derivation.cast this (by simp[←LawfulRewriting.comp_smul])
    have : T ⟹ Rewriting.free φ :: Δ⁺ := (ex &0 this).wk
      (by simp; right; simpa using mem_shifts_iff.mpr hneg)
    exact this.all.wk (by simp[hpos])
  case ex φ ih         =>
    have : T ⟹ Rewriting.free φ :: ∼Rewriting.free φ :: Δ⁺ := ih (by simp) (by simp)
    have : T ⟹ (Rewriting.shift φ)/[&0] :: ∼Rewriting.free φ :: Δ⁺ :=
      Derivation.cast this (by simp[←LawfulRewriting.comp_smul])
    have : T ⟹ Rewriting.free (∼φ) :: Δ⁺ := (ex &0 this).wk
      (by simp; right; simpa using mem_shifts_iff.mpr hpos)
    exact this.all.wk (by simp[hneg])
  case and φ ψ ihp ihq =>
    have ihp : T ⟹ φ :: ∼φ :: ∼ψ :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ ψ :: ∼φ :: ∼ψ :: Δ := ihq (by simp) (by simp)
    have : T ⟹ ∼φ :: ∼ψ :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case or φ ψ ihp ihq  =>
    have ihp : T ⟹ ∼φ :: φ :: ψ :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ ∼ψ :: φ :: ψ :: Δ := ihq (by simp) (by simp)
    have : T ⟹ φ :: ψ :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

instance : Tait (SyntacticFormula L) (Theory L) where
  verum := fun _ Δ => verum Δ
  and := fun dp dq => dp.and dq
  or := fun d => d.or
  wk := fun d ss => d.wk ss
  em := fun hp hn => em hp hn

instance : Tait.Cut (SyntacticFormula L) (Theory L) where
  cut {_ _ _ dp dn} := cut dp dn

def provableOfDerivable {φ} (b : T ⟹. φ) : T ⊢ φ := b

def specialize {φ : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    T ⟹ (∀' φ) :: Γ → T ⟹ φ/[t] :: Γ := fun d ↦
  have : T ⟹ ∼φ/[t] :: φ/[t] :: Γ := Tait.em (φ := φ/[t]) (by simp) (by simp)
  have dn : T ⟹ ∼(∀' φ) :: φ/[t] :: Γ := by
    simp only [neg_all, Nat.reduceAdd, Nat.succ_eq_add_one]
    exact Derivation.ex t (by simpa using this)
  have dp : T ⟹ (∀' φ) :: φ/[t] :: Γ :=
    Derivation.wk d (List.cons_subset_cons _ <| by simp)
  Derivation.cut dp dn

def specializes : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → (v : Fin k → SyntacticTerm L) →
    T ⟹ (∀* φ) :: Γ → T ⟹ (φ ⇜ v) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : T ⟹ (∀' (Rew.substs (v ·.succ)).q • φ) :: Γ := by simpa using specializes (φ := ∀' φ) (v ·.succ) b
    Derivation.cast (specialize (v 0) this) (by
      simp [←LawfulRewriting.comp_smul]; congr 2
      ext x <;> simp [Rew.comp_app]
      cases x using Fin.cases <;> simp)

def instances : {k : ℕ} → {φ : SyntacticSemiformula L k} → {Γ : Sequent L} → {v : Fin k → SyntacticTerm L} →
    T ⟹ (φ ⇜ v) :: Γ → T ⟹ (∃* φ) :: Γ
  | 0,     φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : T ⟹ (∃' (Rew.substs (v ·.succ)).q • φ) :: Γ :=
      ex (v 0) <| Derivation.cast b <| by
        unfold Rewriting.substitute; rw [←LawfulRewriting.comp_smul]; congr 2
        ext x <;> simp [Rew.comp_app]
        cases x using Fin.cases <;> simp
    instances (k := k) (v := (v ·.succ)) (Derivation.cast this (by simp))

def allClosureFixitr {φ : SyntacticFormula L} (dp : T ⊢ φ) : (m : ℕ) → T ⊢ ∀* (@Rew.fixitr L 0 m) • φ
  | 0     => by simpa
  | m + 1 => by
    simp only [LawfulRewriting.allClosure_fixitr, Nat.reduceAdd]
    apply all; simpa using allClosureFixitr dp m

def toClose (b : T ⊢ φ) : T ⊢ ∀∀φ := allClosureFixitr b φ.fvSup

def toClose! (b : T ⊢! φ) : T ⊢! ∀∀φ := ⟨toClose b.get⟩

def rewrite₁ (b : T ⊢ φ) (f : ℕ → SyntacticTerm L) : T ⊢ (Rew.rewrite f) • φ :=
  Derivation.cast (specializes (fun x ↦ f x) (allClosureFixitr b φ.fvSup)) (by simp)

def rewrite {Δ} : T ⟹ Δ → ∀ (f : ℕ → SyntacticTerm L), T ⟹ Δ.map fun φ ↦ Rew.rewrite f • φ
  | axL Δ r v,            f => by simp[rew_rel, rew_nrel]; exact axL _ _ _
  | verum Δ,              f => Derivation.cast (verum (Δ.map fun φ ↦ Rew.rewrite f • φ)) (by simp)
  | @or _ _ Δ φ ψ d,      f =>
    have : T ⟹ Rew.rewrite f • φ ⋎ Rew.rewrite f • ψ :: Δ.map fun φ ↦ Rew.rewrite f • φ :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq, f =>
    have : T ⟹ Rew.rewrite f • φ ⋏ Rew.rewrite f • ψ :: Δ.map fun φ ↦ Rew.rewrite f • φ :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d,       f =>
    have : T ⟹ ((Rewriting.free φ) :: Δ⁺).map fun φ ↦ Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) • φ :=
      rewrite d (&0 :>ₙ fun x => Rew.shift (f x))
    have : T ⟹ (∀' Rew.rewrite (Rew.bShift ∘ f) • φ) :: Δ.map fun φ ↦ Rew.rewrite f • φ :=
      all (Derivation.cast this (by simp [free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Finset.image_image, Function.comp_def]))
    Derivation.cast this (by simp[Rew.q_rewrite])
  | @ex _ _ Δ φ t d,      f =>
    have : T ⟹ (φ/[t] :: Δ).map fun φ ↦ Rew.rewrite f • φ := rewrite d f
    have : T ⟹ (∃' Rew.rewrite (Rew.bShift ∘ f) • φ) :: Δ.map fun φ ↦ Rew.rewrite f • φ :=
      ex (Rew.rewrite f t) (Derivation.cast this (by simp[rewrite_subst_eq]))
    Derivation.cast this (by simp[Rew.q_rewrite])
  | @wk _ _ Δ Γ d ss,     f => (rewrite d f).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn,    f =>
    have dΔ : T ⟹ (Rew.rewrite f • φ) :: Δ.map fun φ ↦ Rew.rewrite f • φ := Derivation.cast (rewrite d f) (by simp)
    have dΓ : T ⟹ ∼(Rew.rewrite f • φ) :: Δ.map fun φ ↦ Rew.rewrite f • φ := Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΔ dΓ) (by simp)
  | root h,               f => rewrite₁ (root h) f

protected def map {Δ : Sequent L} (d : T ⟹ Δ) (f : ℕ → ℕ) :
    T ⟹ Δ.map fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 f • φ := rewrite d (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : T ⟹ Δ) : T ⟹ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by simp only [Rewriting.shifts, List.map_inj_left]; intro _ _; rfl)

/-
lemma CutRestricted.rewrite {C : Set (SyntacticFormula L)}
    (hC : ∀ f : ℕ → SyntacticTerm L, ∀ φ, φ ∈ C → Rew.rewrite f • φ ∈ C)
    {Δ : Sequent L} (f : ℕ → SyntacticTerm L) {d : ⟹ Δ} :
    CutRestricted C d → CutRestricted C (rewrite d f) := by
  induction d generalizing f <;> simp[-List.map_cons, Derivation.rewrite, *]
  case axL _ _ _ _ => simp[Rew.rel, Rew.nrel]
  case and _ _ _ ihp ihq => intro hp hq; exact ⟨ihp _ hp, ihq _ hq⟩
  case or _ _ ih => intro h; exact ih _ h
  case all _ _ _ ih =>
    rw [CutRestricted.cast, CutRestricted.all', CutRestricted.cast]
    exact ih _; simp
  case ex _ _ _ ih =>
    rw [CutRestricted.cast, CutRestricted.ex', CutRestricted.cast]
    exact ih _; simp
  case wk _ _ ih => intro h; exact ih _ h
  case cut _ _ ih ihn => intro hp h hn; exact ⟨hC _ _ hp, ih _ h, ihn _ hn⟩

@[simp] lemma length_rewrite (d : T ⟹ Δ) (f : ℕ → SyntacticTerm L) :
    length (rewrite d f) = length d := by
  induction d generalizing f <;> simp[*, Derivation.rewrite, -List.map_cons]
  case axL => simp[Rew.rel, Rew.nrel]
  case all => simp [Rew.q_rewrite, *]
  case ex => simp [Rew.q_rewrite, *]
  case root => simp []

-/

def trans (F : U ⊢* T) : {Γ : Sequent L} → T ⟹ Γ → U ⟹ Γ
  | _, axL Γ R v => axL Γ R v
  | _, verum Γ   => verum Γ
  | _, and d₁ d₂ => and (trans F d₁) (trans F d₂)
  | _, or d      => or (trans F d)
  | _, all d     => all (trans F d)
  | _, ex t d    => ex t (trans F d)
  | _, wk d ss   => wk (trans F d) ss
  | _, cut d₁ d₂ => cut (trans F d₁) (trans F d₂)
  | _, root h    => F h

instance : Tait.Axiomatized (SyntacticFormula L) (Theory L) where
  root {_ _ h} := root h
  trans {_ _ _ F d} := trans (fun h ↦ F _ h) d

variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

private def not_close' (φ) : T ⟹ [∼(∀∀φ), φ] :=
  have : T ⟹ [∃* ∼(@Rew.fixitr L 0 (fvSup φ) • φ), φ] := instances (v := fun x ↦ &x) (em (φ := φ) (by simp) (by simp))
  Derivation.cast this (by simp [close])

def invClose (b : T ⊢ ∀∀φ) : T ⊢ φ := cut (wk b (by simp)) (not_close' φ)

def invClose! (b : T ⊢! ∀∀φ) : T ⊢! φ := ⟨invClose b.get⟩

private def deductionAux : {Γ : Sequent L} → T ⟹ Γ → T \ {φ} ⟹ ∼(∀∀φ) :: Γ
  | _, axL Γ R v       => Tait.wkTail <| axL Γ R v
  | _, verum Γ         => Tait.wkTail <| verum Γ
  | _, and d₁ d₂       => Tait.rotate₁ <| and (Tait.rotate₁ (deductionAux d₁)) (Tait.rotate₁ (deductionAux d₂))
  | _, or d            => Tait.rotate₁ <| or (Tait.rotate₂ (deductionAux d))
  | _, all d           => Tait.rotate₁ <| all (Derivation.cast (Tait.rotate₁ (deductionAux d)) (by simp))
  | _, ex t d          => Tait.rotate₁ <| ex t <| Tait.rotate₁ (deductionAux d)
  | _, wk d ss         => wk (deductionAux d) (by simp [List.subset_cons_of_subset _ ss])
  | _, cut d₁ d₂       => (Tait.rotate₁ <| deductionAux d₁).cut (Tait.rotate₁ <| deductionAux d₂)
  | _, root (φ := ψ) h => if hq : φ = ψ then Derivation.cast (not_close' φ) (by simp [hq]) else
    have : T \ {φ} ⟹. ψ := root (by simp [h, Ne.symm hq])
    wk this (by simp)

def deduction (d : insert φ T ⟹ Γ) : T ⟹ ∼(∀∀φ) :: Γ := Tait.ofAxiomSubset (by intro x; simp; tauto) (deductionAux d (φ := φ))

def provable_iff_inconsistent : T ⊢! φ ↔ System.Inconsistent (insert (∼∀∀φ) T) := by
  constructor
  · rintro b
    exact System.inconsistent_of_provable_of_unprovable
      (System.wk! (by simp) (toClose! b)) (System.by_axm _ (by simp))
  · intro h
    rcases Tait.inconsistent_iff_provable.mp h with ⟨d⟩
    have : T ⊢ ∀∀φ :=  Derivation.cast (deduction d) (by rw [close_eq_self_of (∼∀∀φ) (by simp)]; simp)
    exact ⟨invClose this⟩

def unprovable_iff_consistent : T ⊬ φ ↔ System.Consistent (insert (∼∀∀φ) T) := by
  simp [←System.not_inconsistent_iff_consistent, ←provable_iff_inconsistent]

section Hom

variable {L₁ : Language} {L₂ : Language} {T₁ : Theory L₁} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) : ∀ {Δ}, T₁ ⟹ Δ → T₁.lMap Φ ⟹ Δ.map (.lMap Φ)
  | _, axL Δ r v          =>
      by simp[Semiformula.lMap_rel, Semiformula.lMap_nrel]; exact axL _ _ _
  | _, verum Δ            => by simpa using verum _
  | _, @or _ _ Δ φ ψ d      => by
      have : T₁.lMap Φ ⟹ (.lMap Φ φ ⋎ .lMap Φ ψ :: Δ.map (.lMap Φ) : Sequent L₂) :=
        or (by simpa using lMap Φ d)
      exact Derivation.cast this (by simp)
  | _, @and _ _ Δ φ ψ dp dq =>
      have : T₁.lMap Φ ⟹ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
      Derivation.cast this (by simp)
  | _, @all _ _ Δ φ d       =>
      have : T₁.lMap Φ ⟹ ((∀' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        all (Derivation.cast (lMap Φ d) (by simp[←Semiformula.lMap_free, shifts_image]))
      Derivation.cast this (by simp)
  | _, @ex _ _ Δ φ t d      =>
      have : T₁.lMap Φ ⟹ ((∃' .lMap Φ φ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        ex (Semiterm.lMap Φ t)
          (Derivation.cast (lMap Φ d) (by simp[Semiformula.lMap_substs, Matrix.constant_eq_singleton]))
      Derivation.cast this (by simp)
  | _, @wk _ _ Δ Γ d ss     => (lMap Φ d).wk (List.map_subset _ ss)
  | _, @cut _ _ Δ φ d dn    =>
      have : T₁.lMap Φ ⟹ (Δ.map (.lMap Φ) : Sequent L₂) :=
        cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
      Derivation.cast this (by simp[Finset.image_union])
  | _, root h               => root (Set.mem_image_of_mem _ h)

/-
def _root_.LO.FirstOrder.Derivation₀.lMap (Φ : L₁ →ᵥ L₂) (d : ⊢ᵀ Δ₁) : ⊢ᵀ Δ₁.map (.lMap Φ) := by simpa [Theory.lMap] using Derivation.lMap Φ d

lemma CutRestricted.lMap {C : Set (SyntacticFormula L₂)} {Δ : Sequent L₁} (Φ : L₁ →ᵥ L₂) (d : ⊢ᵀ Δ) :
    CutRestricted C (d.lMap Φ) ↔ CutRestricted (.lMap Φ ⁻¹' C) d := by
  induction d <;> simp [Derivation.lMap, Derivation₀.lMap, *]

@[simp] lemma CutFree.lMap {Δ : Sequent L₁} (Φ : L₁ →ᵥ L₂) (d : ⟹ Δ) :
    CutFree (lMap Φ d) ↔ CutFree d := by simp[CutFree, CutRestricted.lMap]
-/

lemma inconsistent_lMap (Φ : L₁ →ᵥ L₂) : System.Inconsistent T₁ → System.Inconsistent (T₁.lMap Φ) := by
  simp [System.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨by simpa using lMap Φ b⟩

end Hom

omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

private lemma map_subst_eq_free (φ : SyntacticSemiformula L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) • (φ/[&m] : SyntacticFormula L) = Rewriting.free φ := by
  simp[←LawfulRewriting.comp_smul];
  exact Semiformula.rew_eq_of_funEqOn (by simp[Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp[Rew.comp_app]; rintro rfl; contradiction)

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1) • φ) = Δ⁺ := by
  apply List.map_congr_left
  intro φ hp; exact rew_eq_of_funEqOn₀ (by intro x hx; simp; rintro rfl; have := h φ hp; contradiction)

def genelalizeByNewver {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : T ⟹ φ/[&m] :: Δ) : T ⟹ (∀' φ) :: Δ := by
  have : T ⟹ (Rewriting.free φ) :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
    (by simp[map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : T ⟹ v.map (φ/[·]) ++ Γ) : T ⟹ (∃' φ) :: Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃' φ) :: Γ) ((ex t h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : SyntacticSemiformula L 1)
  (h : T ⟹ (∃' φ) :: v.map (φ/[·]) ++ Γ) : T ⟹ (∃' φ) :: Γ :=
  (exOfInstances (Γ := (∃' φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

end Derivation

namespace Theory

instance {T U : Theory L} : T ≼ T + U := System.Axiomatized.subtheoryOfSubset (by simp [add_def])

instance {T U : Theory L} : U ≼ T + U := System.Axiomatized.subtheoryOfSubset (by simp [add_def])

end Theory

variable (L)

/--
  An auxiliary structure to provide systems of provability of sentence.
-/
structure Theory.Alt where
  thy : Theory L

variable {L}

alias Theory.alt := Theory.Alt.mk

instance : System (Sentence L) (Theory.Alt L) := ⟨fun T σ ↦ T.thy ⊢ ↑σ⟩

@[simp] lemma Theory.alt_thy (T : Theory L) : T.alt.thy = T := rfl

section

abbrev Provable₀ (T : Theory L) (σ : Sentence L) : Prop := T.alt ⊢! σ

infix:45 " ⊢!. " => Provable₀

abbrev Unprovable₀ (T : Theory L) (σ : Sentence L) : Prop := T.alt ⊬ σ

infix:45 " ⊬. " => Unprovable₀

instance (T : Theory.Alt L) : System.Classical T := System.Classical.ofEquiv T.thy T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)

variable {T : Theory L} {σ : Sentence L}

lemma provable₀_iff : T ⊢!. σ ↔ T ⊢! ↑σ := iff_of_eq rfl

lemma unprovable₀_iff : T ⊬. σ ↔ T ⊬ ↑σ := iff_of_eq rfl

end

end FirstOrder

end LO
