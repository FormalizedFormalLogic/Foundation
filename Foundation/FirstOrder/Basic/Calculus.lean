module

/- public import Foundation.Logic.Calculus -/
public import Foundation.Logic.Calculus
public import Foundation.Propositional.Entailment.AxiomEFQ
public import Foundation.FirstOrder.Basic.Syntax.Rew
public import Mathlib.Data.List.MinMax

/-! # One-sided sequent calculus for first-order classical logic -/

@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := List (Proposition L)

namespace Sequent

open Semiformula

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : Proposition L} {Γ : Sequent L} (h : φ ∈ Γ) : ¬FVar? φ Γ.newVar :=
  not_fvar?_of_lt_fvSup φ (by simpa [newVar] using List.le_max_of_le (List.mem_map_of_mem h) (by simp))

@[simp] lemma lcHom_comm {Γ : List (Formula L ξ)} (f : Formula L ξ →ˡᶜ Proposition L) :
    (∼Γ).map f = ∼Γ.map f := by simp [List.tilde_def]

def IsClosed (Γ : Sequent L) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

def embed (Γ : List (Sentence L)) : Sequent L := List.map Rewriting.emb Γ

@[simp] lemma embed_nil : embed ([] : List (Sentence L)) = [] := rfl

@[simp] lemma embed_cons {φ : Sentence L} {Γ : List (Sentence L)} :
    embed (φ :: Γ) = (↑φ :: embed Γ) := rfl

@[simp] lemma embed_shift (Γ : List (Sentence L)) :
    (embed Γ)⁺ = embed Γ := by
  simp [embed, Rewriting.shifts]

end Sequent

/-! ## Derivation for one-sided $\mathbf{LK}$ -/

/-- Derivation for one-sided $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| identity (r : L.Rel k) (v) : Derivation [.rel r v, .nrel r v]
| cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
| wk : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation [⊤]
| or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
| and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
| all : Derivation (φ.free :: Γ⁺) → Derivation ((∀⁰ φ) :: Γ)
| exs : Derivation (φ/[t] :: Γ) → Derivation ((∃⁰ φ) :: Γ)

prefix:45 "⊢ᴸᴷ¹ " => Derivation

namespace Derivation

open Rewriting LawfulSyntacticRewriting

def height {Δ : Sequent L} : ⊢ᴸᴷ¹ Δ → ℕ
  | identity _ _ => 0
  |    cut dp dn => max dp.height dn.height + 1
  |       wk d _ => d.height + 1
  |        verum => 0
  |         or d => d.height + 1
  |    and dp dq => max (height dp) (height dq) + 1
  |        all d => d.height + 1
  |        exs d => d.height + 1

section height

@[simp] lemma height_id {k} {r : L.Rel k} {v} :
  height (identity r v) = 0 := rfl

@[simp] lemma height_cut {φ} (dp : ⊢ᴸᴷ¹ φ :: Δ) (dn : ⊢ᴸᴷ¹ (∼φ) :: Δ) :
  height (cut dp dn) = (max (height dp) (height dn)).succ := rfl

@[simp] lemma height_wk (d : ⊢ᴸᴷ¹ Δ) (h : Δ ⊆ Γ) : height (wk d h) = d.height.succ := rfl

@[simp] lemma height_verum : height (verum : ⊢ᴸᴷ¹ ([⊤] : Sequent L)) = 0 := rfl

@[simp] lemma height_and {φ ψ} (dp : ⊢ᴸᴷ¹ φ :: Δ) (dq : ⊢ᴸᴷ¹ ψ :: Δ) :
    height (and dp dq) = (max (height dp) (height dq)).succ := rfl

@[simp] lemma height_or {φ ψ} (d : ⊢ᴸᴷ¹ φ :: ψ :: Δ) : height (or d) = d.height.succ := rfl

@[simp] lemma height_all {φ : Semiproposition L 1} (d : ⊢ᴸᴷ¹ φ.free :: Δ⁺) : height (all d) = d.height.succ := rfl

@[simp] lemma height_exs {t} {φ} (d : ⊢ᴸᴷ¹ φ/[t] :: Δ) : height (exs d) = d.height.succ := rfl

end height

protected abbrev cast (d : ⊢ᴸᴷ¹ Δ) (e : Δ = Γ := by simp) : ⊢ᴸᴷ¹ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴸᴷ¹ Δ) (e : Δ = Γ) :
    height (Derivation.cast d e) = height d := by rcases e with rfl; simp [Derivation.cast]

def weakening (d : ⊢ᴸᴷ¹ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ¹ Γ := wk d h

def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ := verum.wk (by simp [h])

def identity' (r : L.Rel k) (v) (hpos : Semiformula.rel r v ∈ Δ := by simp) (hneg : Semiformula.nrel r v ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ :=
  (identity r v).wk (by simp [hpos, hneg])

def tensor {φ ψ} (dφ : ⊢ᴸᴷ¹ φ :: Γ) (dψ : ⊢ᴸᴷ¹ ψ :: Δ) : ⊢ᴸᴷ¹ φ ⋏ ψ :: (Γ ++ Δ) := and dφ.weakening dψ.weakening

def rotate (d : ⊢ᴸᴷ¹ φ :: Γ) : ⊢ᴸᴷ¹ Γ ++ [φ] := d.weakening

def eta : (φ : Proposition L) → ⊢ᴸᴷ¹ [φ, ∼φ]
  | .rel R v | .nrel R v => identity' R v
  | ⊤ | ⊥ => top
  | φ ⋏ ψ => ((eta φ).tensor (eta ψ)).rotate.or.rotate
  | φ ⋎ ψ => ((eta φ).rotate.tensor (eta ψ).rotate).rotate.or
  | ∀⁰ φ =>
    have : ⊢ᴸᴷ¹ [(∼φ.shift)/[&0], φ.free] := (eta φ.free).rotate.cast
    have : ⊢ᴸᴷ¹ φ.free :: [∃⁰ ∼φ]⁺ := this.exs.rotate.cast
    this.all
  | ∃⁰ φ =>
    have : ⊢ᴸᴷ¹ [(φ.shift)/[&0], (∼φ).free] := (eta φ.free).cast
    have : ⊢ᴸᴷ¹ (∼φ).free :: [∃⁰ φ]⁺ := this.exs.rotate.cast
    this.all.rotate
  termination_by φ => φ.complexity

def close (φ : Proposition L) (hp : φ ∈ Δ := by simp) (hn : ∼φ ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ :=
  eta φ |>.weakening (by simp [hp, hn])

lemma of_isClosed {Γ : Sequent L} (h : Γ.IsClosed) : Nonempty (⊢ᴸᴷ¹ Γ) := by
  rcases h with ⟨φ, hp, hn⟩
  exact ⟨close φ hp hn⟩

instance : OneSidedLK (Derivation (L := L)) where
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  wk d ss := d.wk ss
  identity φ := eta φ

instance : OneSidedLK.Cut (Derivation (L := L)) where
  cut dp dn := cut dp dn

def rewrite {Γ} (f : ℕ → SyntacticTerm L) : ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (Rew.rewrite f ▹ ·)
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) d₁ d₂ =>
    have d₁ : ⊢ᴸᴷ¹ Rew.rewrite f ▹ φ :: Γ.map (app (Rew.rewrite f)) := (d₁.rewrite f).cast
    have d₂ : ⊢ᴸᴷ¹ ∼(Rew.rewrite f ▹ φ) :: Δ.map (app (Rew.rewrite f)) := (d₂.rewrite f).cast
    d₁.cut d₂ |>.cast
  | wk d ss => d.rewrite f |>.wk (List.map_subset _ ss)
  | verum => verum
  | or d => (d.rewrite f).or
  | and d₁ d₂ => (d₁.rewrite f).and (d₂.rewrite f)
  | all (φ := φ) (Γ := Γ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have : ⊢ᴸᴷ¹ (φ.free :: Γ⁺).map (Rew.rewrite g ▹ ·) := d.rewrite g
    have : ⊢ᴸᴷ¹ (∀⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map (Rew.rewrite f ▹ ·) :=
      all (Derivation.cast this (by simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | exs (φ := φ) (Γ := Γ) (t := t) d =>
    have : ⊢ᴸᴷ¹ (φ/[t] :: Γ).map (Rew.rewrite f ▹ ·) := d.rewrite f
    have : ⊢ᴸᴷ¹ (∃⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map (Rew.rewrite f ▹ ·) :=
      exs (t := Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])

protected def map {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) (f : ℕ → ℕ) :
    ⊢ᴸᴷ¹ Δ.map (Rew.rewriteMap f ▹ ·) := d.rewrite (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) : ⊢ᴸᴷ¹ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by rfl)

section Hom

variable {L₁ : Language} {L₂ : Language} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (Proposition L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Γ} : ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (.lMap Φ)
  | identity r v =>
    .cast (identity (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Function.comp_def])
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn =>
    have : ⊢ᴸᴷ¹ (Γ.map (.lMap Φ) ++ Δ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp)
  | wk (Δ := Δ) (Γ := Γ) d ss => (lMap Φ d).wk (List.map_subset _ ss)
  | verum => by simpa using verum
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    have : ⊢ᴸᴷ¹ (.lMap Φ φ ⋎ .lMap Φ ψ :: Γ.map (.lMap Φ) : Sequent L₂) :=
      or (by simpa using lMap Φ d)
    exact Derivation.cast this (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    have : ⊢ᴸᴷ¹ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    have : ⊢ᴸᴷ¹ ((∀⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [←Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    have : ⊢ᴸᴷ¹ ((∃⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      exs (t := Semiterm.lMap Φ t)
        (.cast (lMap Φ d) (by simp [Semiformula.lMap_subst]))
    Derivation.cast this (by simp)

end Hom

private lemma map_subst_eq_free (φ : Semiproposition L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) ▹ (φ/[&m] : Proposition L) = Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app])
    (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Δ⁺ := by
  apply List.map_congr_left
  intro φ hp; exact Semiformula.rew_eq_of_funEqOn₀
    (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])

def genelalizeByNewver {φ : Semiproposition L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᴸᴷ¹ φ/[&m] :: Δ) : ⊢ᴸᴷ¹ (∀⁰ φ) :: Δ := by
  have : ⊢ᴸᴷ¹ φ.free :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x ↦ if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
  (h : ⊢ᴸᴷ¹ v.map (φ/[·]) ++ Γ) : ⊢ᴸᴷ¹ (∃⁰ φ) :: Γ := by
  induction' v with t v ih generalizing Γ
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃⁰ φ) :: Γ) ((exs h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
  (h : ⊢ᴸᴷ¹ (∃⁰ φ) :: v.map (φ/[·]) ++ Γ) : ⊢ᴸᴷ¹ (∃⁰ φ) :: Γ :=
  (exOfInstances (Γ := (∃⁰ φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

def allNvar {Δ : Sequent L} {φ} (h : ∀⁰ φ ∈ Δ) : ⊢ᴸᴷ¹ φ/[&Δ.newVar] :: Δ → ⊢ᴸᴷ¹ Δ := fun b ↦
  let b : ⊢ᴸᴷ¹ (∀⁰ φ) :: Δ :=
    b.genelalizeByNewver (by simpa [Semiformula.FVar?] using Sequent.not_fvar?_newVar h) (fun _ ↦ Sequent.not_fvar?_newVar)
  b.wk (by simp [h])

end Derivation

/-! ## Classical proof system -/

inductive LK.Symbol (L : Language)
  | symbol

notation "𝐋𝐊¹" => LK.Symbol.symbol

notation "𝐋𝐊¹[" L "]" => LK.Symbol.symbol (L := L)

abbrev LK (φ : Proposition L) := ⊢ᴸᴷ¹ [φ]

instance : Entailment (LK.Symbol L) (Proposition L) where
  Prf _ := LK

namespace LK

lemma def_eq (φ : Proposition L) : (𝐋𝐊¹ ⊢! φ) = (⊢ᴸᴷ¹ [φ]) := rfl

lemma provable_def (φ : Proposition L) : 𝐋𝐊¹ ⊢ φ ↔ Nonempty (⊢ᴸᴷ¹ [φ]) := by rfl

lemma unprovable_def (φ : Proposition L) : 𝐋𝐊¹ ⊬ φ ↔ IsEmpty (⊢ᴸᴷ¹ [φ]) := by
  unfold Entailment.Unprovable; simp [provable_def]

instance : OneSidedLK.PrincipalEntailment (Derivation (L := L)) (𝐋𝐊¹ : LK.Symbol L) where
  equiv := Equiv.refl _

instance classical : Entailment.Cl (𝐋𝐊¹ : LK.Symbol L) := inferInstance

lemma all (φ : Semiproposition L 1) : 𝐋𝐊¹ ⊢ φ.free → 𝐋𝐊¹ ⊢ ∀⁰ φ := fun h ↦ ⟨Derivation.all h.get⟩

lemma allClosure_fixitr {φ : Proposition L} (dp : 𝐋𝐊¹ ⊢ φ) : (m : ℕ) → 𝐋𝐊¹ ⊢ ∀⁰* Rew.fixitr 0 m ▹ φ
  |     0 => by simpa
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    apply all; simpa using allClosure_fixitr dp m

lemma univCl' {φ : Proposition L} (b : 𝐋𝐊¹ ⊢ φ) : 𝐋𝐊¹ ⊢ φ.univCl' := allClosure_fixitr b φ.fvSup

end LK

structure Theory.LK (T : Theory L) (σ : Sentence L) where
  axioms : List (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation Rewriting.emb (σ :: ∼axioms)

namespace Theory

instance : Entailment (Theory L) (Sentence L) where
  Prf := Theory.LK

variable {T : Theory L}

attribute [simp] LK.axioms_mem

instance : Entailment.Compact (Theory L) where
  core b := {φ | φ ∈ b.axioms}
  corePrf b := ⟨b.axioms, by simp, b.derivation⟩
  core_finite b := by simp [AdjunctiveSet.Finite, AdjunctiveSet.set]
  core_subset b := by simpa [AdjunctiveSet.subset_iff] using b.axioms_mem

instance : OneSidedLK.ContextualEntailment (OneSidedLK.Pullback Derivation Rewriting.emb) (Theory L) where
  equiv {T φ} :=
  { toFun b := ⟨⟨b.axioms, b.axioms_mem⟩, b.derivation⟩
    invFun := fun ⟨⟨Γ, hΓ⟩, d⟩ ↦ ⟨Γ, hΓ, d⟩ }

instance : Entailment.Cl T := OneSidedLK.ContextualEntailment.cl T

lemma weakerThan_of_le {T U : Theory L} (h : T ⊆ U) : T ⪯ U := Entailment.Axiomatized.weakerThanOfSubset h

instance (T U : Theory L) : T ⪯ T ∪ U := weakerThan_of_le (by simp)

instance (T U : Theory L) : U ⪯ T ∪ U := weakerThan_of_le (by simp)

lemma provable_iff :
    T ⊢ φ ↔ ∃ Γ : List (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Nonempty (⊢ᴸᴷ¹ φ :: ∼Sequent.embed Γ) := by
  simpa using OneSidedLK.ContextualEntailment.provable_iff (𝓢 := T) (φ := φ)

lemma inconsistent_iff :
    Entailment.Inconsistent T ↔ ∃ Γ : List (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Nonempty (⊢ᴸᴷ¹ ∼Sequent.embed Γ) := by
  simpa using OneSidedLK.ContextualEntailment.inconsistent_iff (𝓢 := T)

open Entailment Derivation

@[simp] lemma empty_provable_iff_eprovable :
    (∅ : Theory L) ⊢ φ ↔ 𝐋𝐊¹ ⊢ (φ : Proposition L) := by
  simpa using OneSidedLK.ContextualEntailment.empty_provable_iff_eprovable
    (S := Theory L)
    (𝓟 := pullback 𝐋𝐊¹[L] (Rewriting.emb : Sentence L → Proposition L))
    (φ := φ)

lemma iff_context {T : Theory L} :
    T ⊢ φ ↔ T *⊢[pullback 𝐋𝐊¹[L] (Rewriting.emb : _ → Proposition L)] φ :=
  OneSidedLK.ContextualEntailment.iff_context

end Theory

namespace Theory

open Entailment Derivation

lemma of_LK_provable {T : Theory L} {φ : Sentence L} : 𝐋𝐊¹ ⊢ (φ : Proposition L) → T ⊢ φ := fun h ↦
  have : pullback 𝐋𝐊¹[L] (Rewriting.emb : Sentence L → Proposition L) ⊢ φ := h
  OneSidedLK.ContextualEntailment.of_principal_provable this

open Classical in
noncomputable instance : Entailment.Deduction (Theory L) :=
  OneSidedLK.ContextualEntailment.deduction (pullback 𝐋𝐊¹[L] (Rewriting.emb : Sentence L → Proposition L))

end Theory

/-! ### Theory -/

def Theory.theory (T : Theory L) : Theory L := {σ | T ⊢ ↑σ}

@[simp] lemma Theory.mem_theory {T : Theory L} :
    σ ∈ T.theory ↔ T ⊢ ↑σ := by simp [Theory.theory]

end FirstOrder

end LO

end
