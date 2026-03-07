module

/- public import Foundation.Logic.Calculus -/
public import Foundation.Logic.Calculus
public import Foundation.Propositional.Entailment.AxiomEFQ
public import Foundation.FirstOrder.Basic.Syntax.Schema
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

@[simp] lemma rew_neg_comm {Γ : Sequent L} (ω : Rew L ℕ 0 ℕ 0) :
    (∼Γ).map (ω ▹ ·) = ∼Γ.map (ω ▹ ·) := by simp [List.tilde_def]

end Sequent

/-! ## Derivation for one-sided $\mathbf{LK}$ -/

/-- Derivation for one-sided $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| protected id (r : L.Rel k) (v) : Derivation [.rel r v, .nrel r v]
| cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
| wk : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation [⊤]
| or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
| and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
| all : Derivation (φ.free :: Γ⁺) → Derivation ((∀⁰ φ) :: Γ)
| exs : Derivation (φ/[t] :: Γ) → Derivation ((∃⁰ φ) :: Γ)

scoped prefix:45 "⊢ᴷ " => Derivation

namespace Derivation

open Rewriting LawfulSyntacticRewriting

def height {Δ : Sequent L} : ⊢ᴷ Δ → ℕ
  |   .id _ _ => 0
  | cut dp dn => (max (height dp) (height dn)).succ
  |    wk d _ => d.height.succ
  |     verum => 0
  |      or d => d.height.succ
  | and dp dq => (max (height dp) (height dq)).succ
  |     all d => d.height.succ
  |     exs d => d.height.succ

section height

@[simp] lemma height_id {k} {r : L.Rel k} {v} :
  height (Derivation.id r v) = 0 := rfl

@[simp] lemma height_cut {φ} (dp : ⊢ᴷ φ :: Δ) (dn : ⊢ᴷ (∼φ) :: Δ) :
  height (cut dp dn) = (max (height dp) (height dn)).succ := rfl

@[simp] lemma height_wk (d : ⊢ᴷ Δ) (h : Δ ⊆ Γ) : height (wk d h) = d.height.succ := rfl

@[simp] lemma height_verum : height (verum : ⊢ᴷ ([⊤] : Sequent L)) = 0 := rfl

@[simp] lemma height_and {φ ψ} (dp : ⊢ᴷ φ :: Δ) (dq : ⊢ᴷ ψ :: Δ) :
    height (and dp dq) = (max (height dp) (height dq)).succ := rfl

@[simp] lemma height_or {φ ψ} (d : ⊢ᴷ φ :: ψ :: Δ) : height (or d) = d.height.succ := rfl

@[simp] lemma height_all {φ : Semiproposition L 1} (d : ⊢ᴷ φ.free :: Δ⁺) : height (all d) = d.height.succ := rfl

@[simp] lemma height_exs {t} {φ} (d : ⊢ᴷ φ/[t] :: Δ) : height (exs d) = d.height.succ := rfl

end height

protected abbrev cast (d : ⊢ᴷ Δ) (e : Δ = Γ := by simp) : ⊢ᴷ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴷ Δ) (e : Δ = Γ) :
    height (Derivation.cast d e) = height d := by rcases e with rfl; simp [Derivation.cast]

def weakening (d : ⊢ᴷ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴷ Γ := wk d h

def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴷ Δ := verum.wk (by simp [h])

def id' (r : L.Rel k) (v) (hpos : Semiformula.rel r v ∈ Δ := by simp) (hneg : Semiformula.nrel r v ∈ Δ := by simp) : ⊢ᴷ Δ :=
  (Derivation.id r v).wk (by simp [hpos, hneg])

def tensor {φ ψ} (dφ : ⊢ᴷ φ :: Γ) (dψ : ⊢ᴷ ψ :: Δ) : ⊢ᴷ φ ⋏ ψ :: (Γ ++ Δ) := and dφ.weakening dψ.weakening

def rotate (d : ⊢ᴷ φ :: Γ) : ⊢ᴷ Γ ++ [φ] := d.weakening

def identity : (φ : Proposition L) → ⊢ᴷ [φ, ∼φ]
  | .rel R v | .nrel R v => id' R v
  | ⊤ | ⊥ => top
  | φ ⋏ ψ => ((identity φ).tensor (identity ψ)).rotate.or.rotate
  | φ ⋎ ψ => ((identity φ).rotate.tensor (identity ψ).rotate).rotate.or
  | ∀⁰ φ =>
    have : ⊢ᴷ [(∼φ.shift)/[&0], φ.free] := (identity φ.free).rotate.cast
    have : ⊢ᴷ φ.free :: [∃⁰ ∼φ]⁺ := this.exs.rotate.cast
    this.all
  | ∃⁰ φ =>
    have : ⊢ᴷ [(φ.shift)/[&0], (∼φ).free] := (identity φ.free).cast
    have : ⊢ᴷ (∼φ).free :: [∃⁰ φ]⁺ := this.exs.rotate.cast
    this.all.rotate
  termination_by φ => φ.complexity

def close (φ : Proposition L) (hp : φ ∈ Δ := by simp) (hn : ∼φ ∈ Δ := by simp) : ⊢ᴷ Δ :=
  identity φ |>.weakening (by simp [hp, hn])

instance : OneSidedLK (Derivation (L := L)) where
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  wk d ss := d.wk ss
  identity φ := identity φ

instance : OneSidedLK.Cut (Derivation (L := L)) where
  cut dp dn := cut dp dn

def rewrite {Γ} (f : ℕ → SyntacticTerm L) : ⊢ᴷ Γ → ⊢ᴷ Γ.map (Rew.rewrite f ▹ ·)
  | .id R v => Derivation.id R (Rew.rewrite f ∘ v)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) d₁ d₂ =>
    have d₁ : ⊢ᴷ Rew.rewrite f ▹ φ :: Γ.map (app (Rew.rewrite f)) := (d₁.rewrite f).cast
    have d₂ : ⊢ᴷ ∼(Rew.rewrite f ▹ φ) :: Δ.map (app (Rew.rewrite f)) := (d₂.rewrite f).cast
    d₁.cut d₂ |>.cast
  | wk d ss => d.rewrite f |>.wk (List.map_subset _ ss)
  | verum => verum
  | or d => (d.rewrite f).or
  | and d₁ d₂ => (d₁.rewrite f).and (d₂.rewrite f)
  | all (φ := φ) (Γ := Γ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have : ⊢ᴷ (φ.free :: Γ⁺).map (Rew.rewrite g ▹ ·) := d.rewrite g
    have : ⊢ᴷ (∀⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map (Rew.rewrite f ▹ ·) :=
      all (Derivation.cast this (by simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | exs (φ := φ) (Γ := Γ) (t := t) d =>
    have : ⊢ᴷ (φ/[t] :: Γ).map (Rew.rewrite f ▹ ·) := d.rewrite f
    have : ⊢ᴷ (∃⁰ Rew.rewrite (Rew.bShift ∘ f) ▹ φ) :: Γ.map (Rew.rewrite f ▹ ·) :=
      exs (t := Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])

protected def map {Δ : Sequent L} (d : ⊢ᴷ Δ) (f : ℕ → ℕ) :
    ⊢ᴷ Δ.map (Rew.rewriteMap f ▹ ·) := d.rewrite (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : ⊢ᴷ Δ) : ⊢ᴷ Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ) (by rfl)

section Hom

variable {L₁ : Language} {L₂ : Language} {𝓢₁ : Schema L₁} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (Proposition L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Γ} : ⊢ᴷ Γ → ⊢ᴷ Γ.map (.lMap Φ)
  | .id r v =>
    .cast (Derivation.id (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Semiformula.lMap_rel, Semiformula.lMap_nrel])
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn =>
    have : ⊢ᴷ (Γ.map (.lMap Φ) ++ Δ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp)
  | wk (Δ := Δ) (Γ := Γ) d ss => (lMap Φ d).wk (List.map_subset _ ss)
  | verum => by simpa using verum
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    have : ⊢ᴷ (.lMap Φ φ ⋎ .lMap Φ ψ :: Γ.map (.lMap Φ) : Sequent L₂) :=
      or (by simpa using lMap Φ d)
    exact Derivation.cast this (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    have : ⊢ᴷ (.lMap Φ φ ⋏ .lMap Φ ψ :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    have : ⊢ᴷ ((∀⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [←Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    have : ⊢ᴷ ((∃⁰ .lMap Φ φ) :: (Γ.map (.lMap Φ)) : Sequent L₂) :=
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
    (d : ⊢ᴷ φ/[&m] :: Δ) : ⊢ᴷ (∀⁰ φ) :: Δ := by
  have : ⊢ᴷ φ.free :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x ↦ if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
  (h : ⊢ᴷ v.map (φ/[·]) ++ Γ) : ⊢ᴷ (∃⁰ φ) :: Γ := by
  induction' v with t v ih generalizing Γ
  · exact weakening h (List.subset_cons_self _ _)
  · exact (ih (Γ := (∃⁰ φ) :: Γ) ((exs h).wk (by simp))).wk (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
  (h : ⊢ᴷ (∃⁰ φ) :: v.map (φ/[·]) ++ Γ) : ⊢ᴷ (∃⁰ φ) :: Γ :=
  (exOfInstances (Γ := (∃⁰ φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)

def allNvar {Δ : Sequent L} {φ} (h : ∀⁰ φ ∈ Δ) : ⊢ᴷ φ/[&Δ.newVar] :: Δ → ⊢ᴷ Δ := fun b ↦
  let b : ⊢ᴷ (∀⁰ φ) :: Δ :=
    b.genelalizeByNewver (by simpa [Semiformula.FVar?] using Sequent.not_fvar?_newVar h) (fun _ ↦ Sequent.not_fvar?_newVar)
  b.wk (by simp [h])

end Derivation

/-! ## Classical proof system -/

inductive Proof.Symbol (L : Language)
  | symbol

notation "𝐋𝐊¹" => Proof.Symbol.symbol

abbrev Proof (φ : Proposition L) := ⊢ᴷ [φ]

instance : Entailment (Proof.Symbol L) (Proposition L) where
  Prf _ := Proof

namespace Proof

lemma def_eq (φ : Proposition L) : (𝐋𝐊¹ ⊢! φ) = (⊢ᴷ [φ]) := rfl

instance : OneSidedLK.EmptyEntailment (Derivation (L := L)) (𝐋𝐊¹ : Proof.Symbol L) where
  equiv := Equiv.refl _

instance classical : Entailment.Cl (𝐋𝐊¹ : Proof.Symbol L) := inferInstance

end Proof

structure Schema.Proof (𝓢 : Schema L) (φ : Proposition L) where
  axioms : List (Proposition L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ 𝓢
  derivation : ⊢ᴷ φ :: ∼axioms

namespace Schema.Proof

instance : Entailment (Schema L) (Proposition L) where
  Prf := Schema.Proof

variable {𝓢 : Schema L}

attribute [simp] axioms_mem

def equiv (𝓢 : Schema L) (φ) :
    (𝓢 ⊢! φ) ≃ (Γ : {Γ : Sequent L // ∀ ψ ∈ Γ, ψ ∈ 𝓢}) × ⊢ᴷ φ :: ∼Γ where
  toFun b := ⟨⟨b.axioms, b.axioms_mem⟩, b.derivation⟩
  invFun := fun ⟨⟨Γ, hΓ⟩, d⟩ ↦ ⟨Γ, hΓ, d⟩

instance : Entailment.Compact (Schema L) where
  core b := ⟨fun φ ↦ φ ∈ b.axioms⟩
  corePrf b := ⟨b.axioms, by simp, b.derivation⟩
  core_finite b := by simp [AdjunctiveSet.Finite, AdjunctiveSet.set]
  core_subset b := by simpa [AdjunctiveSet.subset_iff] using b.axioms_mem

instance : OneSidedLK.Entailment (Derivation (L := L)) (Schema L) where
  equiv {𝓢 φ} := equiv 𝓢 φ

instance : Entailment.Cl 𝓢 := inferInstance

lemma weakerThan_of_le {𝓢 𝓤 : Schema L} (h : 𝓢 ≤ 𝓤) : 𝓢 ⪯ 𝓤 := Entailment.Axiomatized.weakerThanOfSubset h

instance (𝓢 𝓤 : Schema L) : 𝓢 ⪯ 𝓢 ⊔ 𝓤 := weakerThan_of_le (by simp)

instance (𝓢 𝓤 : Schema L) : 𝓤 ⪯ 𝓢 ⊔ 𝓤 := weakerThan_of_le (by simp)

lemma inconsistent_iff :
    Entailment.Inconsistent 𝓢 ↔ ∃ Γ : Sequent L, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (⊢ᴷ ∼Γ) :=
  OneSidedLK.Entailment.inconsistent_iff

def rewrite [𝓢.IsClosed] (b : 𝓢 ⊢! φ) (f : ℕ → SyntacticTerm L) :
    𝓢 ⊢! Rew.rewrite f ▹ φ where
  axioms := b.axioms.map (Rew.rewrite f ▹ ·)
  axioms_mem := by
    suffices ∀ ψ ∈ b.axioms, Rew.rewrite f ▹ ψ ∈ 𝓢 by simpa
    intro ψ hψ
    exact Schema.IsClosed.closed (Rew.rewrite f) _ (b.axioms_mem ψ hψ)
  derivation := b.derivation.rewrite f |>.cast

@[simp] lemma empty_provable_iff_eprovable :
    (⊥ : Schema L) ⊢ φ ↔ 𝐋𝐊¹ ⊢ φ :=
  OneSidedLK.Entailment.empty_provable_iff_eprovable 𝐋𝐊¹

end Schema.Proof

namespace Derivation

open Entailment

variable {Γ Δ : Sequent L}

def eCut (d₁ : ⊢ᴷ φ :: Γ) (d₂ : ⊢ᴷ ψ :: Δ) (e : ∼φ = ψ := by simp) : ⊢ᴷ Γ ++ Δ := cut d₁ (d₂.cast (by simp [e]))

def disj₂ {Γ Δ : Sequent L} : ⊢ᴷ Γ ++ Δ → ⊢ᴷ ⋁Γ :: Δ := fun d ↦
  match Γ with
  |               [] => d.weakening
  |              [φ] => d
  |           [φ, ψ] => d.or
  | φ :: ψ :: χ :: Γ =>
    let Φ := ⋁(χ :: Γ)
    have : ⊢ᴷ (φ ⋎ ψ :: χ :: Γ) ++ Δ := d.or
    have d₁ : ⊢ᴷ (φ ⋎ ψ) ⋎ Φ :: Δ := this.disj₂
    have d₂ : ⊢ᴷ [(∼φ ⋏ ∼ψ) ⋏ ∼Φ, φ ⋎ ψ ⋎ Φ] :=
      have : ⊢ᴷ [φ, ψ ⋎ Φ, (∼φ ⋏ ∼ψ) ⋏ ∼Φ] :=
        ((identity φ).rotate.tensor (identity ψ).rotate).tensor
          (identity Φ).rotate |>.rotate.rotate.or.weakening
      this.or.rotate
    d₂.eCut d₁
  termination_by _ => Γ.length

def conj₂ {Γ Δ : Sequent L} (d : (φ : Proposition L) → φ ∈ Γ → ⊢ᴷ φ :: Δ) : ⊢ᴷ ⋀Γ :: Δ :=
  match Γ with
  |          [] => verum.weakening
  |         [φ] => d φ (by simp)
  | φ :: ψ :: Γ =>
    have : ⊢ᴷ ⋀(ψ :: Γ) :: Δ := conj₂ (Γ := ψ :: Γ) (fun χ h ↦ d χ (by simp_all))
    (d φ (by simp)).and this

def disjClosure : ⊢ᴷ Γ → 𝐋𝐊¹ ⊢! ⋁Γ := fun d ↦
  have : ⊢ᴷ Γ ++ [] := d.cast
  this.disj₂

def disjClosureInv : 𝐋𝐊¹ ⊢! ⋁Γ → ⊢ᴷ Γ := fun d ↦
  have d₁ : ⊢ᴷ [⋁Γ] := d
  have d₂ : ⊢ᴷ ⋀(∼Γ) :: Γ := conj₂ fun φ h ↦ close φ (by simp) (by simp_all)
  d₁.eCut d₂

lemma nonempty_iff_provable_disj : Nonempty (⊢ᴷ Γ) ↔ 𝐋𝐊¹ ⊢ ⋁Γ :=
  ⟨by rintro ⟨d⟩; exact ⟨d.disjClosure⟩, by rintro ⟨d⟩; exact ⟨d.disjClosureInv⟩⟩

end Derivation

namespace Schema.Proof

open Entailment Derivation

lemma iff_context {𝓢 : Schema L} : 𝓢 ⊢ φ ↔ 𝓢 *⊢[𝐋𝐊¹] φ := by
  constructor
  · rintro ⟨d⟩
    have : 𝐋𝐊¹ ⊢! ⋀d.axioms ➝ φ :=
      have : ⊢ᴷ ∼d.axioms ++ [φ] := d.derivation.weakening
      this.disj₂.or.cast <| by simp [Semiformula.imp_eq]
    refine ⟨⟨d.axioms, by simpa using d.axioms_mem, this⟩⟩
  · rintro ⟨Γ, h, d⟩
    have d : ⊢ᴷ [⋁(∼Γ) ⋎ φ] := d.cast (by simp [Semiformula.imp_eq])
    have : ⊢ᴷ ⋀Γ ⋏ ∼φ :: φ :: ∼Γ :=
      have : ⊢ᴷ ⋀Γ :: ∼Γ := Derivation.conj₂ fun φ h ↦ close φ (by simp) (by simp [h])
      this.tensor (identity φ).rotate |>.weakening
    refine ⟨⟨Γ, h, (d.eCut this).cast⟩⟩

open Classical in

noncomputable instance : Entailment.Deduction (Schema L) where
  ofInsert {φ ψ 𝓢 b} :=
    have : insert φ ↑𝓢 *⊢[𝐋𝐊¹] ψ := iff_context.mp ⟨b⟩
    have : ↑𝓢 *⊢[𝐋𝐊¹] φ ➝ ψ := Context.deduct! this
    (iff_context.mpr this).get
  inv {φ ψ 𝓢 b} :=
    have : ↑(adjoin φ 𝓢) *⊢[𝐋𝐊¹] ψ := Context.deductInv! (iff_context.mp ⟨b⟩)
    (iff_context.mpr this).get

end Schema.Proof

/-!
  ### Theory
-/

def Schema.theory (𝓢 : Schema L) : Theory L := {σ | 𝓢 ⊢ ↑σ}

@[simp] lemma Schema.mem_theory {𝓢 : Schema L} :
    σ ∈ 𝓢.theory ↔ 𝓢 ⊢ ↑σ := by simp [Schema.theory]

namespace Theory

instance : Entailment (Theory L) (Sentence L) where
  Prf T σ := PLift (σ ∈ T)

@[simp] lemma provable_iff (σ : Sentence L) (T : Theory L) :
    T ⊢ σ ↔ σ ∈ T :=
  ⟨fun h ↦ PLift.down h.some, fun h ↦ ⟨⟨h⟩⟩⟩

end Theory

end FirstOrder

end LO

end
