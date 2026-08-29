module

/- public import Foundation.Logic.Calculus -/
public import Foundation.Logic.Calculus
public import Foundation.Propositional.Entailment.Int
public import Foundation.FirstOrder.Basic.Syntax.Rew
public import Mathlib.Data.List.MinMax

/-! # One-sided sequent calculus for first-order classical logic -/

@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language}

abbrev Sequent (L : Language) := Multiset (Proposition L)

namespace Sequent

open Semiformula

def newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0

lemma not_fvar?_newVar {φ : Proposition L} {Γ : Sequent L} (h : φ ∈ Γ) :
    ¬FVar? φ Γ.newVar :=
  not_fvar?_of_lt_fvSup φ <| by
    simp only [newVar]
    induction Γ using Multiset.induction_on with
    | empty => simp at h
    | @cons ψ Γ ih =>
      simp only [Multiset.map_cons, Multiset.foldr_cons]
      rcases Multiset.mem_cons.mp h with (rfl | h)
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

@[simp] lemma lcHom_comm {Γ : Multiset (Formula L ξ)} (f : Formula L ξ →ˡᶜ Proposition L) :
    (∼Γ).map f = ∼Γ.map f := by simp [Multiset.tilde_def]

def IsClosed (Γ : Sequent L) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

def embed (Γ : Multiset (Sentence L)) : Sequent L := Γ.map Rewriting.emb

@[simp] lemma embed_nil : embed (0 : Multiset (Sentence L)) = 0 := rfl

@[simp] lemma embed_singleton {φ : Sentence L} :
    embed (⦃φ⦄ : Multiset (Sentence L)) = ⦃(φ : Proposition L)⦄ := rfl

@[simp] lemma embed_add (Γ Δ : Multiset (Sentence L)) :
    embed (Γ + Δ) = embed Γ + embed Δ := by simp [embed]

@[simp] lemma embed_shift (Γ : Multiset (Sentence L)) :
    (embed Γ)⁺ᵐ = embed Γ := by simp [embed, Rewriting.shiftsM]

end Sequent

/-! ## Derivation for $\mathbf{LK}$ -/

/-- Derivation for $\mathbf{LK}$ -/
inductive Derivation : Sequent L → Type _
| identity (r : L.Rel k) (v) : Derivation ⦃.rel r v, .nrel r v⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) →
    Derivation (Γ + ⦃φ ⋏ ψ⦄)
| all : Derivation (Γ⁺ᵐ + ⦃φ.free⦄) → Derivation (Γ + ⦃∀¹ φ⦄)
| exs : Derivation (Γ + ⦃φ/[t]⦄) → Derivation (Γ + ⦃∃¹ φ⦄)

prefix:45 "⊢ᴸᴷ¹ " => Derivation

namespace Derivation

open Rewriting LawfulSyntacticRewriting

def height {Δ : Sequent L} : ⊢ᴸᴷ¹ Δ → ℕ
  |    identity _ _ => 0
  |       cut dp dn => max dp.height dn.height + 1
  | contraction d _ => d.height + 1
  |           verum => 0
  |            or d => d.height + 1
  |       and dp dq => max (height dp) (height dq) + 1
  |           all d => d.height + 1
  |           exs d => d.height + 1

section height

@[simp] lemma height_id {k} {r : L.Rel k} {v} :
  height (identity r v) = 0 := rfl

@[simp] lemma height_cut {φ} (dp : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dn : ⊢ᴸᴷ¹ Δ + ⦃∼φ⦄) :
  height (cut dp dn) = (max (height dp) (height dn)).succ := rfl

@[simp] lemma height_contraction (d : ⊢ᴸᴷ¹ Δ) (h : Δ ⊆ Γ) :
    height (contraction d h) = d.height.succ := rfl

@[simp] lemma height_verum : height (verum : ⊢ᴸᴷ¹ (⦃⊤⦄ : Sequent L)) = 0 := rfl

@[simp] lemma height_and {φ ψ} (dp : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dq : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄) :
    height (and dp dq) = (max (height dp) (height dq)).succ := rfl

@[simp] lemma height_or {φ ψ} (d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄) :
    height (or d) = d.height.succ := rfl

@[simp] lemma height_all {φ : Semiproposition L 1} (d : ⊢ᴸᴷ¹ Γ⁺ᵐ + ⦃φ.free⦄) :
    height (all d) = d.height.succ := rfl

@[simp] lemma height_exs {t} {φ} (d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄) :
    height (exs d) = d.height.succ := rfl

end height

abbrev cast (d : ⊢ᴸᴷ¹ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ¹ Γ := e ▸ d

@[simp] lemma height_cast (d : ⊢ᴸᴷ¹ Δ) (e : Δ = Γ) :
    height (Derivation.cast d e) = height d := by rcases e with rfl; simp [Derivation.cast]

def contra (d : ⊢ᴸᴷ¹ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ¹ Γ := contraction d h

def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ := verum.contraction <| by
  intro φ hφ
  have : φ = ⊤ := by simpa using hφ
  simpa [this] using h

def identity' (r : L.Rel k) (v) (hpos : Semiformula.rel r v ∈ Δ := by simp)
    (hneg : Semiformula.nrel r v ∈ Δ := by simp) : ⊢ᴸᴷ¹ Δ :=
  (identity r v).contraction <| by
    intro φ hφ
    rcases Multiset.mem_add.mp hφ with hφ | hφ <;> simp_all

def tensor {φ ψ} (dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dψ : ⊢ᴸᴷ¹ Δ + ⦃ψ⦄) :
    ⊢ᴸᴷ¹ Γ + Δ + ⦃φ ⋏ ψ⦄ :=
  and
    (dφ.contra <| by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all)
    (dψ.contra <| by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all)

def eta : (φ : Proposition L) → ⊢ᴸᴷ¹ ⦃φ, ∼φ⦄
  | .rel R v | .nrel R v => identity' R v
  | ⊤ | ⊥ => top
  | φ ⋏ ψ =>
    (or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (tensor (Γ := ⦃∼φ⦄) (Δ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ)
        (eta φ).cast (eta ψ).cast).cast).cast (by simp [add_comm])
  | φ ⋎ ψ =>
    (or (Γ := ⦃∼φ ⋏ ∼ψ⦄) (φ := φ) (ψ := ψ)
      (tensor (Γ := ⦃φ⦄) (Δ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
        (eta φ) (eta ψ)).cast).cast (by simp [add_comm])
  | ∀¹ φ =>
    (all (Γ := ⦃∃¹ ∼φ⦄) (φ := φ)
      ((exs (Γ := ⦃φ.free⦄) (φ := ∼φ.shift) (t := &0)
        ((eta φ.free).cast (by simp))).cast
      (by simp [add_comm]))).cast (by simp [add_comm])
  | ∃¹ φ =>
    (all (Γ := ⦃∃¹ φ⦄) (φ := ∼φ) (cast
      (exs (Γ := ⦃(∼φ).free⦄) (φ := φ.shift) (t := &0)
        ((eta φ.free).cast (by simp [add_comm])))
      (by simp [add_comm]))).cast (by simp)
  termination_by φ => φ.complexity

instance : OneSidedLK (Derivation (L := L)) where
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  contraction d ss := d.contraction ss
  identity φ := eta φ

instance : OneSidedLK.Cut (Derivation (L := L)) where
  cut dp dn := cut dp dn

lemma of_isClosed {Γ : Sequent L} (h : Γ.IsClosed) : Nonempty (⊢ᴸᴷ¹ Γ) := by
  rcases h with ⟨φ, hp, hn⟩
  exact ⟨OneSidedLK.close φ hp hn⟩

def rewrite {Γ} (f : ℕ → SyntacticTerm L) :
    ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (Rew.rewrite f ▹ ·)
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) d₁ d₂ =>
    (cut (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (Δ := Δ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))).cast (by simp)
  | contraction d ss => d.rewrite f |>.contraction (Multiset.map_subset_map ss)
  | verum => verum
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (or (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((d.rewrite f).cast (by simp))).cast (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    (and (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))).cast (by simp)
  | all (φ := φ) (Γ := Γ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have : ⊢ᴸᴷ¹ (Γ⁺ᵐ + ⦃φ.free⦄).map (Rew.rewrite g ▹ ·) := d.rewrite g
    (all (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) (Derivation.cast this (by
        simp [g, free_rewrite_eq, Rewriting.shiftsM, shift_rewrite_eq, Function.comp_def]))).cast
      (by simp [Rew.q_rewrite])
  | exs (φ := φ) (Γ := Γ) (t := t) d =>
    have : ⊢ᴸᴷ¹ (Γ + ⦃φ/[t]⦄).map (Rew.rewrite f ▹ ·) := d.rewrite f
    (exs (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) (t := Rew.rewrite f t)
      (Derivation.cast this (by simp [rewrite_subst_eq]))).cast (by simp [Rew.q_rewrite])

protected def map {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) (f : ℕ → ℕ) :
    ⊢ᴸᴷ¹ Δ.map (Rew.rewriteMap f ▹ ·) := d.rewrite (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : ⊢ᴸᴷ¹ Δ) : ⊢ᴸᴷ¹ Δ⁺ᵐ :=
  Derivation.cast (Derivation.map d Nat.succ) (by rfl)

section Hom

variable {L₁ : Language} {L₂ : Language} {Δ₁ : Sequent L₁}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : Multiset (Proposition L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ᵐ = (Δ⁺ᵐ.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shiftsM, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {Γ} : ⊢ᴸᴷ¹ Γ → ⊢ᴸᴷ¹ Γ.map (.lMap Φ)
  | identity r v =>
    .cast (identity (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
    (by simp [Function.comp_def])
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn =>
    (cut (Γ := Γ.map (.lMap Φ)) (Δ := Δ.map (.lMap Φ))
      (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp))
      (Derivation.cast (lMap Φ dn) (by simp))).cast (by simp)
  | contraction (Δ := Δ) (Γ := Γ) d ss => (lMap Φ d).contraction (Multiset.map_subset_map ss)
  | verum => by simpa using verum
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (or (Γ := Γ.map (.lMap Φ)) (φ := .lMap Φ φ) (ψ := .lMap Φ ψ)
      (Derivation.cast (lMap Φ d) (by simp))).cast (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    (and (Γ := Γ.map (.lMap Φ)) (φ := .lMap Φ φ) (ψ := .lMap Φ ψ)
      (Derivation.cast (lMap Φ dp) (by simp))
      (Derivation.cast (lMap Φ dq) (by simp))).cast (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    (all (Γ := Γ.map (.lMap Φ)) (φ := .lMap Φ φ)
      (Derivation.cast (lMap Φ d)
        (by simp [←Semiformula.lMap_free, shifts_image]))).cast (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    (exs (Γ := Γ.map (.lMap Φ)) (φ := .lMap Φ φ)
      (t := Semiterm.lMap Φ t)
      (.cast (lMap Φ d) (by simp [Semiformula.lMap_subst]))).cast (by simp)

end Hom

private lemma map_subst_eq_free (φ : Semiproposition L 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) ▹
      (φ/[&m] : Proposition L) = Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app])
    (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ @Rew.rewriteMap L ℕ ℕ 0
      (fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Δ⁺ᵐ := by
  apply Multiset.map_congr rfl
  intro φ hp
  exact Semiformula.rew_eq_of_funEqOn₀
    (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])

def generalizeByNewVar {φ : Semiproposition L 1} (hp : ¬φ.FVar? m)
    (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m) (d : ⊢ᴸᴷ¹ Δ + ⦃φ/[&m]⦄) :
    ⊢ᴸᴷ¹ Δ + ⦃∀¹ φ⦄ := by
  have : ⊢ᴸᴷ¹ Δ⁺ᵐ + ⦃φ.free⦄ :=
    Derivation.cast (Derivation.map d (fun x ↦ if x = m then 0 else x + 1))
    (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
    (h : ⊢ᴸᴷ¹ (v.map (φ/[·]) : Multiset _) + Γ) : ⊢ᴸᴷ¹ Γ + ⦃∃¹ φ⦄ := by
  induction' v with t v ih generalizing Γ
  · exact contra h (by intro ψ hψ; simp_all)
  · have d : ⊢ᴸᴷ¹ ((v.map (φ/[·]) : Multiset _) + Γ) + ⦃∃¹ φ⦄ :=
      exs (t := t) (h.cast (by
        change (φ/[t] ::ₘ (v.map (φ/[·]) : Multiset _)) + Γ =
          ((v.map (φ/[·]) : Multiset _) + Γ) + ⦃φ/[t]⦄
        rw [← Multiset.add_atom_eq_cons]
        abel))
    have d : ⊢ᴸᴷ¹ (v.map (φ/[·]) : Multiset _) + (Γ + ⦃∃¹ φ⦄) :=
      d.cast (by simp [add_assoc, add_left_comm, add_comm])
    exact (ih d).contraction (by intro ψ hψ; simp_all)

def exOfInstances' (v : List (SyntacticTerm L)) (φ : Semiproposition L 1)
    (h : ⊢ᴸᴷ¹ (v.map (φ/[·]) : Multiset _) + Γ + ⦃∃¹ φ⦄) :
    ⊢ᴸᴷ¹ Γ + ⦃∃¹ φ⦄ :=
  (exOfInstances (Γ := Γ + ⦃∃¹ φ⦄) v φ (h.cast (by simp [add_assoc]))).contraction
    (by intro ψ hψ; simp_all)

def allNvar {Δ : Sequent L} {φ} (h : ∀¹ φ ∈ Δ) :
    ⊢ᴸᴷ¹ Δ + ⦃φ/[&Δ.newVar]⦄ → ⊢ᴸᴷ¹ Δ := fun b ↦
  let b : ⊢ᴸᴷ¹ Δ + ⦃∀¹ φ⦄ :=
    b.generalizeByNewVar (by simpa [Semiformula.FVar?] using Sequent.not_fvar?_newVar h)
      (fun _ ↦ Sequent.not_fvar?_newVar)
  b.contraction (by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · exact hψ
    · exact Multiset.mem_singleton.mp hψ ▸ h)

end Derivation

/-! ## Classical proof system -/

inductive LK (L : Language)
  | symbol

notation "𝐋𝐊¹" => LK.symbol

notation "𝐋𝐊¹[" L "]" => LK.symbol (L := L)

abbrev LK.Proof (φ : Proposition L) := ⊢ᴸᴷ¹ ⦃φ⦄

instance : Entailment (LK L) (Proposition L) where
  Prf _ := LK.Proof

namespace LK.Proof

lemma def_eq (φ : Proposition L) : (𝐋𝐊¹ ⊢! φ) = (⊢ᴸᴷ¹ ⦃φ⦄) := rfl

lemma provable_def (φ : Proposition L) :
    𝐋𝐊¹ ⊢ φ ↔ Nonempty (⊢ᴸᴷ¹ ⦃φ⦄) := by rfl

lemma unprovable_def (φ : Proposition L) :
    𝐋𝐊¹ ⊬ φ ↔ IsEmpty (⊢ᴸᴷ¹ ⦃φ⦄) := by
  unfold Entailment.Unprovable; simp [provable_def]

instance : OneSidedLK.PrincipalEntailment (Derivation (L := L)) (𝐋𝐊¹ : LK L) where
  equiv := Equiv.refl _

instance classical : Entailment.Cl (𝐋𝐊¹ : LK L) := inferInstance

lemma all (φ : Semiproposition L 1) :
    𝐋𝐊¹ ⊢ φ.free → 𝐋𝐊¹ ⊢ ∀¹ φ := fun h ↦
  ⟨Derivation.all (Γ := 0) (φ := φ) (h.get.cast (by simp [Rewriting.shiftsM]))⟩

lemma allClosure_fixitr {φ : Proposition L} (dp : 𝐋𝐊¹ ⊢ φ) :
    (m : ℕ) → 𝐋𝐊¹ ⊢ ∀¹* Rew.fixitr 0 m ▹ φ
  |     0 => by simpa
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    apply all; simpa using allClosure_fixitr dp m

lemma univCl' {φ : Proposition L} (b : 𝐋𝐊¹ ⊢ φ) : 𝐋𝐊¹ ⊢ φ.univCl' :=
  allClosure_fixitr b φ.fvSup

lemma lMap (Φ : L₁ →ᵥ L₂) {φ : Proposition L₁} :
    𝐋𝐊¹ ⊢ φ → 𝐋𝐊¹ ⊢ φ.lMap Φ := by
  rintro ⟨d⟩
  have : ⊢ᴸᴷ¹ ⦃φ⦄ := d
  have : ⊢ᴸᴷ¹ ⦃.lMap Φ φ⦄ := this.lMap Φ
  exact ⟨this⟩

end LK.Proof

structure Theory.Proof (T : Theory L) (σ : Sentence L) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation Rewriting.emb (⦃σ⦄ + ∼axioms)

namespace Theory.Proof

instance : Entailment (Theory L) (Sentence L) where
  Prf := Theory.Proof

variable {T : Theory L}

attribute [simp] Theory.Proof.axioms_mem

/-- A singleton derivation gives a theory proof without using any axioms. -/
def ofDerivation {T : Theory L} {φ : Sentence L}
    (d : OneSidedLK.Pullback Derivation Rewriting.emb ⦃φ⦄) : T ⊢! φ :=
  ⟨0, by simp, OneSidedLK.cast d⟩

instance : Entailment.Compact (Theory L) where
  core b := {φ | φ ∈ b.axioms}
  corePrf b := ⟨b.axioms, by simp, b.derivation⟩
  core_finite b := by simp [AdjunctiveSet.Finite, AdjunctiveSet.set]
  core_subset b := by simpa [AdjunctiveSet.subset_iff] using b.axioms_mem

instance (T : Theory L) : Entailment.ModusPonens T where
  mdp {φ ψ} bi bp := by
    refine ⟨bi.axioms + bp.axioms, ?_, ?_⟩
    · intro χ hχ
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact bi.axioms_mem χ hχ
      · exact bp.axioms_mem χ hχ
    · exact OneSidedLK.cast (OneSidedLK.modusPonens
        (Γ := ∼bi.axioms) (Δ := ∼bp.axioms) (φ := φ) (ψ := ψ)
        (OneSidedLK.cast bi.derivation) (OneSidedLK.cast bp.derivation)) (by simp; abel)

instance : Entailment.Cl T := OneSidedLK.AxiomDerivation.cl T ofDerivation

instance : Entailment.Axiomatized (Theory L) where
  prfAxm {𝓢 φ} h :=
    ⟨⦃φ⦄, by simpa using h, by
      change ⊢ᴸᴷ¹ (⦃φ⦄ + ∼(⦃φ⦄ : Multiset (Sentence L))).map Rewriting.emb
      simpa [Multiset.tilde_def] using Derivation.eta (Rewriting.emb φ)⟩
  weakening {𝓢 𝓣 φ} h b :=
    ⟨b.axioms, fun ψ hψ ↦ h (b.axioms_mem ψ hψ), b.derivation⟩

instance : Entailment.DeductiveExplosion (Theory L) where
  dexp b φ := by
    refine ⟨b.axioms, b.axioms_mem, ?_⟩
    have db : ⊢ᴸᴷ¹ (∼Sequent.embed b.axioms) + ⦃Rewriting.emb (⊥ : Sentence L)⦄ :=
      Derivation.cast b.derivation (by simp [Sequent.embed, add_comm])
    exact (OneSidedLK.removeBot db).contraction (by intro ψ hψ; simp_all [Sequent.embed])

lemma weakerThan_of_le {T U : Theory L} (h : T ⊆ U) : T ⪯ U :=
  Entailment.Axiomatized.weakerThanOfSubset h

instance (T U : Theory L) : T ⪯ T ∪ U := weakerThan_of_le (by simp)

instance (T U : Theory L) : U ⪯ T ∪ U := weakerThan_of_le (by simp)

lemma provable_iff :
    T ⊢ φ ↔ ∃ Γ : Multiset (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Nonempty (⊢ᴸᴷ¹ ⦃(φ : Proposition L)⦄ + ∼Sequent.embed Γ) := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.axioms, b.axioms_mem,
      ⟨by simpa [OneSidedLK.Pullback, Sequent.embed] using b.derivation⟩⟩
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    exact ⟨⟨Γ, hΓ, by simpa [OneSidedLK.Pullback, Sequent.embed] using d⟩⟩

lemma inconsistent_iff :
    Entailment.Inconsistent T ↔ ∃ Γ : Multiset (Sentence L), (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Nonempty (⊢ᴸᴷ¹ ∼Sequent.embed Γ) := by
  rw [Entailment.inconsistent_iff_provable_bot, provable_iff]
  constructor
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    have db : ⊢ᴸᴷ¹ (∼Sequent.embed Γ) + ⦃Rewriting.emb (⊥ : Sentence L)⦄ :=
      d.cast (by rw [add_comm])
    exact ⟨Γ, hΓ, ⟨OneSidedLK.removeBot db⟩⟩
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    exact ⟨Γ, hΓ, ⟨d.contraction (by intro ψ hψ; simp_all)⟩⟩

open Entailment Derivation

@[simp] lemma empty_provable_iff_eprovable :
    (∅ : Theory L) ⊢ φ ↔ 𝐋𝐊¹ ⊢ (φ : Proposition L) := by
  constructor
  · rintro ⟨b⟩
    have hzero : b.axioms = 0 := Multiset.eq_zero_of_forall_notMem fun ψ hψ ↦ by
      simpa using b.axioms_mem ψ hψ
    have d := b.derivation
    rw [hzero] at d
    change ⊢ᴸᴷ¹ ⦃Rewriting.emb φ⦄ at d
    exact ⟨d⟩
  · rintro ⟨d⟩
    change ⊢ᴸᴷ¹ ⦃Rewriting.emb φ⦄ at d
    exact ⟨ofDerivation d⟩

open Entailment Derivation

lemma of_LK_provable {T : Theory L} {φ : Sentence L} :
    𝐋𝐊¹ ⊢ (φ : Proposition L) → T ⊢ φ := by
  rintro ⟨d⟩
  change ⊢ᴸᴷ¹ ⦃Rewriting.emb φ⦄ at d
  exact ⟨ofDerivation d⟩

lemma specialize {T : Theory L} (φ : Semisentence L 1) (t : ClosedTerm L) :
    T ⊢ ∀¹ φ 🡒 Semiformula.subst φ ![t] := by
  apply of_LK_provable
  refine ⟨?_⟩
  let φt : Sentence L := Semiformula.subst φ ![t]
  have d : ⊢ᴸᴷ¹ ⦃(φt : Proposition L)⦄ +
      ⦃(∼(φ : Semiproposition L 1))/[Rew.emb t]⦄ := by
    simpa [φt, Semiformula.coe_subst_eq_subst_coe₁] using
      Derivation.eta (φt : Proposition L)
  exact (Derivation.or (Γ := 0) (φ := ∃¹ ∼(φ : Semiproposition L 1))
    (ψ := (φt : Proposition L)) (Derivation.cast (Derivation.exs
      (Γ := ⦃(φt : Proposition L)⦄) (φ := ∼(φ : Semiproposition L 1))
      (t := Rew.emb t) d) (by simp [add_comm]))).cast (by simp [Semiformula.imp_eq, φt])

open Classical in
noncomputable instance : Entailment.Deduction (Theory L) where
  ofInsert {φ ψ T} b := by
    let Γ := b.axioms.filter (· ≠ φ)
    refine ⟨Γ, ?_, ?_⟩
    · intro χ hχ
      rcases Multiset.mem_filter.mp hχ with ⟨hχ, hnχ⟩
      simpa [hnχ] using b.axioms_mem χ hχ
    · exact Derivation.cast (Derivation.or (Γ := (∼Γ).map Rewriting.emb)
        (φ := Rewriting.emb (∼φ)) (ψ := Rewriting.emb ψ)
        (b.derivation.contraction
          (Γ := (∼Γ).map Rewriting.emb +
            ⦃Rewriting.emb (∼φ), Rewriting.emb ψ⦄)
          (by simpa [OneSidedLK.Pullback, Multiset.tilde_def, Γ, add_assoc] using
            Multiset.map_subset_map (f := Rewriting.emb) <|
              Multiset.add_map_subset_map_filter_add_atom
                (s := b.axioms) (t := ⦃ψ⦄) (f := fun χ ↦ ∼χ) (a := φ))))
        (by simp [Multiset.tilde_def, Semiformula.imp_eq, add_comm])
  inv {φ ψ T} b :=
    Entailment.mdp
      (Entailment.Axiomatized.weakening (by simp) b)
      (Entailment.Axiomatized.byAxm (by simp))

end Theory.Proof

/-! ### Theory -/

def Theory.theory (T : Theory L) : Theory L := {σ | T ⊢ σ}

@[simp] lemma Theory.mem_theory {T : Theory L} :
    σ ∈ T.theory ↔ T ⊢ σ := by simp [Theory.theory]

end FirstOrder

end LO

end
