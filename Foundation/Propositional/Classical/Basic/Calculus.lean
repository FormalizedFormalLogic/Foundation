import Foundation.Propositional.Classical.Basic.Formula
import Foundation.Logic.Calculus

namespace LO

namespace Propositional.Classical

variable {α : Type*}

abbrev Sequent (α : Type*) := List (Formula α)

inductive Derivation (T : Theory α) : Sequent α → Type _
| axL (Δ a)   : Derivation T (Formula.atom a :: Formula.natom a :: Δ)
| verum (Δ)   : Derivation T (⊤ :: Δ)
| or {Δ φ ψ}  : Derivation T (φ :: ψ :: Δ) → Derivation T (φ ⋎ ψ :: Δ)
| and {Δ φ ψ} : Derivation T (φ :: Δ) → Derivation T (ψ :: Δ) → Derivation T (φ ⋏ ψ :: Δ)
| wk {Δ Γ}    : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
| cut {Δ φ}   : Derivation T (φ :: Δ) → Derivation T (∼φ :: Δ) → Derivation T Δ
| root {φ}    : φ ∈ T → Derivation T [φ]

instance : OneSided (Formula α) (Theory α) := ⟨Derivation⟩

namespace Derivation

variable {T U : Theory α} {Δ Δ₁ Δ₂ Γ : Sequent α}

def length : {Δ : Sequent α} → T ⟹ Δ → ℕ
  | _, axL _ _     => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max (length dp) (length dq)).succ
  | _, wk d _      => d.length.succ
  | _, cut dp dn   => (max (length dp) (length dn)).succ
  | _, root _      => 0

protected def cast (d : T ⟹ Δ) (e : Δ = Γ) : T ⟹ Γ := cast (by simp[e]) d

@[simp] lemma length_cast (d : T ⟹ Δ) (e : Δ = Γ) : length (Derivation.cast d e) = length d := by
  rcases e with rfl; simp[Derivation.cast]

def verum' (h : ⊤ ∈ Δ) : T ⟹ Δ := (verum Δ).wk (by simp[h])

def axL' (a : α)
    (h : Formula.atom a ∈ Δ) (hn : Formula.natom a ∈ Δ) : T ⟹ Δ := (axL Δ a).wk (by simp[h, hn])

def em {φ : Formula α} {Δ : Sequent α} (hpos : φ ∈ Δ) (hneg : ∼φ ∈ Δ) : T ⟹ Δ := by
  induction φ using Formula.rec' generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hatom a          => exact axL' a hpos hneg
  case hnatom a         => exact axL' a hneg hpos
  case hand φ ψ ihp ihq =>
    have ihp : T ⟹ φ :: ∼φ :: ∼ψ :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ ψ :: ∼φ :: ∼ψ :: Δ := ihq (by simp) (by simp)
    have : T ⟹ ∼φ :: ∼ψ :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor φ ψ ihp ihq  =>
    have ihp : T ⟹ ∼φ :: φ :: ψ :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ ∼ψ :: φ :: ψ :: Δ := ihq (by simp) (by simp)
    have : T ⟹ φ :: ψ :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

instance : Tait (Formula α) (Theory α) where
  verum := fun _ Δ => Derivation.verum Δ
  and := fun dp dq => Derivation.cast (dp.and dq) (by simp)
  or := fun d => Derivation.cast d.or (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => Derivation.em hp hn

instance : Tait.Cut (Formula α) (Theory α) := ⟨Derivation.cut⟩

def trans (F : U ⊢* T) {Γ : Sequent α} : T ⟹ Γ → U ⟹ Γ
  | axL Γ φ   => axL Γ φ
  | verum Γ   => verum Γ
  | and d₁ d₂ => and (trans F d₁) (trans F d₂)
  | or d      => or (trans F d)
  | wk d ss   => wk (trans F d) ss
  | cut d₁ d₂ => cut (trans F d₁) (trans F d₂)
  | root h    => F h

instance : Tait.Axiomatized (Formula α) (Theory α) where
  root {_ _ h} := root h
  trans {_ _ _ F d} := trans (fun h ↦ F _ h) d

variable [DecidableEq α]

def compact {Γ : Sequent α} : T ⟹ Γ → (s : { s : Finset (Formula α) // ↑s ⊆ T}) × (s : Theory α) ⟹ Γ
  | axL Γ φ   => ⟨⟨∅, by simp⟩, axL Γ φ⟩
  | verum Γ   => ⟨⟨∅, by simp⟩, verum Γ⟩
  | and d₁ d₂ =>
    let ⟨s₁, d₁⟩ := compact d₁
    let ⟨s₂, d₂⟩ := compact d₂
    ⟨⟨(s₁ ∪ s₂ : Finset (Formula α)), by simp [s₁.prop, s₂.prop]⟩,
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
    ⟨⟨(s₁ ∪ s₂ : Finset (Formula α)), by simp [s₁.prop, s₂.prop]⟩,
      cut (Tait.ofAxiomSubset (by simp) d₁) (Tait.ofAxiomSubset (by simp) d₂)⟩
  | root (φ := φ) h =>
    ⟨⟨{φ}, by simp [h]⟩, root (by simp)⟩

instance : System.Compact (Theory α) where
  φ b := (compact b).1
  φPrf b := (compact b).2
  φ_subset b := by simpa using (compact b).1.prop
  φ_finite b := by simp

def deductionAux {Γ : Sequent α} {φ} : T ⟹ Γ → T \ {φ} ⟹ ∼φ :: Γ
  | axL Γ φ   => wk (axL Γ φ) (by simp)
  | verum Γ   => wk (verum Γ) (by simp)
  | and d₁ d₂ =>
    Tait.rotate₁ <| and (Tait.rotate₁ <| deductionAux d₁) (Tait.rotate₁ <| deductionAux d₂)
  | or d      => Tait.rotate₁ <| Tait.or <| Tait.wk (deductionAux d) (by intro x; simp; tauto)
  | wk d ss   => wk (deductionAux d) <| List.cons_subset_cons (∼φ) ss
  | cut d₁ d₂ => cut (Tait.rotate₁ <| deductionAux d₁) (Tait.rotate₁ <| deductionAux d₂)
  | root (φ := ψ) h =>
    if hq : φ = ψ then em (φ := φ) (by simp [hq]) (by simp) else
      Tait.wk (show T \ {φ} ⟹ [ψ] from Tait.root (by simp [h, Ne.symm hq])) (by simp)

def deduction {Γ : Sequent α} {φ} (d : insert φ T ⟹ Γ) : T ⟹ ∼φ :: Γ := Tait.ofAxiomSubset (by simp) (deductionAux d)

lemma inconsistent_iff_provable :
    System.Inconsistent (insert φ T) ↔ T ⊢! ∼φ := by
  constructor
  · intro h; exact ⟨deduction (Tait.inconsistent_iff_provable.mp h).get⟩
  · rintro b
    exact System.inconsistent_of_provable_of_unprovable (φ := φ) (System.by_axm _ <| by simp) (System.wk! (by simp) b)

lemma consistent_iff_unprovable :
    System.Consistent (insert φ T) ↔ T ⊬ ∼φ := by simp [←System.not_inconsistent_iff_consistent, inconsistent_iff_provable]

omit [DecidableEq α]
@[simp] lemma inconsistent_theory_iff :
    System.Inconsistent (System.theory T) ↔ System.Inconsistent T := by
  constructor
  · intro h
    exact System.inconsistent_iff_provable_bot.mpr
      <| System.StrongCut.cut! (by simp) <| System.inconsistent_iff_provable_bot.mp h
  · intro h; exact h.of_supset (by simpa using System.Axiomatized.axm_subset T)

@[simp] lemma consistent_theory_iff :
    System.Consistent (System.theory T) ↔ System.Consistent T := by simp [←System.not_inconsistent_iff_consistent, inconsistent_theory_iff]

end Derivation

end Propositional.Classical

end LO
