import Logic.Propositional.Basic.Formula
import Logic.Logic.Calculus

namespace LO

namespace Propositional

variable {α : Type*}

abbrev Sequent (α : Type*) := List (Formula α)

inductive DerivationCR (P : Formula α → Prop) : Sequent α → Type _
| axL (Δ a)   : DerivationCR P (Formula.atom a :: Formula.natom a :: Δ)
| verum (Δ)   : DerivationCR P (⊤ :: Δ)
| or {Δ p q}  : DerivationCR P (p :: q :: Δ) → DerivationCR P (p ⋎ q :: Δ)
| and {Δ p q} : DerivationCR P (p :: Δ) → DerivationCR P (q :: Δ) → DerivationCR P (p ⋏ q :: Δ)
| wk {Δ Γ}    : DerivationCR P Δ → Δ ⊆ Γ → DerivationCR P Γ
| cut {Δ p}   : P p →
    DerivationCR P (p :: Δ) → DerivationCR P (~p :: Δ) → DerivationCR P Δ

scoped notation :45 "⊢ᴾᶜ[" P "] " Γ:45 => DerivationCR P Γ

abbrev Derivation : Sequent α → Type _ := DerivationCR (fun _ => False)

scoped prefix:45 "⊢ᴾᵀ " => Derivation

abbrev DerivationC : Sequent α → Type _ := DerivationCR (fun _ => True)

abbrev DerivationClx (c : ℕ) : Sequent α → Type _ := DerivationCR (·.complexity < c)

scoped notation :45 "⊢ᴾᶜ[< " c "] " Γ:45 => DerivationClx c Γ

instance : OneSided (Formula α) := ⟨DerivationC⟩

namespace DerivationCR

variable {P : Formula α → Prop} {Δ Δ₁ Δ₂ Γ : Sequent α}

def length : {Δ : Sequent α} → DerivationCR P Δ → ℕ
  | _, axL _ _     => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max dp.length dq.length).succ
  | _, wk d _      => d.length
  | _, cut _ dp dn => (max dp.length dn.length).succ

protected def cast (d : ⊢ᴾᶜ[P] Δ) (e : Δ = Γ) : ⊢ᴾᶜ[P] Γ := cast (by simp[HasVdash.vdash, e]) d

@[simp] lemma length_cast (d : ⊢ᴾᶜ[P] Δ) (e : Δ = Γ) : (d.cast e).length = d.length := by
  rcases e with rfl; simp[DerivationCR.cast]

def cutWeakening {P Q : Formula α → Prop} (h : ∀ p, P p → Q p) : ∀ {Δ}, ⊢ᴾᶜ[P] Δ → ⊢ᴾᶜ[Q] Δ
  | _, axL Δ a      => axL Δ a
  | _, verum Δ      => verum Δ
  | _, and dp dq    => and (dp.cutWeakening h) (dq.cutWeakening h)
  | _, or d         => or (d.cutWeakening h)
  | _, wk d ss      => wk (d.cutWeakening h) ss
  | _, cut hp d₁ d₂ => cut (h _ hp) (d₁.cutWeakening h) (d₂.cutWeakening h)

def verum' (h : ⊤ ∈ Δ) : ⊢ᴾᶜ[P] Δ := (verum Δ).wk (by simp[h])

def axL' (a : α)
    (h : Formula.atom a ∈ Δ) (hn : Formula.natom a ∈ Δ) : ⊢ᴾᶜ[P] Δ := (axL Δ a).wk (by simp[h, hn])

def cCut {p} (d₁ : ⊢¹ p :: Δ) (d₂ : ⊢¹ (~p) :: Δ) : ⊢¹ Δ := cut trivial d₁ d₂

def em {p : Formula α} {Δ : Sequent α} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᴾᶜ[P] Δ := by
  induction p using Formula.rec' generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hrel a           => exact axL' a hpos hneg
  case hnrel a          => exact axL' a hneg hpos
  case hand p q ihp ihq =>
    have ihp : ⊢ᴾᶜ[P] p :: ~p :: ~q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢ᴾᶜ[P] q :: ~p :: ~q :: Δ := ihq (by simp) (by simp)
    have : ⊢ᴾᶜ[P] ~p :: ~q :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor p q ihp ihq  =>
    have ihp : ⊢ᴾᶜ[P] ~p :: p :: q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢ᴾᶜ[P] ~q :: p :: q :: Δ := ihq (by simp) (by simp)
    have : ⊢ᴾᶜ[P] p :: q :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

end DerivationCR

instance : Tait (Formula α) where
  verum := fun Δ => DerivationCR.verum Δ
  and := fun dp dq => (dp.and dq).cast (by simp)
  or := fun d => d.or.cast (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => DerivationCR.em hp hn

instance : Tait.Cut (Formula α) := ⟨DerivationCR.cCut⟩

end Propositional

end LO
