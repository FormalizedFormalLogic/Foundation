import Logic.Propositional.Classical.Basic.Formula
import Logic.Logic.Calculus

namespace LO

namespace Propositional.Classical

variable {α : Type*}

abbrev Sequent (α : Type*) := List (Formula α)

inductive Derivation : Sequent α → Type _
| axL (Δ a)   : Derivation (Formula.atom a :: Formula.natom a :: Δ)
| verum (Δ)   : Derivation (⊤ :: Δ)
| or {Δ p q}  : Derivation (p :: q :: Δ) → Derivation (p ⋎ q :: Δ)
| and {Δ p q} : Derivation (p :: Δ) → Derivation (q :: Δ) → Derivation (p ⋏ q :: Δ)
| wk {Δ Γ}    : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| cut {Δ p}   : Derivation (p :: Δ) → Derivation (~p :: Δ) → Derivation Δ

instance : OneSided (Formula α) := ⟨Derivation⟩

namespace Derivation

variable {Δ Δ₁ Δ₂ Γ : Sequent α}

def length : {Δ : Sequent α} → ⊢¹ Δ → ℕ
  | _, axL _ _     => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max (length dp) (length dq)).succ
  | _, wk d _      => d.length.succ
  | _, cut dp dn => (max (length dp) (length dn)).succ

protected def cast (d : ⊢¹ Δ) (e : Δ = Γ) : ⊢¹ Γ := cast (by simp[HasVdash.vdash, e]) d

@[simp] lemma length_cast (d : ⊢¹ Δ) (e : Δ = Γ) : length (Derivation.cast d e) = length d := by
  rcases e with rfl; simp[Derivation.cast]

def verum' (h : ⊤ ∈ Δ) : ⊢¹ Δ := (verum Δ).wk (by simp[h])

def axL' (a : α)
    (h : Formula.atom a ∈ Δ) (hn : Formula.natom a ∈ Δ) : ⊢¹ Δ := (axL Δ a).wk (by simp[h, hn])

def em {p : Formula α} {Δ : Sequent α} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢¹ Δ := by
  induction p using Formula.rec' generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hatom a          => exact axL' a hpos hneg
  case hnatom a         => exact axL' a hneg hpos
  case hand p q ihp ihq =>
    have ihp : ⊢¹ p :: ~p :: ~q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢¹ q :: ~p :: ~q :: Δ := ihq (by simp) (by simp)
    have : ⊢¹ ~p :: ~q :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor p q ihp ihq  =>
    have ihp : ⊢¹ ~p :: p :: q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢¹ ~q :: p :: q :: Δ := ihq (by simp) (by simp)
    have : ⊢¹ p :: q :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

end Derivation

instance : Tait (Formula α) where
  verum := fun Δ => Derivation.verum Δ
  and := fun dp dq => Derivation.cast (dp.and dq) (by simp)
  or := fun d => Derivation.cast d.or (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => Derivation.em hp hn

instance : Tait.Cut (Formula α) := ⟨Derivation.cut⟩

end Propositional.Classical

end LO
