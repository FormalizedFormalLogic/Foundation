import Logic.Propositional.Classical.Basic.Formula
import Logic.Logic.Calculus

namespace LO

namespace Propositional.Classical

variable {α : Type*}

abbrev Sequent (α : Type*) := List (Formula α)

inductive Derivation (T : Theory α) : Sequent α → Type _
| axL (Δ a)   : Derivation T (Formula.atom a :: Formula.natom a :: Δ)
| verum (Δ)   : Derivation T (⊤ :: Δ)
| or {Δ p q}  : Derivation T (p :: q :: Δ) → Derivation T (p ⋎ q :: Δ)
| and {Δ p q} : Derivation T (p :: Δ) → Derivation T (q :: Δ) → Derivation T (p ⋏ q :: Δ)
| wk {Δ Γ}    : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
| cut {Δ p}   : Derivation T (p :: Δ) → Derivation T (~p :: Δ) → Derivation T Δ
| root {p}    : p ∈ T → Derivation T [p]

instance : OneSided (Formula α) (Theory α) := ⟨Derivation⟩

namespace Derivation

variable {T : Theory α} {Δ Δ₁ Δ₂ Γ : Sequent α}

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

def em {p : Formula α} {Δ : Sequent α} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : T ⟹ Δ := by
  induction p using Formula.rec' generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hatom a          => exact axL' a hpos hneg
  case hnatom a         => exact axL' a hneg hpos
  case hand p q ihp ihq =>
    have ihp : T ⟹ p :: ~p :: ~q :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ q :: ~p :: ~q :: Δ := ihq (by simp) (by simp)
    have : T ⟹ ~p :: ~q :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor p q ihp ihq  =>
    have ihp : T ⟹ ~p :: p :: q :: Δ := ihp (by simp) (by simp)
    have ihq : T ⟹ ~q :: p :: q :: Δ := ihq (by simp) (by simp)
    have : T ⟹ p :: q :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

end Derivation

instance : Tait (Formula α) (Theory α) where
  verum := fun _ Δ => Derivation.verum Δ
  and := fun dp dq => Derivation.cast (dp.and dq) (by simp)
  or := fun d => Derivation.cast d.or (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => Derivation.em hp hn

instance : Tait.Cut (Formula α) (Theory α) := ⟨Derivation.cut⟩

end Propositional.Classical

end LO
