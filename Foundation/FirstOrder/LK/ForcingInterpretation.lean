module

public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.Vorspiel.ExistsUnique

/-!
# Forcing Interpretation

## References

- [Avi04, Sections 2.2–2.4]
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A definable forcing structure with persistent function graphs. -/
structure ForcingTranslation {L : Language} [L.Eq] (T : Theory L) [𝗘𝗤 L ⪯ T] (K : Language) where
  isCond : Semiformula.Operator L 1
  /-- `strongerThan q p` means that `q` is stronger than `p`. -/
  strongerThan : Semiformula.Operator L 2
  domain : Semiformula.Operator L 2
  /-- The arguments are the condition followed by the relation's arguments. -/
  rel {k} : K.Rel k → Semiformula.Operator L (k + 1)
  /-- The arguments are the condition, the value, and the function's arguments. -/
  func {k} : K.Func k → Semiformula.Operator L (k + 2)
  condition_nonempty :
    T ⊢ “∃ p, @isCond p”
  strongerThan_refl :
    T ⊢ “∀ p, @isCond p → @strongerThan p p”
  strongerThan_trans :
    T ⊢ “∀ p q r, @isCond p → @isCond q → @isCond r →
      @strongerThan p q → @strongerThan q r → @strongerThan p r”
  domain_nonempty :
    T ⊢ “∀ p, @isCond p → ∃ x, @domain p x”
  domain_monotone :
    T ⊢ “∀ p q x, @isCond p → @isCond q → @strongerThan q p → @domain p x → @domain q x”
  rel_monotone {k} (R : K.Rel k) :
    T ⊢ ∀¹* “p q. @isCond p → @isCond q → @strongerThan q p →
      @(rel R) p ⋯ → @(rel R) q ⋯”
  func_defined {k} (f : K.Func k) :
    T ⊢ ∀¹* “p. @isCond p → (⋀ i, @domain p #(i : Fin k).succ) →
      ∃! y, @domain p y ∧ @(func f) p y ⋯”
  func_monotone {k} (f : K.Func k) :
    T ⊢ ∀¹* “p q y. @isCond p → @isCond q → @strongerThan q p →
      (⋀ i, @domain p #(i : Fin k).succ.succ.succ) → @domain p y →
      @(func f) p y ⋯ → @(func f) q y ⋯”

namespace ForcingTranslation

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T]

variable (𝔣 : ForcingTranslation T K)

/-- Universal quantification over conditions stronger than `p`. -/
def allCond (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[𝔣.isCond.operator ![#0] ⋏ 𝔣.strongerThan.operator ![#0, Rew.bShift p]] φ

/-- Universal quantification over the domain at `p`. -/
def fal (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[𝔣.domain.operator ![Rew.bShift p, #0]] φ

/-- Existential quantification over the domain at `p`. -/
def exs (p : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃¹[𝔣.domain.operator ![Rew.bShift p, #0]] φ

notation:64 "∀≤[" 𝔣 ", " p "] " φ => allCond 𝔣 p φ
notation:64 "∀_[" 𝔣 ", " p "] " φ => fal 𝔣 p φ
notation:64 "∃_[" 𝔣 ", " p "] " φ => exs 𝔣 p φ

end ForcingTranslation

namespace BinderNotation

open Lean

syntax:max "∀ " ident " ≤[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∀ " ident " ∈[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ∈[" term "] " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $q ≤[$𝔣] $p, $φ ]) => do
    if binders.elem q then Macro.throwErrorAt q "error: variable is duplicated."
    `(∀≤[$𝔣, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $q $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $x ∈[$𝔣] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∀_[$𝔣, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $x ∈[$𝔣] $p, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated."
    `(∃_[$𝔣, ⤫term($type)[ $binders* | $fbinders* | $p ]]
      ⤫formula($type)[ $x $binders* | $fbinders* | $φ ])

end BinderNotation

namespace ForcingTranslation

variable {L K : Language} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T]
variable (𝔣 : ForcingTranslation T K)

/-- The value of a term, with the condition and value preceding the original variables. -/
def varEqual {n} : Semiterm K ξ n → Semiformula L ξ (n + 2)
  | #x => “p y. @𝔣.domain p y ∧ y = #x.succ.succ”
  | &x => “p y. @𝔣.domain p y ∧ y = &x”
  | .func (arity := k) f v =>
    “p y. @𝔣.domain p y” ⋏ ∃¹^[k] (
      (Matrix.conj fun i ↦
        varEqual (v i) ⇜
          (#((0 : Fin (n + 2)).addNat k) :> #(i.addCast (n + 2)) :>
            fun j ↦ #(j.succ.succ.addNat k))) ⋏
      (𝔣.func f).operator
        (#((0 : Fin (n + 2)).addNat k) :> #((1 : Fin (n + 2)).addNat k) :>
          fun i ↦ #(i.addCast (n + 2))))

def translateRel {k} (R : K.Rel k) (v : Fin k → Semiterm K ξ n) : Semiformula L ξ (n + 1) :=
  ∃¹^[k] (
    (Matrix.conj fun i ↦
      𝔣.varEqual (v i) ⇜
        (#((0 : Fin (n + 1)).addNat k) :> #(i.addCast (n + 1)) :>
          fun j ↦ #(j.succ.addNat k))) ⋏
    (𝔣.rel R).operator
      (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))))

/-- Internal description of `p ⊩ φ`, with the condition at bound variable zero. -/
def translationᵢ {n} : Semisentenceᵢ K n → Semisentence L (n + 1)
  | .rel R v => 𝔣.translateRel R v
  | ⊥ => ⊥
  | φ ⋏ ψ => translationᵢ φ ⋏ translationᵢ ψ
  | φ ⋎ ψ => translationᵢ φ ⋎ translationᵢ ψ
  | φ 🡒 ψ => “p. ∀ q ≤[𝔣] p, !(translationᵢ φ) q ⋯ → !(translationᵢ ψ) q ⋯”
  | ∀¹ φ => “p. ∀ q ≤[𝔣] p, ∀ x ∈[𝔣] q, !(translationᵢ φ) q x ⋯”
  | ∃¹ φ => “p. ∃ x ∈[𝔣] p, !(translationᵢ φ) p x ⋯”

end ForcingTranslation

end FFL.FirstOrder
