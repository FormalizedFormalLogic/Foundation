import Arithmetization.ISigmaOne.Metamath.Proof.R
import Arithmetization.ISigmaOne.Metamath.DerivabilityConditions.D1
import Arithmetization.ISigmaOne.Metamath.Coding

/-!

# Formalized $\Sigma_1$-Completeness

-/

namespace LO.FirstOrder

section

open Lean PrettyPrinter Delaborator

syntax:max "let " ident " := " term:max first_order_term:61* "; " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $binders* | let $x:ident := $f:term $vs:first_order_term* ; $p:first_order_formula ”) =>
    `(“ $binders* | ∃ $x, !$f:term #0 $vs:first_order_term* ∧ $p ”)

end

namespace Theory

variable (L : Language) [L.Eq]

inductive EQ₀ : Theory L
  | reflAx : EQ₀ “∀ x, x = x”
  | replaceAx (p : Semisentence L 1) : EQ₀ “∀ x y, x = y → !p x → !p y”

end Theory

namespace Arith

def thEQDef : (Language.lDef ℒₒᵣ).TDef where
  ch := .mkSigma “σ |
    ( let v0 := qqBvarDef 0;
      ∃ eq, !qqEQDef eq 1 v0 v0 ∧
      !qqAllDef σ 0 eq ) ∨
    ( ∃ p, !p⌜ℒₒᵣ⌝.isSemiformulaDef.sigma 1 p ∧
      ∃ x0, !qqBvarDef x0 0 ∧
      ∃ x1, !qqBvarDef x1 1 ∧
      ∃ eq, !qqEQDef eq 2 x0 x1 ∧
      ∃ v0, !mkVec₁Def v0 x0 ∧
      ∃ v1, !mkVec₁Def v1 x1 ∧
      ∃ p0, !p⌜ℒₒᵣ⌝.substsDef p0 2 v0 p ∧
      ∃ p1, !p⌜ℒₒᵣ⌝.substsDef p0 2 v1 p ∧
      ∃ imp0, !p⌜ℒₒᵣ⌝.impDef imp0 2 p0 p1 ∧
      ∃ imp1, !p⌜ℒₒᵣ⌝.impDef imp1 2 eq imp0 ∧
      ∃ all0, !qqAllDef all0 1 imp1 ∧
      !qqAllDef σ 0all0)
    ” (by simp)

end Arith

end LO.FirstOrder

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

namespace Formalized



def thEQ :

variable {T : LOR.Theory V} {pT : (Language.lDef ℒₒᵣ).TDef} [T.Defined pT] [EQTheory T] [R₀Theory T]
