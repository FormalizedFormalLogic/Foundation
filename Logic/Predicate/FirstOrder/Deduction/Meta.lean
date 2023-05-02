import Logic.Predicate.FirstOrder.Deduction.Deduction
import Logic.Predicate.FirstOrder.Meta

namespace FirstOrder

namespace Meta
open Qq

inductive DeductionCode (L : Q(Language.{u})) : Type
  | trans         : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | assumption    : DeductionCode L
  | contradiction : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | trivial       : DeductionCode L
  | explode       : DeductionCode L → DeductionCode L
  | intro         : DeductionCode L → DeductionCode L
  | mdp           : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L  
  | split         : DeductionCode L → DeductionCode L → DeductionCode L
  -- TODO
  | cases         : (e₁ e₂ : Q(SyntacticFormula $L)) → DeductionCode L → DeductionCode L → DeductionCode L → DeductionCode L
  | generalize    : DeductionCode L → DeductionCode L
  -- TODO
  | exCases       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | eqRefl        : DeductionCode L
  | eqSymm        : DeductionCode L → DeductionCode L
  | eqTrans       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | rewriteEq     : (e₁ e₂ : Q(SyntacticTerm $L)) → DeductionCode L → DeductionCode L → DeductionCode L
  | since         : Syntax → DeductionCode L
  | missing       : DeductionCode L
  -- TODO

namespace DeductionCode
variable {L : Q(Language.{u})}

def toStr : DeductionCode L → String
  | trans _ c₁ c₂         => "have: {\n" ++ c₁.toStr ++ "\n}" ++ c₂.toStr
  | assumption            => "assumption"
  | contradiction _ c₁ c₂ => "contradiction: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"    
  | trivial               => "trivial"
  | explode c             => "explode" ++ c.toStr
  | intro c               => "intro\n" ++ c.toStr
  | mdp _ c₁ c₂           => "have: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | split c₁ c₂           => "∧ split: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | cases _ _ c₀ c₁ c₂    => "∨ split: {\n" ++ c₀.toStr ++ "\n}\nor left: {\n" ++ c₁.toStr ++ "\n}\nor right: {\n" ++ c₂.toStr ++ "\n}"
  | generalize c          => "generalize\n" ++ c.toStr
  | exCases _ c₀ c₁       => "∃ cases: {\n" ++ c₀.toStr ++ "\n}\n" ++ c₁.toStr
  | eqRefl                => "refl"
  | eqSymm c              => "symmetry" ++ c.toStr
  | eqTrans _ c₁ c₂       => "trans: {\n" ++ c₁.toStr ++ "\n}\n and: {\n" ++ c₂.toStr ++ "\n}"
  | rewriteEq _ _ c₁ c₂   => "rewrite: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr
  | since _               => "since"
  | missing               => "?"

instance : Repr (DeductionCode L) := ⟨fun b _ => b.toStr⟩

instance : ToString (DeductionCode L) := ⟨toStr⟩

elab "test₁" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let eVerum : Q(SyntacticFormula $L) := q(⊤)
  let eFalsum : Q(SyntacticFormula $L)  := q(⊥)
  let l₀ : List Q(SyntacticFormula $L) := [eFalsum]
  let l₁ : List Q(SyntacticFormula $L) := eVerum :: l₀
  let el₀ := Qq.toQList (u := levelZero) l₀
  let el₁ := Qq.toQList (u := levelZero) l₁
  let eb₁ := q(Proof.trivial (l := $el₀)) -- verum el eVerum
  let some eelem := Qq.toQListOfElem eVerum l₁ | throwError "err" --el eVerum
  let eb₂ : Q(Proof [Formula.verum, Formula.falsum] Formula.verum) := q(Proof.assumption $eelem)
  let eb₁₂ := q(Proof.block $eb₁ $eb₂)
  return eb₁₂

end DeductionCode

end Meta

end FirstOrder