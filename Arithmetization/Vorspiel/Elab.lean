import Logic.FirstOrder.Basic

open Lean PrettyPrinter Delaborator SubExpr

namespace LO

namespace FirstOrder

namespace Semiterm

open Qq Lean Elab Meta Tactic Term

declare_syntax_cat lfoterm
syntax:max "#" num : lfoterm
syntax:max "&" term:max : lfoterm
syntax:max "⋆" : lfoterm
syntax ident : lfoterm
syntax:max "!!" term:max : lfoterm
syntax num : lfoterm
syntax:70 "ᵀ⟨" term "⟩(" lfoterm,* ")" : lfoterm
syntax:50 lfoterm:50 " + " lfoterm:51 : lfoterm
syntax:60 lfoterm:60 " * " lfoterm:61 : lfoterm
syntax:65 lfoterm:65 " ^ " lfoterm:66 : lfoterm
syntax lfoterm " ^' " num  : lfoterm
syntax:67 "exp " lfoterm:68 : lfoterm
syntax:75 "⟨" lfoterm ", " lfoterm "⟩" : lfoterm

syntax "(" lfoterm ")" : lfoterm

syntax lfoterm "ᵀ[" lfoterm,* "]" : lfoterm
syntax "⁂namelistT[ " ident,* " ] “" lfoterm:0 "”" : term

syntax "ᵀ“" lfoterm:0 "”" : term



macro_rules
/-
  | `(ᵀ“ # $n:term ”)                   => `(#$n)
  | `(ᵀ“ & $n:term ”)                   => `(&$n)
  | `(ᵀ“ ⋆ ”)                           => `(Operator.Star.star.const)
-/
  | `( ⁂namelistT[ $names,* ] “ $name:ident ” )                 => do
    if let some n := names.getElems.getIdx? name then
      let s : TSyntax `num := .num n
      `(# $(.num n))
    else (by {  })

/--/
  | `(ᵀ“ !! $t:term ”)                  => `($t)
  | `(ᵀ“ $n:num ”)                      => `(Semiterm.Operator.const (Operator.numeral _ $n))
  | `(ᵀ“ ᵀ⟨ $d:term ⟩( $t:lfoterm,* ) ”) => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Operator.operator $d $v)
  | `(ᵀ“ $t:lfoterm + $u:lfoterm ”)       => `(Operator.Add.add.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:lfoterm * $u:lfoterm ”)       => `(Operator.Mul.mul.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:lfoterm ^ $u:lfoterm ”)       => `(Operator.Pow.pow.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:lfoterm ^' $n:num ”)         => `((Operator.npow _ $n).operator ![ᵀ“$t”])
  | `(ᵀ“ exp $t:lfoterm ”)               => `(Operator.Exp.exp.operator ![ᵀ“$t”])
  | `(ᵀ“ ⟨ $t:lfoterm, $u:lfoterm ⟩ ”)    => `(Operator.Pairing.pair.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:lfoterm ᵀ[$u:lfoterm,*] ”)    => do
    let v ← u.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Rew.substs $v ᵀ“$t”)
  | `(ᵀ“ ( $x ) ”)                      => `(ᵀ“$x”)

#check (ᵀ“ ᵀ⟨Operator.Add.add⟩(&2 + &0, ᵀ⟨Operator.Zero.zero⟩())” : Semiterm Language.oRing ℕ 8)
#check (ᵀ“ ᵀ⟨Operator.Add.add⟩(&2 + &0, ᵀ⟨Operator.Zero.zero⟩())” : Semiterm Language.oRing ℕ 8)
#check (ᵀ“#3 ^' 2” : Semiterm Language.oRing ℕ 8)
#check Semiterm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty)
