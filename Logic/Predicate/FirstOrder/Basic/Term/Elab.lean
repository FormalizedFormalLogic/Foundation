import Logic.Predicate.FirstOrder.Basic.Term.Term
open Lean PrettyPrinter Delaborator SubExpr

namespace LO

namespace FirstOrder

namespace Subterm

declare_syntax_cat foterm
syntax:max "#" term:max : foterm
syntax:max "&" term:max : foterm
syntax ident : foterm
syntax:max "ᵀ!" term:max : foterm
syntax num : foterm
syntax:70 "ᵀ⟨" term "⟩(" foterm,* ")" : foterm
syntax:50 foterm:50 " + " foterm:51 : foterm
syntax:60 foterm:60 " * " foterm:61 : foterm
syntax:65 foterm:65 " ^ " foterm:66 : foterm
syntax:67 "exp " foterm:68 : foterm
syntax:75 "⟨" foterm ", " foterm "⟩" : foterm

syntax "(" foterm ")" : foterm

syntax foterm "ᵀ[" foterm,* "]" : foterm
syntax:80 "⤒" foterm:80 : foterm
syntax:80 "ᵀ⇑" foterm:80 : foterm
syntax:80 "ᵀᶠ" foterm:80 : foterm
syntax:80 "ᵀᵇ" foterm:80 : foterm

syntax "ᵀ“" foterm:0 "”" : term

macro_rules
  | `(ᵀ“ # $n:term”)                               => `(#$n)
  | `(ᵀ“ & $n:term ”)                              => `(&$n)
  | `(ᵀ“ $name:ident ”)                            => `(& $(quote name.getId.getString!))
  | `(ᵀ“ ᵀ! $t:term ”)                             => `($t)
  | `(ᵀ“ $n:num ”)                                 => `(Subterm.Operator.const (numeral _ $n))
  | `(ᵀ“ ᵀ⟨ $d:term ⟩( $t:foterm,* ) ”)            => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(func $d $v)
  | `(ᵀ“ $t:foterm + $u:foterm ”)                  => `(Operator.operator Subterm.Add.add ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:foterm * $u:foterm ”)                  => `(Operator.operator Subterm.Mul.mul ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:foterm ^ $u:foterm ”)                  => `(Operator.operator Subterm.Pow.pow ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ exp $t:foterm ”)                          => `(Operator.operator Subterm.Exp.exp ![ᵀ“$t”])
  | `(ᵀ“ ⟨ $t:foterm, $u:foterm ⟩ ”)               => `(Operator.operator Subterm.Pairing.pair ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ ᵀ⇑$t:foterm ”)                           => `(Rew.shift ᵀ“$t”)
  | `(ᵀ“ $t:foterm ᵀ[$u:foterm,*] ”)               => do
    let v ← u.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Rew.substs $v ᵀ“$t”)
  | `(ᵀ“ ⤒$t:foterm ”)                            => `(Rew.bShift ᵀ“$t”)
  | `(ᵀ“ ᵀᶠ $t:foterm ”)                           => `(Rew.free ᵀ“$t”)
  | `(ᵀ“ ᵀᵇ $t:foterm ”)                           => `(Rew.fix ᵀ“$t”)
  | `(ᵀ“ ( $x ) ”)                                 => `(ᵀ“$x”)

#check Operator.operator Subterm.Add.add

#check (ᵀ“ ᵀ⟨Language.ORing.Func.mul⟩(&2 + &0, ᵀ⟨Language.ORing.Func.zero⟩())” : Subterm Language.oRing ℕ 8)
#check (ᵀ“ ᵀ⟨Language.ORing.Func.mul⟩(&2 + &0, ᵀ⟨Language.ORing.Func.zero⟩())” : Subterm Language.oRing ℕ 8)
#check ᵀ“ᵀ⇑(3 * #3 + 9)”
#check Subterm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty)

section delab

instance : Coe NumLit (TSyntax `foterm) where
  coe s := ⟨s.raw⟩

/-
@[app_unexpander Subterm.fvar]
def unexpsnderFver : Unexpander
  | `($_ $name:str) => `($name)
  | _ => throw ()
-/

@[app_unexpander numeral]
def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z)
  | _ => throw ()

@[app_unexpander Operator.const]
def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(ᵀ“$z”)
  | _ => throw ()

notation "lang(+)" => Language.Add.add
notation "lang(*)" => Language.Mul.mul
notation "lang(^)" => Language.Pow.pow
notation "lang(exp)" => Language.Exp.exp
notation "lang(⟨⟩)" => Language.Pairing.pair

@[app_unexpander Language.Add.add]
def unexpsnderAdd : Unexpander
  | `($_) => `(lang(+))

@[app_unexpander Language.Mul.mul]
def unexpsnderMul : Unexpander
  | `($_) => `(lang(*))

@[app_unexpander Language.Pow.pow]
def unexpsnderPow : Unexpander
  | `($_) => `(lang(^))

@[app_unexpander FunLike.coe]
def unexpandShift : Unexpander
  | `($_ ⇑                          ᵀ“$t”) => `(ᵀ“ ᵀ⇑$t ”)
  | `($_ [→ ]                       ᵀ“$t”) => `(ᵀ“ $t ᵀ[] ”)
  | `($_ [→ ᵀ“$t₁”]                 ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁] ”)
  | `($_ [→ ᵀ“$t₁”, ᵀ“$t₂”]         ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁, $t₂] ”)
  | `($_ [→ ᵀ“$t₁”, ᵀ“$t₂”, ᵀ“$t₃”] ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁, $t₂, $t₃] ”)
  | _           => throw ()

@[app_unexpander Subterm.func]
def unexpandFuncArith : Unexpander
  | `($_ lang(exp) ![ᵀ“$t:foterm”]) => `(ᵀ“ exp $t ”)
  | `($_ lang(exp) ![#$x:term])      => `(ᵀ“ exp #$x ”)
  | `($_ lang(exp) ![&$x:term])      => `(ᵀ“ exp &$x ”)
  | `($_ lang(exp) ![$t])            => `(ᵀ“ exp ᵀ!$t ”)

  | `($_ lang(+) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(ᵀ“ ($t + $u) ”)
  | `($_ lang(+) ![ᵀ“$t:foterm”, #$x:term     ]) => `(ᵀ“ ($t + #$x) ”)
  | `($_ lang(+) ![ᵀ“$t:foterm”, &$x:term     ]) => `(ᵀ“ ($t + &$x) ”)
  | `($_ lang(+) ![ᵀ“$t:foterm”, $u           ]) => `(ᵀ“ ($t + ᵀ!$u) ”)
  | `($_ lang(+) ![#$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (#$x + $u) ”)
  | `($_ lang(+) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x + #$y) ”)
  | `($_ lang(+) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x + &$y) ”)
  | `($_ lang(+) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x + ᵀ!$u) ”)
  | `($_ lang(+) ![&$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (&$x + $u) ”)
  | `($_ lang(+) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x + #$y) ”)
  | `($_ lang(+) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x + &$y) ”)
  | `($_ lang(+) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x + ᵀ!$u) ”)
  | `($_ lang(+) ![$t,            ᵀ“$u:foterm”]) => `(ᵀ“ (ᵀ!$t + $u) ”)
  | `($_ lang(+) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t + #$y) ”)
  | `($_ lang(+) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t + &$y) ”)
  | `($_ lang(+) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t + ᵀ!$u) ”)

  | `($_ lang(*) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(ᵀ“ ($t * $u) ”)
  | `($_ lang(*) ![ᵀ“$t:foterm”, #$x:term     ]) => `(ᵀ“ ($t * #$x) ”)
  | `($_ lang(*) ![ᵀ“$t:foterm”, &$x:term     ]) => `(ᵀ“ ($t * &$x) ”)
  | `($_ lang(*) ![ᵀ“$t:foterm”, $u           ]) => `(ᵀ“ ($t * ᵀ!$u) ”)
  | `($_ lang(*) ![#$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (#$x * $u) ”)
  | `($_ lang(*) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x * #$y) ”)
  | `($_ lang(*) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x * &$y) ”)
  | `($_ lang(*) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x * ᵀ!$u) ”)
  | `($_ lang(*) ![&$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (&$x * $u) ”)
  | `($_ lang(*) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x * #$y) ”)
  | `($_ lang(*) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x * &$y) ”)
  | `($_ lang(*) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x * ᵀ!$u) ”)
  | `($_ lang(*) ![$t,            ᵀ“$u:foterm”]) => `(ᵀ“ (ᵀ!$t * $u) ”)
  | `($_ lang(*) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t * #$y) ”)
  | `($_ lang(*) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t * &$y) ”)
  | `($_ lang(*) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t * ᵀ!$u) ”)

  | `($_ lang(^) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(ᵀ“ ($t ^ $u) ”)
  | `($_ lang(^) ![ᵀ“$t:foterm”, #$x:term     ]) => `(ᵀ“ ($t ^ #$x) ”)
  | `($_ lang(^) ![ᵀ“$t:foterm”, &$x:term     ]) => `(ᵀ“ ($t ^ &$x) ”)
  | `($_ lang(^) ![ᵀ“$t:foterm”, $u           ]) => `(ᵀ“ ($t ^ ᵀ!$u) ”)
  | `($_ lang(^) ![#$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (#$x ^ $u) ”)
  | `($_ lang(^) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x ^ #$y) ”)
  | `($_ lang(^) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x ^ &$y) ”)
  | `($_ lang(^) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x ^ ᵀ!$u) ”)
  | `($_ lang(^) ![&$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ (&$x ^ $u) ”)
  | `($_ lang(^) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x ^ #$y) ”)
  | `($_ lang(^) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x ^ &$y) ”)
  | `($_ lang(^) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x ^ ᵀ!$u) ”)
  | `($_ lang(^) ![$t,            ᵀ“$u:foterm”]) => `(ᵀ“ (ᵀ!$t ^ $u) ”)
  | `($_ lang(^) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t ^ #$y) ”)
  | `($_ lang(^) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t ^ &$y) ”)
  | `($_ lang(^) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t ^ ᵀ!$u) ”)

  | `($_ lang(⟨⟩) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(ᵀ“ ⟨$t, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:foterm”, #$x:term     ]) => `(ᵀ“ ⟨$t, #$x ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:foterm”, &$x:term     ]) => `(ᵀ“ ⟨$t, &$x ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:foterm”, $u           ]) => `(ᵀ“ ⟨$t, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ ⟨#$x, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      #$y:term     ]) => `(ᵀ“ ⟨#$x, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      &$y:term     ]) => `(ᵀ“ ⟨#$x, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      $u           ]) => `(ᵀ“ ⟨#$x, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      ᵀ“$u:foterm”]) => `(ᵀ“ ⟨&$x, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      #$y:term     ]) => `(ᵀ“ ⟨&$x, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      &$y:term     ]) => `(ᵀ“ ⟨&$x, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      $u           ]) => `(ᵀ“ ⟨&$x, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            ᵀ“$u:foterm”]) => `(ᵀ“ ⟨ᵀ!$t, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            #$y:term     ]) => `(ᵀ“ ⟨ᵀ!$t, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            &$y:term     ]) => `(ᵀ“ ⟨ᵀ!$t, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            $u           ]) => `(ᵀ“ ⟨ᵀ!$t, ᵀ!$u⟩ ”)
  | _                                             => throw ()

#check numeral Language.oRing 99
#check (ᵀ“1 + 8” : Subterm Language.oRing ℕ 8)
#check (Subterm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty) : Subterm Language.oRing ℕ 8)
#check [→ &0, &5] ᵀ“3 * #3 + 9”
#check Rew.shift ᵀ“(3 * #3 + 9)”
#check ᵀ“(3 * #3 * x + y + z)”

end delab

end Subterm

end FirstOrder

end LO
