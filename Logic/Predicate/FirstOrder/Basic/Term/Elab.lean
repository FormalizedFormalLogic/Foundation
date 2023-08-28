import Logic.Predicate.FirstOrder.Basic.Term.Term

namespace LO

namespace FirstOrder

namespace SubTerm

declare_syntax_cat subterm
syntax:max "#" term:max : subterm
syntax:max "&" term:max : subterm
syntax:max "ᵀ!" term:max : subterm
syntax num : subterm
syntax:70 "ᵀ⟨" term "⟩(" subterm,* ")" : subterm
syntax:50 subterm:50 " + " subterm:51 : subterm
syntax:60 subterm:60 " * " subterm:61 : subterm
syntax:65 subterm:65 " ^ " subterm:66 : subterm
syntax:67 "exp " subterm:68 : subterm
syntax:75 "⟨" subterm ", " subterm "⟩" : subterm

syntax "(" subterm ")" : subterm

syntax subterm "ᵀ[" subterm,* "]" : subterm
syntax:80 "⤒" subterm:80 : subterm
syntax:80 "ᵀ⇑" subterm:80 : subterm
syntax:80 "ᵀᶠ" subterm:80 : subterm
syntax:80 "ᵀᵇ" subterm:80 : subterm

syntax "ᵀ“" subterm:0 "”" : term
 
macro_rules
  | `(ᵀ“ # $n:term”)                                 => `(#$n)
  | `(ᵀ“ & $n:term ”)                                => `(&$n)
  | `(ᵀ“ ᵀ! $t:term ”)                               => `($t)
  | `(ᵀ“ $n:num ”)                                   => `(SubTerm.Operator.const (natLit _ $n))
  | `(ᵀ“ ᵀ⟨ $d:term ⟩( $t:subterm,* ) ”)              => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(func $d $v)
  | `(ᵀ“ $t:subterm + $u:subterm ”)                  => `(func Language.Add.add ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:subterm * $u:subterm ”)                  => `(func Language.Mul.mul ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:subterm ^ $u:subterm ”)                  => `(func Language.Pow.pow ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ exp $t:subterm ”)                           => `(func Language.Exp.exp ![ᵀ“$t”])
  | `(ᵀ“ ⟨ $t:subterm, $u:subterm ⟩ ”)               => `(func Language.Pairing.pair ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ ᵀ⇑$t:subterm ”)                            => `(Rew.shift ᵀ“$t”)
  | `(ᵀ“ $t:subterm ᵀ[$u:subterm,*] ”)               => do
    let v ← u.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Rew.substs $v ᵀ“$t”)
  | `(ᵀ“ ⤒$t:subterm ”)                             => `(Rew.bShift ᵀ“$t”)
  | `(ᵀ“ ᵀᶠ $t:subterm ”)                            => `(Rew.free ᵀ“$t”)
  | `(ᵀ“ ᵀᵇ $t:subterm ”)                            => `(Rew.fix ᵀ“$t”)
  | `(ᵀ“ ( $x ) ”)                                   => `(ᵀ“$x”)

#check Language.Add.add

#check (ᵀ“ ᵀ⟨Language.ORingFunc.mul⟩(&2 + &0, ᵀ⟨Language.ORingFunc.zero⟩())” : SubTerm Language.oRing ℕ 8)
#check (ᵀ“ ᵀ⟨Language.ORingFunc.mul⟩(&2 + &0, ᵀ⟨Language.ORingFunc.zero⟩())” : SubTerm Language.oRing ℕ 8)
#check ᵀ“ᵀ⇑(3 * #3 + 9)”
#check SubTerm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty)

section delab
open Lean PrettyPrinter Delaborator SubExpr

instance : Coe NumLit (TSyntax `subterm) where
  coe s := ⟨s.raw⟩

@[app_unexpander natLit]
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

@[app_unexpander SubTerm.func]
def unexpandFuncArith : Unexpander
  | `($_ lang(exp) ![ᵀ“$t:subterm”]) => `(ᵀ“ exp $t ”)
  | `($_ lang(exp) ![#$x:term])      => `(ᵀ“ exp #$x ”)
  | `($_ lang(exp) ![&$x:term])      => `(ᵀ“ exp &$x ”)
  | `($_ lang(exp) ![$t])            => `(ᵀ“ exp ᵀ!$t ”)

  | `($_ lang(+) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(ᵀ“ ($t + $u) ”)
  | `($_ lang(+) ![ᵀ“$t:subterm”, #$x:term     ]) => `(ᵀ“ ($t + #$x) ”)
  | `($_ lang(+) ![ᵀ“$t:subterm”, &$x:term     ]) => `(ᵀ“ ($t + &$x) ”)
  | `($_ lang(+) ![ᵀ“$t:subterm”, $u           ]) => `(ᵀ“ ($t + ᵀ!$u) ”)
  | `($_ lang(+) ![#$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (#$x + $u) ”)
  | `($_ lang(+) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x + #$y) ”)
  | `($_ lang(+) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x + &$y) ”)
  | `($_ lang(+) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x + ᵀ!$u) ”)
  | `($_ lang(+) ![&$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (&$x + $u) ”)
  | `($_ lang(+) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x + #$y) ”)
  | `($_ lang(+) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x + &$y) ”)
  | `($_ lang(+) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x + ᵀ!$u) ”)
  | `($_ lang(+) ![$t,            ᵀ“$u:subterm”]) => `(ᵀ“ (ᵀ!$t + $u) ”)
  | `($_ lang(+) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t + #$y) ”)
  | `($_ lang(+) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t + &$y) ”)
  | `($_ lang(+) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t + ᵀ!$u) ”)

  | `($_ lang(*) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(ᵀ“ ($t * $u) ”)
  | `($_ lang(*) ![ᵀ“$t:subterm”, #$x:term     ]) => `(ᵀ“ ($t * #$x) ”)
  | `($_ lang(*) ![ᵀ“$t:subterm”, &$x:term     ]) => `(ᵀ“ ($t * &$x) ”)
  | `($_ lang(*) ![ᵀ“$t:subterm”, $u           ]) => `(ᵀ“ ($t * ᵀ!$u) ”)
  | `($_ lang(*) ![#$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (#$x * $u) ”)
  | `($_ lang(*) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x * #$y) ”)
  | `($_ lang(*) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x * &$y) ”)
  | `($_ lang(*) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x * ᵀ!$u) ”)
  | `($_ lang(*) ![&$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (&$x * $u) ”)
  | `($_ lang(*) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x * #$y) ”)
  | `($_ lang(*) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x * &$y) ”)
  | `($_ lang(*) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x * ᵀ!$u) ”)
  | `($_ lang(*) ![$t,            ᵀ“$u:subterm”]) => `(ᵀ“ (ᵀ!$t * $u) ”)
  | `($_ lang(*) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t * #$y) ”)
  | `($_ lang(*) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t * &$y) ”)
  | `($_ lang(*) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t * ᵀ!$u) ”)

  | `($_ lang(^) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(ᵀ“ ($t ^ $u) ”)
  | `($_ lang(^) ![ᵀ“$t:subterm”, #$x:term     ]) => `(ᵀ“ ($t ^ #$x) ”)
  | `($_ lang(^) ![ᵀ“$t:subterm”, &$x:term     ]) => `(ᵀ“ ($t ^ &$x) ”)
  | `($_ lang(^) ![ᵀ“$t:subterm”, $u           ]) => `(ᵀ“ ($t ^ ᵀ!$u) ”)
  | `($_ lang(^) ![#$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (#$x ^ $u) ”)
  | `($_ lang(^) ![#$x:term,      #$y:term     ]) => `(ᵀ“ (#$x ^ #$y) ”)
  | `($_ lang(^) ![#$x:term,      &$y:term     ]) => `(ᵀ“ (#$x ^ &$y) ”)
  | `($_ lang(^) ![#$x:term,      $u           ]) => `(ᵀ“ (#$x ^ ᵀ!$u) ”)
  | `($_ lang(^) ![&$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ (&$x ^ $u) ”)
  | `($_ lang(^) ![&$x:term,      #$y:term     ]) => `(ᵀ“ (&$x ^ #$y) ”)
  | `($_ lang(^) ![&$x:term,      &$y:term     ]) => `(ᵀ“ (&$x ^ &$y) ”)
  | `($_ lang(^) ![&$x:term,      $u           ]) => `(ᵀ“ (&$x ^ ᵀ!$u) ”)
  | `($_ lang(^) ![$t,            ᵀ“$u:subterm”]) => `(ᵀ“ (ᵀ!$t ^ $u) ”)
  | `($_ lang(^) ![$t,            #$y:term     ]) => `(ᵀ“ (ᵀ!$t ^ #$y) ”)
  | `($_ lang(^) ![$t,            &$y:term     ]) => `(ᵀ“ (ᵀ!$t ^ &$y) ”)
  | `($_ lang(^) ![$t,            $u           ]) => `(ᵀ“ (ᵀ!$t ^ ᵀ!$u) ”)

  | `($_ lang(⟨⟩) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(ᵀ“ ⟨$t, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:subterm”, #$x:term     ]) => `(ᵀ“ ⟨$t, #$x ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:subterm”, &$x:term     ]) => `(ᵀ“ ⟨$t, &$x ⟩ ”)
  | `($_ lang(⟨⟩) ![ᵀ“$t:subterm”, $u           ]) => `(ᵀ“ ⟨$t, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ ⟨#$x, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      #$y:term     ]) => `(ᵀ“ ⟨#$x, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      &$y:term     ]) => `(ᵀ“ ⟨#$x, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![#$x:term,      $u           ]) => `(ᵀ“ ⟨#$x, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      ᵀ“$u:subterm”]) => `(ᵀ“ ⟨&$x, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      #$y:term     ]) => `(ᵀ“ ⟨&$x, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      &$y:term     ]) => `(ᵀ“ ⟨&$x, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![&$x:term,      $u           ]) => `(ᵀ“ ⟨&$x, ᵀ!$u⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            ᵀ“$u:subterm”]) => `(ᵀ“ ⟨ᵀ!$t, $u  ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            #$y:term     ]) => `(ᵀ“ ⟨ᵀ!$t, #$y ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            &$y:term     ]) => `(ᵀ“ ⟨ᵀ!$t, &$y ⟩ ”)
  | `($_ lang(⟨⟩) ![$t,            $u           ]) => `(ᵀ“ ⟨ᵀ!$t, ᵀ!$u⟩ ”)
  | _                                             => throw ()

#check natLit Language.oRing 99
#check (ᵀ“1 + 8” : SubTerm Language.oRing ℕ 8)
#check (SubTerm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty) : SubTerm Language.oRing ℕ 8)
#check ᵀ“3 + 8 * exp &6 + 2 * ᵀ!(#3)”
#check [→ &0, &5] ᵀ“3 * #3 + 9”
#check Rew.shift ᵀ“(3 * #3 + 9)”

end delab

end SubTerm

end FirstOrder

end LO