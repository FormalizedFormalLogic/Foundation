import Logic.Predicate.FirstOrder.Basic.Term
import Logic.Predicate.FirstOrder.Basic.Formula
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
  | `(ᵀ“ $n:num ”)                                 => `(Subterm.Operator.const (Operator.numeral _ $n))
  | `(ᵀ“ ᵀ⟨ $d:term ⟩( $t:foterm,* ) ”)            => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(func $d $v)
  | `(ᵀ“ $t:foterm + $u:foterm ”)                  => `(Operator.Add.add.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:foterm * $u:foterm ”)                  => `(Operator.Mul.mul.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ $t:foterm ^ $u:foterm ”)                  => `(Operator.Pow.pow.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ exp $t:foterm ”)                          => `(Operator.Exp.exp.operator ![ᵀ“$t”])
  | `(ᵀ“ ⟨ $t:foterm, $u:foterm ⟩ ”)               => `(Operator.Pairing.pair.operator ![ᵀ“$t”, ᵀ“$u”])
  | `(ᵀ“ ᵀ⇑$t:foterm ”)                           => `(Rew.shift ᵀ“$t”)
  | `(ᵀ“ $t:foterm ᵀ[$u:foterm,*] ”)               => do
    let v ← u.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Rew.substs $v ᵀ“$t”)
  | `(ᵀ“ ⤒$t:foterm ”)                            => `(Rew.bShift ᵀ“$t”)
  | `(ᵀ“ ᵀᶠ $t:foterm ”)                           => `(Rew.free ᵀ“$t”)
  | `(ᵀ“ ᵀᵇ $t:foterm ”)                           => `(Rew.fix ᵀ“$t”)
  | `(ᵀ“ ( $x ) ”)                                 => `(ᵀ“$x”)

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

@[app_unexpander Operator.numeral]
def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z)
  | _ => throw ()

@[app_unexpander Operator.const]
def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(ᵀ“$z”)
  | _ => throw ()

notation "lang(+)" => Add.add
notation "lang(*)" => Mul.mul
notation "lang(^)" => Pow.pow

@[app_unexpander Add.add]
def unexpsnderAdd : Unexpander
  | `($_) => `(lang(+))

@[app_unexpander Mul.mul]
def unexpsnderMul : Unexpander
  | `($_) => `(lang(*))

@[app_unexpander FunLike.coe]
def unexpandShift : Unexpander
  | `($_ ⇑                          ᵀ“$t”) => `(ᵀ“ ᵀ⇑$t ”)
  | `($_ [→ ]                       ᵀ“$t”) => `(ᵀ“ $t ᵀ[] ”)
  | `($_ [→ ᵀ“$t₁”]                 ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁] ”)
  | `($_ [→ ᵀ“$t₁”, ᵀ“$t₂”]         ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁, $t₂] ”)
  | `($_ [→ ᵀ“$t₁”, ᵀ“$t₂”, ᵀ“$t₃”] ᵀ“$t”) => `(ᵀ“ $t ᵀ[$t₁, $t₂, $t₃] ”)
  | _           => throw ()

@[app_unexpander Subterm.Operator.operator]
def unexpandFuncArith : Unexpander
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
  | _                                             => throw ()

#check Operator.numeral Language.oRing 99
#check (ᵀ“1 + 8” : Subterm Language.oRing ℕ 8)
#check (Subterm.func Language.Mul.mul (ᵀ“1” :> ᵀ“3” :> Matrix.vecEmpty) : Subterm Language.oRing ℕ 8)
#check [→ &0, &5] ᵀ“3 * #3 + 9”
#check Rew.shift ᵀ“(3 * #3 + 9)”
#check ᵀ“(3 * #3 * x + y + z)”

end delab

end Subterm


namespace Subformula

declare_syntax_cat foformula
syntax "⊤" : foformula
syntax "⊥" : foformula
syntax:45 foterm:45 " = " foterm:0 : foformula
syntax:45 foterm:45 " ≠ " foterm:0 : foformula
syntax:45 foterm:45 " < " foterm:0 : foformula
syntax:45 foterm:45 " ≮ " foterm:0 : foformula
syntax:45 "⟨" term "⟩(" foterm,* ")" : foformula
syntax:max "¬" foformula:35 : foformula
syntax:32 foformula:32 " ∧ " foformula:33 : foformula
syntax:32 "⋀ " ident ", " foformula : foformula
syntax:30 foformula:30 " ∨ " foformula:31 : foformula
syntax:max "∀ " foformula:35 : foformula
syntax:max "∃ " foformula:35 : foformula
syntax:max "∀[" foformula "] " foformula:35 : foformula
syntax:25 "∀* " foformula:24 : foformula
syntax:max "∃[" foformula "] " foformula:35 : foformula

syntax foformula "[" foterm,* "]" : foformula
syntax:max "⇑" foformula:10 : foformula

syntax "(" foformula ")" : foformula
syntax:max "!" term:max : foformula
syntax "“" foformula "”" : term

macro_rules
  | `(“ ⊤ ”)                                       => `(⊤)
  | `(“ ⊥ ”)                                       => `(⊥)
  | `(“ ! $t:term ”)                               => `($t)
  | `(“ ⟨ $d:term ⟩( $t:foterm,* ) ”)             => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(rel $d $v)
  | `(“ ¬ $p:foformula ”)                         => `(~“$p”)
  | `(“ $t:foterm = $u:foterm ”)                 => `(Operator.operator Operator.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:foterm ≠ $u:foterm ”)                 => `(~(Operator.operator Operator.Eq.eq ![ᵀ“$t”, ᵀ“$u”]))
  | `(“ $t:foterm < $u:foterm ”)                 => `(Operator.operator Operator.LT.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:foterm ≮ $u:foterm ”)                 => `(~(Operator.operator Operator.LT.lt ![ᵀ“$t”, ᵀ“$u”]))
  | `(“ $p:foformula ∧ $q:foformula ”)           => `(“$p” ⋏ “$q”)
  | `(“ ⋀ $i, $p:foformula ”)                    => `(Matrix.conj fun $i => “$p”)
  | `(“ $p:foformula ∨ $q:foformula ”)           => `(“$p” ⋎ “$q”)
  | `(“ ∀ $p:foformula ”)                         => `(∀' “$p”)
  | `(“ ∃ $p:foformula ”)                         => `(∃' “$p”)
  | `(“ ∀[$p:foformula] $q:foformula ”)          => `(∀[“$p”] “$q”)
  | `(“ ∃[$p:foformula] $q:foformula ”)          => `(∃[“$p”] “$q”)
  | `(“ ∀* $p:foformula ”)                        => `(univClosure “$p”)
  | `(“ $p:foformula [ $t:foterm,* ] ”)            => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `((Rew.substs $v).hom “$p”)
  | `(“ ⇑$p:foformula ”)                         => `(Rew.shift.hom “$p”)
  | `(“ ( $x ) ”)                                  => `(“$x”)

#check “ ¬(∀ ∀ (#0 + 1) * #1 < #0 + #1 ∨ 0 < 5) ”
#check “⋀ i, #i < #i + 9”

syntax:10 foformula:9 " → " foformula:10 : foformula
syntax:10 foformula:10 " ↔ " foformula:10 : foformula

macro_rules
  | `(“ $p:foformula → $q:foformula ”) => `(“$p” ⟶ “$q”)
  | `(“ $p:foformula ↔ $q:foformula ”) => `(“$p” ⟷ “$q”)

#reduce (“(∃ ⊤) ↔ !(∃' ⊤)” : Sentence Language.oRing)

section delab
open Lean PrettyPrinter Delaborator SubExpr

notation "op(=)" => Eq.eq
notation "op(<)" => LT.lt

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

@[app_unexpander Language.LT.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

@[app_unexpander Subformula.rel]
def unexpandFunc : Unexpander
  | `($_ $c ![])                 => `(“ ⟨$c⟩() ”)
  | `($_ $f ![ᵀ“ $t ”])          => `(“ ⟨$f⟩($t) ”)
  | `($_ $f ![ᵀ“ $t ”, ᵀ“ $u ”]) => `(“ ⟨$f⟩($t, $u) ”)
  | _                            => throw ()

@[app_unexpander Wedge.wedge]
def unexpandAnd : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ ($p ∧ $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ ($p ∧ !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (!$t ∧ $q) ”)
  | _                                     => throw ()

@[app_unexpander Vee.vee]
def unexpandOr : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ ($p ∨ $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ ($p ∨ !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (!$t ∨ $q) ”)
  | _                                     => throw ()

@[app_unexpander Tilde.tilde]
def unexpandNeg : Unexpander
  | `($_ “$p:foformula”) => `(“ ¬$p ”)
  | _                     => throw ()

@[app_unexpander UnivQuantifier.univ]
def unexpandUniv : Unexpander
  | `($_ “$p:foformula”) => `(“ ∀ $p ”)
  | _                     => throw ()

@[app_unexpander ExQuantifier.ex]
def unexpandEx : Unexpander
  | `($_ “$p:foformula”) => `(“ ∃ $p ”)
  | _                     => throw ()

@[app_unexpander Arrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ ($p → $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ ($p → !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (!$t → $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicSymbol.iff]
def unexpandIff : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ ($p ↔ $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ ($p ↔ !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (!$t ↔ $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicSymbol.ball]
def unexpandBall : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ (∀[$p] $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ (∀[$p] !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (∀[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicSymbol.bex]
def unexpandBEx : Unexpander
  | `($_ “$p:foformula” “$q:foformula”) => `(“ (∃[$p] $q) ”)
  | `($_ “$p:foformula” $u:term)         => `(“ (∃[$p] !$u) ”)
  | `($_ $t:term         “$q:foformula”) => `(“ (∃[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander FunLike.coe]
def unexpandRewToFum : Unexpander
  | `($_ [→ ᵀ“$t:foterm”]                “$p:foformula”) => `(“ ($p:foformula)[$t ] ”)
  | `($_ [→ #$x]                          “$p:foformula”) => `(“ ($p:foformula)[#$x] ”)
  | `($_ [→ &$x]                          “$p:foformula”) => `(“ ($p:foformula)[&$x] ”)
  | `($_ [→ $t ]                          “$p:foformula”) => `(“ ($p:foformula)[ᵀ!$t] ”)
  | `($_ [→ ᵀ“$t:foterm”, ᵀ“$u:foterm”] “$p:foformula”) => `(“ ($p:foformula)[$t,  $u ] ”)
  | `($_ [→ ᵀ“$t:foterm”, #$y          ] “$p:foformula”) => `(“ ($p:foformula)[$t,  #$y] ”)
  | `($_ [→ ᵀ“$t:foterm”, &$y          ] “$p:foformula”) => `(“ ($p:foformula)[$t,  &$y] ”)
  | `($_ [→ ᵀ“$t:foterm”, $u           ] “$p:foformula”) => `(“ ($p:foformula)[$t,  ᵀ!$u] ”)
  | `($_ [→ #$x,           ᵀ“$u:foterm”] “$p:foformula”) => `(“ ($p:foformula)[#$x, $u ] ”)
  | `($_ [→ #$x,           #$y          ] “$p:foformula”) => `(“ ($p:foformula)[#$x, #$y] ”)
  | `($_ [→ #$x,           &$y          ] “$p:foformula”) => `(“ ($p:foformula)[#$x, &$y] ”)
  | `($_ [→ #$x,           $u           ] “$p:foformula”) => `(“ ($p:foformula)[#$x, ᵀ!$u] ”)
  | `($_ [→ &$x,           ᵀ“$u:foterm”] “$p:foformula”) => `(“ ($p:foformula)[&$x, $u ] ”)
  | `($_ [→ &$x,           #$y          ] “$p:foformula”) => `(“ ($p:foformula)[&$x, #$y] ”)
  | `($_ [→ &$x,           &$y          ] “$p:foformula”) => `(“ ($p:foformula)[&$x, &$y] ”)
  | `($_ [→ &$x,           $u           ] “$p:foformula”) => `(“ ($p:foformula)[&$x, ᵀ!$u] ”)
  | `($_ [→ $t,            ᵀ“$u:foterm”] “$p:foformula”) => `(“ ($p:foformula)[ᵀ!$t, $u ] ”)
  | `($_ [→ $t,            #$y          ] “$p:foformula”) => `(“ ($p:foformula)[ᵀ!$t, #$y] ”)
  | `($_ [→ $t,            &$y          ] “$p:foformula”) => `(“ ($p:foformula)[ᵀ!$t, &$y] ”)
  | `($_ [→ $t,            $u           ] “$p:foformula”) => `(“ ($p:foformula)[ᵀ!$t, ᵀ!$u] ”)
  | _                                           => throw ()

@[app_unexpander Matrix.conj]
def unexpandMatrixConj : Unexpander
  | `($_ fun $i:ident => “$p:foformula”) => `(“ (⋀ $i, $p) ”)
  | _                                     => throw ()

@[app_unexpander FunLike.coe]
def unexpandShift : Unexpander
  | `($_ “$p:foformula”) => `(“ ⇑ $p ”)
  | _                     => throw ()

@[app_unexpander Subformula.Operator.operator]
def unexpandOpArith : Unexpander
  | `($_ op(=) ![ᵀ“$t:foterm”,  ᵀ“$u:foterm”]) => `(“ $t:foterm = $u   ”)
  | `($_ op(=) ![ᵀ“$t:foterm”,  #$y:term    ]) => `(“ $t:foterm = #$y  ”)
  | `($_ op(=) ![ᵀ“$t:foterm”,  &$y:term    ]) => `(“ $t:foterm = &$y  ”)
  | `($_ op(=) ![ᵀ“$t:foterm”,  $u          ]) => `(“ $t:foterm = ᵀ!$u ”)
  | `($_ op(=) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x       = $u   ”)
  | `($_ op(=) ![#$x:term,      #$y:term    ]) => `(“ #$x       = #$y  ”)
  | `($_ op(=) ![#$x:term,      &$y:term    ]) => `(“ #$x       = &$y  ”)
  | `($_ op(=) ![#$x:term,      $u          ]) => `(“ #$x       = ᵀ!$u ”)
  | `($_ op(=) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x       = $u   ”)
  | `($_ op(=) ![&$x:term,      #$y:term    ]) => `(“ &$x       = #$y  ”)
  | `($_ op(=) ![&$x:term,      &$y:term    ]) => `(“ &$x       = &$y  ”)
  | `($_ op(=) ![&$x:term,      $u          ]) => `(“ &$x       = ᵀ!$u ”)
  | `($_ op(=) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t      = $u   ”)
  | `($_ op(=) ![$t:term,       #$y:term    ]) => `(“ ᵀ!$t      = #$y  ”)
  | `($_ op(=) ![$t:term,       &$y:term    ]) => `(“ ᵀ!$t      = &$y  ”)
  | `($_ op(=) ![$t:term,       $u          ]) => `(“ ᵀ!$t      = ᵀ!$u ”)

  | `($_ op(<) ![ᵀ“$t:foterm”, ᵀ“$u:foterm” ]) => `(“ $t:foterm < $u    ”)
  | `($_ op(<) ![ᵀ“$t:foterm”, #$y:term     ]) => `(“ $t:foterm < #$y   ”)
  | `($_ op(<) ![ᵀ“$t:foterm”, &$y:term     ]) => `(“ $t:foterm < &$y   ”)
  | `($_ op(<) ![ᵀ“$t:foterm”, $u           ]) => `(“ $t:foterm < ᵀ!$u  ”)
  | `($_ op(<) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x        < $u   ”)
  | `($_ op(<) ![#$x:term,      #$y:term    ]) => `(“ #$x        < #$y  ”)
  | `($_ op(<) ![#$x:term,      &$y:term    ]) => `(“ #$x        < &$y  ”)
  | `($_ op(<) ![#$x:term,      $u          ]) => `(“ #$x        < ᵀ!$u ”)
  | `($_ op(<) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x        < $u   ”)
  | `($_ op(<) ![&$x:term,      #$y:term    ]) => `(“ &$x        < #$y  ”)
  | `($_ op(<) ![&$x:term,      &$y:term    ]) => `(“ &$x        < &$y  ”)
  | `($_ op(<) ![&$x:term,      $u          ]) => `(“ &$x        < ᵀ!$u ”)
  | `($_ op(<) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t       < $u   ”)
  | `($_ op(<) ![$t:term,       #$y:term    ]) => `(“ ᵀ!$t       < #$y  ”)
  | `($_ op(<) ![$t:term,       &$y:term    ]) => `(“ ᵀ!$t       < &$y  ”)
  | `($_ op(<) ![$t:term,       $u          ]) => `(“ ᵀ!$t       < ᵀ!$u ”)

  | _                                             => throw ()

#check “ ¬∃ ∀ ((#0 + 1) * #1 < #0 + #1 ↔ 0 < &5) ”
#check (“0 < 0 → ∀ 0 < #0 → 0 ≮ 2” : Sentence Language.oRing)
#check “¬⊤ ∨ ((#0 < 5)) [#3, 7][2, #3]”
#check “⋀ i, #i < #i + 9”
#check “∀[#0 < 1] #0 = 0”
#check “x < y → y < z → x < z”

end delab

end Subformula

end FirstOrder

end LO
