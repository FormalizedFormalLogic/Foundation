import Logic.FirstOrder.Basic.Operator

open Lean PrettyPrinter Delaborator SubExpr

namespace LO.FirstOrder

namespace DeBruijnIndex

open Semiterm Semiformula

declare_syntax_cat foterm
syntax:max "#" term:max : foterm
syntax:max "&" term:max : foterm
syntax:max "⋆" : foterm
syntax ident : foterm
syntax:max "!!" term:max : foterm
syntax num : foterm
syntax:70 "ᵀ⟨" term "⟩(" foterm,* ")" : foterm
syntax:50 foterm:50 " + " foterm:51 : foterm
syntax:60 foterm:60 " * " foterm:61 : foterm
syntax:65 foterm:65 " ^ " foterm:66 : foterm
syntax foterm " ^' " num  : foterm
syntax:67 "exp " foterm:68 : foterm
syntax:75 "⟨" foterm ", " foterm "⟩" : foterm

syntax "(" foterm ")" : foterm

syntax foterm "ᵀ[" foterm,* "]" : foterm
syntax "dᵀ“" foterm:0 "”" : term

macro_rules
  | `(dᵀ“ # $n:term ”)                   => `(#$n)
  | `(dᵀ“ & $n:term ”)                   => `(&$n)
  | `(dᵀ“ ⋆ ”)                           => `(Operator.Star.star.const)
  | `(dᵀ“ $name:ident ”)                 => `(& $(quote name.getId.getString!))
  | `(dᵀ“ !! $t:term ”)                  => `($t)
  | `(dᵀ“ $n:num ”)                      => `(Semiterm.Operator.const (Operator.numeral _ $n))
  | `(dᵀ“ ᵀ⟨ $d:term ⟩( $t:foterm,* ) ”) => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(dᵀ“$a” :> $s))
    `(Operator.operator $d $v)
  | `(dᵀ“ $t:foterm + $u:foterm ”)       => `(Operator.Add.add.operator ![dᵀ“$t”, dᵀ“$u”])
  | `(dᵀ“ $t:foterm * $u:foterm ”)       => `(Operator.Mul.mul.operator ![dᵀ“$t”, dᵀ“$u”])
  | `(dᵀ“ $t:foterm ^ $u:foterm ”)       => `(Operator.Pow.pow.operator ![dᵀ“$t”, dᵀ“$u”])
  | `(dᵀ“ $t:foterm ^' $n:num ”)         => `((Operator.npow _ $n).operator ![dᵀ“$t”])
  | `(dᵀ“ exp $t:foterm ”)               => `(Operator.Exp.exp.operator ![dᵀ“$t”])
  | `(dᵀ“ ⟨ $t:foterm, $u:foterm ⟩ ”)    => `(Operator.Pairing.pair.operator ![dᵀ“$t”, dᵀ“$u”])
  | `(dᵀ“ $t:foterm ᵀ[$u:foterm,*] ”)    => do
    let v ← u.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(dᵀ“$a” :> $s))
    `(Rew.substs $v dᵀ“$t”)
  | `(dᵀ“ ( $x ) ”)                      => `(dᵀ“$x”)

#check (dᵀ“ ᵀ⟨Operator.Add.add⟩(&2 + &0, ᵀ⟨Operator.Zero.zero⟩())” : Semiterm Language.oRing ℕ 8)
#check (dᵀ“ ᵀ⟨Operator.Add.add⟩(&2 + &0, ᵀ⟨Operator.Zero.zero⟩())” : Semiterm Language.oRing ℕ 8)
#check (dᵀ“#3 ^' 2” : Semiterm Language.oRing ℕ 8)
#check Semiterm.func Language.Mul.mul (dᵀ“1” :> dᵀ“3” :> Matrix.vecEmpty)

/-
section delab

instance : Coe NumLit (TSyntax `foterm) where
  coe s := ⟨s.raw⟩

@[app_unexpander Semiterm.fvar]
def unexpsnderFver : Unexpander
  | `($_ $name:str) => `($name)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.numeral]
def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.const]
def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(dᵀ“$z”)
  | _ => throw ()

@[app_unexpander Add.add]
def unexpsnderAdd : Unexpander
  | `($_) => `(op(+))

@[app_unexpander Mul.mul]
def unexpsnderMul : Unexpander
  | `($_) => `(op(*))

@[app_unexpander DFunLike.coe]
def unexpandShift : Unexpander
  | `($_ [→ ]                       dᵀ“$t”) => `(dᵀ“ $t ᵀ[] ”)
  | `($_ [→ dᵀ“$t₁”]                 dᵀ“$t”) => `(dᵀ“ $t ᵀ[$t₁] ”)
  | `($_ [→ dᵀ“$t₁”, dᵀ“$t₂”]         dᵀ“$t”) => `(dᵀ“ $t ᵀ[$t₁, $t₂] ”)
  | `($_ [→ dᵀ“$t₁”, dᵀ“$t₂”, dᵀ“$t₃”] dᵀ“$t”) => `(dᵀ“ $t ᵀ[$t₁, $t₂, $t₃] ”)
  | _           => throw ()

@[app_unexpander Semiterm.Operator.operator]
def unexpandFuncArith : Unexpander
  | `($_ op(+) ![dᵀ“$t:foterm”, dᵀ“$u:foterm”]) => `(dᵀ“ ($t + $u) ”)
  | `($_ op(+) ![dᵀ“$t:foterm”, #$x:term     ]) => `(dᵀ“ ($t + #$x) ”)
  | `($_ op(+) ![dᵀ“$t:foterm”, &$x:term     ]) => `(dᵀ“ ($t + &$x) ”)
  | `($_ op(+) ![dᵀ“$t:foterm”, $u           ]) => `(dᵀ“ ($t + !!$u) ”)
  | `($_ op(+) ![#$x:term,      dᵀ“$u:foterm”]) => `(dᵀ“ (#$x + $u) ”)
  | `($_ op(+) ![#$x:term,      #$y:term     ]) => `(dᵀ“ (#$x + #$y) ”)
  | `($_ op(+) ![#$x:term,      &$y:term     ]) => `(dᵀ“ (#$x + &$y) ”)
  | `($_ op(+) ![#$x:term,      $u           ]) => `(dᵀ“ (#$x + !!$u) ”)
  | `($_ op(+) ![&$x:term,      dᵀ“$u:foterm”]) => `(dᵀ“ (&$x + $u) ”)
  | `($_ op(+) ![&$x:term,      #$y:term     ]) => `(dᵀ“ (&$x + #$y) ”)
  | `($_ op(+) ![&$x:term,      &$y:term     ]) => `(dᵀ“ (&$x + &$y) ”)
  | `($_ op(+) ![&$x:term,      $u           ]) => `(dᵀ“ (&$x + !!$u) ”)
  | `($_ op(+) ![$t,            dᵀ“$u:foterm”]) => `(dᵀ“ (!!$t + $u) ”)
  | `($_ op(+) ![$t,            #$y:term     ]) => `(dᵀ“ (!!$t + #$y) ”)
  | `($_ op(+) ![$t,            &$y:term     ]) => `(dᵀ“ (!!$t + &$y) ”)
  | `($_ op(+) ![$t,            $u           ]) => `(dᵀ“ (!!$t + !!$u) ”)

  | `($_ op(*) ![dᵀ“$t:foterm”, dᵀ“$u:foterm”]) => `(dᵀ“ ($t * $u) ”)
  | `($_ op(*) ![dᵀ“$t:foterm”, #$x:term     ]) => `(dᵀ“ ($t * #$x) ”)
  | `($_ op(*) ![dᵀ“$t:foterm”, &$x:term     ]) => `(dᵀ“ ($t * &$x) ”)
  | `($_ op(*) ![dᵀ“$t:foterm”, $u           ]) => `(dᵀ“ ($t * !!$u) ”)
  | `($_ op(*) ![#$x:term,      dᵀ“$u:foterm”]) => `(dᵀ“ (#$x * $u) ”)
  | `($_ op(*) ![#$x:term,      #$y:term     ]) => `(dᵀ“ (#$x * #$y) ”)
  | `($_ op(*) ![#$x:term,      &$y:term     ]) => `(dᵀ“ (#$x * &$y) ”)
  | `($_ op(*) ![#$x:term,      $u           ]) => `(dᵀ“ (#$x * !!$u) ”)
  | `($_ op(*) ![&$x:term,      dᵀ“$u:foterm”]) => `(dᵀ“ (&$x * $u) ”)
  | `($_ op(*) ![&$x:term,      #$y:term     ]) => `(dᵀ“ (&$x * #$y) ”)
  | `($_ op(*) ![&$x:term,      &$y:term     ]) => `(dᵀ“ (&$x * &$y) ”)
  | `($_ op(*) ![&$x:term,      $u           ]) => `(dᵀ“ (&$x * !!$u) ”)
  | `($_ op(*) ![$t,            dᵀ“$u:foterm”]) => `(dᵀ“ (!!$t * $u) ”)
  | `($_ op(*) ![$t,            #$y:term     ]) => `(dᵀ“ (!!$t * #$y) ”)
  | `($_ op(*) ![$t,            &$y:term     ]) => `(dᵀ“ (!!$t * &$y) ”)
  | `($_ op(*) ![$t,            $u           ]) => `(dᵀ“ (!!$t * !!$u) ”)

  | _                                             => throw ()



end delab
-/
#check Operator.numeral Language.oRing 99
#check (dᵀ“1 + 8” : Semiterm Language.oRing ℕ 8)
#check (Semiterm.func Language.Mul.mul (dᵀ“1” :> dᵀ“3” :> Matrix.vecEmpty) : Semiterm Language.oRing ℕ 8)
#check [→ &0, &5] dᵀ“3 * #3 + 9”
#check Rew.shift dᵀ“(3 * #3 + 9)”
#check dᵀ“(3 * #3 * x + y + z)”

declare_syntax_cat foformula
syntax "⊤" : foformula
syntax "⊥" : foformula
syntax:45 foterm:45 " = " foterm:0 : foformula
syntax:45 foterm:45 " ≠ " foterm:0 : foformula
syntax:45 foterm:45 " < " foterm:0 : foformula
syntax:45 foterm:45 " ≮ " foterm:0 : foformula
syntax:45 "⟨" term "⟩(" foterm,* ")" : foformula
syntax:max "¬" foformula:35 : foformula
syntax:32 foformula:33 " ∧ " foformula:32 : foformula
syntax:32 "⋀ " ident ", " foformula : foformula
syntax:30 foformula:31 " ∨ " foformula:30 : foformula
syntax:max "∀ " foformula:35 : foformula
syntax:max "∃ " foformula:35 : foformula
syntax:max "∀[" foformula "] " foformula:35 : foformula
syntax:25 "∀* " foformula:24 : foformula
syntax:max "∃[" foformula "] " foformula:35 : foformula

syntax foformula "[" foterm,* "]" : foformula
syntax foformula ".[" foterm,* "]" : foformula
syntax:max "⇑" foformula:10 : foformula

syntax "(" foformula ")" : foformula
syntax:max "!" term:max : foformula
syntax "d“" foformula "”" : term

macro_rules
  | `(d“ ⊤ ”)                             => `(⊤)
  | `(d“ ⊥ ”)                             => `(⊥)
  | `(d“ ! $t:term ”)                     => `($t)
  | `(d“ ⟨ $d:term ⟩( $t:foterm,* ) ”)    => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(dᵀ“$a” :> $s))
    `(Operaator.operator $d $v)
  | `(d“ ¬ $p:foformula ”)                => `(~d“$p”)
  | `(d“ $t:foterm = $u:foterm ”)         => `(Operator.operator Operator.Eq.eq ![dᵀ“$t”, dᵀ“$u”])
  | `(d“ $t:foterm ≠ $u:foterm ”)         => `(~(Operator.operator Operator.Eq.eq ![dᵀ“$t”, dᵀ“$u”]))
  | `(d“ $t:foterm < $u:foterm ”)         => `(Operator.operator Operator.LT.lt ![dᵀ“$t”, dᵀ“$u”])
  | `(d“ $t:foterm ≮ $u:foterm ”)         => `(~(Operator.operator Operator.LT.lt ![dᵀ“$t”, dᵀ“$u”]))
  | `(d“ $p:foformula ∧ $q:foformula ”)   => `(d“$p” ⋏ d“$q”)
  | `(d“ ⋀ $i, $p:foformula ”)           => `(Matrix.conj fun $i => d“$p”)
  | `(d“ $p:foformula ∨ $q:foformula ”)   => `(d“$p” ⋎ d“$q”)
  | `(d“ ∀ $p:foformula ”)                => `(∀' d“$p”)
  | `(d“ ∃ $p:foformula ”)                => `(∃' d“$p”)
  | `(d“ ∀[$p:foformula] $q:foformula ”)  => `(∀[d“$p”] d“$q”)
  | `(d“ ∃[$p:foformula] $q:foformula ”)  => `(∃[d“$p”] d“$q”)
  | `(d“ ∀* $p:foformula ”)               => `(univClosure d“$p”)
  | `(d“ $p:foformula [ $t:foterm,* ] ”)  => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(dᵀ“$a” :> $s))
    `((Rew.substs $v).hom d“$p”)
  | `(d“ $p:foformula .[ $t:foterm,* ] ”) => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(dᵀ“$a” :> $s))
    `((Rew.embSubsts $v).hom d“$p”)
  | `(d“ ⇑$p:foformula ”)                => `(Rew.shift.hom d“$p”)
  | `(d“ ( $x ) ”)                        => `(d“$x”)

#check d“ ¬(∀ ∀ (#0 + 1) * #1 < #0 + #1 ∨ 0 < 5) ”
#check d“⋀ i, #i < #i + 9”
#check d“0 < 1 ∨ 0 = 1 ∨1 < 0”

syntax:10 foformula:9 " → " foformula:10 : foformula
syntax:10 foformula:10 " ↔ " foformula:10 : foformula

macro_rules
  | `(d“ $p:foformula → $q:foformula ”) => `(d“$p” ⟶ d“$q”)
  | `(d“ $p:foformula ↔ $q:foformula ”) => `(d“$p” ⟷ d“$q”)

#reduce (d“(∃ ⊤) ↔ !(∃' ⊤)” : Sentence Language.oRing)

/-
section delab

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

@[app_unexpander Language.LT.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

@[app_unexpander Semiformula.rel]
def unexpandFunc : Unexpander
  | `($_ $c ![])                 => `(d“ ⟨$c⟩() ”)
  | `($_ $f ![dᵀ“ $t ”])          => `(d“ ⟨$f⟩($t) ”)
  | `($_ $f ![dᵀ“ $t ”, dᵀ“ $u ”]) => `(d“ ⟨$f⟩($t, $u) ”)
  | _                            => throw ()

@[app_unexpander Wedge.wedge]
def unexpandAnd : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ ($p ∧ $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ ($p ∧ !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (!$t ∧ $q) ”)
  | _                                     => throw ()

@[app_unexpander Vee.vee]
def unexpandOr : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ ($p ∨ $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ ($p ∨ !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (!$t ∨ $q) ”)
  | _                                     => throw ()

@[app_unexpander Tilde.tilde]
def unexpandNeg : Unexpander
  | `($_ d“$p:foformula”) => `(d“ ¬$p ”)
  | _                     => throw ()

@[app_unexpander UnivQuantifier.univ]
def unexpandUniv : Unexpander
  | `($_ d“$p:foformula”) => `(d“ ∀ $p ”)
  | _                     => throw ()

@[app_unexpander ExQuantifier.ex]
def unexpandEx : Unexpander
  | `($_ d“$p:foformula”) => `(d“ ∃ $p ”)
  | _                     => throw ()

@[app_unexpander Arrow.arrow]
def unexpandArrow : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ ($p → $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ ($p → !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (!$t → $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicalConnective.iff]
def unexpandIff : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ ($p ↔ $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ ($p ↔ !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (!$t ↔ $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicalConnective.ball]
def unexpandBall : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ (∀[$p] $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ (∀[$p] !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (∀[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander LogicalConnective.bex]
def unexpandBEx : Unexpander
  | `($_ d“$p:foformula” d“$q:foformula”) => `(d“ (∃[$p] $q) ”)
  | `($_ d“$p:foformula” $u:term)         => `(d“ (∃[$p] !$u) ”)
  | `($_ $t:term         d“$q:foformula”) => `(d“ (∃[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander DFunLike.coe]
def unexpandRewToFum : Unexpander
  | `($_ [→ dᵀ“$t:foterm”]                d“$p:foformula”) => `(d“ ($p:foformula)[$t ] ”)
  | `($_ [→ #$x]                          d“$p:foformula”) => `(d“ ($p:foformula)[#$x] ”)
  | `($_ [→ &$x]                          d“$p:foformula”) => `(d“ ($p:foformula)[&$x] ”)
  | `($_ [→ $t ]                          d“$p:foformula”) => `(d“ ($p:foformula)[!!$t] ”)
  | `($_ [→ dᵀ“$t:foterm”, dᵀ“$u:foterm”] d“$p:foformula”) => `(d“ ($p:foformula)[$t,  $u ] ”)
  | `($_ [→ dᵀ“$t:foterm”, #$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[$t,  #$y] ”)
  | `($_ [→ dᵀ“$t:foterm”, &$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[$t,  &$y] ”)
  | `($_ [→ dᵀ“$t:foterm”, $u           ] d“$p:foformula”) => `(d“ ($p:foformula)[$t,  !!$u] ”)
  | `($_ [→ #$x,           dᵀ“$u:foterm”] d“$p:foformula”) => `(d“ ($p:foformula)[#$x, $u ] ”)
  | `($_ [→ #$x,           #$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[#$x, #$y] ”)
  | `($_ [→ #$x,           &$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[#$x, &$y] ”)
  | `($_ [→ #$x,           $u           ] d“$p:foformula”) => `(d“ ($p:foformula)[#$x, !!$u] ”)
  | `($_ [→ &$x,           dᵀ“$u:foterm”] d“$p:foformula”) => `(d“ ($p:foformula)[&$x, $u ] ”)
  | `($_ [→ &$x,           #$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[&$x, #$y] ”)
  | `($_ [→ &$x,           &$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[&$x, &$y] ”)
  | `($_ [→ &$x,           $u           ] d“$p:foformula”) => `(d“ ($p:foformula)[&$x, !!$u] ”)
  | `($_ [→ $t,            dᵀ“$u:foterm”] d“$p:foformula”) => `(d“ ($p:foformula)[!!$t, $u ] ”)
  | `($_ [→ $t,            #$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[!!$t, #$y] ”)
  | `($_ [→ $t,            &$y          ] d“$p:foformula”) => `(d“ ($p:foformula)[!!$t, &$y] ”)
  | `($_ [→ $t,            $u           ] d“$p:foformula”) => `(d“ ($p:foformula)[!!$t, !!$u] ”)
  | _                                           => throw ()

@[app_unexpander Matrix.conj]
def unexpandMatrixConj : Unexpander
  | `($_ fun $i:ident => d“$p:foformula”) => `(d“ (⋀ $i, $p) ”)
  | _                                     => throw ()

@[app_unexpander DFunLike.coe]
def unexpandShift : Unexpander
  | `($_ d“$p:foformula”) => `(d“ ⇑ $p ”)
  | _                     => throw ()

@[app_unexpander Semiformula.Operator.operator]
def unexpandOpArith : Unexpander
  | `($_ op(=) ![dᵀ“$t:foterm”,  dᵀ“$u:foterm”]) => `(d“ $t:foterm = $u   ”)
  | `($_ op(=) ![dᵀ“$t:foterm”,  #$y:term    ]) => `(d“ $t:foterm = #$y  ”)
  | `($_ op(=) ![dᵀ“$t:foterm”,  &$y:term    ]) => `(d“ $t:foterm = &$y  ”)
  | `($_ op(=) ![dᵀ“$t:foterm”,  $u          ]) => `(d“ $t:foterm = !!$u ”)
  | `($_ op(=) ![#$x:term,      dᵀ“$u:foterm”]) => `(d“ #$x       = $u   ”)
  | `($_ op(=) ![#$x:term,      #$y:term    ]) => `(d“ #$x       = #$y  ”)
  | `($_ op(=) ![#$x:term,      &$y:term    ]) => `(d“ #$x       = &$y  ”)
  | `($_ op(=) ![#$x:term,      $u          ]) => `(d“ #$x       = !!$u ”)
  | `($_ op(=) ![&$x:term,      dᵀ“$u:foterm”]) => `(d“ &$x       = $u   ”)
  | `($_ op(=) ![&$x:term,      #$y:term    ]) => `(d“ &$x       = #$y  ”)
  | `($_ op(=) ![&$x:term,      &$y:term    ]) => `(d“ &$x       = &$y  ”)
  | `($_ op(=) ![&$x:term,      $u          ]) => `(d“ &$x       = !!$u ”)
  | `($_ op(=) ![$t:term,       dᵀ“$u:foterm”]) => `(d“ !!$t      = $u   ”)
  | `($_ op(=) ![$t:term,       #$y:term    ]) => `(d“ !!$t      = #$y  ”)
  | `($_ op(=) ![$t:term,       &$y:term    ]) => `(d“ !!$t      = &$y  ”)
  | `($_ op(=) ![$t:term,       $u          ]) => `(d“ !!$t      = !!$u ”)

  | `($_ op(<) ![dᵀ“$t:foterm”, dᵀ“$u:foterm” ]) => `(d“ $t:foterm < $u    ”)
  | `($_ op(<) ![dᵀ“$t:foterm”, #$y:term     ]) => `(d“ $t:foterm < #$y   ”)
  | `($_ op(<) ![dᵀ“$t:foterm”, &$y:term     ]) => `(d“ $t:foterm < &$y   ”)
  | `($_ op(<) ![dᵀ“$t:foterm”, $u           ]) => `(d“ $t:foterm < !!$u  ”)
  | `($_ op(<) ![#$x:term,      dᵀ“$u:foterm”]) => `(d“ #$x        < $u   ”)
  | `($_ op(<) ![#$x:term,      #$y:term    ]) => `(d“ #$x        < #$y  ”)
  | `($_ op(<) ![#$x:term,      &$y:term    ]) => `(d“ #$x        < &$y  ”)
  | `($_ op(<) ![#$x:term,      $u          ]) => `(d“ #$x        < !!$u ”)
  | `($_ op(<) ![&$x:term,      dᵀ“$u:foterm”]) => `(d“ &$x        < $u   ”)
  | `($_ op(<) ![&$x:term,      #$y:term    ]) => `(d“ &$x        < #$y  ”)
  | `($_ op(<) ![&$x:term,      &$y:term    ]) => `(d“ &$x        < &$y  ”)
  | `($_ op(<) ![&$x:term,      $u          ]) => `(d“ &$x        < !!$u ”)
  | `($_ op(<) ![$t:term,       dᵀ“$u:foterm”]) => `(d“ !!$t       < $u   ”)
  | `($_ op(<) ![$t:term,       #$y:term    ]) => `(d“ !!$t       < #$y  ”)
  | `($_ op(<) ![$t:term,       &$y:term    ]) => `(d“ !!$t       < &$y  ”)
  | `($_ op(<) ![$t:term,       $u          ]) => `(d“ !!$t       < !!$u ”)

  | _                                             => throw ()

#check d“ ¬∃ ∀ ((#0 + 1) * #1 < #0 + #1 ↔ 0 < &5) ”
#check (d“0 < 0 → ∀ 0 < #0 → 0 ≮ 2” : Sentence Language.oRing)
#check d“¬⊤ ∨ ((#0 < 5)) [#3, 7][2, #3]”
#check d“⋀ i, #i < #i + 9”
#check d“∀[#0 < 1] #0 = 0”
#check d“x < y → y < z → x < z”

end delab
-/

end DeBruijnIndex

end FirstOrder

end LO
