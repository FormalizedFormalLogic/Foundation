import Logic.Predicate.FirstOrder.Basic.Term.Elab
import Logic.Predicate.FirstOrder.Basic.Formula.Formula

namespace LO

namespace FirstOrder

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
  | `(“ $t:foterm = $u:foterm ”)                 => `(rel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:foterm ≠ $u:foterm ”)                 => `(nrel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:foterm < $u:foterm ”)                 => `(rel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:foterm ≮ $u:foterm ”)                 => `(nrel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
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

notation "lang(=)" => Language.Eq.eq
notation "lang(<)" => Language.Lt.lt

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(lang(=))

@[app_unexpander Language.Lt.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(lang(<))

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

@[app_unexpander Subformula.rel]
def unexpandRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm = $u  ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, #$y:term     ]) => `(“ $t:foterm = #$y ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, &$y:term     ]) => `(“ $t:foterm = &$y ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, $u           ]) => `(“ $t:foterm = ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x        = $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        = #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        = &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        = ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x        = $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        = #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        = &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        = ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t       = $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       = #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       = &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       = ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm < $u  ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, #$y:term     ]) => `(“ $t:foterm < #$y ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, &$y:term     ]) => `(“ $t:foterm < &$y ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, $u           ]) => `(“ $t:foterm < ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x        < $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        < #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        < &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        < ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x        < $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        < #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        < &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        < ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t       < $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       < #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       < &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       < ᵀ!$u ”)

  | _                                             => throw ()

@[app_unexpander Subformula.nrel]
def unexpandNRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm ≠ $u  ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, #$y:term     ]) => `(“ $t:foterm ≠ #$y ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, &$y:term     ]) => `(“ $t:foterm ≠ &$y ”)
  | `($_ lang(=) ![ᵀ“$t:foterm”, $u           ]) => `(“ $t:foterm ≠ ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x        ≠ $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≠ #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≠ &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x        ≠ $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≠ #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≠ &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t       ≠ $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≠ #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≠ &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≠ ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm ≮ $u  ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, #$y:term     ]) => `(“ $t:foterm ≮ #$y ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, &$y:term     ]) => `(“ $t:foterm ≮ &$y ”)
  | `($_ lang(<) ![ᵀ“$t:foterm”, $u           ]) => `(“ $t:foterm ≮ ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:foterm”]) => `(“ #$x        ≮ $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≮ #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≮ &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:foterm”]) => `(“ &$x        ≮ $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≮ #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≮ &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:foterm”]) => `(“ ᵀ!$t       ≮ $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≮ #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≮ &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≮ ᵀ!$u ”)

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