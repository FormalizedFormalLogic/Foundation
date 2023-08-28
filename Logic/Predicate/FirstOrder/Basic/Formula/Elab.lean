import Logic.Predicate.FirstOrder.Basic.Term.Elab
import Logic.Predicate.FirstOrder.Basic.Formula.Formula

namespace FirstOrder

namespace SubFormula

declare_syntax_cat subformula
syntax "⊤" : subformula
syntax "⊥" : subformula
syntax:45 subterm:45 " = " subterm:0 : subformula
syntax:45 subterm:45 " ≠ " subterm:0 : subformula
syntax:45 subterm:45 " < " subterm:0 : subformula
syntax:45 subterm:45 " ≮ " subterm:0 : subformula
syntax:45 "⟨" term "⟩(" subterm,* ")" : subformula
syntax:max "¬" subformula:35 : subformula
syntax:32 subformula:32 " ∧ " subformula:33 : subformula
syntax:32 "⋀ " ident ", " subformula : subformula
syntax:30 subformula:30 " ∨ " subformula:31 : subformula
syntax:max "∀ " subformula:35 : subformula
syntax:max "∃ " subformula:35 : subformula
syntax:max "∀[" subformula "] " subformula:35 : subformula
syntax:25 "∀* " subformula:24 : subformula
syntax:max "∃[" subformula "] " subformula:35 : subformula

syntax subformula "[" subterm,* "]" : subformula
syntax:max "⇑" subformula:10 : subformula

syntax "(" subformula ")" : subformula
syntax:max "!" term:max : subformula
syntax "“" subformula "”" : term
 
macro_rules
  | `(“ ⊤ ”)                                       => `(⊤)
  | `(“ ⊥ ”)                                       => `(⊥)
  | `(“ ! $t:term ”)                               => `($t)
  | `(“ ⟨ $d:term ⟩( $t:subterm,* ) ”)             => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(rel $d $v)
  | `(“ ¬ $p:subformula ”)                         => `(~“$p”)
  | `(“ $t:subterm = $u:subterm ”)                 => `(rel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm ≠ $u:subterm ”)                 => `(nrel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm < $u:subterm ”)                 => `(rel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm ≮ $u:subterm ”)                 => `(nrel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $p:subformula ∧ $q:subformula ”)           => `(“$p” ⋏ “$q”)
  | `(“ ⋀ $i, $p:subformula ”)                    => `(Matrix.conj fun $i => “$p”)
  | `(“ $p:subformula ∨ $q:subformula ”)           => `(“$p” ⋎ “$q”)
  | `(“ ∀ $p:subformula ”)                         => `(∀' “$p”)
  | `(“ ∃ $p:subformula ”)                         => `(∃' “$p”)
  | `(“ ∀[$p:subformula] $q:subformula ”)          => `(∀[“$p”] “$q”)
  | `(“ ∃[$p:subformula] $q:subformula ”)          => `(∃[“$p”] “$q”)
  | `(“ ∀* $p:subformula ”)                        => `(univClosure “$p”)
  | `(“ $p:subformula [ $t:subterm,* ] ”)            => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(Rew.substsl $v “$p”)
  | `(“ ⇑$p:subformula ”)                         => `(Rew.shiftl “$p”)
  | `(“ ( $x ) ”)                                  => `(“$x”)

#check “ ¬(∀ ∀ (#0 + 1) * #1 < #0 + #1 ∨ 0 < 5) ”
#check “⋀ i, #i < #i + 9”

syntax:10 subformula:9 " → " subformula:10 : subformula
syntax:10 subformula:10 " ↔ " subformula:10 : subformula

macro_rules
  | `(“ $p:subformula → $q:subformula ”) => `(“$p” ⟶ “$q”)
  | `(“ $p:subformula ↔ $q:subformula ”) => `(“$p” ⟷ “$q”)

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

@[app_unexpander SubFormula.rel]
def unexpandFunc : Unexpander
  | `($_ $c ![])                 => `(“ ⟨$c⟩() ”)
  | `($_ $f ![ᵀ“ $t ”])          => `(“ ⟨$f⟩($t) ”)
  | `($_ $f ![ᵀ“ $t ”, ᵀ“ $u ”]) => `(“ ⟨$f⟩($t, $u) ”)
  | _                            => throw ()

@[app_unexpander HasAnd.and]
def unexpandAnd : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ∧ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ∧ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ∧ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasOr.or]
def unexpandOr : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ∨ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ∨ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ∨ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasNeg.neg]
def unexpandNeg : Unexpander
  | `($_ “$p:subformula”) => `(“ ¬$p ”)
  | _                     => throw ()

@[app_unexpander HasUniv.univ]
def unexpandUniv : Unexpander
  | `($_ “$p:subformula”) => `(“ ∀ $p ”)
  | _                     => throw ()

@[app_unexpander HasEx.ex]
def unexpandEx : Unexpander
  | `($_ “$p:subformula”) => `(“ ∃ $p ”)
  | _                     => throw ()

@[app_unexpander HasArrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p → $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p → !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t → $q) ”)
  | _                                     => throw ()

@[app_unexpander HasLogicSymbols.iff]
def unexpandIff : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ↔ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ↔ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ↔ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasLogicSymbols.ball]
def unexpandBall : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ (∀[$p] $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ (∀[$p] !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (∀[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander HasLogicSymbols.bex]
def unexpandBEx : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ (∃[$p] $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ (∃[$p] !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (∃[!$t] $q) ”)
  | _                                     => throw ()

@[app_unexpander FunLike.coe]
def unexpandRewToFum : Unexpander
  | `($_ [→ ᵀ“$t:subterm”]                “$p:subformula”) => `(“ ($p:subformula)[$t ] ”)
  | `($_ [→ #$x]                          “$p:subformula”) => `(“ ($p:subformula)[#$x] ”)
  | `($_ [→ &$x]                          “$p:subformula”) => `(“ ($p:subformula)[&$x] ”)
  | `($_ [→ $t ]                          “$p:subformula”) => `(“ ($p:subformula)[ᵀ!$t] ”)
  | `($_ [→ ᵀ“$t:subterm”, ᵀ“$u:subterm”] “$p:subformula”) => `(“ ($p:subformula)[$t,  $u ] ”)
  | `($_ [→ ᵀ“$t:subterm”, #$y          ] “$p:subformula”) => `(“ ($p:subformula)[$t,  #$y] ”)
  | `($_ [→ ᵀ“$t:subterm”, &$y          ] “$p:subformula”) => `(“ ($p:subformula)[$t,  &$y] ”)
  | `($_ [→ ᵀ“$t:subterm”, $u           ] “$p:subformula”) => `(“ ($p:subformula)[$t,  ᵀ!$u] ”)
  | `($_ [→ #$x,           ᵀ“$u:subterm”] “$p:subformula”) => `(“ ($p:subformula)[#$x, $u ] ”)
  | `($_ [→ #$x,           #$y          ] “$p:subformula”) => `(“ ($p:subformula)[#$x, #$y] ”)
  | `($_ [→ #$x,           &$y          ] “$p:subformula”) => `(“ ($p:subformula)[#$x, &$y] ”)
  | `($_ [→ #$x,           $u           ] “$p:subformula”) => `(“ ($p:subformula)[#$x, ᵀ!$u] ”)
  | `($_ [→ &$x,           ᵀ“$u:subterm”] “$p:subformula”) => `(“ ($p:subformula)[&$x, $u ] ”)
  | `($_ [→ &$x,           #$y          ] “$p:subformula”) => `(“ ($p:subformula)[&$x, #$y] ”)
  | `($_ [→ &$x,           &$y          ] “$p:subformula”) => `(“ ($p:subformula)[&$x, &$y] ”)
  | `($_ [→ &$x,           $u           ] “$p:subformula”) => `(“ ($p:subformula)[&$x, ᵀ!$u] ”)
  | `($_ [→ $t,            ᵀ“$u:subterm”] “$p:subformula”) => `(“ ($p:subformula)[ᵀ!$t, $u ] ”)
  | `($_ [→ $t,            #$y          ] “$p:subformula”) => `(“ ($p:subformula)[ᵀ!$t, #$y] ”)
  | `($_ [→ $t,            &$y          ] “$p:subformula”) => `(“ ($p:subformula)[ᵀ!$t, &$y] ”)
  | `($_ [→ $t,            $u           ] “$p:subformula”) => `(“ ($p:subformula)[ᵀ!$t, ᵀ!$u] ”)
  | _                                           => throw ()


@[app_unexpander Matrix.conj]
def unexpandMatrixConj : Unexpander
  | `($_ fun $i:ident => “$p:subformula”) => `(“ (⋀ $i, $p) ”)
  | _                                     => throw ()

@[app_unexpander FunLike.coe]
def unexpandShift : Unexpander
  | `($_ “$p:subformula”) => `(“ ⇑ $p ”)
  | _                     => throw ()

@[app_unexpander SubFormula.rel]
def unexpandRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm = $u  ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm = #$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm = &$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm = ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        = $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        = #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        = &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        = ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        = $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        = #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        = &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        = ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       = $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       = #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       = &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       = ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm < $u  ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm < #$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm < &$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm < ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        < $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        < #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        < &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        < ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        < $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        < #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        < &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        < ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       < $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       < #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       < &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       < ᵀ!$u ”)

  | _                                             => throw ()

@[app_unexpander SubFormula.nrel]
def unexpandNRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm ≠ $u  ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm ≠ #$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm ≠ &$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm ≠ ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        ≠ $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≠ #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≠ &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        ≠ $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≠ #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≠ &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       ≠ $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≠ #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≠ &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≠ ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm ≮ $u  ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm ≮ #$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm ≮ &$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm ≮ ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        ≮ $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≮ #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≮ &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        ≮ $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≮ #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≮ &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       ≮ $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≮ #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≮ &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≮ ᵀ!$u ”)

  | _                                             => throw ()

#check “ ¬∃ ∀ ((#0 + 1) * #1 < #0 + #1 ↔ 0 < &5) ”
#check (“0 < 0 → ∀ 0 < #0 → 0 ≮ 2” : Sentence Language.oRing)
#check “¬⊤ ∨ ((#0 < 5)) [#3, 7][2, #3]”
#check “⋀ i, #i < #i + 9”
#check “∀[#0 < 1] #0 = 0” 

end delab

end SubFormula