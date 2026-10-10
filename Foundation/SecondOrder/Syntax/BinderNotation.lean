module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.SecondOrder.Syntax.Rew

/-!
# Binder notation for second-order arithmetic

`s“∀² X, ∀ x, x ∈ X → x + 0 = x”` denotes a second-order arithmetic formula.
In `s“X Y ; x y. …”`, the headers name bound set and number variables, respectively;
replace `.` by `|` to name free variables. Each header starts at index zero.
Numerical terms share the `first_order_term` syntax category. Quantifiers maintain independent
stacks of set and number variables. Names cannot be repeated within either sort.

`!!φ` inserts a formula unchanged. `!φ t₁ … tₙ` substitutes its bound number variables;
`!φ[X₁ … Xₖ] t₁ … tₙ` first substitutes its bound set variables as well.
An optional `⋯` after the number arguments supplies the remaining bound number variables,
starting after the named number binders, as in the first-order notation.
Parenthesize compound formula expressions, as in `!(f a)[X] x`.
Sets can also be written `#i` (bound) or `&i` (free).

The intermediate notation is `⤫formula[boundSets ; boundNumbers | freeSets ; freeNumbers | φ]`.
Extend `second_order_formula` and add `macro_rules` for this notation to define new formula syntax.
Every subformula passes through this notation, including under quantifiers.
Numerical terms use `⤫term[boundNumbers | freeNumbers | t]`. Extend `first_order_term` and add
`macro_rules` for this intermediate notation to define new term syntax, including inside arithmetic
operations and substitution arguments.

These syntax translations are specific to this formalization.
-/

@[expose] public section

namespace FFL.SecondOrder.BinderNotation

open Lean FirstOrder FirstOrder.BinderNotation

syntax "⤫term[" ident* " | " ident* " | " first_order_term:0 "]" : term

macro_rules
  | `(⤫term[ $xs* | $fx* | $t:first_order_term ]) =>
    `(⤫term(lit)[ $xs* | $fx* | $t ])

macro_rules
  | `(⤫term[ $xs* | $fx* | ($t) ]) => `(⤫term[ $xs* | $fx* | $t ])
  | `(⤫term[ $xs* | $fx* | $t + $u ]) =>
    `(FirstOrder.Semiterm.Operator.Add.add.operator
      ![⤫term[ $xs* | $fx* | $t ], ⤫term[ $xs* | $fx* | $u ]])
  | `(⤫term[ $xs* | $fx* | $t * $u ]) =>
    `(FirstOrder.Semiterm.Operator.Mul.mul.operator
      ![⤫term[ $xs* | $fx* | $t ], ⤫term[ $xs* | $fx* | $u ]])
  | `(⤫term[ $xs* | $fx* | $t ^ $u ]) =>
    `(FirstOrder.Semiterm.Operator.Pow.pow.operator
      ![⤫term[ $xs* | $fx* | $t ], ⤫term[ $xs* | $fx* | $u ]])
  | `(⤫term[ $xs* | $fx* | $t ^' $n ]) =>
    `((FirstOrder.Semiterm.Operator.npow _ $n).operator ![⤫term[ $xs* | $fx* | $t ]])
  | `(⤫term[ $xs* | $fx* | $t² ]) =>
    `(⤫term[ $xs* | $fx* | $t ^' 2 ])
  | `(⤫term[ $xs* | $fx* | $t³ ]) =>
    `(⤫term[ $xs* | $fx* | $t ^' 3 ])
  | `(⤫term[ $xs* | $fx* | $t⁴ ]) =>
    `(⤫term[ $xs* | $fx* | $t ^' 4 ])
  | `(⤫term[ $xs* | $fx* | exp $t ]) =>
    `(FirstOrder.Semiterm.Operator.Exp.exp.operator ![⤫term[ $xs* | $fx* | $t ]])
  | `(⤫term[ $xs* | $fx* | !$t:term $vs:first_order_term* $[⋯%$tail]? ]) => do
    let tail ← match tail with
      | none => `(![])
      | some _ => `(fun i => FirstOrder.Semiterm.bvar (finSuccItr i $(quote xs.size)))
    let args ← vs.foldrM (fun v rest => `(⤫term[ $xs* | $fx* | $v ] :> $rest)) tail
    `(FirstOrder.Rew.subst $args $t)
  | `(⤫term[ $xs* | $fx* | .!$t:term $vs:first_order_term* $[⋯%$tail]? ]) => do
    let tail ← match tail with
      | none => `(![])
      | some _ => `(fun i => FirstOrder.Semiterm.bvar (finSuccItr i $(quote xs.size)))
    let args ← vs.foldrM (fun v rest => `(⤫term[ $xs* | $fx* | $v ] :> $rest)) tail
    `(FirstOrder.Rew.embSubsts $args $t)

declare_syntax_cat second_order_set
declare_syntax_cat second_order_formula
declare_syntax_cat second_order_splice

syntax ident : second_order_splice
syntax "(" term ")" : second_order_splice

syntax ident : second_order_set
syntax "#" term:max : second_order_set
syntax "&" term:max : second_order_set
syntax "(" second_order_formula ")" : second_order_formula
syntax "⊤" : second_order_formula
syntax "⊥" : second_order_formula
syntax:32 second_order_formula:33 " ∧ " second_order_formula:32 : second_order_formula
syntax:30 second_order_formula:31 " ∨ " second_order_formula:30 : second_order_formula
syntax:max "¬" second_order_formula:35 : second_order_formula
syntax:10 second_order_formula:9 " → " second_order_formula:10 : second_order_formula
syntax:5 second_order_formula " ↔ " second_order_formula : second_order_formula
syntax:max "∀ " ident+ ", " second_order_formula:0 : second_order_formula
syntax:max "∃ " ident+ ", " second_order_formula:0 : second_order_formula
syntax:max "∀² " ident+ ", " second_order_formula:0 : second_order_formula
syntax:max "∃² " ident+ ", " second_order_formula:0 : second_order_formula
syntax:max "∀¹ " second_order_formula:0 : second_order_formula
syntax:max "∃¹ " second_order_formula:0 : second_order_formula
syntax:max "∀² " second_order_formula:0 : second_order_formula
syntax:max "∃² " second_order_formula:0 : second_order_formula
syntax:45 first_order_term:45 " = " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ≠ " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " < " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ≤ " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " > " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ≥ " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ≮ " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ≰ " first_order_term:0 : second_order_formula
syntax:45 first_order_term:45 " ∈ " second_order_set : second_order_formula
syntax:45 first_order_term:45 " ∉ " second_order_set : second_order_formula
syntax:max "∀ " ident " < " first_order_term ", " second_order_formula:0 : second_order_formula
syntax:max "∃ " ident " < " first_order_term ", " second_order_formula:0 : second_order_formula
syntax:max "∀ " ident " ≤ " first_order_term ", " second_order_formula:0 : second_order_formula
syntax:max "∃ " ident " ≤ " first_order_term ", " second_order_formula:0 : second_order_formula
syntax:max "∀ " ident " ∈ " second_order_set ", " second_order_formula:0 : second_order_formula
syntax:max "∃ " ident " ∈ " second_order_set ", " second_order_formula:0 : second_order_formula
syntax:60 "!!" term:max : second_order_formula
syntax:60 "!" second_order_splice ("[" second_order_set* "]")?
  first_order_term:61* ("⋯")? : second_order_formula
syntax:max "⋀ " ident ", " second_order_formula:0 : second_order_formula
syntax:max "⋁ " ident ", " second_order_formula:0 : second_order_formula

syntax "⤫formula[" ident* ";" ident* " | " ident* ";" ident* " | "
  second_order_formula:0 "]" : term

syntax "s“" second_order_formula:0 "”" : term
syntax "s“" ident* ";" ident* "." second_order_formula:0 "”" : term
syntax "s“" ident* ";" ident* "|" second_order_formula:0 "”" : term

private meta def checkNames (xs : TSyntaxArray `ident) : MacroM Unit := do
  let mut seen := #[]
  for x in xs do
    if seen.contains x.getId then Macro.throwErrorAt x "duplicate variable name"
    seen := seen.push x.getId

private meta def extend (bound free xs : TSyntaxArray `ident) :
    MacroM (TSyntaxArray `ident) := do
  checkNames (bound ++ free ++ xs)
  return xs.reverse ++ bound

private meta def membership (bound free : TSyntaxArray `ident)
    (s : TSyntax `second_order_set) (t : TSyntax `term) : MacroM (TSyntax `term) := do
  match s with
  | `(second_order_set| #$i:term) => `(Semiformula.bvar $i $t)
  | `(second_order_set| &$i:term) => `(Semiformula.fvar $i $t)
  | `(second_order_set| $x:ident) =>
    if let some i := bound.findIdx? (·.getId == x.getId) then
      `(Semiformula.bvar $(quote i) $t)
    else if let some i := free.findIdx? (·.getId == x.getId) then
      `(Semiformula.fvar $(quote i) $t)
    else Macro.throwErrorAt x "unknown set variable"
  | _ => Macro.throwUnsupported

macro_rules
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ($p) ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $_* ; $_* | $_* ; $_* | ⊤ ]) =>
    `(Semiformula.verum)
  | `(⤫formula[ $_* ; $_* | $_* ; $_* | ⊥ ]) =>
    `(Semiformula.falsum)
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ∧ $q ]) =>
    `(Semiformula.and ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ]
      ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $q ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ∨ $q ]) =>
    `(Semiformula.or ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ]
      ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $q ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ¬$p ]) =>
    `(Semiformula.neg ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p → $q ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ] 🡒
      ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $q ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ↔ $q ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ] 🡘
      ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $q ])
  | `(⤫formula[ $_* ; $xs* | $_* ; $fx* | $t:first_order_term = $u:first_order_term ]) =>
    `(Semiformula.rel Language.ORing.Rel.eq
      ![⤫term[ $xs* | $fx* | $t:first_order_term ],
        ⤫term[ $xs* | $fx* | $u:first_order_term ]])
  | `(⤫formula[ $_* ; $xs* | $_* ; $fx* | $t:first_order_term < $u:first_order_term ]) =>
    `(Semiformula.rel Language.ORing.Rel.lt
      ![⤫term[ $xs* | $fx* | $t:first_order_term ],
        ⤫term[ $xs* | $fx* | $u:first_order_term ]])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ≠ $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      ¬($t:first_order_term = $u:first_order_term) ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ≤ $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      $t:first_order_term = $u:first_order_term ∨ $t:first_order_term < $u:first_order_term ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term > $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      $u:first_order_term < $t:first_order_term ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ≥ $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      $u:first_order_term ≤ $t:first_order_term ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ≮ $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      ¬($t:first_order_term < $u:first_order_term) ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ≰ $u:first_order_term ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      ¬($t:first_order_term ≤ $u:first_order_term) ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ∈ $s:second_order_set ]) => do
    membership ss fs s (← `(⤫term[ $xs* | $fx* | $t:first_order_term ]))
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ∉ $s:second_order_set ]) =>
    `(Semiformula.neg
      ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $t:first_order_term ∈ $s:second_order_set ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $vs*, $p ]) => do
    let xs' ← extend xs fx vs
    let mut p ← `(⤫formula[ $ss* ; $xs'* | $fs* ; $fx* | $p ])
    for _ in vs do p ← `(Semiformula.all₁ $p)
    return p
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $vs*, $p ]) => do
    let xs' ← extend xs fx vs
    let mut p ← `(⤫formula[ $ss* ; $xs'* | $fs* ; $fx* | $p ])
    for _ in vs do p ← `(Semiformula.exs₁ $p)
    return p
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀² $vs*, $p ]) => do
    let ss' ← extend ss fs vs
    let mut p ← `(⤫formula[ $ss'* ; $xs* | $fs* ; $fx* | $p ])
    for _ in vs do p ← `(Semiformula.all₂ $p)
    return p
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃² $vs*, $p ]) => do
    let ss' ← extend ss fs vs
    let mut p ← `(⤫formula[ $ss'* ; $xs* | $fs* ; $fx* | $p ])
    for _ in vs do p ← `(Semiformula.exs₂ $p)
    return p
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀¹ $p ]) => do
    let x ← TSyntax.freshIdent
    `(Semiformula.all₁ ⤫formula[ $ss* ; $x $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃¹ $p ]) => do
    let x ← TSyntax.freshIdent
    `(Semiformula.exs₁ ⤫formula[ $ss* ; $x $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀² $p ]) => do
    let x ← TSyntax.freshIdent
    `(Semiformula.all₂ ⤫formula[ $x $ss* ; $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃² $p ]) => do
    let x ← TSyntax.freshIdent
    `(Semiformula.exs₂ ⤫formula[ $x $ss* ; $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x < $t, $p ]) => do
    let t ← `(FirstOrder.Rew.bShift ⤫term[ $xs* | $fx* | $t:first_order_term ])
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x, $x:ident < !!$t → $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x < $t, $p ]) => do
    let t ← `(FirstOrder.Rew.bShift ⤫term[ $xs* | $fx* | $t:first_order_term ])
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x, $x:ident < !!$t ∧ $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x ≤ $t, $p ]) => do
    let t ← `(FirstOrder.Rew.bShift ⤫term[ $xs* | $fx* | $t:first_order_term ])
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x, $x:ident ≤ !!$t → $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x ≤ $t, $p ]) => do
    let t ← `(FirstOrder.Rew.bShift ⤫term[ $xs* | $fx* | $t:first_order_term ])
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x, $x:ident ≤ !!$t ∧ $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x ∈ $s, $p ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∀ $x, $x:ident ∈ $s:second_order_set → $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x ∈ $s, $p ]) =>
    `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ∃ $x, $x:ident ∈ $s:second_order_set ∧ $p ])
  | `(⤫formula[ $_* ; $_* | $_* ; $_* | !!$p:term ]) =>
    pure p
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* |
      !$p:second_order_splice $[[$ss₀*]]? $ts* $[⋯%$tail]? ]) => do
    let p : TSyntax `term ← match p with
      | `(second_order_splice| $p:ident) => pure ⟨p.raw⟩
      | `(second_order_splice| ($p:term)) => pure p
      | _ => Macro.throwUnsupported
    let p ← match ss₀ with
      | none => pure p
      | some ss₀ => do
        let args ← ss₀.mapM fun s => do membership ss fs s (← `(FirstOrder.Semiterm.bvar 0))
        `((SecondOrder.Rew.subst ![$args,*]).app $p)
    let tail ← match tail with
      | none => `(![])
      | some _ => `(fun i => FirstOrder.Semiterm.bvar (finSuccItr i $(quote xs.size)))
    let args ← ts.foldrM (fun t rest => `(⤫term[ $xs* | $fx* | $t ] :> $rest)) tail
    `(FirstOrder.Rewriting.subst $p $args)
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ⋀ $i, $p ]) =>
    `(Matrix.conj fun $i => ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ])
  | `(⤫formula[ $ss* ; $xs* | $fs* ; $fx* | ⋁ $i, $p ]) =>
    `(Matrix.disj fun $i => ⤫formula[ $ss* ; $xs* | $fs* ; $fx* | $p ])

macro_rules
  | `(s“$p:second_order_formula”) =>
    `((⤫formula[ ; | ; | $p ] : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))
  | `(s“$ss* ; $xs*. $p:second_order_formula”) => do
    checkNames ss
    checkNames xs
    `((⤫formula[ $ss* ; $xs* | ; | $p ] : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))
  | `(s“$ss* ; $xs* | $p:second_order_formula”) => do
    checkNames ss
    checkNames xs
    `((⤫formula[ ; | $ss* ; $xs* | $p ] : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))

open PrettyPrinter Delaborator SubExpr

open scoped Semiformula

private meta partial def termSyntax (s : Syntax) : DelabM (TSyntax `first_order_term) :=
  match s with
  | `(($t)) => termSyntax t
  | `(‘$t:first_order_term’) => pure t
  | `(↑$n:num) => `(first_order_term| $n:num)
  | `(#$i) => `(first_order_term| #$i)
  | `(&$i) => `(first_order_term| &$i)
  | _ => do
    let t : TSyntax `term := ⟨s⟩
    `(first_order_term| !!$t)

private meta partial def formulaSyntax (s : Syntax) : DelabM (TSyntax `second_order_formula) :=
  match s with
  | `(($p)) => formulaSyntax p
  | `(s“$p:second_order_formula”) => pure p
  | `($t ∈# $i) => do `(second_order_formula| $(← termSyntax t):first_order_term ∈ #$i)
  | `($t ∉# $i) => do `(second_order_formula| $(← termSyntax t):first_order_term ∉ #$i)
  | `($t ∈& $i) => do `(second_order_formula| $(← termSyntax t):first_order_term ∈ &$i)
  | `($t ∉& $i) => do `(second_order_formula| $(← termSyntax t):first_order_term ∉ &$i)
  | _ => do
    let t : TSyntax `term := ⟨s⟩
    `(second_order_formula| !!$t)

@[delab app.FFL.HArrow.hArrow,
  delab app.FFL.Arrow.arrow,
  delab app.FFL.LogicalConnective.iff,
  delab app.FFL.SecondOrder.Semiformula.verum,
  delab app.FFL.SecondOrder.Semiformula.falsum,
  delab app.FFL.SecondOrder.Semiformula.bvar,
  delab app.FFL.SecondOrder.Semiformula.nbvar,
  delab app.FFL.SecondOrder.Semiformula.fvar,
  delab app.FFL.SecondOrder.Semiformula.nfvar,
  delab app.FFL.SecondOrder.Semiformula.rel,
  delab app.FFL.SecondOrder.Semiformula.nrel,
  delab app.FFL.SecondOrder.Semiformula.and,
  delab app.FFL.SecondOrder.Semiformula.or,
  delab app.FFL.SecondOrder.Semiformula.neg,
  delab app.FFL.SecondOrder.Semiformula.all₁,
  delab app.FFL.SecondOrder.Semiformula.exs₁,
  delab app.FFL.SecondOrder.Semiformula.all₂,
  delab app.FFL.SecondOrder.Semiformula.exs₂]
meta def delabArithmetic : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let e ← getExpr
  let type ← Meta.whnf (← Meta.inferType e)
  guard <| type.isAppOfArity ``SecondOrder.Semiformula 5
  guard <| ← Meta.isDefEq type.getAppArgs[0]! (mkConst ``Language.oRing)
  let last := withAppArg delab
  let penultimate := withAppFn <| withAppArg delab
  let body := do formulaSyntax (← last)
  match e.getAppFn.constName! with
  | ``HArrow.hArrow | ``Arrow.arrow =>
    `(s“$(← formulaSyntax (← penultimate)) → $(← body)”)
  | ``LogicalConnective.iff => `(s“$(← formulaSyntax (← penultimate)) ↔ $(← body)”)
  | ``Semiformula.verum => `(s“⊤”)
  | ``Semiformula.falsum => `(s“⊥”)
  | ``Semiformula.bvar => `(s“$(← termSyntax (← last)):first_order_term ∈ #$(← penultimate)”)
  | ``Semiformula.nbvar => `(s“$(← termSyntax (← last)):first_order_term ∉ #$(← penultimate)”)
  | ``Semiformula.fvar => `(s“$(← termSyntax (← last)):first_order_term ∈ &$(← penultimate)”)
  | ``Semiformula.nfvar => `(s“$(← termSyntax (← last)):first_order_term ∉ &$(← penultimate)”)
  | ``Semiformula.and => `(s“$(← formulaSyntax (← penultimate)) ∧ $(← body)”)
  | ``Semiformula.or => `(s“$(← formulaSyntax (← penultimate)) ∨ $(← body)”)
  | ``Semiformula.neg => `(s“¬$(← body)”)
  | ``Semiformula.all₁ => `(s“∀¹ $(← body)”)
  | ``Semiformula.exs₁ => `(s“∃¹ $(← body)”)
  | ``Semiformula.all₂ => `(s“∀² $(← body)”)
  | ``Semiformula.exs₂ => `(s“∃² $(← body)”)
  | ``Semiformula.rel | ``Semiformula.nrel =>
    let r ← withAppFn <| withAppArg do Meta.whnf (← getExpr)
    let `(![$t, $u]) ← last | failure
    let t ← termSyntax t
    let u ← termSyntax u
    let p ← match r.getAppFn.constName! with
      | ``Language.ORing.Rel.eq => `(second_order_formula| $t:first_order_term = $u)
      | ``Language.ORing.Rel.lt => `(second_order_formula| $t:first_order_term < $u)
      | _ => failure
    if e.isAppOf ``Semiformula.nrel then `(s“¬$p”) else `(s“$p”)
  | _ => failure

end FFL.SecondOrder.BinderNotation
