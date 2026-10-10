module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.SecondOrder.Syntax.Rew

/-!
# Binder notation for second-order arithmetic

`s“∀² X, ∀ x, x ∈ X → x + 0 = x”` denotes a second-order arithmetic formula.
In `s“X Y ; x y. …”`, the headers name bound set and number variables, respectively;
replace `.` by `|` to name free variables. Each header starts at index zero.
Numerical terms use the first-order literal notation. Quantifiers maintain independent
stacks of set and number variables. Names cannot be repeated within either sort.

`!!φ` inserts a formula unchanged. `!φ t₁ … tₙ` substitutes its bound number variables;
`!φ[X₁ … Xₖ] t₁ … tₙ` first substitutes its bound set variables as well.
An optional `⋯` after the number arguments supplies the remaining bound number variables,
starting after the named number binders, as in the first-order notation.
Parenthesize compound formula expressions, as in `!(f a)[X] x`.
Sets can also be written `#i` (bound) or `&i` (free).

These syntax translations are specific to this formalization.
-/

@[expose] public section

namespace FFL.SecondOrder.BinderNotation

open Lean FirstOrder FirstOrder.BinderNotation

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

private meta partial def expand (sets fsets nums fnums : TSyntaxArray `ident)
    (φ : TSyntax `second_order_formula) : MacroM (TSyntax `term) := do
  let go := expand sets fsets nums fnums
  let term := fun t => `(⤫term(lit)[$nums* | $fnums* | $t:first_order_term])
  match φ with
  | `(second_order_formula| ($p)) => go p
  | `(second_order_formula| ⊤) => `(Semiformula.verum)
  | `(second_order_formula| ⊥) => `(Semiformula.falsum)
  | `(second_order_formula| $p ∧ $q) => `(Semiformula.and $(← go p) $(← go q))
  | `(second_order_formula| $p ∨ $q) => `(Semiformula.or $(← go p) $(← go q))
  | `(second_order_formula| ¬$p) => `(Semiformula.neg $(← go p))
  | `(second_order_formula| $p → $q) => `($(← go p) 🡒 $(← go q))
  | `(second_order_formula| $p ↔ $q) => `($(← go p) 🡘 $(← go q))
  | `(second_order_formula| $t:first_order_term = $u:first_order_term) =>
    `(Semiformula.rel Language.ORing.Rel.eq ![$(← term t), $(← term u)])
  | `(second_order_formula| $t:first_order_term ≠ $u:first_order_term) =>
    go (← `(second_order_formula| ¬($t:first_order_term = $u:first_order_term)))
  | `(second_order_formula| $t:first_order_term < $u:first_order_term) =>
    `(Semiformula.rel Language.ORing.Rel.lt ![$(← term t), $(← term u)])
  | `(second_order_formula| $t:first_order_term ≤ $u:first_order_term) =>
    go (← `(second_order_formula|
      $t:first_order_term = $u:first_order_term ∨ $t:first_order_term < $u:first_order_term))
  | `(second_order_formula| $t:first_order_term > $u:first_order_term) =>
    go (← `(second_order_formula| $u:first_order_term < $t:first_order_term))
  | `(second_order_formula| $t:first_order_term ≥ $u:first_order_term) =>
    go (← `(second_order_formula| $u:first_order_term ≤ $t:first_order_term))
  | `(second_order_formula| $t:first_order_term ≮ $u:first_order_term) =>
    go (← `(second_order_formula| ¬($t:first_order_term < $u:first_order_term)))
  | `(second_order_formula| $t:first_order_term ≰ $u:first_order_term) =>
    go (← `(second_order_formula| ¬($t:first_order_term ≤ $u:first_order_term)))
  | `(second_order_formula| $t:first_order_term ∈ $s:second_order_set) =>
    membership sets fsets s (← term t)
  | `(second_order_formula| $t:first_order_term ∉ $s:second_order_set) =>
    `(Semiformula.neg $(← membership sets fsets s (← term t)))
  | `(second_order_formula| ∀ $xs*, $p) =>
    let mut p ← expand sets fsets (← extend nums fnums xs) fnums p
    for _ in xs do p ← `(Semiformula.all₁ $p)
    return p
  | `(second_order_formula| ∃ $xs*, $p) =>
    let mut p ← expand sets fsets (← extend nums fnums xs) fnums p
    for _ in xs do p ← `(Semiformula.exs₁ $p)
    return p
  | `(second_order_formula| ∀² $xs*, $p) =>
    let mut p ← expand (← extend sets fsets xs) fsets nums fnums p
    for _ in xs do p ← `(Semiformula.all₂ $p)
    return p
  | `(second_order_formula| ∃² $xs*, $p) =>
    let mut p ← expand (← extend sets fsets xs) fsets nums fnums p
    for _ in xs do p ← `(Semiformula.exs₂ $p)
    return p
  | `(second_order_formula| ∀¹ $p) =>
    let x ← TSyntax.freshIdent
    `(Semiformula.all₁ $(← expand sets fsets (#[x] ++ nums) fnums p))
  | `(second_order_formula| ∃¹ $p) =>
    let x ← TSyntax.freshIdent
    `(Semiformula.exs₁ $(← expand sets fsets (#[x] ++ nums) fnums p))
  | `(second_order_formula| ∀² $p) =>
    let x ← TSyntax.freshIdent
    `(Semiformula.all₂ $(← expand (#[x] ++ sets) fsets nums fnums p))
  | `(second_order_formula| ∃² $p) =>
    let x ← TSyntax.freshIdent
    `(Semiformula.exs₂ $(← expand (#[x] ++ sets) fsets nums fnums p))
  | `(second_order_formula| ∀ $x < $t, $p) => do
    let t ← `(FirstOrder.Rew.bShift $(← term t))
    go (← `(second_order_formula| ∀ $x, $x:ident < !!$t → $p))
  | `(second_order_formula| ∃ $x < $t, $p) => do
    let t ← `(FirstOrder.Rew.bShift $(← term t))
    go (← `(second_order_formula| ∃ $x, $x:ident < !!$t ∧ $p))
  | `(second_order_formula| ∀ $x ≤ $t, $p) => do
    let t ← `(FirstOrder.Rew.bShift $(← term t))
    go (← `(second_order_formula| ∀ $x, $x:ident ≤ !!$t → $p))
  | `(second_order_formula| ∃ $x ≤ $t, $p) => do
    let t ← `(FirstOrder.Rew.bShift $(← term t))
    go (← `(second_order_formula| ∃ $x, $x:ident ≤ !!$t ∧ $p))
  | `(second_order_formula| ∀ $x ∈ $s, $p) =>
    go (← `(second_order_formula| ∀ $x, $x:ident ∈ $s:second_order_set → $p))
  | `(second_order_formula| ∃ $x ∈ $s, $p) =>
    go (← `(second_order_formula| ∃ $x, $x:ident ∈ $s:second_order_set ∧ $p))
  | `(second_order_formula| !!$p:term) => return p
  | `(second_order_formula| !$p:second_order_splice $[[$ss*]]? $ts* $[⋯%$tail]?) =>
    let p : TSyntax `term ← match p with
      | `(second_order_splice| $p:ident) => pure ⟨p.raw⟩
      | `(second_order_splice| ($p:term)) => pure p
      | _ => Macro.throwUnsupported
    let p ← match ss with
      | none => pure p
      | some ss => do
        let args ← ss.mapM fun s => do membership sets fsets s (← `(FirstOrder.Semiterm.bvar 0))
        `((SecondOrder.Rew.subst ![$args,*]).app $p)
    let tail ← match tail with
      | none => `(![])
      | some _ => `(fun i => FirstOrder.Semiterm.bvar (finSuccItr i $(quote nums.size)))
    let args ← ts.foldrM (fun t rest => do `($(← term t) :> $rest)) tail
    `(FirstOrder.Rewriting.subst $p $args)
  | `(second_order_formula| ⋀ $i, $p) => `(Matrix.conj fun $i => $(← go p))
  | `(second_order_formula| ⋁ $i, $p) => `(Matrix.disj fun $i => $(← go p))
  | _ => Macro.throwUnsupported

macro_rules
  | `(s“$p:second_order_formula”) => do
    let p ← expand #[] #[] #[] #[] p
    `(($p : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))
  | `(s“$ss* ; $xs*. $p:second_order_formula”) => do
    checkNames ss
    checkNames xs
    let p ← expand ss #[] xs #[] p
    `(($p : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))
  | `(s“$ss* ; $xs* | $p:second_order_formula”) => do
    checkNames ss
    checkNames xs
    let p ← expand #[] ss #[] xs p
    `(($p : SecondOrder.Semiformula ℒₒᵣ _ _ _ _))

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
