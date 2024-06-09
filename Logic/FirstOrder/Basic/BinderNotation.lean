import Logic.FirstOrder.Basic.Elab

open Lean PrettyPrinter Delaborator SubExpr

namespace LO.FirstOrder

namespace BinderNotation

abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ

@[simp] lemma finSuccItr_one {x : Fin n} : BinderNotation.finSuccItr x 1 = x.succ := rfl

@[simp] lemma finSuccItr_two {x : Fin n} : BinderNotation.finSuccItr x 2 = x.succ.succ := rfl

open Semiterm Semiformula

declare_syntax_cat first_order_term

syntax bvBinder := ident*

partial def elabBVBinder : Syntax → MacroM (TSyntax `term × TSyntaxArray `ident)
  | `(bvBinder | $vars*) => do
    let n := Syntax.mkNumLit (toString vars.size)
    return (←`(_ + $n), vars)
  | decl                   => Macro.throwErrorAt decl "unexpected kind of bvBinder"

syntax "‘" bvBinder " | "  first_order_term:0 "’" : term
syntax "‘" first_order_term:0 "’" : term

syntax "(" first_order_term ")" : first_order_term

syntax:max ident : first_order_term         -- bounded variable
syntax:max "#" term:max : first_order_term  -- bounded variable
syntax:max "&" term:max : first_order_term  -- free variable
syntax:80 "!" term:max first_order_term:81* (" ⋯")? : first_order_term
syntax:80 "!!" term:max : first_order_term

syntax num : first_order_term
syntax:max "⋆" : first_order_term
syntax:50 first_order_term:50 " + " first_order_term:51 : first_order_term
syntax:60 first_order_term:60 " * " first_order_term:61 : first_order_term
syntax:65 first_order_term:65 " ^ " first_order_term:66 : first_order_term
syntax first_order_term " ^' " num  : first_order_term
syntax:67  "exp " first_order_term:68 : first_order_term

macro_rules
  | `(‘ $e:first_order_term ’) => `(‘ | $e ’)
  | `(‘ $bd | ($e) ’)          => `(‘ $bd | $e ’)
  | `(‘ $bd | $x:ident ’)      => do
    let (n, names) ← elabBVBinder bd
    let some x := names.getIdx? x | Macro.throwErrorAt x "error: variable did not found."
    let i := Syntax.mkNumLit (toString x)
    `(@bvar _ _ $n $i)
  | `(‘ $bd | #$x:term ’)      => do
    let (n, _) ← elabBVBinder bd
    `(@bvar _ _ $n $x)
  | `(‘ $bd | &$x:term ’)      => do
    let (n, _) ← elabBVBinder bd
    `(@fvar _ _ $n $x)
  | `(‘ $_ | $m:num ’)         => do
    --let (n, _) ← elabBVBinder bd
    `(@Semiterm.Operator.const _ _ _ (Operator.numeral _ $m))
  | `(‘ $bd | ⋆ ’)             => do
    let (n, _) ← elabBVBinder bd
    `(@Operator.const _ _ $n Operator.Star.star)
  | `(‘ $bd | $e₁ + $e₂ ’)     => `(Semiterm.Operator.Add.add.operator ![‘ $bd | $e₁ ’, ‘ $bd | $e₂ ’])
  | `(‘ $bd | $e₁ * $e₂ ’)     => `(Semiterm.Operator.Mul.mul.operator ![‘ $bd | $e₁ ’, ‘ $bd | $e₂ ’])
  | `(‘ $bd | $e₁ ^ $e₂ ’)     => `(Semiterm.Operator.Pow.pow.operator ![‘ $bd | $e₁ ’, ‘ $bd | $e₂ ’])
  | `(‘ $bd | $e ^' $n ’)      => `((Semiterm.Operator.npow _ $n).operator ![‘ $bd | $e ’])
  | `(‘ $bd | exp $e ’)        => `(Semiterm.Operator.Exp.exp.operator ![‘ $bd | $e ’])
  | `(‘ $_  | !!$t:term ’)   => `($t)
  | `(‘ $bd | !$t:term $vs:first_order_term* ’)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $bd | $a ’ :> $s))
    `(Rew.substs $v $t)
  | `(‘ $bd | !$t:term $vs:first_order_term* ⋯ ’) =>
    do
    let (_, names) ← elabBVBinder bd
    let length := Syntax.mkNumLit (toString names.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $bd | $a ’ :> $s))
    `(Rew.substs $v $t)

#check (‘x | &4 + (4 + 2 * #0 + #1)’ : Semiterm ℒₒᵣ ℕ 1)

section delab

@[app_unexpander Semiterm.Operator.numeral]
def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.const]
def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.Add.add]
def unexpsnderAdd : Unexpander
  | `($_) => `(op(+))

@[app_unexpander Semiterm.Operator.Mul.mul]
def unexpsnderMul : Unexpander
  | `($_) => `(op(*))

@[app_unexpander Semiterm.Operator.operator]
def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘ $t ’, ‘ $u ’]) => `(‘ ($t    + $u  ) ’)
  | `($_ op(+) ![‘ $t ’, #$x   ]) => `(‘ ($t    + #$x ) ’)
  | `($_ op(+) ![‘ $t ’, &$x   ]) => `(‘ ($t    + &$x ) ’)
  | `($_ op(+) ![‘ $t ’, $u    ]) => `(‘ ($t    + !!$u) ’)
  | `($_ op(+) ![#$x,    ‘ $u ’]) => `(‘ (#$x   + $u  ) ’)
  | `($_ op(+) ![#$x,    #$y   ]) => `(‘ (#$x   + #$y ) ’)
  | `($_ op(+) ![#$x,    &$y   ]) => `(‘ (#$x   + &$y ) ’)
  | `($_ op(+) ![#$x,    $u    ]) => `(‘ (#$x   + !!$u) ’)
  | `($_ op(+) ![&$x,    ‘ $u ’]) => `(‘ (&$x   + $u  ) ’)
  | `($_ op(+) ![&$x,    #$y   ]) => `(‘ (&$x   + #$y ) ’)
  | `($_ op(+) ![&$x,    &$y   ]) => `(‘ (&$x   + &$y ) ’)
  | `($_ op(+) ![&$x,    $u    ]) => `(‘ (&$x   + !!$u) ’)
  | `($_ op(+) ![$t,     ‘ $u ’]) => `(‘ (!!$t + $u   ) ’)
  | `($_ op(+) ![$t,     #$y   ]) => `(‘ (!!$t + #$y  ) ’)
  | `($_ op(+) ![$t,     &$y   ]) => `(‘ (!!$t + &$y  ) ’)
  | `($_ op(+) ![$t,     $u    ]) => `(‘ (!!$t + !!$u ) ’)

  | `($_ op(*) ![‘ $t ’, ‘ $u ’]) => `(‘ ($t    * $u  ) ’)
  | `($_ op(*) ![‘ $t ’, #$x   ]) => `(‘ ($t    * #$x ) ’)
  | `($_ op(*) ![‘ $t ’, &$x   ]) => `(‘ ($t    * &$x ) ’)
  | `($_ op(*) ![‘ $t ’, $u    ]) => `(‘ ($t    * !!$u) ’)
  | `($_ op(*) ![#$x,    ‘ $u ’]) => `(‘ (#$x   * $u  ) ’)
  | `($_ op(*) ![#$x,    #$y   ]) => `(‘ (#$x   * #$y ) ’)
  | `($_ op(*) ![#$x,    &$y   ]) => `(‘ (#$x   * &$y ) ’)
  | `($_ op(*) ![#$x,    $u    ]) => `(‘ (#$x   * !!$u) ’)
  | `($_ op(*) ![&$x,    ‘ $u ’]) => `(‘ (&$x   * $u  ) ’)
  | `($_ op(*) ![&$x,    #$y   ]) => `(‘ (&$x   * #$y ) ’)
  | `($_ op(*) ![&$x,    &$y   ]) => `(‘ (&$x   * &$y ) ’)
  | `($_ op(*) ![&$x,    $u    ]) => `(‘ (&$x   * !!$u) ’)
  | `($_ op(*) ![$t,     ‘ $u ’]) => `(‘ (!!$t * $u   ) ’)
  | `($_ op(*) ![$t,     #$y   ]) => `(‘ (!!$t * #$y  ) ’)
  | `($_ op(*) ![$t,     &$y   ]) => `(‘ (!!$t * &$y  ) ’)
  | `($_ op(*) ![$t,     $u    ]) => `(‘ (!!$t * !!$u ) ’)
  | _                             => throw ()

#check ‘ x | &4 + ((4 + 2) * #0 + #1)’

end delab

open Semiformula

declare_syntax_cat first_order_formula

syntax "“" bvBinder " | "  first_order_formula:0 "”" : term
syntax "“" first_order_formula:0 "”" : term

syntax "(" first_order_formula ")" : first_order_formula

syntax:60 "!" term:max first_order_term:61* ("⋯")? : first_order_formula
syntax:60 "!!" term:max : first_order_formula

syntax "⊤" : first_order_formula
syntax "⊥" : first_order_formula
syntax:32 first_order_formula:33 " ∧ " first_order_formula:32 : first_order_formula
syntax:30 first_order_formula:31 " ∨ " first_order_formula:30 : first_order_formula
syntax:max "¬" first_order_formula:35 : first_order_formula
syntax:10 first_order_formula:9 " → " first_order_formula:10 : first_order_formula
syntax:5 first_order_formula " ↔ " first_order_formula : first_order_formula

syntax:max "∀ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∀' " first_order_formula:0 : first_order_formula
syntax:max "∃' " first_order_formula:0 : first_order_formula
syntax:max "∀[" first_order_formula "] " first_order_formula:0 : first_order_formula
syntax:max "∃[" first_order_formula "] " first_order_formula:0 : first_order_formula

partial def bvBinderCons (x : TSyntax `ident) : TSyntax `LO.FirstOrder.BinderNotation.bvBinder → MacroM (TSyntax `LO.FirstOrder.BinderNotation.bvBinder)
  | `(bvBinder | $vars*)   => `(bvBinder | $x $vars*)
  | decl                   => Macro.throwErrorAt decl "unexpected kind of bvBinder"

macro_rules
  | `(“ $e:first_order_formula ”)                 => `(“ | $e ”)
  | `(“ $bd | ($e:first_order_formula) ”)         => `(“ $bd | $e ”)
  | `(“ $_  | !!$p:term ”)                        => `($p)
  | `(“ $bd | !$p:term $vs:first_order_term* ”)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $bd | $a ’ :> $s))
    `(Rew.substs $v |>.hom $p)
  | `(“ $bd | !$p:term $vs:first_order_term* ⋯ ”) =>
    do
    let (_, names) ← elabBVBinder bd
    let length := Syntax.mkNumLit (toString names.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $bd | $a ’ :> $s))
    `(Rew.substs $v |>.hom $p)
  | `(“ $_ | ⊤ ”)                                 => `(⊤)
  | `(“ $_ | ⊥ ”)                                 => `(⊥)
  | `(“ $bd | $p ∧ $q ”)                          => `(“ $bd | $p ” ⋏ “ $bd | $q ”)
  | `(“ $bd | $p ∨ $q ”)                          => `(“ $bd | $p ” ⋎ “ $bd | $q ”)
  | `(“ $bd | ¬$p ”)                              => `(~“ $bd | $p ”)
  | `(“ $bd | $p → $q ”)                          => `(“ $bd | $p ” ⟶ “ $bd | $q ”)
  | `(“ $bd | $p ↔ $q ”)                          => `(“ $bd | $p ” ⟷ “ $bd | $q ”)
  | `(“ $bd | ∀ $xs*, $p ”)                       => do
    let xs := xs.reverse
    let bd' : TSyntax `LO.FirstOrder.BinderNotation.bvBinder ← xs.foldrM
      (fun z bd' ↦ do
        let (_, names) ← elabBVBinder bd'
        if names.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        bvBinderCons z bd')
      bd
    let s : TSyntax `term ← xs.size.rec `(“ $bd' | $p ”) (fun _ q ↦ q >>= fun q ↦ `(∀' $q))
    return s
  | `(“ $bd | ∃ $xs*, $p ”)                       => do
    let xs := xs.reverse
    let bd' : TSyntax `LO.FirstOrder.BinderNotation.bvBinder ← xs.foldrM
      (fun z bd' ↦ do
        let (_, names) ← elabBVBinder bd'
        if names.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        bvBinderCons z bd')
      bd
    let s : TSyntax `term ← xs.size.rec `(“ $bd' | $p ”) (fun _ q ↦ q >>= fun q ↦ `(∃' $q))
    return s
  | `(“ $bd | ∀' $p ”)                            => do
    let (_, names) ← elabBVBinder bd
    let v := mkIdent (Name.mkSimple ("var" ++ toString names.size))
    let bd' ← bvBinderCons v bd
    `(∀' “ $bd' | $p ”)
  | `(“ $bd | ∃' $p ”)                            => do
    let (_, names) ← elabBVBinder bd
    let v := mkIdent (Name.mkSimple ("var" ++ toString names.size))
    let bd' ← bvBinderCons v bd
    `(∃' “ $bd' | $p ”)
  | `(“ $bd | ∀[ $p ] $q ”)                       => do
    let (_, names) ← elabBVBinder bd
    let v := mkIdent (Name.mkSimple ("var" ++ toString names.size))
    let bd' ← bvBinderCons v bd
    `(∀[“ $bd' | $p ”] “ $bd' | $q ”)
  | `(“ $bd | ∃[ $p ] $q ”)                       => do
    let (_, names) ← elabBVBinder bd
    let v := mkIdent (Name.mkSimple ("var" ++ toString names.size))
    let bd' ← bvBinderCons v bd
    `(∃[“ $bd' | $p ”] “ $bd' | $q ”)

syntax:45 first_order_term:45 " = " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " < " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " > " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≤ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≥ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ∈ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ∋ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≠ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≮ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≰ " first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ∉ " first_order_term:0 : first_order_formula

syntax:max "∀ " ident " < " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∀ " ident " ≤ " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∀ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " < " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ≤ " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $bd | ∀ $x < $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.ballLT ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | ∀ $x ≤ $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.ballLE ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | ∀ $x ∈ $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.ballMem ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | ∃ $x < $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.bexLT ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | ∃ $x ≤ $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.bexLE ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | ∃ $x ∈ $t, $p ”) => do
    let (_, names) ← elabBVBinder bd
    if names.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let bd' ← bvBinderCons x bd
    `(Semiformula.bexMem ‘ $bd | $t ’ “ $bd' | $p ”)
  | `(“ $bd | $t:first_order_term = $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Eq.eq ![‘ $bd | $t ’, ‘ $bd | $u ’])
  | `(“ $bd | $t:first_order_term < $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LT.lt ![‘ $bd | $t ’, ‘ $bd | $u ’])
  | `(“ $bd | $t:first_order_term > $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LT.lt ![‘ $bd | $u ’, ‘ $bd | $t’])
  | `(“ $bd | $t:first_order_term ≤ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LE.le ![‘ $bd | $t ’, ‘ $bd | $u ’])
  | `(“ $bd | $t:first_order_term ≥ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LE.le ![‘ $bd | $u ’, ‘ $bd | $t ’])
  | `(“ $bd | $t:first_order_term ∈ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Mem.mem ![‘ $bd | $t ’, ‘ $bd | $u ’])
  | `(“ $bd | $t:first_order_term ∋ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Mem.mem ![‘ $bd | $u ’, ‘ $bd | $t ’])
  | `(“ $bd | $t:first_order_term ≠ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.Eq.eq ![‘ $bd | $t ’, ‘ $bd | $u ’]))
  | `(“ $bd | $t:first_order_term ≮ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.LT.lt ![‘ $bd | $t ’, ‘ $bd | $u ’]))
  | `(“ $bd | $t:first_order_term ≰ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.LE.le ![‘ $bd | $t ’, ‘ $bd | $u ’]))
  | `(“ $bd | $t:first_order_term ∉ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.Mem.mem ![‘ $bd | $t ’, ‘ $bd | $u ’]))

#check “∀ x, ∀ y, ∀ z, ∀ v, ∀ w, x + y + z + v + w = 0”
#check “∀ x y z v w, x + y + z + v + w = 0”

#check “x y z | ∃ v w, ∀ r < z + v + 7, ∀' x + y + v = x ↔ z = w”

section delab

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

@[app_unexpander Language.LT.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

@[app_unexpander Wedge.wedge]
def unexpandAnd : Unexpander
  | `($_ “ $p:first_order_formula ” “ $q:first_order_formula ”) => `(“ ($p ∧ $q) ”)
  | `($_ “ $p:first_order_formula ” $u:term                   ) => `(“ ($p ∧ !$u) ”)
  | `($_ $t:term                    “ $q:first_order_formula ”) => `(“ (!$t ∧ $q) ”)
  | _                                                           => throw ()

@[app_unexpander Vee.vee]
def unexpandOr : Unexpander
  | `($_ “ $p:first_order_formula ” “ $q:first_order_formula ”) => `(“ ($p ∨ $q) ”)
  | `($_ “ $p:first_order_formula ” $u:term                   ) => `(“ ($p ∨ !$u) ”)
  | `($_ $t:term                    “ $q:first_order_formula ”) => `(“ (!$t ∨ $q) ”)
  | _                                                           => throw ()

@[app_unexpander Tilde.tilde]
def unexpandNeg : Unexpander
  | `($_ “ $p:first_order_formula ”) => `(“ ¬$p ”)
  | _                                => throw ()

@[app_unexpander UnivQuantifier.univ]
def unexpandUniv : Unexpander
  | `($_ “ $p:first_order_formula ”) => `(“ ∀' $p:first_order_formula ”)
  | _                                => throw ()

@[app_unexpander ExQuantifier.ex]
def unexpandEx : Unexpander
  | `($_ “ $p:first_order_formula”) => `(“ ∃' $p:first_order_formula ”)
  | _                                   => throw ()

@[app_unexpander LogicalConnective.ball]
def unexpandBall : Unexpander
  | `($_ “ $p:first_order_formula ” “ $q:first_order_formula ”) => `(“ (∀[$p] $q) ”)
  | `($_ “ $p:first_order_formula ” $u:term                   ) => `(“ (∀[$p] !$u) ”)
  | `($_ $t:term                    “ $q:first_order_formula ”) => `(“ (∀[!$t] $q) ”)
  | _                                                           => throw ()

@[app_unexpander LogicalConnective.bex]
def unexpandBex : Unexpander
  | `($_ “ $p:first_order_formula ” “ $q:first_order_formula ”) => `(“ (∃[$p] $q) ”)
  | `($_ “ $p:first_order_formula ” $u:term                   ) => `(“ (∃[$p] !$u) ”)
  | `($_ $t:term                    “ $q:first_order_formula ”) => `(“ (∃[!$t] $q) ”)
  | _                                                           => throw ()

@[app_unexpander Arrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “ $p:first_order_formula ” “ $q:first_order_formula”) => `(“ ($p → $q) ”)
  | `($_ “ $p:first_order_formula ” $u:term                  ) => `(“ ($p → !$u) ”)
  | `($_ $t:term                    “ $q:first_order_formula”) => `(“ (!$t → $q) ”)
  | _                                                          => throw ()

@[app_unexpander LogicalConnective.iff]
def unexpandIff : Unexpander
  | `($_ “ $p:first_order_formula” “ $q:first_order_formula”) => `(“ ($p ↔ $q) ”)
  | `($_ “ $p:first_order_formula” $u:term                  ) => `(“ ($p ↔ !$u) ”)
  | `($_ $t:term                   “ $q:first_order_formula”) => `(“ (!$t ↔ $q) ”)
  | _                                                         => throw ()

@[app_unexpander Semiformula.Operator.operator]
def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term = $u   ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term = #$y  ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term = &$y  ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term = !!$u ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 = $u   ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 = #$y  ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 = &$y  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) => `(“ #$x                 = !!$u ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 = $u   ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 = #$y  ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 = &$y  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) => `(“ &$x                 = !!$u ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                = $u   ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) => `(“ !!$t                = #$y  ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) => `(“ !!$t                = &$y  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) => `(“ !!$t                = !!$u ”)

  | `($_ op(<) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term < $u   ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term < #$y  ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term < &$y  ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term < !!$u ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 < $u   ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 < #$y  ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 < &$y  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) => `(“ #$x                 < !!$u ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 < $u   ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 < #$y  ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 < &$y  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) => `(“ &$x                 < !!$u ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                < $u   ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) => `(“ !!$t                < #$y  ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) => `(“ !!$t                < &$y  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) => `(“ !!$t                < !!$u ”)

  | `($_ op(≤) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ≤ $u   ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ≤ #$y  ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ≤ &$y  ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ≤ !!$u ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ≤ $u   ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ≤ #$y  ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ≤ &$y  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) => `(“ #$x                 ≤ !!$u ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ≤ $u   ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ≤ #$y  ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ≤ &$y  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) => `(“ &$x                 ≤ !!$u ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ≤ $u   ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ≤ #$y  ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ≤ &$y  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) => `(“ !!$t                ≤ !!$u ”)

  | `($_ op(∈) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ∈ $u   ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ∈ #$y  ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ∈ &$y  ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ∈ !!$u ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ∈ $u   ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ∈ #$y  ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ∈ &$y  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) => `(“ #$x                 ∈ !!$u ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ∈ $u   ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ∈ #$y  ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ∈ &$y  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) => `(“ &$x                 ∈ !!$u ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ∈ $u   ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ∈ #$y  ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ∈ &$y  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) => `(“ !!$t                ∈ !!$u ”)
  | _                                                            => throw ()

#check “x y z | ∃ v w, ∀ r < z + v, y + v ≤ x ↔ z = w”

end delab

end BinderNotation

end LO.FirstOrder
