import Foundation.FirstOrder.Basic.Operator

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

syntax "⤫term[" ident* " | " ident* " | " first_order_term:0 "]" : term

syntax "(" first_order_term ")" : first_order_term

syntax:max ident : first_order_term         -- bounded variable
syntax:max "#" term:max : first_order_term  -- bounded variable
syntax:max "&" term:max : first_order_term  -- free variable
syntax:80 "!" term:max first_order_term:81* (" ⋯")? : first_order_term
syntax:80 "!!" term:max : first_order_term
syntax:80 ".!" term:max first_order_term:81* (" ⋯")? : first_order_term
syntax:80 ".!!" term:max : first_order_term

syntax num : first_order_term
syntax:max "↑" term:max : first_order_term
syntax:max "⋆" : first_order_term
syntax:50 first_order_term:50 " + " first_order_term:51 : first_order_term
syntax:60 first_order_term:60 " * " first_order_term:61 : first_order_term
syntax:65 first_order_term:65 " ^ " first_order_term:66 : first_order_term
syntax:70 first_order_term " ^' " num  : first_order_term
syntax:max first_order_term "²"  : first_order_term
syntax:max first_order_term "³"  : first_order_term
syntax:max first_order_term "⁴"  : first_order_term
syntax:max "⌜" term:max "⌝" : first_order_term

syntax:67  "exp " first_order_term:68 : first_order_term

macro_rules
  | `(⤫term[ $binders* | $fbinders* | ($e)    ]) => `(⤫term[ $binders* | $fbinders* | $e ])
  | `(⤫term[ $binders* | $fbinders* | $x:ident]) => do
    match binders.getIdx? x with
    | none =>
      match fbinders.getIdx? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(⤫term[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(⤫term[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(⤫term[ $_*       | $_*        | $m:num     ]) => `(@Semiterm.Operator.const _ _ _ (Operator.numeral _ $m))
  | `(⤫term[ $_*       | $_*        | ↑$m:term   ]) => `(@Semiterm.Operator.const _ _ _ (Operator.numeral _ $m))
  | `(⤫term[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(⤫term[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(⤫term[ $binders* | $fbinders* | $e₁ + $e₂  ]) => `(Semiterm.Operator.Add.add.operator ![⤫term[ $binders* | $fbinders* | $e₁ ], ⤫term[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term[ $binders* | $fbinders* | $e₁ * $e₂  ]) => `(Semiterm.Operator.Mul.mul.operator ![⤫term[ $binders* | $fbinders* | $e₁ ], ⤫term[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) => `(Semiterm.Operator.Pow.pow.operator ![⤫term[ $binders* | $fbinders* | $e₁ ], ⤫term[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term[ $binders* | $fbinders* | $e ^' $n   ]) => `((Semiterm.Operator.npow _ $n).operator ![⤫term[ $binders* | $fbinders* | $e ]])
  | `(⤫term[ $binders* | $fbinders* | $e²        ]) => `((Semiterm.Operator.npow _ 2).operator ![⤫term[ $binders* | $fbinders* | $e ]])
  | `(⤫term[ $binders* | $fbinders* | $e³        ]) => `((Semiterm.Operator.npow _ 3).operator ![⤫term[ $binders* | $fbinders* | $e ]])
  | `(⤫term[ $binders* | $fbinders* | $e⁴        ]) => `((Semiterm.Operator.npow _ 4).operator ![⤫term[ $binders* | $fbinders* | $e ]])
  | `(⤫term[ $binders* | $fbinders* | exp $e     ]) => `(Semiterm.Operator.Exp.exp.operator ![⤫term[ $binders* | $fbinders* | $e ]])
  | `(⤫term[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(⤫term[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)
  | `(⤫term[ $binders* | $fbinders* | !$t:term $vs:first_order_term* ])    => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(⤫term[ $binders* | $fbinders* | $a ] :> $s))
    `(Rew.substs $v $t)
  | `(⤫term[ $binders* | $fbinders* | !$t:term $vs:first_order_term* ⋯ ])  =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.substs $v $t)
  | `(⤫term[ $binders* | $fbinders* | .!$t:term $vs:first_order_term* ])   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(⤫term[ $binders* | $fbinders* | .!$t:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)

syntax "‘" first_order_term:0 "’" : term
syntax "‘" ident* "| " first_order_term:0 "’" : term
syntax "‘" ident* ". " first_order_term:0 "’" : term

macro_rules
  | `(‘ $e:first_order_term ’)              => `(⤫term[           |            | $e ])
  | `(‘ $fbinders* | $e:first_order_term ’) => `(⤫term[           | $fbinders* | $e ])
  | `(‘ $binders*. $e:first_order_term ’)   => `(⤫term[ $binders* |            | $e ])

#check (⤫term[ x y z | A B C | B + (4 + A * (x⁴ + z)²) + ↑4] : Semiterm ℒₒᵣ ℕ 1)
#check ‘a x. a’

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
  | `($_ op(+) ![‘ $t:first_order_term ’, ‘ $u:first_order_term ’]) => `(‘ ($t    + $u  ) ’)
  | `($_ op(+) ![‘ $t:first_order_term ’, #$x   ]) => `(‘ ($t    + #$x ) ’)
  | `($_ op(+) ![‘ $t:first_order_term ’, &$x   ]) => `(‘ ($t    + &$x ) ’)
  | `($_ op(+) ![‘ $t:first_order_term ’, $u    ]) => `(‘ ($t    + !!$u) ’)
  | `($_ op(+) ![#$x,    ‘ $u:first_order_term ’]) => `(‘ (#$x   + $u  ) ’)
  | `($_ op(+) ![#$x,    #$y   ]) => `(‘ (#$x   + #$y ) ’)
  | `($_ op(+) ![#$x,    &$y   ]) => `(‘ (#$x   + &$y ) ’)
  | `($_ op(+) ![#$x,    $u    ]) => `(‘ (#$x   + !!$u) ’)
  | `($_ op(+) ![&$x,    ‘ $u:first_order_term ’]) => `(‘ (&$x   + $u  ) ’)
  | `($_ op(+) ![&$x,    #$y   ]) => `(‘ (&$x   + #$y ) ’)
  | `($_ op(+) ![&$x,    &$y   ]) => `(‘ (&$x   + &$y ) ’)
  | `($_ op(+) ![&$x,    $u    ]) => `(‘ (&$x   + !!$u) ’)
  | `($_ op(+) ![$t,     ‘ $u:first_order_term ’]) => `(‘ (!!$t + $u   ) ’)
  | `($_ op(+) ![$t,     #$y   ]) => `(‘ (!!$t + #$y  ) ’)
  | `($_ op(+) ![$t,     &$y   ]) => `(‘ (!!$t + &$y  ) ’)
  | `($_ op(+) ![$t,     $u    ]) => `(‘ (!!$t + !!$u ) ’)

  | `($_ op(*) ![‘ $t:first_order_term ’, ‘ $u:first_order_term ’]) => `(‘ ($t    * $u  ) ’)
  | `($_ op(*) ![‘ $t:first_order_term ’, #$x   ]) => `(‘ ($t    * #$x ) ’)
  | `($_ op(*) ![‘ $t:first_order_term ’, &$x   ]) => `(‘ ($t    * &$x ) ’)
  | `($_ op(*) ![‘ $t:first_order_term ’, $u    ]) => `(‘ ($t    * !!$u) ’)
  | `($_ op(*) ![#$x,    ‘ $u:first_order_term ’]) => `(‘ (#$x   * $u  ) ’)
  | `($_ op(*) ![#$x,    #$y   ]) => `(‘ (#$x   * #$y ) ’)
  | `($_ op(*) ![#$x,    &$y   ]) => `(‘ (#$x   * &$y ) ’)
  | `($_ op(*) ![#$x,    $u    ]) => `(‘ (#$x   * !!$u) ’)
  | `($_ op(*) ![&$x,    ‘ $u:first_order_term ’]) => `(‘ (&$x   * $u  ) ’)
  | `($_ op(*) ![&$x,    #$y   ]) => `(‘ (&$x   * #$y ) ’)
  | `($_ op(*) ![&$x,    &$y   ]) => `(‘ (&$x   * &$y ) ’)
  | `($_ op(*) ![&$x,    $u    ]) => `(‘ (&$x   * !!$u) ’)
  | `($_ op(*) ![$t,     ‘ $u:first_order_term ’]) => `(‘ (!!$t * $u   ) ’)
  | `($_ op(*) ![$t,     #$y   ]) => `(‘ (!!$t * #$y  ) ’)
  | `($_ op(*) ![$t,     &$y   ]) => `(‘ (!!$t * &$y  ) ’)
  | `($_ op(*) ![$t,     $u    ]) => `(‘ (!!$t * !!$u ) ’)
  | _                             => throw ()

#check ‘ x | &4 + ((4 + 2) * #0 + #1)’

end delab

open Semiformula

declare_syntax_cat first_order_formula

syntax "⤫formula[" ident* " | " ident* " | " first_order_formula:0 "]" : term

syntax "(" first_order_formula ")" : first_order_formula

syntax:60 "!" term:max first_order_term:61* ("⋯")? : first_order_formula
syntax:60 "!!" term:max : first_order_formula

syntax:60 ".!" term:max first_order_term:61* ("⋯")? : first_order_formula
syntax:60 ".!!" term:max : first_order_formula

syntax "⊤" : first_order_formula
syntax "⊥" : first_order_formula
syntax:32 first_order_formula:33 " ∧ " first_order_formula:32 : first_order_formula
syntax:30 first_order_formula:31 " ∨ " first_order_formula:30 : first_order_formula
syntax:max "¬" first_order_formula:35 : first_order_formula
syntax:10 first_order_formula:9 " → " first_order_formula:10 : first_order_formula
syntax:5 first_order_formula " ↔ " first_order_formula : first_order_formula
syntax:max "⋀ " ident ", " first_order_formula:0 : first_order_formula
syntax:max "⋁ " ident ", " first_order_formula:0 : first_order_formula
syntax:max "⋀ " ident " < " term ", " first_order_formula:0 : first_order_formula
syntax:max "⋁ " ident " < " term ", " first_order_formula:0 : first_order_formula

syntax:max "∀ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∀' " first_order_formula:0 : first_order_formula
syntax:max "∃' " first_order_formula:0 : first_order_formula
syntax:max "∀[" first_order_formula "] " first_order_formula:0 : first_order_formula
syntax:max "∃[" first_order_formula "] " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | ($e:first_order_formula)          ]) => `(⤫formula[ $binders* | $fbinders* | $e ])
  | `(⤫formula[ $_*       | $_*        | !!$φ:term                         ]) => `($φ)
  | `(⤫formula[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*    ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(⤫term[ $binders* | $fbinders* | $a ] :> $s))
    `($φ ⇜ $v)
  | `(⤫formula[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯  ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term[ $binders* | $fbinders* | $a] :> $s))
    `($φ ⇜ $v)
  | `(⤫formula[ $_*       | $_*        | .!!$φ:term ])                        => `(Rewriting.embedding $φ)
  | `(⤫formula[ $_*       | $_*        | ⊤                                 ]) => `(⊤)
  | `(⤫formula[ $_*       | $_*        | ⊥                                 ]) => `(⊥)
  | `(⤫formula[ $binders* | $fbinders* | $φ ∧ $ψ                           ]) => `(⤫formula[ $binders* | $fbinders* | $φ ] ⋏ ⤫formula[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula[ $binders* | $fbinders* | $φ ∨ $ψ                           ]) => `(⤫formula[ $binders* | $fbinders* | $φ ] ⋎ ⤫formula[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula[ $binders* | $fbinders* | ¬$φ                               ]) => `(∼⤫formula[ $binders* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | $φ → $ψ                           ]) => `(⤫formula[ $binders* | $fbinders* | $φ ] ➝ ⤫formula[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula[ $binders* | $fbinders* | $φ ↔ $ψ                           ]) => `(⤫formula[ $binders* | $fbinders* | $φ ] ⭤ ⤫formula[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula[ $binders* | $fbinders* | ⋀ $i, $φ                          ]) => `(Matrix.conj fun $i ↦ ⤫formula[ $binders* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ⋁ $i, $φ                          ]) => `(Matrix.disj fun $i ↦ ⤫formula[ $binders* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ⋀ $i < $t, $φ                     ]) => `(conjLt (fun $i ↦ ⤫formula[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula[ $binders* | $fbinders* | ⋁ $i < $t, $φ                     ]) => `(disjLt (fun $i ↦ ⤫formula[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula[ $binders* | $fbinders* | ∀ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertAt 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀' $ψ))
    return s
  | `(⤫formula[ $binders* | $fbinders* | ∃ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertAt 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃' $ψ))
    return s
  | `(⤫formula[ $binders* | $fbinders* | ∀' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∀' ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∃' ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∀[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∀[⤫formula[ $binders'* | $fbinders* | $φ ]] ⤫formula[ $binders'* | $fbinders* | $ψ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∃[⤫formula[ $binders'* | $fbinders* | $φ ]] ⤫formula[ $binders'* | $fbinders* | $ψ ])

syntax "“" ident* "| "  first_order_formula:0 "”" : term
syntax "“" ident* ". "  first_order_formula:0 "”" : term
syntax "“" first_order_formula:0 "”" : term

macro_rules
  | `(“ $e:first_order_formula ”)              => `(⤫formula[           |            | $e ])
  | `(“ $binders*. $e:first_order_formula ”)   => `(⤫formula[ $binders* |            | $e ])
  | `(“ $fbinders* | $e:first_order_formula ”) => `(⤫formula[           | $fbinders* | $e ])

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
  | `(⤫formula[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballLT ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballLE ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballMem ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexLT ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexLE ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexMem ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Eq.eq ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term < $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LT.lt ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term > $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LT.lt ![⤫term[ $binders* | $fbinders* | $u ], ⤫term[ $binders* | $fbinders* | $t]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ≤ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LE.le ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ≥ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LE.le ![⤫term[ $binders* | $fbinders* | $u ], ⤫term[ $binders* | $fbinders* | $t ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Mem.mem ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ∋ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Mem.mem ![⤫term[ $binders* | $fbinders* | $u ], ⤫term[ $binders* | $fbinders* | $t ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.Eq.eq ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ≮ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.LT.lt ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ≰ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.LE.le ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.Mem.mem ![⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]]))

#check “∀ x, ∀ y, ∀ z, ∀ v, ∀ w, x + y + z + v + w = 0”
#check “∀ x y z v w, x + y + z + v + w = 0”
#check “x y z | ∃ v w, ∀ r < z + v + 7, ∀' x + y + v = x ↔ z = .!(‘#0 + #1’) x y”

section delab

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

@[app_unexpander Language.LT.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

@[app_unexpander Wedge.wedge]
def unexpandAnd : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Vee.vee]
def unexpandOr : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Tilde.tilde]
def unexpandNeg : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ¬$φ ”)
  | _                                => throw ()

@[app_unexpander UnivQuantifier.univ]
def unexpandUniv : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ∀' $φ:first_order_formula ”)
  | _                                => throw ()

@[app_unexpander ExQuantifier.ex]
def unexpandEx : Unexpander
  | `($_ “ $φ:first_order_formula”) => `(“ ∃' $φ:first_order_formula ”)
  | _                                   => throw ()

@[app_unexpander ball]
def unexpandBall : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∀[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∀[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∀[!$t] $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander bex]
def unexpandBex : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∃[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∃[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∃[!$t] $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Arrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()

@[app_unexpander LogicalConnective.iff]
def unexpandIff : Unexpander
  | `($_ “ $φ:first_order_formula” “ $ψ:first_order_formula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:first_order_formula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:first_order_formula”) => `(“ (!$t ↔ $ψ) ”)
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

#check “x y z. ∃ v w, ∀ r < z + v, y + v ≤ x ↔ z = w”
#check “x y | x = y → y = x”
#check “x y . x = y → y = x”
#check “∀ x y, x = y → y = x”

end delab

end BinderNotation

end LO.FirstOrder
