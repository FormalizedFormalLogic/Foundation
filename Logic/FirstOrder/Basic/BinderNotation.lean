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

syntax "‘" ident* " | "  first_order_term:0 "’" : term
syntax "‘" first_order_term:0 "’" : term

syntax "(" first_order_term ")" : first_order_term

syntax:max ident : first_order_term         -- bounded variable
syntax:max "#" term:max : first_order_term  -- bounded variable
syntax:max "&" term:max : first_order_term  -- free variable
syntax:80 "!" term:max first_order_term:81* (" ⋯")? : first_order_term
syntax:80 "!!" term:max : first_order_term
syntax:80 ".!" term:max first_order_term:81* (" ⋯")? : first_order_term
syntax:80 ".!!" term:max : first_order_term

syntax num : first_order_term
syntax:max "⋆" : first_order_term
syntax:50 first_order_term:50 " + " first_order_term:51 : first_order_term
syntax:60 first_order_term:60 " * " first_order_term:61 : first_order_term
syntax:65 first_order_term:65 " ^ " first_order_term:66 : first_order_term
syntax:70 first_order_term " ^' " num  : first_order_term
syntax:max first_order_term "²"  : first_order_term
syntax:max first_order_term "³"  : first_order_term
syntax:max first_order_term "⁴"  : first_order_term

syntax:67  "exp " first_order_term:68 : first_order_term

macro_rules
  | `(‘ $e:first_order_term ’)       => `(‘ | $e ’)
  | `(‘ $binders* | ($e) ’)          => `(‘ $binders* | $e ’)
  | `(‘ $binders* | $x:ident ’)      => do
    let some x := binders.getIdx? x | Macro.throwErrorAt x "error: variable did not found."
    let i := Syntax.mkNumLit (toString x)
    `(#$i)
  | `(‘ $_* | #$x:term ’)            => do
    `(#$x)
  | `(‘ $_* | &$x:term ’)            => do
    `(&$x)
  | `(‘ $_* | $m:num ’)              => do
    `(@Semiterm.Operator.const _ _ _ (Operator.numeral _ $m))
  | `(‘ $_* | ⋆ ’)                   => do
    `(Operator.const Operator.Star.star)
  | `(‘ $binders* | $e₁ + $e₂ ’)     => `(Semiterm.Operator.Add.add.operator ![‘ $binders* | $e₁ ’, ‘ $binders* | $e₂ ’])
  | `(‘ $binders* | $e₁ * $e₂ ’)     => `(Semiterm.Operator.Mul.mul.operator ![‘ $binders* | $e₁ ’, ‘ $binders* | $e₂ ’])
  | `(‘ $binders* | $e₁ ^ $e₂ ’)     => `(Semiterm.Operator.Pow.pow.operator ![‘ $binders* | $e₁ ’, ‘ $binders* | $e₂ ’])
  | `(‘ $binders* | $e ^' $n ’)      => `((Semiterm.Operator.npow _ $n).operator ![‘ $binders* | $e ’])
  | `(‘ $binders* | $e² ’)           => `((Semiterm.Operator.npow _ 2).operator ![‘ $binders* | $e ’])
  | `(‘ $binders* | $e³ ’)           => `((Semiterm.Operator.npow _ 3).operator ![‘ $binders* | $e ’])
  | `(‘ $binders* | $e⁴ ’)           => `((Semiterm.Operator.npow _ 4).operator ![‘ $binders* | $e ’])
  | `(‘ $binders* | exp $e ’)        => `(Semiterm.Operator.Exp.exp.operator ![‘ $binders* | $e ’])
  | `(‘ $_*       | !!$t:term ’)     => `($t)
  | `(‘ $_*       | .!!$t:term ’)    => `(Rew.emb $t)
  | `(‘ $binders* | !$t:term $vs:first_order_term* ’)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.substs $v $t)
  | `(‘ $binders* | !$t:term $vs:first_order_term* ⋯ ’) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.substs $v $t)
  | `(‘ $binders* | .!$t:term $vs:first_order_term* ’)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.embSubsts $v $t)
  | `(‘ $binders* | .!$t:term $vs:first_order_term* ⋯ ’) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.embSubsts $v $t)

#check (‘x y z | &4 + (4 + 2 * (x⁴ + z)²)’ : Semiterm ℒₒᵣ ℕ 1)

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

syntax "“" ident* " | "  first_order_formula:0 "”" : term
syntax "“" first_order_formula:0 "”" : term

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

syntax:max "∀ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident+ ", " first_order_formula:0 : first_order_formula
syntax:max "∀' " first_order_formula:0 : first_order_formula
syntax:max "∃' " first_order_formula:0 : first_order_formula
syntax:max "∀[" first_order_formula "] " first_order_formula:0 : first_order_formula
syntax:max "∃[" first_order_formula "] " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $e:first_order_formula ”)                 => `(“ | $e ”)
  | `(“ $binders* | ($e:first_order_formula) ”)         => `(“ $binders* | $e ”)
  | `(“ $_*  | !!$p:term ”)                        => `($p)
  | `(“ $binders* | !$p:term $vs:first_order_term* ”)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.substs $v |>.hom $p)
  | `(“ $binders* | !$p:term $vs:first_order_term* ⋯ ”) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.substs $v |>.hom $p)
  | `(“ $_*  | .!!$p:term ”)                        => `(Rew.emb.hom $p)
  | `(“ $binders* | .!$p:term $vs:first_order_term* ”)   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.embSubsts $v |>.hom $p)
  | `(“ $binders* | .!$p:term $vs:first_order_term* ⋯ ”) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s => `(‘ $binders* | $a ’ :> $s))
    `(Rew.embSubsts $v |>.hom $p)
  | `(“ $_* | ⊤ ”)                                 => `(⊤)
  | `(“ $_* | ⊥ ”)                                 => `(⊥)
  | `(“ $binders* | $p ∧ $q ”)                          => `(“ $binders* | $p ” ⋏ “ $binders* | $q ”)
  | `(“ $binders* | $p ∨ $q ”)                          => `(“ $binders* | $p ” ⋎ “ $binders* | $q ”)
  | `(“ $binders* | ¬$p ”)                              => `(~“ $binders* | $p ”)
  | `(“ $binders* | $p → $q ”)                          => `(“ $binders* | $p ” ⟶ “ $binders* | $q ”)
  | `(“ $binders* | $p ↔ $q ”)                          => `(“ $binders* | $p ” ⟷ “ $binders* | $q ”)
  | `(“ $binders* | ∀ $xs*, $p ”)                       => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertAt 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(“ $binders'* | $p ”) (fun _ q ↦ q >>= fun q ↦ `(∀' $q))
    return s
  | `(“ $binders* | ∃ $xs*, $p ”)                       => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertAt 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(“ $binders'* | $p ”) (fun _ q ↦ q >>= fun q ↦ `(∃' $q))
    return s
  | `(“ $binders* | ∀' $p ”)                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∀' “ $binders'* | $p ”)
  | `(“ $binders* | ∃' $p ”)                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∃' “ $binders'* | $p ”)
  | `(“ $binders* | ∀[ $p ] $q ”)                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∀[“ $binders'* | $p ”] “ $binders* | $q ”)
  | `(“ $binders* | ∃[ $p ] $q ”)                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertAt 0 v
    `(∃[“ $binders'* | $p ”] “ $binders'* | $q ”)

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
  | `(“ $binders* | ∀ $x < $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballLT ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∀ $x ≤ $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballLE ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∀ $x ∈ $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.ballMem ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∃ $x < $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexLT ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∃ $x ≤ $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexLE ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∃ $x ∈ $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(Semiformula.bexMem ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | $t:first_order_term = $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Eq.eq ![‘ $binders* | $t ’, ‘ $binders* | $u ’])
  | `(“ $binders* | $t:first_order_term < $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LT.lt ![‘ $binders* | $t ’, ‘ $binders* | $u ’])
  | `(“ $binders* | $t:first_order_term > $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LT.lt ![‘ $binders* | $u ’, ‘ $binders* | $t’])
  | `(“ $binders* | $t:first_order_term ≤ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LE.le ![‘ $binders* | $t ’, ‘ $binders* | $u ’])
  | `(“ $binders* | $t:first_order_term ≥ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.LE.le ![‘ $binders* | $u ’, ‘ $binders* | $t ’])
  | `(“ $binders* | $t:first_order_term ∈ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Mem.mem ![‘ $binders* | $t ’, ‘ $binders* | $u ’])
  | `(“ $binders* | $t:first_order_term ∋ $u:first_order_term ”) => `(Semiformula.Operator.operator Operator.Mem.mem ![‘ $binders* | $u ’, ‘ $binders* | $t ’])
  | `(“ $binders* | $t:first_order_term ≠ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.Eq.eq ![‘ $binders* | $t ’, ‘ $binders* | $u ’]))
  | `(“ $binders* | $t:first_order_term ≮ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.LT.lt ![‘ $binders* | $t ’, ‘ $binders* | $u ’]))
  | `(“ $binders* | $t:first_order_term ≰ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.LE.le ![‘ $binders* | $t ’, ‘ $binders* | $u ’]))
  | `(“ $binders* | $t:first_order_term ∉ $u:first_order_term ”) => `(~(Semiformula.Operator.operator Operator.Mem.mem ![‘ $binders* | $t ’, ‘ $binders* | $u ’]))

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
