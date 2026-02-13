module

public import Foundation.FirstOrder.Basic.Operator
public import Foundation.Vorspiel.Fin.Matrix

@[expose] public section

open Lean Elab PrettyPrinter Delaborator SubExpr

namespace Lean.TSyntax

meta def freshIdent [Monad m] [MonadQuotation m] : m (TSyntax `ident) := do
  let name ← Term.mkFreshBinderName
  return ⟨mkIdent name⟩

end Lean.TSyntax

namespace LO.FirstOrder

namespace Semiformula

variable {L : Language} {ξ : Type*}

def nestFormulae (φ : Semiformula L ξ n) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ m :=
  let σ : Semiformula L ξ (m + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m) :> fun j ↦ #(j.addNat n))) ➝
      Rewriting.subst φ fun i ↦ #(i.addCast m)
  ∀⁰^[n] σ

def nestFormulaeFunc (φ : Semiformula L ξ (n + 1)) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ (m + 1) :=
  let σ : Semiformula L ξ ((m + 1) + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m.succ) :> fun j ↦ #(j.succ.addNat n))) ➝
      Rewriting.subst φ (#((0 : Fin (m + 1)).addNat n) :> fun i ↦ #(i.addCast m.succ))
  ∀⁰^[n] σ

variable {M : Type*} [s : Structure L M]

lemma eval_nestFormulae {φ : Semiformula L ξ n} {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval s e ε (φ.nestFormulae Ψ) ↔ ∀ v : Fin n → M, (∀ i, Eval s (v i :> e) ε (Ψ i)) → Eval s v ε φ := by
  simp [nestFormulae, Matrix.comp_vecCons']

@[simp] lemma eval_nestFormulae₀ {φ : Semiformula L ξ 0} :
    Eval s e ε (φ.nestFormulae ![]) ↔ Eval s ![] ε φ := by
  simp [eval_nestFormulae, Matrix.empty_eq]

@[simp] lemma eval_nestFormulae₁ {φ : Semiformula L ξ 1} {ψ : Semiformula L ξ (m + 1)} :
    Eval s e ε (φ.nestFormulae ![ψ]) ↔ ∀ x : M, Eval s (x :> e) ε ψ → Eval s ![x] ε φ := by
  simp [eval_nestFormulae, Matrix.forall_iff, Matrix.empty_eq]

@[simp] lemma eval_nestFormulae₂ {φ : Semiformula L ξ 2} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval s e ε (φ.nestFormulae ![ψ₁, ψ₂]) ↔ ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → Eval s ![x₁, x₂] ε φ := by
  suffices
    (∀ x₁ x₂, Eval s (x₁ :> e) ε ψ₁ → Eval s (x₂ :> e) ε ψ₂ → Eval s ![x₁, x₂] ε φ) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → Eval s ![x₁, x₂] ε φ by
    simpa [eval_nestFormulae, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind

@[simp] lemma eval_nestFormulae₃ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval s e ε (φ.nestFormulae ![ψ₁, ψ₂, ψ₃]) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → ∀ x₃, Eval s (x₃ :> e) ε ψ₃ → Eval s ![x₁, x₂, x₃] ε φ := by
  suffices
    (∀ x₁ x₂ x₃, Eval s (x₁ :> e) ε ψ₁ → Eval s (x₂ :> e) ε ψ₂ → Eval s (x₃ :> e) ε ψ₃ → Eval s ![x₁, x₂, x₃] ε φ) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → ∀ x₃, Eval s (x₃ :> e) ε ψ₃ → Eval s ![x₁, x₂, x₃] ε φ by
    simpa [eval_nestFormulae, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

@[simp] lemma eval_nestFormulae₄ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval s e ε (φ.nestFormulae ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ →
    ∀ x₂, Eval s (x₂ :> e) ε ψ₂ →
    ∀ x₃, Eval s (x₃ :> e) ε ψ₃ →
    ∀ x₄, Eval s (x₄ :> e) ε ψ₄ →
    Eval s ![x₁, x₂, x₃, x₄] ε φ := by
  suffices
    (∀ x₁ x₂ x₃ x₄,
      Eval s (x₁ :> e) ε ψ₁ →
      Eval s (x₂ :> e) ε ψ₂ →
      Eval s (x₃ :> e) ε ψ₃ →
      Eval s (x₄ :> e) ε ψ₄ →
      Eval s ![x₁, x₂, x₃, x₄] ε φ) ↔
    ( ∀ x₁, Eval s (x₁ :> e) ε ψ₁ →
      ∀ x₂, Eval s (x₂ :> e) ε ψ₂ →
      ∀ x₃, Eval s (x₃ :> e) ε ψ₃ →
      ∀ x₄, Eval s (x₄ :> e) ε ψ₄ →
      Eval s ![x₁, x₂, x₃, x₄] ε φ) by
    simpa [eval_nestFormulae, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

lemma eval_nestFormulaeFunc {φ : Semiformula L ξ (n + 1)} {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc Ψ) ↔ ∀ v : Fin n → M, (∀ i, Eval s (v i :> e) ε (Ψ i)) → Eval s (z :> v) ε φ := by
  simp [nestFormulaeFunc, Matrix.comp_vecCons']

@[simp] lemma eval_nestFormulaeFunc₀ {φ : Semiformula L ξ 1} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc ![]) ↔ Eval s ![z] ε φ := by
  simp [eval_nestFormulaeFunc, Matrix.empty_eq]

@[simp] lemma eval_nestFormulaeFunc₁ {φ : Semiformula L ξ 2} {ψ : Semiformula L ξ (m + 1)} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc ![ψ]) ↔ ∀ x, Eval s (x :> e) ε ψ → Eval s ![z, x] ε φ := by
  simp [eval_nestFormulaeFunc, Matrix.forall_iff, Matrix.empty_eq]

@[simp] lemma eval_nestFormulaeFunc₂ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc ![ψ₁, ψ₂]) ↔ ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → Eval s ![z, x₁, x₂] ε φ := by
  suffices
    (∀ x₁ x₂, Eval s (x₁ :> e) ε ψ₁ → Eval s (x₂ :> e) ε ψ₂ → Eval s ![z, x₁, x₂] ε φ) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → Eval s ![z, x₁, x₂] ε φ by
    simpa [eval_nestFormulaeFunc, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind

@[simp] lemma eval_nestFormulaeFunc₃ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃]) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → ∀ x₃, Eval s (x₃ :> e) ε ψ₃ → Eval s ![z, x₁, x₂, x₃] ε φ := by
  suffices
    (∀ x₁ x₂ x₃, Eval s (x₁ :> e) ε ψ₁ → Eval s (x₂ :> e) ε ψ₂ → Eval s (x₃ :> e) ε ψ₃ → Eval s ![z, x₁, x₂, x₃] ε φ) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ → ∀ x₂, Eval s (x₂ :> e) ε ψ₂ → ∀ x₃, Eval s (x₃ :> e) ε ψ₃ → Eval s ![z, x₁, x₂, x₃] ε φ by
    simpa [eval_nestFormulaeFunc, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

@[simp] lemma eval_nestFormulaeFunc₄ {φ : Semiformula L ξ 5} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval s (z :> e) ε (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
    ∀ x₁, Eval s (x₁ :> e) ε ψ₁ →
    ∀ x₂, Eval s (x₂ :> e) ε ψ₂ →
    ∀ x₃, Eval s (x₃ :> e) ε ψ₃ →
    ∀ x₄, Eval s (x₄ :> e) ε ψ₄ →
    Eval s ![z, x₁, x₂, x₃, x₄] ε φ := by
  suffices
    (∀ x₁ x₂ x₃ x₄,
      Eval s (x₁ :> e) ε ψ₁ →
      Eval s (x₂ :> e) ε ψ₂ →
      Eval s (x₃ :> e) ε ψ₃ →
      Eval s (x₄ :> e) ε ψ₄ →
      Eval s ![z, x₁, x₂, x₃, x₄] ε φ) ↔
    ( ∀ x₁, Eval s (x₁ :> e) ε ψ₁ →
      ∀ x₂, Eval s (x₂ :> e) ε ψ₂ →
      ∀ x₃, Eval s (x₃ :> e) ε ψ₃ →
      ∀ x₄, Eval s (x₄ :> e) ε ψ₄ →
      Eval s ![z, x₁, x₂, x₃, x₄] ε φ) by
    simpa [eval_nestFormulaeFunc, Matrix.forall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

end Semiformula

namespace BinderNotation

@[simp] abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ

open Semiterm Semiformula

/-! ### (Literal) Notation for terms -/

declare_syntax_cat first_order_term

declare_syntax_cat first_order.quote_type

syntax:max "lit" : first_order.quote_type -- literal notation
syntax:max "faf" : first_order.quote_type -- formula-as-function notation

syntax "⤫term(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_term:0 "]" : term

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
  | `(⤫term($type)[ $binders* | $fbinders* | ($e) ]) => `(⤫term($type)[ $binders* | $fbinders* | $e ])

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(⤫term(lit)[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(⤫term(lit)[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(⤫term(lit)[ $_*       | $_*        | $m:num     ]) => `(Semiterm.numeral $m)
  | `(⤫term(lit)[ $_*       | $_*        | ↑$m:term   ]) => `(Semiterm.numeral $m)
  | `(⤫term(lit)[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(⤫term(lit)[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ + $e₂  ]) => `(Semiterm.Operator.Add.add.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ * $e₂  ]) => `(Semiterm.Operator.Mul.mul.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) => `(Semiterm.Operator.Pow.pow.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e ^' $n   ]) => `((Semiterm.Operator.npow _ $n).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e²        ]) => `((Semiterm.Operator.npow _ 2).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e³        ]) => `((Semiterm.Operator.npow _ 3).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e⁴        ]) => `((Semiterm.Operator.npow _ 4).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | exp $e     ]) => `(Semiterm.Operator.Exp.exp.operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(⤫term(lit)[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | !$t:term $vs:first_order_term*    ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(⤫term(lit)[ $binders* | $fbinders* | $a ] :> $s))
    `(Rew.subst $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | !$t:term $vs:first_order_term* ⋯  ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.subst $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | .!$t:term $vs:first_order_term*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | .!$t:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)

syntax "‘" first_order_term:0 "’" : term
syntax "‘" ident* "| " first_order_term:0 "’" : term
syntax "‘" ident* ". " first_order_term:0 "’" : term

macro_rules
  | `(‘ $e:first_order_term ’)              => `(⤫term(lit)[           |            | $e ])
  | `(‘ $fbinders* | $e:first_order_term ’) => `(⤫term(lit)[           | $fbinders* | $e ])
  | `(‘ $binders*. $e:first_order_term ’)   => `(⤫term(lit)[ $binders* |            | $e ])

#check (⤫term(lit)[ x y z | A B C | B + (4 + A * (x⁴ + z)²) + ↑4] : Semiterm ℒₒᵣ ℕ 1)
#check ‘a x. a’

section delab

@[app_unexpander Semiterm.Operator.numeral]
meta def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.const]
meta def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()

@[app_unexpander Semiterm.Operator.Add.add]
meta def unexpsnderAdd : Unexpander
  | `($_) => `(op(+))

@[app_unexpander Semiterm.Operator.Mul.mul]
meta def unexpsnderMul : Unexpander
  | `($_) => `(op(*))

@[app_unexpander Semiterm.Operator.operator]
meta def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘$t:first_order_term’,   ‘$u:first_order_term’   ]) => `(‘($t     + $u     )’)
  | `($_ op(+) ![‘$t:first_order_term’,   #$x                     ]) => `(‘($t     + #$x    )’)
  | `($_ op(+) ![‘$t:first_order_term’,   &$x                     ]) => `(‘($t     + &$x    )’)
  | `($_ op(+) ![‘$t:first_order_term’,   ↑$m:num                 ]) => `(‘($t     + $m:num )’)
  | `($_ op(+) ![‘$t:first_order_term’,   $u:term                 ]) => `(‘($t     + !!$u   )’)
  | `($_ op(+) ![#$x,                     ‘$u:first_order_term’   ]) => `(‘(#$x    + $u     )’)
  | `($_ op(+) ![#$x,                     #$y                     ]) => `(‘(#$x    + #$y    )’)
  | `($_ op(+) ![#$x,                     &$y                     ]) => `(‘(#$x    + &$y    )’)
  | `($_ op(+) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    + $m:num )’)
  | `($_ op(+) ![#$x,                     $u                      ]) => `(‘(#$x    + !!$u   )’)
  | `($_ op(+) ![&$x,                     ‘$u:first_order_term’   ]) => `(‘(&$x    + $u     )’)
  | `($_ op(+) ![&$x,                     #$y                     ]) => `(‘(&$x    + #$y    )’)
  | `($_ op(+) ![&$x,                     &$y                     ]) => `(‘(&$x    + &$y    )’)
  | `($_ op(+) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    + $m:num )’)
  | `($_ op(+) ![&$x,                     $u                      ]) => `(‘(&$x    + !!$u   )’)
  | `($_ op(+) ![↑$n:num,                 ‘$u:first_order_term’   ]) => `(‘($n:num + $u     )’)
  | `($_ op(+) ![↑$n:num,                 #$y                     ]) => `(‘($n:num + #$y    )’)
  | `($_ op(+) ![↑$n:num,                 &$y                     ]) => `(‘($n:num + &$y    )’)
  | `($_ op(+) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num + $m:num )’)
  | `($_ op(+) ![↑$n:num,                 $u                      ]) => `(‘($n:num + !!$u   )’)
  | `($_ op(+) ![$t:term,                 ‘$u:first_order_term’   ]) => `(‘(!!$t   + $u     )’)
  | `($_ op(+) ![$t:term,                 #$y                     ]) => `(‘(!!$t   + #$y    )’)
  | `($_ op(+) ![$t:term,                 &$y                     ]) => `(‘(!!$t   + &$y    )’)
  | `($_ op(+) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   + $m:num )’)
  | `($_ op(+) ![$t:term,                 $u                      ]) => `(‘(!!$t   + !!$u   )’)

  | `($_ op(*) ![‘$t:first_order_term’,   ‘$u:first_order_term’   ]) => `(‘($t     * $u     )’)
  | `($_ op(*) ![‘$t:first_order_term’,   #$x                     ]) => `(‘($t     * #$x    )’)
  | `($_ op(*) ![‘$t:first_order_term’,   &$x                     ]) => `(‘($t     * &$x    )’)
  | `($_ op(*) ![‘$t:first_order_term’,   ↑$m:num                 ]) => `(‘($t     * $m:num )’)
  | `($_ op(*) ![‘$t:first_order_term’,   $u:term                 ]) => `(‘($t     * !!$u   )’)
  | `($_ op(*) ![#$x,                     ‘$u:first_order_term’   ]) => `(‘(#$x    * $u     )’)
  | `($_ op(*) ![#$x,                     #$y                     ]) => `(‘(#$x    * #$y    )’)
  | `($_ op(*) ![#$x,                     &$y                     ]) => `(‘(#$x    * &$y    )’)
  | `($_ op(*) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    * $m:num )’)
  | `($_ op(*) ![#$x,                     $u                      ]) => `(‘(#$x    * !!$u   )’)
  | `($_ op(*) ![&$x,                     ‘$u:first_order_term’   ]) => `(‘(&$x    * $u     )’)
  | `($_ op(*) ![&$x,                     #$y                     ]) => `(‘(&$x    * #$y    )’)
  | `($_ op(*) ![&$x,                     &$y                     ]) => `(‘(&$x    * &$y    )’)
  | `($_ op(*) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    * $m:num )’)
  | `($_ op(*) ![&$x,                     $u                      ]) => `(‘(&$x    * !!$u   )’)
  | `($_ op(*) ![↑$n:num,                 ‘$u:first_order_term’   ]) => `(‘($n:num * $u     )’)
  | `($_ op(*) ![↑$n:num,                 #$y                     ]) => `(‘($n:num * #$y    )’)
  | `($_ op(*) ![↑$n:num,                 &$y                     ]) => `(‘($n:num * &$y    )’)
  | `($_ op(*) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num * $m:num )’)
  | `($_ op(*) ![↑$n:num,                 $u                      ]) => `(‘($n:num * !!$u   )’)
  | `($_ op(*) ![$t:term,                 ‘$u:first_order_term’   ]) => `(‘(!!$t   * $u     )’)
  | `($_ op(*) ![$t:term,                 #$y                     ]) => `(‘(!!$t   * #$y    )’)
  | `($_ op(*) ![$t:term,                 &$y                     ]) => `(‘(!!$t   * &$y    )’)
  | `($_ op(*) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   * $m:num )’)
  | `($_ op(*) ![$t:term,                 $u                      ]) => `(‘(!!$t   * !!$u   )’)
  | _                             => throw ()

@[app_unexpander Semiterm.numeral]
meta def unexpandNumeral : Unexpander
  | `($_ $n:num) => `(‘$n:num’)
  | _            => throw ()

#check ‘ x | &4 + ((4 + 2) * #0 + #1)’

end delab

/-! ### Notation for formulae -/

open Semiformula

declare_syntax_cat first_order_formula


syntax "⤫formula(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_formula:0 "]" : term

syntax "(" first_order_formula ")" : first_order_formula

syntax:60 "of_term[" first_order_term:61 "]" : first_order_formula

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
syntax:max "∀⁰ " first_order_formula:0 : first_order_formula
syntax:max "∃⁰ " first_order_formula:0 : first_order_formula
syntax:max "∀⁰[" first_order_formula "] " first_order_formula:0 : first_order_formula
syntax:max "∃⁰[" first_order_formula "] " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ($e)          ]) => `(⤫formula($type)[ $binders* | $fbinders* | $e ])
  | `(⤫formula($type)[ $_*       | $_*        | !!$φ:term     ]) => `($φ)
  | `(⤫formula($type)[ $_*       | $_*        | .!!$φ:term    ]) => `(Rewriting.emb $φ)
  | `(⤫formula($type)[ $_*       | $_*        | ⊤             ]) => `(⊤)
  | `(⤫formula($type)[ $_*       | $_*        | ⊥             ]) => `(⊥)
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∧ $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] ⋏ ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∨ $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] ⋎ ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ¬$φ           ]) => `(∼⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ → $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] ➝ ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ↔ $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] ⭤ ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋀ $i, $φ      ]) => `(Matrix.conj fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋁ $i, $φ      ]) => `(Matrix.disj fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋀ $i < $t, $φ ]) => `(conjLt (fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋁ $i < $t, $φ ]) => `(disjLt (fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀⁰ $ψ))
    return s
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃⁰ $ψ))
    return s
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀⁰ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀⁰ ⤫formula($type)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃⁰ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃⁰ ⤫formula($type)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀⁰[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀⁰[⤫formula($type)[ $binders'* | $fbinders* | $φ ]] ⤫formula($type)[ $binders'* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃⁰[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃⁰[⤫formula($type)[ $binders'* | $fbinders* | $φ ]] ⤫formula($type)[ $binders'* | $fbinders* | $ψ ])

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a ] :> $s))
    `($φ ⇜ $v)
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `($φ ⇜ $v)

syntax "“" ident* "| "  first_order_formula:0 "”" : term
syntax "“" ident* ". "  first_order_formula:0 "”" : term
syntax "“" first_order_formula:0 "”" : term

macro_rules
  | `(“ $e:first_order_formula ”)              => `(⤫formula(lit)[           |            | $e ])
  | `(“ $binders*. $e:first_order_formula ”)   => `(⤫formula(lit)[ $binders* |            | $e ])
  | `(“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(lit)[           | $fbinders* | $e ])

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
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term > $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term < $t:first_order_term ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ≥ $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term ≤ $t:first_order_term ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ∋ $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term ∈ $t:first_order_term ])

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term < $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LT.lt ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≤ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LE.le ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≮ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.LT.lt ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≰ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.LE.le ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => `(∼(Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballLT ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballLE ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsLT ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsLE ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])

#check “∀ x, ∀ y, ∀ z, ∀ v, ∀ w, x + y + z + v + w = 0”
#check “∀ x y z v w, x + y + z + v + w = 0”
#check “x y z | ∃ v w, ∀ r < z + v + 7, ∀⁰ x + y + v = x ↔ z = .!(‘#0 + #1’) x y”
#check “x y. ∀ z < 0, ∀ w < y, x = z + w”

section delab

@[app_unexpander Language.Eq.eq]
meta def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

@[app_unexpander Language.LT.lt]
meta def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

@[app_unexpander Wedge.wedge]
meta def unexpandAnd : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Vee.vee]
meta def unexpandOr : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Tilde.tilde]
meta def unexpandNeg : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ¬$φ ”)
  | _                                => throw ()

@[app_unexpander UnivQuantifier.all]
meta def unexpandUniv : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ∀⁰ $φ:first_order_formula ”)
  | _                                => throw ()

@[app_unexpander ExsQuantifier.exs]
meta def unexpandEx : Unexpander
  | `($_ “ $φ:first_order_formula”) => `(“ ∃⁰ $φ:first_order_formula ”)
  | _                                   => throw ()

@[app_unexpander ball]
meta def unexpandBall : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∀⁰[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∀⁰[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∀⁰[!$t] $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander bexs]
meta def unexpandBex : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∃⁰[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∃⁰[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∃⁰[!$t] $ψ) ”)
  | _                                                           => throw ()

@[app_unexpander Arrow.arrow]
meta def unexpandArrow : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()

@[app_unexpander LogicalConnective.iff]
meta def unexpandIff : Unexpander
  | `($_ “ $φ:first_order_formula” “ $ψ:first_order_formula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:first_order_formula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:first_order_formula”) => `(“ (!$t ↔ $ψ) ”)
  | _                                                         => throw ()

@[app_unexpander Semiformula.Operator.operator]
meta def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term = $u      ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term = #$y     ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term = &$y     ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term = $m:num  ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term = !!$u    ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 = $u      ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 = #$y     ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 = &$y     ”)
  | `($_ op(=) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 = $m:num  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) => `(“ #$x                 = !!$u    ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 = $u      ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 = #$y     ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 = &$y     ”)
  | `($_ op(=) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 = $m:num  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) => `(“ &$x                 = !!$u    ”)
  | `($_ op(=) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              = $u      ”)
  | `($_ op(=) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              = #$y     ”)
  | `($_ op(=) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              = &$y     ”)
  | `($_ op(=) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              = $m:num  ”)
  | `($_ op(=) ![↑$n:num,                  $u                     ]) => `(“ $n:num              = !!$u    ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                = $u      ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) => `(“ !!$t                = #$y     ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) => `(“ !!$t                = &$y     ”)
  | `($_ op(=) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                = $m:num  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) => `(“ !!$t                = !!$u    ”)

  | `($_ op(<) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term < $u      ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term < #$y     ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term < &$y     ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term < $m:num  ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term < !!$u    ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 < $u      ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 < #$y     ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 < &$y     ”)
  | `($_ op(<) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 < $m:num  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) => `(“ #$x                 < !!$u    ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 < $u      ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 < #$y     ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 < &$y     ”)
  | `($_ op(<) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 < $m:num  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) => `(“ &$x                 < !!$u    ”)
  | `($_ op(<) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              < $u      ”)
  | `($_ op(<) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              < #$y     ”)
  | `($_ op(<) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              < &$y     ”)
  | `($_ op(<) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              < $m:num  ”)
  | `($_ op(<) ![↑$n:num,                  $u                     ]) => `(“ $n:num              < !!$u    ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                < $u      ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) => `(“ !!$t                < #$y     ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) => `(“ !!$t                < &$y     ”)
  | `($_ op(<) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                < $m:num  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) => `(“ !!$t                < !!$u    ”)

  | `($_ op(≤) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ≤ $u      ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ≤ #$y     ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ≤ &$y     ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term ≤ $m:num  ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ≤ !!$u    ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ≤ $u      ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ≤ #$y     ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ≤ &$y     ”)
  | `($_ op(≤) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 ≤ $m:num  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) => `(“ #$x                 ≤ !!$u    ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ≤ $u      ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ≤ #$y     ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ≤ &$y     ”)
  | `($_ op(≤) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 ≤ $m:num  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) => `(“ &$x                 ≤ !!$u    ”)
  | `($_ op(≤) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              ≤ $u      ”)
  | `($_ op(≤) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              ≤ #$y     ”)
  | `($_ op(≤) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              ≤ &$y     ”)
  | `($_ op(≤) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              ≤ $m:num  ”)
  | `($_ op(≤) ![↑$n:num,                  $u                     ]) => `(“ $n:num              ≤ !!$u    ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ≤ $u      ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ≤ #$y     ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ≤ &$y     ”)
  | `($_ op(≤) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                ≤ $m:num  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) => `(“ !!$t                ≤ !!$u    ”)

  | `($_ op(∈) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ∈ $u      ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ∈ #$y     ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ∈ &$y     ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term ∈ $m:num  ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ∈ !!$u    ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ∈ $u      ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ∈ #$y     ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ∈ &$y     ”)
  | `($_ op(∈) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 ∈ $m:num  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) => `(“ #$x                 ∈ !!$u    ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ∈ $u      ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ∈ #$y     ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ∈ &$y     ”)
  | `($_ op(∈) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 ∈ $m:num  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) => `(“ &$x                 ∈ !!$u    ”)
  | `($_ op(∈) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              ∈ $u      ”)
  | `($_ op(∈) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              ∈ #$y     ”)
  | `($_ op(∈) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              ∈ &$y     ”)
  | `($_ op(∈) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              ∈ $m:num  ”)
  | `($_ op(∈) ![↑$n:num,                  $u                     ]) => `(“ $n:num              ∈ !!$u    ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ∈ $u      ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ∈ #$y     ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ∈ &$y     ”)
  | `($_ op(∈) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                ∈ $m:num  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) => `(“ !!$t                ∈ !!$u    ”)

  | _                                                            => throw ()

#check “x y z. ∃ v w, ∀ r < z + v, y + v ≤ x ↔ z = w”
#check “x y | x = y → y = x”
#check “x y . x = y → 4 * y = 3”
#check “∀ x y, x = y → y = x”

end delab

/-! ### Notation for formula as term -/

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a ] :> $s)
    `(($φ).nestFormulae $Ψ)
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a] :> $s)
    `(($φ).nestFormulae $Ψ)

macro_rules
  | `(⤫term(faf)[ $binders* | $fbinders* | $x:ident                         ]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable does not appeared."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(“#0 = &$i”)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(“#0 = #$i”)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a ] :> $s)
    `(($f).nestFormulaeFunc $Ψ)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a] :> $s)
    `(($f).nestFormulaeFunc $Ψ)

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 = #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ≠ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term < $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 < #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≮ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ≮ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≤ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ≤ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≰ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ≰ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ∈ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀⁰ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] ➝ ∀⁰ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] ➝ “#1 ∉ #0”)))

macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.ballLT #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.ballLE #0 ⤫formula(faf)[ $x $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.ballMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.bexsLT #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.bexsLE #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀⁰ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] ➝ Semiformula.bexsMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))

syntax "f‘" first_order_term:0 "’" : term
syntax "f‘" ident* "| " first_order_term:0 "’" : term
syntax "f‘" ident* ". " first_order_term:0 "’" : term

macro_rules
  | `(f‘ $e:first_order_term ’)              => `(⤫term(faf)[           |            | $e ])
  | `(f‘ $fbinders* | $e:first_order_term ’) => `(⤫term(faf)[           | $fbinders* | $e ])
  | `(f‘ $binders*. $e:first_order_term ’)   => `(⤫term(faf)[ $binders* |            | $e ])

#check f‘a x. x’

syntax "f“" ident* "| "  first_order_formula:0 "”" : term
syntax "f“" ident* ". "  first_order_formula:0 "”" : term
syntax "f“" first_order_formula:0 "”" : term

macro_rules
  | `(f“ $e:first_order_formula ”)              => `(⤫formula(faf)[           |            | $e ])
  | `(f“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(faf)[           | $fbinders* | $e ])
  | `(f“ $binders*. $e:first_order_formula ”)   => `(⤫formula(faf)[ $binders* |            | $e ])

#check f“x y. x = y”

/-
variable {L : Language} [L.Eq] [L.Mem]

def func : Semisentence L 3 := sorry

def rel : Semisentence L 2 := sorry

def sent : Semisentence L 3 := f“F X Y. ∀ f, f ∈ F ↔ f ∈ !func X Y”

def sent₂ : Semisentence L 3 := f“F X Y. ∀ f, f ∈ F”

variable {M : Type*} [Membership M M] [s : Structure L M] [Structure.Eq L M] [Structure.Mem L M]

def Func : M → M → M := sorry

def Rel : M → M → Prop := sorry

@[simp] lemma eval_func : M ⊧/![x, y, z] (func : Semisentence L 3) ↔ x = Func y z := sorry

@[simp] lemma eval_rel : M ⊧/![x, y] (rel : Semisentence L 2) ↔ Rel x y := sorry

lemma egegege : M ⊧/![x, y, z] (f“x y z. ∀ w ∈ x, w ∈ z” : Semisentence L 3) := by {

  simp

 }
-/

end BinderNotation

end LO.FirstOrder

end
