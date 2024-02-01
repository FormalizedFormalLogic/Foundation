import Logic.FirstOrder.Arith.PAminus

namespace Matrix

lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  rfl

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl

@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) : (a :> s) 5 = s 4 := rfl

@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) : (a :> s) 6 = s 5 := rfl

end Matrix

instance : ToString Empty := ⟨Empty.elim⟩

class Hash (α : Type*) where
  hash : α → α → α

infix:80 " # " => Hash.hash

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x


namespace LO

namespace FirstOrder

variable {L : Language} [L.Zero] [L.One] [L.Add] [L.Mul]

namespace Semiterm

def complexity : Semiterm L ξ n → ℕ
  | #_       => 0
  | &_       => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl

lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 := rfl

@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  simp [complexity_func, Nat.lt_add_one_iff]; exact Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)

@[simp] lemma complexity_zero : (ᵀ“0” : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Zero.term_eq, complexity_func]

@[simp] lemma complexity_one : (ᵀ“1” : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.One.term_eq, complexity_func]

@[simp] lemma complexity_add (t u : Semiterm L ξ n) :
    (ᵀ“!!t + !!u” : Semiterm L ξ n).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Add.term_eq, complexity_func, Rew.func]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]
  simp [sup_eq_max]

@[simp] lemma complexity_mul (t u : Semiterm L ξ n) :
    (ᵀ“!!t * !!u” : Semiterm L ξ n).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Mul.term_eq, complexity_func, Rew.func]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]
  simp [sup_eq_max]

lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L μ n) :
    (Rew.bShift t).val s e ε = t.val s (e ·.succ) ε := by simp[val_rew, Function.comp]

namespace Operator

variable {L : Language} [Operator.One L] [Operator.Mul L]

def npow (L : Language) [Operator.One L] [Operator.Mul L] (n : ℕ) : Operator L 1 := op(*).foldr (One.one.comp ![]) (List.replicate n (bvar 0))

lemma npow_zero : npow L 0 = One.one.comp ![] := rfl

lemma npow_succ : npow L (n + 1) = op(*).comp ![npow L n, bvar 0] := by simp [npow, foldr]

@[simp] lemma npow_positive_iff {L : Language} [Operator.One L] [L.Mul] (t : Semiterm L μ (n + 1)) (k : ℕ) :
    ((Operator.npow L k).operator ![t]).Positive ↔ k = 0 ∨ t.Positive := by
  cases k <;> simp [positive_operator_iff, operator_comp, npow_zero, npow_succ]
  case succ k _ =>
    simp [Mul.term_eq, bv_func]
    constructor
    · intro h; exact h 1 0 (by simp [bvar])
    · intro h _ _ _
      exact h

variable {M : Type*} {s : Structure L M}

@[simp] lemma val_bvar {n} (x : Fin n) (v : Fin n → M) :
    (Operator.bvar (L := L) x).val v = v x := by simp [Operator.bvar, Operator.val]

end Operator

end Semiterm

namespace Rew

def embSubsts (v : Fin k → Semiterm L μ n) : Rew L Empty k μ n := Rew.bind v Empty.elim

section embSubsts

variable {k} (w : Fin k → Semiterm L μ n)

@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x :=
  by simp[embSubsts]

@[simp] lemma embSubsts_zero (w : Fin 0 → Term L μ) : embSubsts w = Rew.emb := by
  ext x <;> try simp
  · exact Fin.elim0 x
  · exact Empty.elim x

lemma substs_comp_embSubsts (v : Fin l → Semiterm L μ k) (w : Fin k → Semiterm L μ n) :
    (substs w).comp (embSubsts v) = embSubsts (substs w ∘ v) := by
  ext x <;> simp[comp_app]
  exact Empty.elim x

@[simp] lemma embSubsts_eq_id : (embSubsts Semiterm.bvar : Rew L Empty n μ n) = Rew.emb := by
  ext x <;> try simp
  · exact Empty.elim x

lemma q_embSubsts (w : Fin k → Semiterm L μ n) :
    (embSubsts w).q = embSubsts (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simp; exact Empty.elim x }

end embSubsts

end Rew

scoped syntax (name := embSubstsHomNotation) term:max ".[" term,* "]" : term

scoped macro_rules (kind := embSubstsHomNotation)
  | `($p:term .[$terms:term,*]) => `((Rew.embSubsts ![$terms,*]).hom $p)

namespace Semiterm

variable {M : Type w} {s : Structure L M} {e : Fin n → M} {ε : μ → M}

lemma val_embSubsts (w : Fin k → Semiterm L μ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val s e ε = t.bVal s (fun x ↦ (w x).val s e ε) := by
  simp [val_rew, Empty.eq_elim]; congr

end Semiterm

namespace Semiformula

variable {M : Type w} {s : Structure L M} {e : Fin n → M} {ε : μ → M}

lemma eval_embSubsts {k} (w : Fin k → Semiterm L μ n) (σ : Semisentence L k) :
    Eval s e ε ((Rew.embSubsts w).hom σ) ↔ PVal s (fun x ↦ (w x).val s e ε) σ := by
  simp[eval_rew, Function.comp, Empty.eq_elim]

section fvEnum'

variable [DecidableEq μ] [Inhabited μ]

def fvEnum' (p : Semiformula L μ n) : μ → ℕ := p.fvarList.indexOf

def fvEnumInv' (p : Semiformula L μ n) : ℕ → μ :=
  fun i ↦ if hi : i < p.fvarList.length then p.fvarList.get ⟨i, hi⟩ else default

lemma fvEnumInv'_fvEnum' (p : Semiformula L μ n) {x : μ} (hx : x ∈ p.fvarList) :
    fvEnumInv' p (fvEnum' p x) = x := by
  simp [fvEnumInv', fvEnum']; intro h
  exact False.elim <| not_le.mpr (List.indexOf_lt_length.mpr $ hx) h

end fvEnum'

end Semiformula

section

open Lean PrettyPrinter Delaborator SubExpr

syntax foterm " ^ⁿ " num  : foterm
syntax foformula ".[" foterm,* "]" : foformula

macro_rules
  | `(“ $p:foformula .[ $t:foterm,* ] ”) => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `((Rew.embSubsts $v).hom “$p”)
  | `(ᵀ“ $t:foterm ^ⁿ $n:num ”)          => `(Semiterm.Operator.const (Operator.npow _ $n ![ᵀ“$t”]))

end

namespace Arith

attribute [simp] Semiformula.eval_substs Semiformula.eval_embSubsts
  Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

section ToString

variable [ToString μ]

open Semiterm Semiformula

def termToStr : Semiterm ℒₒᵣ μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _   => "1"
  | func Language.Add.add v   => "(" ++ termToStr (v 0) ++ " + " ++ termToStr (v 1) ++ ")"
  | func Language.Mul.mul v   => "(" ++ termToStr (v 0) ++ " \\cdot " ++ termToStr (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ μ n) := ⟨fun t _ => termToStr t⟩

instance : ToString (Semiterm ℒₒᵣ μ n) := ⟨termToStr⟩

def formulaToStr : ∀ {n}, Semiformula ℒₒᵣ μ n → String
  | _, ⊤                             => "\\top"
  | _, ⊥                             => "\\bot"
  | _, rel Language.Eq.eq v          => termToStr (v 0) ++ " = " ++ termToStr (v 1)
  | _, rel Language.LT.lt v          => termToStr (v 0) ++ " < " ++ termToStr (v 1)
  | _, nrel Language.Eq.eq v         => termToStr (v 0) ++ " \\not = " ++ termToStr (v 1)
  | _, nrel Language.LT.lt v         => termToStr (v 0) ++ " \\not < " ++ termToStr (v 1)
  | _, p ⋏ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\land " ++ "[" ++ formulaToStr q ++ "]"
  | _, p ⋎ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\lor "  ++ "[" ++ formulaToStr q ++ "]"
  | n, ∀' (rel Language.LT.lt v ⟶ p) => "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ p) => "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p  ++ "]"
  | n, ∀' p                          => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' p                          => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"

instance : Repr (Semiformula ℒₒᵣ μ n) := ⟨fun t _ => formulaToStr t⟩

instance : ToString (Semiformula ℒₒᵣ μ n) := ⟨formulaToStr⟩

end ToString

namespace Hierarchy

variable {L : Language} [L.LT]

lemma of_zero {b b'} {s : ℕ} {p : Semiformula L μ n} (hp : Hierarchy b 0 p) : Hierarchy b' s p := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp b' pos

lemma iff_iff {p q : Semiformula L μ n} :
    Hierarchy b s (p ⟷ q) ↔ (Hierarchy b s p ∧ Hierarchy b.alt s p ∧ Hierarchy b s q ∧ Hierarchy b.alt s q) := by
  simp[Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {p q : Semiformula L μ n} :
    Hierarchy b 0 (p ⟷ q) ↔ (Hierarchy b 0 p ∧ Hierarchy b 0 q) := by
  simp[Semiformula.iff_eq]; tauto

end Hierarchy

end Arith

end FirstOrder

end LO
