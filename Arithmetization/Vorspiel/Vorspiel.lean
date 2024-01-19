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

end Matrix

instance : ToString Empty := ⟨Empty.elim⟩

namespace LO

namespace FirstOrder


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

lemma val_rewriteMap (f : μ₁ → μ₂) (t : Semiterm L μ₁ n) :
    (Rew.rewriteMap f t).val s e ε₂ = t.val s e (fun x => ε₂ (f x)) :=
  by simp[val_rew]; congr

lemma val_embSubsts (w : Fin k → Semiterm L μ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val s e ε = t.bVal s (fun x ↦ (w x).val s e ε) := by
  simp [val_rew, Empty.eq_elim]; congr

end Semiterm

namespace Semiformula

variable {M : Type w} {s : Structure L M} {e : Fin n → M} {ε : μ → M}

lemma eval_embSubsts {k} (w : Fin k → Semiterm L μ n) (σ : Semisentence L k) :
    Eval s e ε ((Rew.embSubsts w).hom σ) ↔ PVal s (fun x ↦ (w x).val s e ε) σ := by
  simp[eval_rew, Function.comp, Empty.eq_elim]

open Lean PrettyPrinter Delaborator SubExpr

syntax foformula ".[" foterm,* "]" : foformula

macro_rules
  | `(“ $p:foformula .[ $t:foterm,* ] ”) => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `((Rew.embSubsts $v).hom “$p”)

end Semiformula

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
