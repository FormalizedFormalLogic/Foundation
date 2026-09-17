module

public import Foundation.FirstOrder.Tarski.Basic
public import Foundation.FirstOrder.Syntax.Classical.Operator

@[expose] public section

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option autoImplicit true
set_option linter.style.whitespace false

namespace FFL

namespace FirstOrder

universe w

variable {L : Language}

namespace Semiterm

def Operator.val {M : Type w} [s : Tarski.Structure L M] (v : Fin k → M) (o : Operator L k) : M :=
  Semiterm.val v Empty.elim o.term

variable {M : Type w} {s : Tarski.Structure L M}

@[simp] lemma val_operator {k} (b : Fin n → M) (f : ξ → M) (o : Operator L k) (v : Fin k → Semiterm L ξ n) :
    val b f (o.operator v) = o.val (Semiterm.val b f ∘ v) := by
  simp [Operator.operator, val_substs, Empty.eq_elim]; congr

lemma val_operator' {k} (b : Fin k → M) (f : ξ → M) (o : Operator L k) (v) :
    val b f (o.operator v) = o.val fun i ↦ (v i).val b f := val_operator b f o v

lemma Operator.val_comp (o₁ : Operator L k) (o₂ : Fin k → Operator L m) (v : Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (val v ∘ o₂) := by
  simp [comp, val, Function.comp_def]

@[simp] lemma Operator.val_bvar {n} (x : Fin n) (v : Fin n → M) :
    (Operator.bvar (L := L) x).val v = v x := by simp [Operator.bvar, Operator.val]

end Semiterm

namespace Semiformula

def Operator.val {M : Type w} [s : Tarski.Structure L M] {k} (v : Fin k → M) (o : Operator L k) : Prop :=
  o.sentence.Eval v Empty.elim

section

variable {M : Type w} {s : Tarski.Structure L M}

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp [Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp [Operator.or, Operator.val]

@[simp] lemma eval_operator {k} {o : Operator L k} {e : Fin n → M} {f : ξ → M} {v : Fin k → Semiterm L ξ n} :
    Eval e f (o.operator v) ↔ o.val (Semiterm.val e f ∘ v) := by
  simp [Operator.operator, eval_substs, Operator.val]

end

end Semiformula

namespace Tarski.Structure

open Semiterm Semiformula

variable (L) (M : Type*) [Tarski.Structure L M]

protected class Zero [Operator.Zero L] [Zero M] : Prop where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)

protected class One [Operator.One L] [One M] : Prop where
  one : (@Operator.One.one L _).val ![] = (1 : M)

protected class Add [Operator.Add L] [Add M] : Prop where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b

protected class Mul [Operator.Mul L] [Mul M] : Prop where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b

protected class Exp [Operator.Exp L] [Exp M] : Prop where
  exp : ∀ a : M, (@Operator.Exp.exp L _).val ![a] = Exp.exp a

protected class Eq [Operator.Eq L] : Prop where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b

protected class LT [Operator.LT L] [LT M] : Prop where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b

protected class LE [Operator.LE L] [LE M] : Prop where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b

protected class Mem [Operator.Mem L] [Membership M M] : Prop where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b

attribute [simp] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt LE.le Mem.mem

instance [L.Eq] [L.LT] [Tarski.Structure.Eq L M] [PartialOrder M] [Tarski.Structure.LT L M] :
  Tarski.Structure.LE L M := ⟨by intro a b; simpa [Operator.LE.def_of_Eq_of_LT] using le_iff_eq_or_lt.symm⟩

variable {L M}

@[simp] lemma zero_eq_of_lang [L.Zero] [Zero M] [Tarski.Structure.Zero L M] (v : Fin 0 → M) :
    Tarski.Structure.func (L := L) Language.Zero.zero v = (0 : M) := by
  simpa [Matrix.empty_eq, Semiterm.Operator.val, Semiterm.Operator.Zero.zero, ←Matrix.fun_eq_vec_two] using
    Tarski.Structure.Zero.zero (L := L) (M := M)

@[simp] lemma one_eq_of_lang [L.One] [One M] [Tarski.Structure.One L M] (v : Fin 0 → M) :
    Tarski.Structure.func (L := L) Language.One.one v = (1 : M) := by
  simpa [Matrix.empty_eq, Semiterm.Operator.val, Semiterm.Operator.One.one, ←Matrix.fun_eq_vec_two] using
    Tarski.Structure.One.one (L := L) (M := M)

@[simp] lemma add_eq_of_lang [L.Add] [Add M] [Tarski.Structure.Add L M] {v : Fin 2 → M} :
    Tarski.Structure.func (L := L) Language.Add.add v = v 0 + v 1 := by
  have h := Tarski.Structure.Add.add (L := L) (v 0) (v 1)
  simp only [←Matrix.fun_eq_vec_two] at h
  exact h

@[simp] lemma mul_eq_of_lang [L.Mul] [Mul M] [Tarski.Structure.Mul L M] {v : Fin 2 → M} :
    Tarski.Structure.func (L := L) Language.Mul.mul v = v 0 * v 1 := by
  have h := Tarski.Structure.Mul.mul (L := L) (v 0) (v 1)
  simp only [←Matrix.fun_eq_vec_two] at h
  exact h

@[simp] lemma exp_eq_of_lang [L.Exp] [Exp M] [Tarski.Structure.Exp L M] {v : Fin 1 → M} :
    Tarski.Structure.func (L := L) Language.Exp.exp v = FFL.Exp.exp (v 0) := by
  have h := Tarski.Structure.Exp.exp (L := L) (v 0)
  simp only [←Matrix.fun_eq_vec_one] at h
  exact h

@[simp] lemma eq_iff_eq [Operator.Eq L] [Tarski.Structure.Eq L M] {v : Fin 2 →M} :
    (@Operator.Eq.eq L _).val v ↔ v 0 = v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp

@[simp] lemma lt_iff_lt [Operator.LT L] [LT M] [Tarski.Structure.LT L M] {v : Fin 2 →M} :
    (@Operator.LT.lt L _).val v ↔ v 0 < v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp

@[simp] lemma mem_iff_mem [Operator.Mem L] [Membership M M] [Tarski.Structure.Mem L M] {v : Fin 2 →M} :
    (@Operator.Mem.mem L _).val v ↔ v 0 ∈ v 1 := by
  rw [Matrix.fun_eq_vec_two v]; simp

lemma le_iff_of_eq_of_lt [Operator.Eq L] [Operator.LT L] [LT M] [Tarski.Structure.Eq L M] [Tarski.Structure.LT L M] {a b : M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp [Operator.LE.def_of_Eq_of_LT]

@[simp] lemma eq_lang [L.Eq] [Tarski.Structure.Eq L M] {v : Fin 2 → M} :
    Tarski.Structure.rel (L := L) Language.Eq.eq v ↔ v 0 = v 1 := by simpa [-eq_iff_eq] using! eq_iff_eq (L := L) (v := v)

@[simp] lemma lt_lang [L.LT] [LT M] [Tarski.Structure.LT L M] {v : Fin 2 → M} :
    Tarski.Structure.rel (L := L) Language.LT.lt v ↔ v 0 < v 1 := by simpa [-lt_iff_lt] using! lt_iff_lt (L := L) (v := v)

@[simp] lemma mem_lang [L.Mem] [Membership M M] [Tarski.Structure.Mem L M] {v : Fin 2 → M} :
    Tarski.Structure.rel (L := L) Language.Mem.mem v ↔ v 0 ∈ v 1 := by simpa [-mem_iff_mem] using! mem_iff_mem (L := L) (v := v)

lemma operator_val_ofEquiv_iff (φ : M ≃ N) {k : ℕ} {o : Semiformula.Operator L k} {v : Fin k → N} :
    letI : Tarski.Structure L N := ofEquiv φ
    o.val v ↔ o.val (φ.symm ∘ v) := by simp [Semiformula.Operator.val, eval_ofEquiv_iff, Empty.eq_elim]

end Tarski.Structure

namespace Semiformula

variable {M : Type*} {s : Tarski.Structure L M}

variable {e : Fin n → M} {f : ξ → M} {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}

@[simp] lemma eval_ballLT [Operator.LT L] [LT M] [Tarski.Structure.LT L M] :
    (φ.ballLT t).Eval e f ↔ ∀ x < t.val e f, φ.Eval (x :> e) f := by simp [ballLT]

@[simp] lemma eval_bexsLT [Operator.LT L] [LT M] [Tarski.Structure.LT L M] :
    (φ.bexsLT t).Eval e f ↔ ∃ x < t.val e f, φ.Eval (x :> e) f := by simp [bexsLT]

@[simp] lemma eval_ballLE [Operator.LE L] [LE M] [Tarski.Structure.LE L M] :
    (φ.ballLE t).Eval e f ↔ ∀ x ≤ t.val e f, φ.Eval (x :> e) f := by simp [ballLE]

@[simp] lemma eval_bexsLE [Operator.LE L] [LE M] [Tarski.Structure.LE L M] :
    (φ.bexsLE t).Eval e f ↔ ∃ x ≤ t.val e f, φ.Eval (x :> e) f := by simp [bexsLE]

@[simp] lemma eval_ballMem [Operator.Mem L] [Membership M M] [Tarski.Structure.Mem L M] :
    (φ.ballMem t).Eval e f ↔ ∀ x ∈ t.val e f, φ.Eval (x :> e) f := by simp [ballMem]

@[simp] lemma eval_bexsMem [Operator.Mem L] [Membership M M] [Tarski.Structure.Mem L M] :
    (φ.bexsMem t).Eval e f ↔ ∃ x ∈ t.val e f, φ.Eval (x :> e) f := by simp [bexsMem]

end Semiformula

end FirstOrder

end FFL

end
