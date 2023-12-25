import Logic.FirstOrder.Basic.Semantics.Semantics

namespace LO

namespace FirstOrder

variable {L : Language}

namespace Semiterm

structure Operator (L : Language) (n : ℕ) where
  term : Semiterm L Empty n

abbrev Const (L : Language.{u}) := Operator L 0

def Semiterm.fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩

namespace Operator

def equiv : Operator L n ≃ Semiterm L Empty n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L μ n) : Semiterm L μ n :=
  Rew.substs v (Rew.emb o.term)

def const (c : Const L) : Semiterm L μ n := c.operator ![]

instance : Coe (Const L) (Semiterm L μ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l) (v : Fin l → Semiterm L μ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp[operator, comp, ←Rew.comp_app]; congr 1
    ext <;> simp[Rew.comp_app]; contradiction

def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L μ n) : (bvar x).operator v = v x := by
  simp[operator, bvar]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]

@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl

@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k) (os : List (Operator L k))
  (v : Fin k → Semiterm L μ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp[foldr, operator_comp, Matrix.fun_eq_vec₂]

def iterr (f : Operator L 2) (z : Const L) : (n : ℕ) → Operator L n
  | 0     => z
  | _ + 1 => f.foldr (bvar 0) (List.ofFn fun x => bvar x.succ)

@[simp] lemma iterr_zero (f : Operator L 2) (z : Const L) : f.iterr z 0 = z := rfl

section numeral

protected class Zero (L : Language) where
  zero : Semiterm.Const L

protected class One (L : Language) where
  one : Semiterm.Const L

protected class Add (L : Language) where
  add : Semiterm.Operator L 2

protected class Mul (L : Language) where
  mul : Semiterm.Operator L 2

protected class Sub (L : Language) where
  sub : Semiterm.Operator L 2

protected class Div (L : Language) where
  div : Semiterm.Operator L 2

protected class Star (L : Language) where
  star : Semiterm.Const L

instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩

instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩

instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩

instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩

instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma Zero.term_eq [L.Zero] : (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] := rfl

lemma One.term_eq [L.One] : (@One.one L _).term = Semiterm.func Language.One.one ![] := rfl

lemma Add.term_eq [L.Add] : (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar := rfl

lemma Mul.term_eq [L.Mul] : (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

lemma Star.term_eq [L.Star] : (@Star.star L _).term = Semiterm.func Language.Star.star ![] := rfl

open Language Semiterm

def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)

variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) : numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  simp[numeral]
  cases' z with z
  · simp at hz
  · simp[Operator.foldr]

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)

abbrev godelNumber (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Primcodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)

end numeral

end Operator

def Operator.val {M : Type w} [s : Structure L M] (o : Operator L k) (v : Fin k → M) : M :=
  Semiterm.val s v Empty.elim o.term

variable {M : Type w} {s : Structure L M}

lemma val_operator {k} (o : Operator L k) (v) :
    val s e ε (o.operator v) = o.val (fun x => (v x).val s e ε) := by
  simp[Operator.operator, val_substs]; congr; funext x; contradiction

@[simp] lemma val_const (o : Const L) :
    val s e ε o.const = o.val ![] := by
  simp[Operator.const, val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₀ (o : Const L) :
    val s e ε (o.operator v) = o.val ![] := by
  simp[val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₁ (o : Operator L 1) :
    val s e ε (o.operator ![t]) = o.val ![t.val s e ε] := by
  simp[val_operator, Matrix.empty_eq]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_operator₂ (o : Operator L 2) (t u) :
    val s e ε (o.operator ![t, u]) = o.val ![t.val s e ε, u.val s e ε] :=
  by simp[val_operator]; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma Operator.val_comp (o₁ : Operator L k) (o₂ : Fin k → Operator L m) (v : Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (fun i => (o₂ i).val v) := by simp[comp, val, val_operator]

end Semiterm

namespace Semiformula

structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Semisentence L n

abbrev Const (L : Language.{u}) := Operator L 0

namespace Operator

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L μ n) : Semiformula L μ n :=
  (Rew.substs v).hom (Rew.emb.hom o.sentence)

def const (c : Const L) : Semiformula L μ n := c.operator ![]

instance : Coe (Const L) (Semiformula L μ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) (v : Fin l → Semiterm L μ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp[operator, comp, ←Rew.hom_comp_app]; congr 2
    ext <;> simp[Rew.comp_app]
    · congr
    · contradiction

def and {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋏ o₂.sentence⟩

def or {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋎ o₂.sentence⟩

@[simp] lemma operator_and (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L μ n) :
  (o₁.and o₂).operator v = o₁.operator v ⋏ o₂.operator v := by simp[operator, and]

@[simp] lemma operator_or (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L μ n) :
  (o₁.or o₂).operator v = o₁.operator v ⋎ o₂.operator v := by simp[operator, or]

protected class Eq (L : Language) where
  eq : Semiformula.Operator L 2

protected class LT (L : Language) where
  lt : Semiformula.Operator L 2

protected class LE (L : Language) where
  le : Semiformula.Operator L 2

protected class Mem (L : Language) where
  mem : Semiformula.Operator L 2

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩

instance [Language.LT L] : Operator.LT L := ⟨⟨Semiformula.rel Language.LT.lt Semiterm.bvar⟩⟩

instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma Eq.sentence_eq [L.Eq] : (@Operator.Eq.eq L _).sentence = Semiformula.rel Language.Eq.eq Semiterm.bvar := rfl

lemma LT.sentence_eq [L.LT] : (@Operator.LT.lt L _).sentence = Semiformula.rel Language.LT.lt Semiterm.bvar := rfl

lemma LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl

end Operator

def Operator.val {M : Type w} [s : Structure L M] {k} (o : Operator L k) (v : Fin k → M) : Prop :=
  Semiformula.Eval s v Empty.elim o.sentence

variable {M : Type w} {s : Structure L M}

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp[Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp[Operator.or, Operator.val]

lemma eval_operator {k} {o : Operator L k} {v : Fin k → Semiterm L μ n} :
    Eval s e ε (o.operator v) ↔ o.val (fun i => (v i).val s e ε) := by
  simp[Operator.operator, eval_substs, Operator.val]

@[simp] lemma eval_operator₀ {o : Const L} {v} :
    Eval s e ε (o.operator v) ↔ o.val (M := M) ![] := by
  simp[eval_operator, Matrix.empty_eq]

@[simp] lemma eval_operator₁ {o : Operator L 1} {t : Semiterm L μ n} :
    Eval s e ε (o.operator ![t]) ↔ o.val ![t.val s e ε] := by
  simp[eval_operator, Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₂ {o : Operator L 2} {t₁ t₂ : Semiterm L μ n} :
    Eval s e ε (o.operator ![t₁, t₂]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_operator]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

end Semiformula

namespace Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

protected lemma operator (o : Semiterm.Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp[Semiterm.Operator.operator, ←comp_app]; congr 1
  ext <;> simp[comp_app]; try contradiction

protected lemma operator' (o : Semiterm.Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v

@[simp] lemma finitary0 (o : Semiterm.Operator L 0) (v : Fin 0 → Semiterm L μ₁ n₁) :
    ω (o.operator v) = o.operator ![] := by simp[ω.operator', Matrix.empty_eq]

@[simp] lemma finitary1 (o : Semiterm.Operator L 1) (t : Semiterm L μ₁ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp[ω.operator']

@[simp] lemma finitary2 (o : Semiterm.Operator L 2) (t₁ t₂ : Semiterm L μ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp[ω.operator']

@[simp] lemma finitary3 (o : Semiterm.Operator L 3) (t₁ t₂ t₃ : Semiterm L μ₁ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp[ω.operator']

@[simp] protected lemma const (c : Semiterm.Const L) : ω c = c :=
  by simp[Semiterm.Operator.const, Empty.eq_elim]

lemma hom_operator (o : Semiformula.Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp[Semiformula.Operator.operator, ←Rew.hom_comp_app]; congr 2
  ext <;> simp[Rew.comp_app]; contradiction

lemma hom_operator' (o : Semiformula.Operator L k) (v : Fin k → Semiterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator (ω ∘ v) := ω.hom_operator o v

@[simp] lemma hom_finitary0 (o : Semiformula.Operator L 0) (v : Fin 0 → Semiterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator ![] := by simp[ω.hom_operator', Matrix.empty_eq]

@[simp] lemma hom_finitary1 (o : Semiformula.Operator L 1) (t : Semiterm L μ₁ n₁) :
    ω.hom (o.operator ![t]) = o.operator ![ω t] := by simp[ω.hom_operator']

@[simp] lemma hom_finitary2 (o : Semiformula.Operator L 2) (t₁ t₂ : Semiterm L μ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp[ω.hom_operator']

@[simp] lemma hom_finitary3 (o : Semiformula.Operator L 3) (t₁ t₂ t₃ : Semiterm L μ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp[ω.hom_operator']

@[simp] lemma hom_const (o : Semiformula.Const L) : ω.hom (Semiformula.Operator.const c) = Semiformula.Operator.const c := by
  simp[Semiformula.Operator.const, ω.hom_operator']

end Rew

namespace Structure

open Semiterm Semiformula

variable (L) (M : Type*) [Structure L M]

protected class Zero [Operator.Zero L] [Zero M] where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)

protected class One [Operator.One L] [One M] where
  one : (@Operator.One.one L _).val ![] = (1 : M)

protected class Add [Operator.Add L] [Add M] where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b

protected class Mul [Operator.Mul L] [Mul M] where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b

protected class Eq [Operator.Eq L] where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b

protected class LT [Operator.LT L] [LT M] where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b

protected class LE [Operator.LE L] [LE M] where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b

class Mem [Operator.Mem L] [Membership M M] where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b

attribute [simp] Zero.zero One.one Add.add Mul.mul Eq.eq LT.lt LE.le Mem.mem

variable {L}

@[simp] lemma zero_eq_of_lang [L.Zero] [Zero M] [Structure.Zero L M] :
    Structure.func (L := L) Language.Zero.zero ![] = (0 : M) := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.Zero.zero, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Zero.zero (L := L) (M := M)

@[simp] lemma one_eq_of_lang [L.One] [One M] [Structure.One L M] :
    Structure.func (L := L) Language.One.one ![] = (1 : M) := by
  simpa[Semiterm.Operator.val, Semiterm.Operator.One.one, val_func, ←Matrix.fun_eq_vec₂] using
    Structure.One.one (L := L) (M := M)

@[simp] lemma add_eq_of_lang [L.Add] [Add M] [Structure.Add L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Add.add v = v 0 + v 1 := by
  simpa[val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Add.add (L := L) (v 0) (v 1)

@[simp] lemma mul_eq_of_lang [L.Mul] [Mul M] [Structure.Mul L M] {v : Fin 2 → M} :
    Structure.func (L := L) Language.Mul.mul v = v 0 * v 1 := by
  simpa[val_func, ←Matrix.fun_eq_vec₂] using
    Structure.Mul.mul (L := L) (v 0) (v 1)

@[simp] lemma le_iff_of_eq_of_lt [Operator.Eq L] [Operator.LT L] [LT M] [Structure.Eq L M] [Structure.LT L M] {a b : M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp[Operator.LE.def_of_Eq_of_LT]

@[simp] lemma eq_lang [L.Eq] [Structure.Eq L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.Eq.eq v ↔ v 0 = v 1 := by
  simpa[Semiformula.Operator.Eq.sentence_eq, eval_rel, ←Matrix.fun_eq_vec₂] using
    Structure.Eq.eq (L := L) (v 0) (v 1)

@[simp] lemma lt_lang [L.LT] [LT M] [Structure.LT L M] {v : Fin 2 → M} :
    Structure.rel (L := L) Language.LT.lt v ↔ v 0 < v 1 := by
  simpa[Semiformula.Operator.LT.sentence_eq, eval_rel, ←Matrix.fun_eq_vec₂] using
    Structure.LT.lt (L := L) (v 0) (v 1)

lemma operator_val_ofEquiv_iff (φ : M ≃ N) {k : ℕ} {o : Semiformula.Operator L k} {v : Fin k → N} :
    letI : Structure L N := ofEquiv φ
    o.val v ↔ o.val (φ.symm ∘ v) := by simp[Semiformula.Operator.val, eval_ofEquiv_iff, Empty.eq_elim]

end Structure

end FirstOrder

end LO
