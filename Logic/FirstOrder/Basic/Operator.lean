import Logic.FirstOrder.Basic.Semantics.Semantics
import Logic.Vorspiel.NotationClass

namespace LO

namespace FirstOrder

variable {L : Language}

namespace Semiterm

structure Operator (L : Language) (n : ℕ) where
  term : Semiterm L Empty n

abbrev Const (L : Language.{u}) := Operator L 0

def fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩

namespace Operator

def equiv : Operator L n ≃ Semiterm L Empty n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiterm L ξ n :=
  Rew.substs v (Rew.emb o.term)

abbrev const (c : Const L) : Semiterm L ξ n := c.operator ![]

instance : Coe (Const L) (Semiterm L ξ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

@[simp] lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l) (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp [operator, comp, ←Rew.comp_app]; congr 1
    ext <;> simp [Rew.comp_app]; contradiction

def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L ξ n) : (bvar x).operator v = v x := by
  simp [operator, bvar]

lemma bv_operator {k} (o : Operator L k) (v : Fin k → Semiterm L ξ (n + 1)) :
    (o.operator v).bv = .biUnion o.term.bv fun i ↦ (v i).bv  := by
  simp [operator]
  generalize o.term = s
  induction s <;> try simp [Rew.func, bv_func, Finset.biUnion_biUnion, *]
  case fvar => contradiction

lemma positive_operator_iff {k} {o : Operator L k} {v : Fin k → Semiterm L ξ (n + 1)} :
    (o.operator v).Positive ↔ ∀ i ∈ o.term.bv, (v i).Positive := by
  simp [Positive, bv_operator]
  exact ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩

@[simp] lemma positive_const (c : Const L) : (c : Semiterm L ξ (n + 1)).Positive := by simp [const, positive_operator_iff]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]

@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl

@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k) (os : List (Operator L k))
  (v : Fin k → Semiterm L ξ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp [foldr, operator_comp, Matrix.fun_eq_vec₂]

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

protected class Exp (L : Language) where
  exp : Semiterm.Operator L 1

protected class Sub (L : Language) where
  sub : Semiterm.Operator L 2

protected class Div (L : Language) where
  div : Semiterm.Operator L 2

protected class Star (L : Language) where
  star : Semiterm.Const L

class GoedelNumber (L : Language) (α : Type*) where
  goedelNumber : α → Semiterm.Const L

notation "op(0)" => Zero.zero

notation "op(1)" => One.one

notation "op(+)" => Add.add

notation "op(*)" => Mul.mul

instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩

instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩

instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩

instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩

instance [L.Exp] : Operator.Exp L := ⟨⟨Semiterm.func Language.Exp.exp Semiterm.bvar⟩⟩

instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma Zero.term_eq [L.Zero] : (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] := rfl

lemma One.term_eq [L.One] : (@One.one L _).term = Semiterm.func Language.One.one ![] := rfl

lemma Add.term_eq [L.Add] : (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar := rfl

lemma Mul.term_eq [L.Mul] : (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

lemma Exp.term_eq [L.Exp] : (@Exp.exp L _).term = Semiterm.func Language.Exp.exp Semiterm.bvar := rfl

lemma Star.term_eq [L.Star] : (@Star.star L _).term = Semiterm.func Language.Star.star ![] := rfl

open Language Semiterm

def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)

variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) : numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  simp [numeral]
  cases' z with z
  · simp at hz
  · simp [Operator.foldr]

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)

protected abbrev encode (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Primcodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)

end numeral

@[simp] lemma Add.positive_iff [L.Add] (t u : Semiterm L ξ (n + 1)) :
    (Operator.Add.add.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Add.term_eq, bv_func]
  exact ⟨by intro h; exact ⟨h 0, h 1⟩,
    by intro h i; cases i using Fin.cases <;> simp [Fin.eq_zero, *]⟩

@[simp] lemma Mul.positive_iff [L.Mul] (t u : Semiterm L ξ (n + 1)) :
    (Operator.Mul.mul.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Mul.term_eq, bv_func]
  exact ⟨by intro h; exact ⟨h 0, h 1⟩,
    by intro h i; cases i using Fin.cases <;> simp [Fin.eq_zero, *]⟩

@[simp] lemma Exp.positive_iff [L.Exp] (t : Semiterm L ξ (n + 1)) :
    (Operator.Exp.exp.operator ![t]).Positive ↔ t.Positive := by
  simp [positive_operator_iff, Exp.term_eq, bv_func]

section npow

def npow (L : Language) [Operator.One L] [Operator.Mul L] (n : ℕ) : Operator L 1 :=
  Operator.Mul.mul.foldr (One.one.comp ![]) (List.replicate n (bvar 0))

variable [Operator.One L] [Operator.Mul L]


lemma npow_zero : npow L 0 = One.one.comp ![] := rfl

lemma npow_succ : npow L (n + 1) = Operator.Mul.mul.comp ![npow L n, bvar 0] := by simp [npow, foldr]

end npow

@[simp] lemma npow_positive_iff [Operator.One L] [L.Mul] (t : Semiterm L ξ (n + 1)) (k : ℕ) :
    ((Operator.npow L k).operator ![t]).Positive ↔ k = 0 ∨ t.Positive := by
  cases k <;> simp [positive_operator_iff, operator_comp, npow_zero, npow_succ]
  case succ k _ =>
    simp [Mul.term_eq, bv_func]
    constructor
    · intro h; exact h 1 0 (by simp [bvar])
    · intro h _ _ _
      exact h

namespace GoedelNumber

variable {α} [GoedelNumber L α]

abbrev goedelNumber' (a : α) : Semiterm L ξ n := const (goedelNumber a)

instance : GoedelQuote α (Semiterm L ξ n) := ⟨goedelNumber'⟩

def ofEncodable
    [Operator.Zero L] [Operator.One L] [Operator.Add L] {α : Type*} [Primcodable α] : GoedelNumber L α := ⟨Operator.encode L⟩

end GoedelNumber

end Operator

section complexity

variable {L : Language} [L.Zero] [L.One] [L.Add] [L.Mul]

@[simp] lemma complexity_zero : ((Operator.Zero.zero : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Zero.term_eq, complexity_func]

@[simp] lemma complexity_one : ((Operator.One.one : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.One.term_eq, complexity_func]

@[simp] lemma complexity_add (t u : Semiterm L ξ n) :
    (Operator.Add.add.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Add.term_eq, complexity_func, Rew.func]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]
  simp [sup_eq_max]

@[simp] lemma complexity_mul (t u : Semiterm L ξ n) :
    (Operator.Mul.mul.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.const, Operator.operator, Operator.numeral, Operator.Mul.term_eq, complexity_func, Rew.func]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by ext i; cases i using Fin.cases <;> simp [Fin.eq_zero]]
  simp [sup_eq_max]

end complexity

section semantics

def Operator.val {M : Type w} [s : Structure L M] (o : Operator L k) (v : Fin k → M) : M :=
  Semiterm.val s v Empty.elim o.term

variable {M : Type w} {s : Structure L M}

lemma val_operator {k} (o : Operator L k) (v) :
    val s e ε (o.operator v) = o.val (fun x => (v x).val s e ε) := by
  simp [Operator.operator, val_substs]; congr; funext x; contradiction

@[simp] lemma val_const (o : Const L) :
    val s e ε o.const = o.val ![] := by
  simp [Operator.const, val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₀ (o : Const L) :
    val s e ε (o.operator v) = o.val ![] := by
  simp [val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₁ (o : Operator L 1) :
    val s e ε (o.operator ![t]) = o.val ![t.val s e ε] := by
  simp [val_operator, Matrix.empty_eq]; congr; funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma val_operator₂ (o : Operator L 2) (t u) :
    val s e ε (o.operator ![t, u]) = o.val ![t.val s e ε, u.val s e ε] :=
  by simp [val_operator]; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma Operator.val_comp (o₁ : Operator L k) (o₂ : Fin k → Operator L m) (v : Fin m → M) :
  (o₁.comp o₂).val v = o₁.val (fun i => (o₂ i).val v) := by simp [comp, val, val_operator]

@[simp] lemma Operator.val_bvar {n} (x : Fin n) (v : Fin n → M) :
    (Operator.bvar (L := L) x).val v = v x := by simp [Operator.bvar, Operator.val]

end semantics

end Semiterm

namespace Semiformula

structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Semisentence L n

abbrev Const (L : Language.{u}) := Operator L 0

namespace Operator

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiformula L ξ n :=
  (Rew.substs v).hom (Rew.emb.hom o.sentence)

def const (c : Const L) : Semiformula L ξ n := c.operator ![]

instance : Coe (Const L) (Semiformula L ξ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp [operator, comp, ←Rew.hom_comp_app]; congr 2
    ext <;> simp [Rew.comp_app]
    · congr
    · contradiction

def and {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋏ o₂.sentence⟩

def or {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋎ o₂.sentence⟩

@[simp] lemma operator_and (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.and o₂).operator v = o₁.operator v ⋏ o₂.operator v := by simp [operator, and]

@[simp] lemma operator_or (o₁ o₂ : Operator L k) (v : Fin k → Semiterm L ξ n) :
  (o₁.or o₂).operator v = o₁.operator v ⋎ o₂.operator v := by simp [operator, or]

protected class Eq (L : Language) where
  eq : Semiformula.Operator L 2

protected class LT (L : Language) where
  lt : Semiformula.Operator L 2

protected class LE (L : Language) where
  le : Semiformula.Operator L 2

protected class Mem (L : Language) where
  mem : Semiformula.Operator L 2

notation "op(=)" => Operator.Eq.eq

notation "op(<)" => Operator.LT.lt

notation "op(≤)" => Operator.LE.le

notation "op(∈)" => Operator.Mem.mem

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩

instance [Language.LT L] : Operator.LT L := ⟨⟨Semiformula.rel Language.LT.lt Semiterm.bvar⟩⟩

instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma Eq.sentence_eq [L.Eq] : (@Eq.eq L _).sentence = Semiformula.rel Language.Eq.eq Semiterm.bvar := rfl

lemma LT.sentence_eq [L.LT] : (@LT.lt L _).sentence = Semiformula.rel Language.LT.lt Semiterm.bvar := rfl

lemma LE.sentence_eq [L.Eq] [L.LT] : (@LE.le L _).sentence = Eq.eq.sentence ⋎ LT.lt.sentence := rfl

lemma LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl

@[simp] lemma Eq.equal_inj [L.Eq] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    Eq.eq.operator ![t₁, u₁] = Eq.eq.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec₂]

@[simp] lemma LT.lt_inj [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LT.lt.operator ![t₁, u₁] = LT.lt.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec₂]

@[simp] lemma LE.le_inj [L.Eq] [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LE.le.operator ![t₁, u₁] = LE.le.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LE.sentence_eq, Eq.sentence_eq, LT.sentence_eq, Matrix.fun_eq_vec₂]

variable {L : Language} [L.Eq] [L.LT]

@[simp] lemma Eq.open (t u : Semiterm L ξ n) : (Eq.eq.operator ![t, u]).Open := by simp [Operator.operator, Operator.Eq.sentence_eq]

@[simp] lemma LT.open (t u : Semiterm L ξ n) : (LT.lt.operator ![t, u]).Open := by simp [Operator.operator, Operator.LT.sentence_eq]

@[simp] lemma LE.open (t u : Semiterm L ξ n) : (LE.le.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LE.sentence_eq, Operator.Eq.sentence_eq, Operator.LT.sentence_eq]

end Operator

def Operator.val {M : Type w} [s : Structure L M] {k} (o : Operator L k) (v : Fin k → M) : Prop :=
  Semiformula.Eval s v Empty.elim o.sentence

section

variable {M : Type w} {s : Structure L M}

@[simp] lemma val_operator_and {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.and o₂).val v ↔ o₁.val v ∧ o₂.val v := by simp [Operator.and, Operator.val]

@[simp] lemma val_operator_or {k} {o₁ o₂ : Operator L k} {v : Fin k → M} :
    (o₁.or o₂).val v ↔ o₁.val v ∨ o₂.val v := by simp [Operator.or, Operator.val]

lemma eval_operator {k} {o : Operator L k} {v : Fin k → Semiterm L ξ n} :
    Eval s e ε (o.operator v) ↔ o.val (fun i => (v i).val s e ε) := by
  simp [Operator.operator, eval_substs, Operator.val]

@[simp] lemma eval_operator₀ {o : Const L} {v} :
    Eval s e ε (o.operator v) ↔ o.val (M := M) ![] := by
  simp [eval_operator, Matrix.empty_eq]

@[simp] lemma eval_operator₁ {o : Operator L 1} {t : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t]) ↔ o.val ![t.val s e ε] := by
  simp [eval_operator, Matrix.constant_eq_singleton]

@[simp] lemma eval_operator₂ {o : Operator L 2} {t₁ t₂ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε] := by
  simp [eval_operator]; apply of_eq; congr; funext i; cases' i using Fin.cases with i <;> simp

end

def ballLT [Operator.LT L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀[Operator.LT.lt.operator ![#0, Rew.bShift t]] p

def bexLT [Operator.LT L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃[Operator.LT.lt.operator ![#0, Rew.bShift t]] p

def ballLE [Operator.LE L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀[Operator.LE.le.operator ![#0, Rew.bShift t]] p

def bexLE [Operator.LE L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃[Operator.LE.le.operator ![#0, Rew.bShift t]] p

def ballMem [Operator.Mem L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∀[Operator.Mem.mem.operator ![#0, Rew.bShift t]] p

def bexMem [Operator.Mem L] (t : Semiterm L ξ n) (p : Semiformula L ξ (n + 1)) : Semiformula L ξ n := ∃[Operator.Mem.mem.operator ![#0, Rew.bShift t]] p

end Semiformula

namespace Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ ξ' : Type v} {ξ₁ : Type v₁} {ξ₂ : Type v₂} {ξ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

protected lemma operator (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp [Semiterm.Operator.operator, ←comp_app]; congr 1
  ext <;> simp [comp_app]; try contradiction

protected lemma operator' (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (ω ∘ v) := ω.operator o v

@[simp] lemma finitary0 (o : Semiterm.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator ![] := by simp [ω.operator', Matrix.empty_eq]

@[simp] lemma finitary1 (o : Semiterm.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t]) = o.operator ![ω t] := by simp [ω.operator']

@[simp] lemma finitary2 (o : Semiterm.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.operator']

@[simp] lemma finitary3 (o : Semiterm.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.operator']

@[simp] protected lemma const (c : Semiterm.Const L) : ω c = c :=
  by simp [Semiterm.Operator.const, Empty.eq_elim]

lemma hom_operator (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω.hom (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp [Semiformula.Operator.operator, ←Rew.hom_comp_app]; congr 2
  ext <;> simp [Rew.comp_app]; contradiction

lemma hom_operator' (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω.hom (o.operator v) = o.operator (ω ∘ v) := ω.hom_operator o v

@[simp] lemma hom_finitary0 (o : Semiformula.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω.hom (o.operator v) = o.operator ![] := by simp [ω.hom_operator', Matrix.empty_eq]

@[simp] lemma hom_finitary1 (o : Semiformula.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω.hom (o.operator ![t]) = o.operator ![ω t] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary2 (o : Semiformula.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary3 (o : Semiformula.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.hom_operator']

@[simp] lemma hom_const : ω.hom (Semiformula.Operator.const c) = Semiformula.Operator.const c := by
  simp [Semiformula.Operator.const, ω.hom_operator']

open Semiformula

lemma eq_equal_iff [L.Eq] {p} {t u : Semiterm L ξ₂ n₂} :
    ω.hom p = Operator.Eq.eq.operator ![t, u] ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ p = Operator.Eq.eq.operator ![t', u'] := by
  cases p using Semiformula.rec' <;> simp [Rew.rel, Rew.nrel, Operator.operator, Operator.Eq.sentence_eq]
  case hrel k' r' v =>
    by_cases hk : k' = 2 <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = Language.Eq.eq <;> simp [hr, Function.funext_iff]
    constructor
    · rintro H; exact ⟨v 0, H 0, v 1, H 1, by intro i; cases i using Fin.cases <;> simp [Fin.eq_zero]⟩
    · rintro ⟨t', rfl, u', rfl, H⟩; intro i; cases i using Fin.cases <;> simp [H, Fin.eq_zero]

lemma eq_lt_iff [L.LT] {p} {t u : Semiterm L ξ₂ n₂} :
    ω.hom p = Operator.LT.lt.operator ![t, u] ↔
    ∃ t' u', ω t' = t ∧ ω u' = u ∧ p = Operator.LT.lt.operator ![t', u'] := by
  cases p using Semiformula.rec' <;> simp [Rew.rel, Rew.nrel, Operator.operator, Operator.LT.sentence_eq]
  case hrel k' r' v =>
    by_cases hk : k' = 2 <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = Language.LT.lt <;> simp [hr, Function.funext_iff]
    constructor
    · rintro H; exact ⟨v 0, H 0, v 1, H 1, by intro i; cases i using Fin.cases <;> simp [Fin.eq_zero]⟩
    · rintro ⟨t', rfl, u', rfl, H⟩; intro i; cases i using Fin.cases <;> simp [H, Fin.eq_zero]

end Rew

namespace Structure

open Semiterm Semiformula

variable (L) (M : Type*) [Structure L M]

protected class Zero [Operator.Zero L] [Zero M] : Prop where
  zero : (@Operator.Zero.zero L _).val ![] = (0 : M)

protected class One [Operator.One L] [One M] : Prop where
  one : (@Operator.One.one L _).val ![] = (1 : M)

protected class Add [Operator.Add L] [Add M] : Prop where
  add : ∀ a b : M, (@Operator.Add.add L _).val ![a, b] = a + b

protected class Mul [Operator.Mul L] [Mul M] : Prop where
  mul : ∀ a b : M, (@Operator.Mul.mul L _).val ![a, b] = a * b

protected class Exp [Operator.Exp L] [Exp M] : Prop where
  exp : ∀ a : M, (@Operator.Exp.exp L _).val ![a] = exp a

protected class Eq [Operator.Eq L] : Prop where
  eq : ∀ a b : M, (@Operator.Eq.eq L _).val ![a, b] ↔ a = b

protected class LT [Operator.LT L] [LT M] : Prop where
  lt : ∀ a b : M, (@Operator.LT.lt L _).val ![a, b] ↔ a < b

protected class LE [Operator.LE L] [LE M] : Prop where
  le : ∀ a b : M, (@Operator.LE.le L _).val ![a, b] ↔ a ≤ b

class Mem [Operator.Mem L] [Membership M M] : Prop where
  mem : ∀ a b : M, (@Operator.Mem.mem L _).val ![a, b] ↔ a ∈ b

attribute [simp] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt LE.le Mem.mem

instance [L.Eq] [L.LT] [Structure.Eq L M] [PartialOrder M] [Structure.LT L M] :
  Structure.LE L M := ⟨by intro a b; simp [Operator.LE.def_of_Eq_of_LT]; exact le_iff_eq_or_lt.symm⟩

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

@[simp] lemma exp_eq_of_lang [L.Exp] [Exp M] [Structure.Exp L M] {v : Fin 1 → M} :
    Structure.func (L := L) Language.Exp.exp v = exp (v 0) := by
  simpa[val_func, ←Matrix.constant_eq_singleton'] using
    Structure.Exp.exp (L := L) (v 0)

lemma le_iff_of_eq_of_lt [Operator.Eq L] [Operator.LT L] [LT M] [Structure.Eq L M] [Structure.LT L M] {a b : M} :
    (@Operator.LE.le L _).val ![a, b] ↔ a = b ∨ a < b := by
  simp [Operator.LE.def_of_Eq_of_LT]

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
    o.val v ↔ o.val (φ.symm ∘ v) := by simp [Semiformula.Operator.val, eval_ofEquiv_iff, Empty.eq_elim]

end Structure

namespace Semiformula

variable {M : Type*} {s : Structure L M}

variable {t : Semiterm L ξ n} {p : Semiformula L ξ (n + 1)}

@[simp] lemma eval_ballLT [Operator.LT L] [LT M] [Structure.LT L M] {e ε} :
    Eval s e ε (p.ballLT t) ↔ ∀ x < t.val s e ε, Eval s (x :> e) ε p := by simp [ballLT]

@[simp] lemma eval_bexLT [Operator.LT L] [LT M] [Structure.LT L M] {e ε} :
    Eval s e ε (p.bexLT t) ↔ ∃ x < t.val s e ε, Eval s (x :> e) ε p := by simp [bexLT]

@[simp] lemma eval_ballLE [Operator.LE L] [LE M] [Structure.LE L M] {e ε} :
    Eval s e ε (p.ballLE t) ↔ ∀ x ≤ t.val s e ε, Eval s (x :> e) ε p := by simp [ballLE]

@[simp] lemma eval_bexLE [Operator.LE L] [LE M] [Structure.LE L M] {e ε} :
    Eval s e ε (p.bexLE t) ↔ ∃ x ≤ t.val s e ε, Eval s (x :> e) ε p := by simp [bexLE]

@[simp] lemma eval_ballMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] {e ε} :
    Eval s e ε (p.ballMem t) ↔ ∀ x ∈ t.val s e ε, Eval s (x :> e) ε p := by simp [ballMem]

@[simp] lemma eval_bexMem [Operator.Mem L] [Membership M M] [Structure.Mem L M] {e ε} :
    Eval s e ε (p.bexMem t) ↔ ∃ x ∈ t.val s e ε, Eval s (x :> e) ε p := by simp [bexMem]

end Semiformula

end FirstOrder

end LO
