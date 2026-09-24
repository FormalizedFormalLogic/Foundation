module

public import Foundation.FirstOrder.Syntax.Classical.Rew

@[expose] public section
set_option autoImplicit true

namespace FFL

namespace FirstOrder

variable {L : Language}

namespace Semiterm

structure Operator (L : Language) (n : ℕ) where
  term : ClosedSemiterm L n

abbrev Const (L : Language.{u}) := Operator L 0

def fn {k} (f : L.Func k) : Operator L k := ⟨Semiterm.func f (#·)⟩

namespace Operator

def equiv : Operator L n ≃ ClosedSemiterm L n where
  toFun := Operator.term
  invFun := Operator.mk
  left_inv := by intro _; simp
  right_inv := by intro _; simp

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) : Semiterm L ξ n :=
  Rew.subst v (Rew.emb o.term)

@[coe] abbrev const (c : Const L) : Semiterm L ξ n := c.operator ![]

instance : Coe (Const L) (Semiterm L ξ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

@[simp] lemma operator_comp (o : Operator L k) (w : Fin k → Operator L l)
  (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x ↦ (w x).operator v) := by
    simp only [operator, comp, Rew.emb_eq_id, Rew.id_app, ← Rew.comp_app]; congr 1
    ext
    · simp [Rew.comp_app]
    · contradiction

def bvar (x : Fin n) : Operator L n := ⟨#x⟩

lemma operator_bvar (x : Fin k) (v : Fin k → Semiterm L ξ n) : (bvar x).operator v = v x := by
  simp [operator, bvar]

lemma bv_operator {k} (o : Operator L k) (v : Fin k → Semiterm L ξ (n + 1)) :
    (o.operator v).bv = .biUnion o.term.bv fun i ↦ (v i).bv  := by
  simp only [operator]
  generalize o.term = s
  induction s
  case bvar => simp
  case fvar => contradiction
  case func => simp [Rew.func, bv_func, Finset.biUnion_biUnion, *]

lemma positive_operator_iff {k} {o : Operator L k} {v : Fin k → Semiterm L ξ (n + 1)} :
    (o.operator v).Positive ↔ ∀ i ∈ o.term.bv, (v i).Positive := by
  simpa [Positive, bv_operator] using ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩

@[simp] lemma positive_const (c : Const L) : (c : Semiterm L ξ (n + 1)).Positive := by
  simp [const, positive_operator_iff]

-- f.operator ![ ... f.operator ![f.operator ![z, t 0], t 1], ... ,t (n-1)]
def foldr (f : Operator L 2) (z : Operator L k) : List (Operator L k) → Operator L k
  | []      => z
  | o :: os => f.comp ![foldr f z os, o]

@[simp] lemma foldr_nil (f : Operator L 2) (z : Operator L k) : f.foldr z [] = z := rfl

@[simp] lemma operator_foldr_cons (f : Operator L 2) (z : Operator L k) (o : Operator L k)
  (os : List (Operator L k))
  (v : Fin k → Semiterm L ξ n) :
    (f.foldr z (o :: os)).operator v = f.operator ![(f.foldr z os).operator v, o.operator v] := by
  simp [foldr, operator_comp, Matrix.fun_eq_vec_two]

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

class GödelNumber (L : Language) (α : Type*) where
  gödelNumber : α → Semiterm.Const L

notation "op(0)" => Zero.zero

notation "op(0)[" L "]" => Zero.zero (L := L)

notation "op(1)" => One.one

notation "op(1)[" L "]" => One.one (L := L)

notation "op(+)" => Add.add

notation "op(+)[" L "]" => Add.add (L := L)

notation "op(*)" => Mul.mul

notation "op(*)[" L "]" => Mul.mul (L := L)

instance [L.Zero] : Operator.Zero L := ⟨⟨Semiterm.func Language.Zero.zero ![]⟩⟩

instance [L.One] : Operator.One L := ⟨⟨Semiterm.func Language.One.one ![]⟩⟩

instance [L.Add] : Operator.Add L := ⟨⟨Semiterm.func Language.Add.add Semiterm.bvar⟩⟩

instance [L.Mul] : Operator.Mul L := ⟨⟨Semiterm.func Language.Mul.mul Semiterm.bvar⟩⟩

instance [L.Exp] : Operator.Exp L := ⟨⟨Semiterm.func Language.Exp.exp Semiterm.bvar⟩⟩

instance [L.Star] : Operator.Star L := ⟨⟨Semiterm.func Language.Star.star ![]⟩⟩

lemma Zero.term_eq [L.Zero] : (@Zero.zero L _).term = Semiterm.func Language.Zero.zero ![] := rfl

lemma One.term_eq [L.One] : (@One.one L _).term = Semiterm.func Language.One.one ![] := rfl

lemma Add.term_eq [L.Add] : (@Add.add L _).term = Semiterm.func Language.Add.add Semiterm.bvar :=
  rfl

lemma Mul.term_eq [L.Mul] : (@Mul.mul L _).term = Semiterm.func Language.Mul.mul Semiterm.bvar :=
  rfl

lemma Exp.term_eq [L.Exp] : (@Exp.exp L _).term = Semiterm.func Language.Exp.exp Semiterm.bvar :=
  rfl

lemma Star.term_eq [L.Star] : (@Star.star L _).term = Semiterm.func Language.Star.star ![] := rfl

open Language Semiterm

def numeral (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L] : ℕ → Const L
  | 0     => Zero.zero
  | n + 1 => Add.add.foldr One.one (List.replicate n One.one)

variable [hz : Operator.Zero L] [ho : Operator.One L] [ha : Operator.Add L]

lemma numeral_zero : numeral L 0 = Zero.zero := by rfl

lemma numeral_one : numeral L 1 = One.one := by rfl

lemma numeral_succ (hz : z ≠ 0) :
    numeral L (z + 1) = Operator.Add.add.comp ![numeral L z, One.one] := by
  simp only [numeral]
  cases z with
  | zero => simp at hz
  | succ z => rfl

lemma numeral_add_two : numeral L (z + 2) = Operator.Add.add.comp ![numeral L (z + 1), One.one] :=
  numeral_succ (by simp)

protected abbrev encode (L : Language) [Operator.Zero L] [Operator.One L] [Operator.Add L]
    {α : Type*} [Encodable α] (a : α) : Semiterm.Const L :=
  Semiterm.Operator.numeral L (Encodable.encode a)

end numeral

@[simp] lemma Add.positive_iff [L.Add] (t u : Semiterm L ξ (n + 1)) :
    (add.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Add.term_eq, bv_func]

@[simp] lemma Mul.positive_iff [L.Mul] (t u : Semiterm L ξ (n + 1)) :
    (mul.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Mul.term_eq, bv_func]

@[simp] lemma Exp.positive_iff [L.Exp] (t : Semiterm L ξ (n + 1)) :
    (exp.operator ![t]).Positive ↔ t.Positive := by
  simp [positive_operator_iff, Exp.term_eq, bv_func]

section npow

def npow (L : Language) [Operator.One L] [Operator.Mul L] (n : ℕ) : Operator L 1 :=
  Operator.Mul.mul.foldr (One.one.comp ![]) (List.replicate n (bvar 0))

variable [Operator.One L] [Operator.Mul L]


lemma npow_zero : npow L 0 = One.one.comp ![] := rfl

lemma npow_succ : npow L (n + 1) = Operator.Mul.mul.comp ![npow L n, bvar 0] := rfl

end npow

@[simp] lemma npow_positive_iff [Operator.One L] [L.Mul] (t : Semiterm L ξ (n + 1)) (k : ℕ) :
    ((Operator.npow L k).operator ![t]).Positive ↔ k = 0 ∨ t.Positive := by
  cases k
  case zero =>
    simp [positive_operator_iff, operator_comp, npow_zero]
  case succ k n =>
    simp [positive_operator_iff, operator_comp, npow_succ, Mul.term_eq,
      bv_func, Fin.forall_fin_iff_zero_and_forall_succ, bvar]
    tauto

namespace GödelNumber

variable {α} [GödelNumber L α]

abbrev gödelNumber' (a : α) : Semiterm L ξ n := const (gödelNumber a)

instance : GödelQuote α (Semiterm L ξ n) := ⟨gödelNumber'⟩

abbrev ofEncodable [Operator.Zero L] [Operator.One L] [Operator.Add L] {α : Type*} [Encodable α] :
    GödelNumber L α := ⟨Operator.encode L⟩

end GödelNumber

end Operator

section complexity

variable {L : Language}

@[simp] lemma complexity_zero [L.Zero] :
    ((Operator.Zero.zero : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.Zero.term_eq, complexity_func]

@[simp] lemma complexity_one [L.One] :
    ((Operator.One.one : Const L) : Semiterm L ξ n).complexity = 1 := by
  simp [Operator.const, Operator.operator, Operator.One.term_eq, complexity_func]

@[simp] lemma complexity_add [L.Add] (t u : Semiterm L ξ n) :
    (Operator.Add.add.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Add.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
    ext i; cases i using Fin.cases <;> simp]

@[simp] lemma complexity_mul [L.Mul] (t u : Semiterm L ξ n) :
    (Operator.Mul.mul.operator ![t, u]).complexity = max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Mul.term_eq, complexity_func, Rew.func]
  simp [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by
    ext i; cases i using Fin.cases <;> simp]

end complexity


end Semiterm

namespace Semiformula

structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Semisentence L n

abbrev Const (L : Language.{u}) := Operator L 0

namespace Operator

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Semiterm L ξ n) :
    Semiformula L ξ n :=
  Rewriting.emb o.sentence ⇜ v

/-- Auxiliary condition for this formalization: rewriting to an application of `o` recovers an
application of `o` whose arguments rewrite to the given ones. -/
class SymbolLike (o : Operator L k) (ξ₁ ξ₂ : Type*) : Prop where
  symbolLike {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula L ξ₁ n₁} {v : Fin k → Semiterm L ξ₂ n₂} :
    ω ▹ φ = o.operator v →
      ∃ w : Fin k → Semiterm L ξ₁ n₁,
        φ = o.operator w ∧ ∀ i, ω (w i) = v i

@[coe] def const (c : Const L) : Semiformula L ξ n := c.operator ![]

instance : Coe (Const L) (Semiformula L ξ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Semiterm.Operator L l)
  (v : Fin l → Semiterm L ξ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    unfold operator Rewriting.emb Rewriting.subst comp
    simp only [operator, ← TransitiveRewriting.comp_app, Rew.emb_eq_id, Rew.comp_id];
    congr 2
    ext
    · simp [Rew.comp_app]; congr
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

notation "op(=)[" L "]" => Operator.Eq.eq (L := L)

notation "op(<)" => Operator.LT.lt

notation "op(<)[" L "]" => Operator.LT.lt (L := L)

notation "op(≤)" => Operator.LE.le

notation "op(≤)[" L "]" => Operator.LE.le (L := L)

notation "op(∈)" => Operator.Mem.mem

notation "op(∈)[" L "]" => Operator.Mem.mem (L := L)

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Semiformula.rel Language.Eq.eq Semiterm.bvar⟩⟩

instance [Language.LT L] : Operator.LT L := ⟨⟨Semiformula.rel Language.LT.lt Semiterm.bvar⟩⟩

instance [L.Mem] : Operator.Mem L := ⟨⟨Semiformula.rel Language.Mem.mem Semiterm.bvar⟩⟩

instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma Eq.sentence_eq [L.Eq] :
    (@Eq.eq L _).sentence = Semiformula.rel Language.Eq.eq Semiterm.bvar := rfl

lemma LT.sentence_eq [L.LT] :
    (@LT.lt L _).sentence = Semiformula.rel Language.LT.lt Semiterm.bvar := rfl

lemma Mem.sentence_eq [L.Mem] :
    (@Mem.mem L _).sentence = Semiformula.rel Language.Mem.mem Semiterm.bvar := rfl

lemma LE.sentence_eq [L.Eq] [L.LT] : (@LE.le L _).sentence = Eq.eq.sentence ⋎ LT.lt.sentence := rfl

lemma LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl

@[simp] lemma Eq.equal_inj [L.Eq] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    Eq.eq.operator ![t₁, u₁] = Eq.eq.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec_two]

@[simp] lemma LT.lt_inj [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LT.lt.operator ![t₁, u₁] = LT.lt.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec_two]

@[simp] lemma Mem.mem_inj [L.Mem] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    Mem.mem.operator ![t₁, u₁] = Mem.mem.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, Mem.sentence_eq, Matrix.fun_eq_vec_two]

@[simp] lemma LE.le_inj [L.Eq] [L.LT] {t₁ t₂ u₁ u₂ : Semiterm L ξ₂ n₂} :
    LE.le.operator ![t₁, u₁] = LE.le.operator ![t₂, u₂] ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [operator, LE.sentence_eq, Eq.sentence_eq, LT.sentence_eq, Matrix.fun_eq_vec_two];


lemma lt_def [L.LT] (t u : Semiterm L ξ n) :
    LT.lt.operator ![t, u] = Semiformula.rel Language.LT.lt ![t, u] := by
  simp [operator, LT.sentence_eq, Matrix.fun_eq_vec_two]

lemma eq_def [L.Eq] (t u : Semiterm L ξ n) :
    Eq.eq.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t, u] := by
  simp [operator, Eq.sentence_eq, Matrix.fun_eq_vec_two]

lemma mem_def [L.Mem] (t u : Semiterm L ξ n) :
    Mem.mem.operator ![t, u] = Semiformula.rel Language.Mem.mem ![t, u] := by
  simp [operator, Mem.sentence_eq, Matrix.fun_eq_vec_two]

lemma le_def [L.Eq] [L.LT] (t u : Semiterm L ξ n) :
    LE.le.operator ![t, u] = Semiformula.rel Language.Eq.eq ![t, u] ⋎
        Semiformula.rel Language.LT.lt ![t, u] := by
  simp [operator, Eq.sentence_eq, LT.sentence_eq, LE.sentence_eq, Matrix.fun_eq_vec_two]

variable {L : Language}

@[simp] lemma Eq.open [L.Eq] (t u : Semiterm L ξ n) : (Eq.eq.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.Eq.sentence_eq]

@[simp] lemma LT.open [L.LT] (t u : Semiterm L ξ n) : (LT.lt.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LT.sentence_eq]

@[simp] lemma Mem.open [L.Mem] (t u : Semiterm L ξ n) : (Mem.mem.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.Mem.sentence_eq]

@[simp] lemma LE.open [L.Eq] [L.LT] (t u : Semiterm L ξ n) : (LE.le.operator ![t, u]).Open := by
  simp [Operator.operator, Operator.LE.sentence_eq, Operator.Eq.sentence_eq,
      Operator.LT.sentence_eq]

end Operator


def ballLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ

def bexsLT [Operator.LT L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃¹[Operator.LT.lt.operator ![#0, Rew.bShift t]] φ

def ballLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀¹[Operator.LE.le.operator ![#0, Rew.bShift t]] φ

def bexsLE [Operator.LE L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃¹[Operator.LE.le.operator ![#0, Rew.bShift t]] φ

def ballMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n := ∀¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

def bexsMem [Operator.Mem L] (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) :
    Semiformula L ξ n := ∃¹[Operator.Mem.mem.operator ![#0, Rew.bShift t]] φ

end Semiformula

namespace Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

protected lemma operator (o : Semiterm.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (o.operator v) = o.operator (fun i ↦ ω (v i)) := by
  simp only [Semiterm.Operator.operator, ← comp_app]; congr 1
  ext
  · simp [comp_app]
  · contradiction

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

@[simp] protected lemma const (c : Semiterm.Const L) : ω c = c := by simp [Semiterm.Operator.const]

lemma hom_operator (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator fun i ↦ ω (v i) := by
  unfold Semiformula.Operator.operator Rewriting.subst Rewriting.emb
  simp only [← TransitiveRewriting.comp_app]; congr 2
  ext
  · simp [Rew.comp_app]
  · contradiction

lemma hom_operator' (o : Semiformula.Operator L k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ o.operator v = o.operator (ω ∘ v) := ω.hom_operator o v

@[simp] lemma hom_finitary0 (o : Semiformula.Operator L 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator v) = o.operator ![] := by simp [ω.hom_operator', Matrix.empty_eq]

@[simp] lemma hom_finitary1 (o : Semiformula.Operator L 1) (t : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t]) = o.operator ![ω t] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary2 (o : Semiformula.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.hom_operator']

@[simp] lemma hom_finitary3 (o : Semiformula.Operator L 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω ▹ (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp [ω.hom_operator']

@[simp] lemma hom_const : ω ▹ (Semiformula.Operator.const c : Semiformula L ξ₁ n₁) =
    Semiformula.Operator.const c := by
  simp [Semiformula.Operator.const, ω.hom_operator']

open Semiformula

lemma eq_equal_iff [L.Eq] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.Eq.eq.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.Eq.eq.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.Eq.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.Eq.eq
    case neg => simp [Operator.operator, Operator.Eq.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.Eq.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.Eq.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.Eq.sentence_eq]

lemma eq_lt_iff [L.LT] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.LT.lt.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.LT.lt.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.LT.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.LT.lt
    case neg => simp [Operator.operator, Operator.LT.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.LT.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.LT.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.LT.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.LT.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.LT.sentence_eq]

lemma eq_mem_iff [L.Mem] {φ : Semiformula L ξ₁ n₁} {t u : Semiterm L ξ₂ n₂} :
    ω ▹ φ = Operator.Mem.mem.operator ![t, u]
    ↔ ∃ t' u', ω t' = t ∧ ω u' = u ∧ φ = Operator.Mem.mem.operator ![t', u'] := by
  match φ with
  | .rel (arity := k') r' v =>
    by_cases hk : k' = 2
    case neg => simp [Operator.operator, Operator.Mem.sentence_eq, hk]
    rcases hk
    by_cases hr : r' = Language.Mem.mem
    case neg => simp [Operator.operator, Operator.Mem.sentence_eq, hr]
    rcases hr
    simp [Operator.operator, Operator.Mem.sentence_eq,
      funext_iff, Fin.forall_fin_iff_zero_and_forall_succ]
  | .nrel _ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |         ⊤ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |         ⊥ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |     _ ⋏ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |     _ ⋎ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |      ∀¹ _ => simp [Operator.operator, Operator.Mem.sentence_eq]
  |      ∃¹ _ => simp [Operator.operator, Operator.Mem.sentence_eq]

end Rew

namespace Semiformula.Operator

instance symbolLikeEq [L.Eq] (ξ₁ ξ₂ : Type*) :
    (Eq.eq : Operator L 2).SymbolLike ξ₁ ξ₂ where
  symbolLike := by
    intro n₁ n₂ ω φ v h;
    rw [Matrix.fun_eq_vec_two v] at h;
    obtain ⟨t, u, ht, hu, hφ⟩ := (Rew.eq_equal_iff (ω := ω)).mp h;
    exact ⟨![t, u], hφ, by rw [Matrix.fun_eq_vec_two v]; simp [ht, hu]⟩;

instance symbolLikeLT [L.LT] (ξ₁ ξ₂ : Type*) :
    (LT.lt : Operator L 2).SymbolLike ξ₁ ξ₂ where
  symbolLike := by
    intro n₁ n₂ ω φ v h;
    rw [Matrix.fun_eq_vec_two v] at h;
    obtain ⟨t, u, ht, hu, hφ⟩ := (Rew.eq_lt_iff (ω := ω)).mp h;
    exact ⟨![t, u], hφ, by rw [Matrix.fun_eq_vec_two v]; simp [ht, hu]⟩;

instance symbolLikeMem [L.Mem] (ξ₁ ξ₂ : Type*) :
    (Mem.mem : Operator L 2).SymbolLike ξ₁ ξ₂ where
  symbolLike := by
    intro n₁ n₂ ω φ v h;
    rw [Matrix.fun_eq_vec_two v] at h;
    obtain ⟨t, u, ht, hu, hφ⟩ := (Rew.eq_mem_iff (ω := ω)).mp h;
    exact ⟨![t, u], hφ, by rw [Matrix.fun_eq_vec_two v]; simp [ht, hu]⟩;

end Semiformula.Operator

namespace Semiterm

variable [L.Zero] [L.One] [L.Add]

@[coe] abbrev numeral (k : ℕ) : Semiterm L ξ n := Operator.numeral L k

instance : Coe ℕ (Semiterm L ξ n) := ⟨numeral⟩

end Semiterm

end FirstOrder

end FFL

end
