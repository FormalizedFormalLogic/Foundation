import Arithmetization.ISigmaOne.Metamath.Term.Typed
import Arithmetization.ISigmaOne.Metamath.Formula.Iteration

/-!

# Typed Formalized Semiformula/Formula

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

lemma sub_succ_lt_self {a b : V} (h : b < a) : a - (b + 1) < a := by
  simp [tsub_lt_iff_left (succ_le_iff_lt.mpr h)]

lemma sub_succ_lt_selfs {a b : V} (h : b < a) : a - (a - (b + 1) + 1) = b := by
  rw [←sub_sub]
  apply sub_remove_left
  apply sub_remove_left
  rw [←add_sub_of_le (succ_le_iff_lt.mpr h)]
  simp

section typed_formula

variable (L)

structure Language.TSemiformula (n : V) where
  val : V
  prop : L.Semiformula n val

attribute [simp] Language.TSemiformula.prop

abbrev Language.TFormula := L.TSemiformula 0

variable {L}

def Language.imp (n p q : V) : V := L.neg p ^⋎[n] q

@[simp] lemma Language.Semiformula.imp {n p q : V} :
    L.Semiformula n (L.imp n p q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by
  simp [Language.imp]

scoped instance : LogicalConnective (L.TSemiformula n) where
  top := ⟨^⊤[n], by simp⟩
  bot := ⟨^⊥[n], by simp⟩
  wedge (p q) := ⟨p.val ^⋏[n] q.val, by simp⟩
  vee (p q) := ⟨p.val ^⋎[n] q.val, by simp⟩
  tilde (p) := ⟨L.neg p.val, by simp⟩
  arrow (p q) := ⟨L.imp n p.val q.val, by simp⟩

def Language.TSemiformula.cast (p : L.TSemiformula n) (eq : n = n' := by simp) : L.TSemiformula n' := eq ▸ p

@[simp] lemma Language.TSemiformula.val_cast (p : L.TSemiformula n) (eq : n = n') :
    (p.cast eq).val = p.val := by rcases eq; simp [Language.TSemiformula.cast]

def Language.TSemiformula.all (p : L.TSemiformula (n + 1)) : L.TSemiformula n := ⟨^∀[n] p.val, by simp⟩

def Language.TSemiformula.ex (p : L.TSemiformula (n + 1)) : L.TSemiformula n := ⟨^∃[n] p.val, by simp⟩

namespace Language.TSemiformula

@[simp] lemma val_verum : (⊤ : L.TSemiformula n).val = ^⊤[n] := rfl

@[simp] lemma val_falsum : (⊥ : L.TSemiformula n).val = ^⊥[n] := rfl

@[simp] lemma val_and (p q : L.TSemiformula n) :
    (p ⋏ q).val = p.val ^⋏[n] q.val := rfl

@[simp] lemma val_or (p q : L.TSemiformula n) :
    (p ⋎ q).val = p.val ^⋎[n] q.val := rfl

@[simp] lemma val_neg (p : L.TSemiformula n) :
    (~p).val = L.neg p.val := rfl

@[simp] lemma val_imp (p q : L.TSemiformula n) :
    (p ⟶ q).val = L.imp n p.val q.val := rfl

@[simp] lemma val_all (p : L.TSemiformula (n + 1)) :
    p.all.val = ^∀[n] p.val := rfl

@[simp] lemma val_ex (p : L.TSemiformula (n + 1)) :
    p.ex.val = ^∃[n] p.val := rfl

lemma val_inj {p q : L.TSemiformula n} :
    p.val = q.val ↔ p = q := by rcases p; rcases q; simp

@[ext] lemma ext {p q : L.TSemiformula n} (h : p.val = q.val) : p = q := val_inj.mp h

@[simp] lemma neg_verum : ~(⊤ : L.TSemiformula n) = ⊥ := by ext; simp
@[simp] lemma neg_falsum : ~(⊥ : L.TSemiformula n) = ⊤ := by ext; simp
@[simp] lemma neg_and (p q : L.TSemiformula n) : ~(p ⋏ q) = ~p ⋎ ~q := by ext; simp
@[simp] lemma neg_or (p q : L.TSemiformula n) : ~(p ⋎ q) = ~p ⋏ ~q := by ext; simp
@[simp] lemma neg_all (p : L.TSemiformula (n + 1)) : ~p.all = (~p).ex := by ext; simp
@[simp] lemma neg_ex (p : L.TSemiformula (n + 1)) : ~p.ex = (~p).all := by ext; simp

lemma imp_def (p q : L.TSemiformula n) : p ⟶ q = ~p ⋎ q := by ext; simp [imp]

@[simp] lemma neg_neg (p : L.TSemiformula n) : ~~p = p := by
  ext; simp [shift, Arith.neg_neg p.prop]

def shift (p : L.TSemiformula n) : L.TSemiformula n := ⟨L.shift p.val, p.prop.shift⟩

def substs (p : L.TSemiformula n) (w : L.TSemitermVec n m) : L.TSemiformula m :=
  ⟨L.substs m w.val p.val, p.prop.substs w.prop⟩

@[simp] lemma val_shift (p : L.TSemiformula n) : p.shift.val = L.shift p.val := rfl
@[simp] lemma val_substs (p : L.TSemiformula n) (w : L.TSemitermVec n m) : (p.substs w).val = L.substs m w.val p.val := rfl

@[simp] lemma shift_verum : (⊤ : L.TSemiformula n).shift = ⊤ := by ext; simp [shift]
@[simp] lemma shift_falsum : (⊥ : L.TSemiformula n).shift = ⊥ := by ext; simp [shift]
@[simp] lemma shift_and (p q : L.TSemiformula n) : (p ⋏ q).shift = p.shift ⋏ q.shift := by ext; simp [shift]
@[simp] lemma shift_or (p q : L.TSemiformula n) : (p ⋎ q).shift = p.shift ⋎ q.shift := by ext; simp [shift]
@[simp] lemma shift_all (p : L.TSemiformula (n + 1)) : p.all.shift = p.shift.all := by ext; simp [shift]
@[simp] lemma shift_ex (p : L.TSemiformula (n + 1)) : p.ex.shift = p.shift.ex := by ext; simp [shift]

@[simp] lemma shift_neg (p : L.TSemiformula n) : (~p).shift = ~(p.shift) := by
  ext; simp [shift, val_neg, TSemitermVec.prop]
  rw [Arith.shift_neg p.prop]
@[simp] lemma shift_imp (p q : L.TSemiformula n) : (p ⟶ q).shift = p.shift ⟶ q.shift := by
  simp [imp_def]

@[simp] lemma substs_verum (w : L.TSemitermVec n m) : (⊤ : L.TSemiformula n).substs w = ⊤ := by ext; simp [substs]
@[simp] lemma substs_falsum (w : L.TSemitermVec n m) : (⊥ : L.TSemiformula n).substs w = ⊥ := by ext; simp [substs]
@[simp] lemma substs_and (w : L.TSemitermVec n m) (p q : L.TSemiformula n) :
    (p ⋏ q).substs w = p.substs w ⋏ q.substs w := by ext; simp [substs]
@[simp] lemma substs_or (w : L.TSemitermVec n m) (p q : L.TSemiformula n) :
    (p ⋎ q).substs w = p.substs w ⋎ q.substs w := by ext; simp [substs]
@[simp] lemma substs_all (w : L.TSemitermVec n m) (p : L.TSemiformula (n + 1)) :
    p.all.substs w = (p.substs w.q).all := by
  ext; simp [substs, Language.bvar, Language.qVec, Language.TSemitermVec.bShift, Language.TSemitermVec.q]
@[simp] lemma substs_ex (w : L.TSemitermVec n m) (p : L.TSemiformula (n + 1)) :
    p.ex.substs w = (p.substs w.q).ex := by
  ext; simp [substs, Language.bvar, Language.qVec, Language.TSemitermVec.bShift, Language.TSemitermVec.q]

@[simp] lemma substs_neg (w : L.TSemitermVec n m) (p : L.TSemiformula n) : (~p).substs w = ~(p.substs w) := by
  ext; simp only [substs, val_neg, TSemitermVec.prop, Arith.substs_neg p.prop]
@[simp] lemma substs_imp (w : L.TSemitermVec n m) (p q : L.TSemiformula n) : (p ⟶ q).substs w = p.substs w ⟶ q.substs w := by
  simp [imp_def]
@[simp] lemma substs_imply (w : L.TSemitermVec n m) (p q : L.TSemiformula n) : (p ⟷ q).substs w = p.substs w ⟷ q.substs w := by
  simp [LogicalConnective.iff]

end Language.TSemiformula

notation p:max "^/[" w "]" => Language.TSemiformula.substs p w

structure Language.TSemiformulaVec (n : V) where
  val : V
  prop : ∀ i < len val, L.Semiformula n val.[i]

namespace Language.TSemiformulaVec

def conj (ps : L.TSemiformulaVec n) : L.TSemiformula n := ⟨^⋀[n] ps.val, by simpa using ps.prop⟩

def disj (ps : L.TSemiformulaVec n) : L.TSemiformula n := ⟨^⋁[n] ps.val, by simpa using ps.prop⟩

def nth (ps : L.TSemiformulaVec n) (i : V) (hi : i < len ps.val) : L.TSemiformula n :=
  ⟨ps.val.[i], ps.prop i hi⟩

@[simp] lemma val_conj (ps : L.TSemiformulaVec n) : ps.conj.val = ^⋀[n] ps.val := rfl

@[simp] lemma val_disj (ps : L.TSemiformulaVec n) : ps.disj.val = ^⋁[n] ps.val := rfl

@[simp] lemma val_nth (ps : L.TSemiformulaVec n) (i : V) (hi : i < len ps.val) :
    (ps.nth i hi).val = ps.val.[i] := rfl

end Language.TSemiformulaVec

namespace Language.TSemifromula

lemma subst_eq_self {n : V} (w : L.TSemitermVec n n) (p : L.TSemiformula n) (H : ∀ i, (hi : i < n) → w.nth i hi = L.bvar i hi) :
    p^/[w] = p := by
  ext; simp; rw [Arith.subst_eq_self p.prop w.prop]
  intro i hi
  simpa using congr_arg Language.TSemiterm.val (H i hi)

@[simp] lemma subst_eq_self₁ (p : L.TSemiformula (0 + 1)) :
    p^/[(L.bvar 0 (by simp)).sing] = p := by
  apply subst_eq_self
  simp only [zero_add, lt_one_iff_eq_zero]
  rintro _ rfl
  simp

lemma shift_substs {n m : V} (w : L.TSemitermVec n m) (p : L.TSemiformula n) :
    (p^/[w]).shift = p.shift^/[w.shift] := by ext; simp; rw [Arith.shift_substs p.prop w.prop]

lemma substs_substs {n m l : V} (v : L.TSemitermVec m l) (w : L.TSemitermVec n m) (p : L.TSemiformula n) :
    (p^/[w])^/[v] = p^/[w.substs v] := by ext; simp; rw [Arith.substs_substs p.prop v.prop w.prop]

end Language.TSemifromula

end typed_formula

open Formalized

def Language.TSemiterm.equals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^=[n] u.val, by simp [qqEQ]⟩

def Language.TSemiterm.notEquals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^≠[n] u.val, by simp [qqNEQ]⟩

def Language.TSemiterm.lessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^<[n] u.val, by simp [qqLT]⟩

def Language.TSemiterm.notLessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^≮[n] u.val, by simp [qqNLT]⟩

scoped infix:75 " =' " => Language.TSemiterm.equals

scoped infix:75 " ≠' " => Language.TSemiterm.notEquals

scoped infix:75 " <' " => Language.TSemiterm.lessThan

scoped infix:75 " ≮' " => Language.TSemiterm.notLessThan

def Language.TSemiformula.ball {n : V} (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) : ⌜ℒₒᵣ⌝.TSemiformula n :=
  (⌜ℒₒᵣ⌝.bvar 0 ≮' t.bShift ⋎ p).all

def Language.TSemiformula.bex {n : V} (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) : ⌜ℒₒᵣ⌝.TSemiformula n :=
  (⌜ℒₒᵣ⌝.bvar 0 <' t.bShift ⋏ p).ex

namespace Formalized

variable {n m : V}

@[simp] lemma val_equals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : (t =' u).val = t.val ^=[n] u.val := rfl
@[simp] lemma val_notEquals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : (t ≠' u).val = t.val ^≠[n] u.val := rfl
@[simp] lemma val_lessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : (t <' u).val = t.val ^<[n] u.val := rfl
@[simp] lemma val_notLessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : (t ≮' u).val = t.val ^≮[n] u.val := rfl

@[simp] lemma neg_equals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    ~(t₁ =' t₂) = (t₁ ≠' t₂) := by
  ext; simp [Language.TSemiterm.equals, Language.TSemiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_notEquals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    ~(t₁ ≠' t₂) = (t₁ =' t₂) := by
  ext; simp [Language.TSemiterm.equals, Language.TSemiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_lessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    ~(t₁ <' t₂) = (t₁ ≮' t₂) := by
  ext; simp [Language.TSemiterm.lessThan, Language.TSemiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma neg_notLessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    ~(t₁ ≮' t₂) = (t₁ <' t₂) := by
  ext; simp [Language.TSemiterm.lessThan, Language.TSemiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma shift_equals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ =' t₂).shift = (t₁.shift =' t₂.shift) := by
  ext; simp [Language.TSemiterm.equals, Language.TSemiterm.shift, Language.TSemiformula.shift, qqEQ]

@[simp] lemma shift_notEquals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≠' t₂).shift = (t₁.shift ≠' t₂.shift) := by
  ext; simp [Language.TSemiterm.notEquals, Language.TSemiterm.shift, Language.TSemiformula.shift, qqNEQ]

@[simp] lemma shift_lessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ <' t₂).shift = (t₁.shift <' t₂.shift) := by
  ext; simp [Language.TSemiterm.lessThan, Language.TSemiterm.shift, Language.TSemiformula.shift, qqLT]

@[simp] lemma shift_notLessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≮' t₂).shift = (t₁.shift ≮' t₂.shift) := by
  ext; simp [Language.TSemiterm.notLessThan, Language.TSemiterm.shift, Language.TSemiformula.shift, qqNLT]

@[simp] lemma substs_equals (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ =' t₂).substs w = (t₁.substs w =' t₂.substs w) := by
  ext; simp [Language.TSemiterm.equals, Language.TSemiterm.substs, Language.TSemiformula.substs, qqEQ]

@[simp] lemma substs_notEquals (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≠' t₂).substs w = (t₁.substs w ≠' t₂.substs w) := by
  ext; simp [Language.TSemiterm.notEquals, Language.TSemiterm.substs, Language.TSemiformula.substs, qqNEQ]

@[simp] lemma substs_lessThan (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ <' t₂).substs w = (t₁.substs w <' t₂.substs w) := by
  ext; simp [Language.TSemiterm.lessThan, Language.TSemiterm.substs, Language.TSemiformula.substs, qqLT]

@[simp] lemma substs_notLessThan (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≮' t₂).substs w = (t₁.substs w ≮' t₂.substs w) := by
  ext; simp [Language.TSemiterm.notLessThan, Language.TSemiterm.substs, Language.TSemiformula.substs, qqNLT]

@[simp] lemma val_ball {n : V} (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.ball t).val = ^∀[n] (^#0 ^≮[n + 1] ⌜ℒₒᵣ⌝.termBShift n t.val) ^⋎[n + 1] p.val := by
  simp [Language.TSemiformula.ball]

@[simp] lemma val_bex {n : V} (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.bex t).val = ^∃[n] (^#0 ^<[n + 1] ⌜ℒₒᵣ⌝.termBShift n t.val) ^⋏[n + 1] p.val := by
  simp [Language.TSemiformula.bex]

lemma neg_ball (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    ~(p.ball t) = (~p).bex t := by
  ext; simp; rw [neg_all, neg_or] <;> simp [qqNLT, qqLT]

lemma neg_bex (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    ~(p.bex t) = (~p).ball t := by
  ext; simp; rw [neg_ex, neg_and] <;> simp [qqNLT, qqLT]

@[simp] lemma shifts_ball (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.ball t).shift = p.shift.ball t.shift := by
  simp [Language.TSemiformula.ball, Language.TSemiterm.bShift_shift_comm]

@[simp] lemma shifts_bex (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.bex t).shift = p.shift.bex t.shift := by
  simp [Language.TSemiformula.bex, Language.TSemiterm.bShift_shift_comm]

@[simp] lemma substs_ball (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.ball t)^/[w] = (p^/[w.q]).ball (t^ᵗ/[w]) := by
  simp [Language.TSemiformula.ball]

@[simp] lemma substs_bex (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    (p.bex t)^/[w] = (p^/[w.q]).bex (t^ᵗ/[w]) := by
  simp [Language.TSemiformula.bex]

def tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    ⌜ℒₒᵣ⌝.TSemiformulaVec m := ⟨substItr m w.val p.val k, by
  intro i hi
  have : i < k := by simpa using hi
  simp only [gt_iff_lt, this, substItr_nth]
  exact Language.Semiformula.substs p.prop (w.prop.cons (by simp))⟩

@[simp] lemma val_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    (tSubstItr w p k).val = substItr m w.val p.val k := by simp [tSubstItr]

@[simp] lemma len_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    len (tSubstItr w p k).val = k := by simp

lemma nth_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth i (by simp [hi]) = p.substs (↑(k - (i + 1)) ∷ᵗ w) := by ext; simp [tSubstItr, Language.TSemiformula.substs, hi]

lemma nth_tSubstItr' {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth (k - (i + 1)) (by simpa using sub_succ_lt_self hi) = p.substs (↑i ∷ᵗ w) := by
  ext; simp [tSubstItr, Language.TSemiformula.substs, hi, sub_succ_lt_self hi, sub_succ_lt_selfs hi]

@[simp] lemma neg_conj_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    ~(tSubstItr w p k).conj = (tSubstItr w (~p) k).disj := by
  ext; simp [neg_conj_substItr p.prop w.prop]

@[simp] lemma neg_disj_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    ~(tSubstItr w p k).disj = (tSubstItr w (~p) k).conj := by
  ext; simp [neg_disj_substItr p.prop w.prop]

@[simp] lemma substs_conj_tSubstItr {n m l : V} (v : ⌜ℒₒᵣ⌝.TSemitermVec m l) (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    (tSubstItr w p k).conj.substs v = (tSubstItr (w.substs v) p k).conj := by
  ext; simp [Language.TSemiformula.substs, Language.TSemitermVec.substs]
  rw [substs_conj_substItr p.prop w.prop v.prop]

@[simp] lemma substs_disj_tSubstItr {n m l : V} (v : ⌜ℒₒᵣ⌝.TSemitermVec m l) (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) (k : V) :
    (tSubstItr w p k).disj.substs v = (tSubstItr (w.substs v) p k).disj := by
  ext; simp [Language.TSemiformula.substs, Language.TSemitermVec.substs]
  rw [substs_disj_substItr p.prop w.prop v.prop]

end Formalized

lemma Language.TSemiformula.ball_eq_imp {n : V} (t : ⌜ℒₒᵣ⌝.TSemiterm n) (p : ⌜ℒₒᵣ⌝.TSemiformula (n + 1)) :
    p.ball t = (⌜ℒₒᵣ⌝.bvar 0 <' t.bShift ⟶ p).all := by simp [Language.TSemiformula.ball, imp_def]

end LO.Arith
