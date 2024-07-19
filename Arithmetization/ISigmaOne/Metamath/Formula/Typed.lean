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

@[simp] lemma shift_verum : (⊤ : L.TSemiformula n).shift = ⊤ := by ext; simp [shift]
@[simp] lemma shift_falsum : (⊥ : L.TSemiformula n).shift = ⊥ := by ext; simp [shift]
@[simp] lemma shift_and (p q : L.TSemiformula n) : (p ⋏ q).shift = p.shift ⋏ q.shift := by ext; simp [shift]
@[simp] lemma shift_or (p q : L.TSemiformula n) : (p ⋎ q).shift = p.shift ⋎ q.shift := by ext; simp [shift]
@[simp] lemma shift_all (p : L.TSemiformula (n + 1)) : p.all.shift = p.shift.all := by ext; simp [shift]
@[simp] lemma shift_ex (p : L.TSemiformula (n + 1)) : p.ex.shift = p.shift.ex := by ext; simp [shift]

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

end typed_formula

namespace Formalized

def equals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^=[n] u.val, by simp [qqEQ]⟩

def notEquals {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^≠[n] u.val, by simp [qqNEQ]⟩

def lessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^<[n] u.val, by simp [qqLT]⟩

def notLessThan {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiformula n := ⟨t.val ^≮[n] u.val, by simp [qqNLT]⟩

scoped infix:75 " =' " => equals

scoped infix:75 " ≠' " => notEquals

scoped infix:75 " <' " => lessThan

scoped infix:75 " ≮' " => notLessThan

variable {n m : V}

@[simp] lemma shift_equals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ =' t₂).shift = (t₁.shift =' t₂.shift) := by
  ext; simp [equals, Language.TSemiterm.shift, Language.TSemiformula.shift, qqEQ]

@[simp] lemma shift_notEquals (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≠' t₂).shift = (t₁.shift ≠' t₂.shift) := by
  ext; simp [notEquals, Language.TSemiterm.shift, Language.TSemiformula.shift, qqNEQ]

@[simp] lemma shift_lessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ <' t₂).shift = (t₁.shift <' t₂.shift) := by
  ext; simp [lessThan, Language.TSemiterm.shift, Language.TSemiformula.shift, qqLT]

@[simp] lemma shift_notLessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≮' t₂).shift = (t₁.shift ≮' t₂.shift) := by
  ext; simp [notLessThan, Language.TSemiterm.shift, Language.TSemiformula.shift, qqNLT]

@[simp] lemma substs_equals (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ =' t₂).substs w = (t₁.substs w =' t₂.substs w) := by
  ext; simp [equals, Language.TSemiterm.substs, Language.TSemiformula.substs, qqEQ]

@[simp] lemma substs_notEquals (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≠' t₂).substs w = (t₁.substs w ≠' t₂.substs w) := by
  ext; simp [notEquals, Language.TSemiterm.substs, Language.TSemiformula.substs, qqNEQ]

@[simp] lemma substs_lessThan (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ <' t₂).substs w = (t₁.substs w <' t₂.substs w) := by
  ext; simp [lessThan, Language.TSemiterm.substs, Language.TSemiformula.substs, qqLT]

@[simp] lemma substs_notLessThan (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ ≮' t₂).substs w = (t₁.substs w ≮' t₂.substs w) := by
  ext; simp [notLessThan, Language.TSemiterm.substs, Language.TSemiformula.substs, qqNLT]

end Formalized

end LO.Arith
