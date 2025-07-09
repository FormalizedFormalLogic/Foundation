import Foundation.FirstOrder.ISigma1.Metamath.Term.Typed
import Foundation.FirstOrder.ISigma1.Metamath.Formula.Iteration

/-!

# Typed Formalized Semiformula/Formula

-/
namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Metamath.Language V} {pL : LDef} [Metamath.Language.Defined L pL]

lemma sub_succ_lt_self {a b : V} (h : b < a) : a - (b + 1) < a := by
  simp [tsub_lt_iff_left (succ_le_iff_lt.mpr h)]

lemma sub_succ_lt_selfs {a b : V} (h : b < a) : a - (a - (b + 1) + 1) = b := by
  rw [←PeanoMinus.sub_sub]
  apply sub_remove_left
  apply sub_remove_left
  rw [←add_sub_of_le (succ_le_iff_lt.mpr h)]
  simp

section typed_formula

variable (L)

structure Language.Semiformula (n : V) where
  val : V
  prop : L.IsSemiformula n val

attribute [simp] Language.Semiformula.prop

abbrev Language.Formula := L.Semiformula 0

variable {L}

@[simp] lemma Language.Semiformula.isUFormula (p : L.Semiformula n) : L.IsUFormula p.val := p.prop.isUFormula

noncomputable scoped instance : LogicalConnective (L.Semiformula n) where
  top := ⟨^⊤, by simp⟩
  bot := ⟨^⊥, by simp⟩
  wedge (p q) := ⟨p.val ^⋏ q.val, by simp⟩
  vee (p q) := ⟨p.val ^⋎ q.val, by simp⟩
  tilde (p) := ⟨L.neg p.val, by simp⟩
  arrow (p q) := ⟨L.imp p.val q.val, by simp⟩

def Language.Semiformula.cast (p : L.Semiformula n) (eq : n = n' := by simp) : L.Semiformula n' := eq ▸ p

noncomputable def verums (k : V) : L.Semiformula n := ⟨qqVerums k, by simp⟩

@[simp] lemma Language.Semiformula.val_cast (p : L.Semiformula n) (eq : n = n') :
    (p.cast eq).val = p.val := by rcases eq; simp [Language.Semiformula.cast]

noncomputable def Language.Semiformula.all (p : L.Semiformula (n + 1)) : L.Semiformula n := ⟨^∀ p.val, by simp⟩

noncomputable def Language.Semiformula.ex (p : L.Semiformula (n + 1)) : L.Semiformula n := ⟨^∃ p.val, by simp⟩

namespace Language.Semiformula

@[simp] lemma val_verum : (⊤ : L.Semiformula n).val = ^⊤ := rfl

@[simp] lemma val_falsum : (⊥ : L.Semiformula n).val = ^⊥ := rfl

@[simp] lemma val_and (p q : L.Semiformula n) :
    (p ⋏ q).val = p.val ^⋏ q.val := rfl

@[simp] lemma val_or (p q : L.Semiformula n) :
    (p ⋎ q).val = p.val ^⋎ q.val := rfl

@[simp] lemma val_neg (p : L.Semiformula n) :
    (∼p).val = L.neg p.val := rfl

@[simp] lemma val_imp (p q : L.Semiformula n) :
    (p ➝ q).val = L.imp p.val q.val := rfl

@[simp] lemma val_all (p : L.Semiformula (n + 1)) :
    p.all.val = ^∀ p.val := rfl

@[simp] lemma val_ex (p : L.Semiformula (n + 1)) :
    p.ex.val = ^∃ p.val := rfl

@[simp] lemma val_iff (p q : L.Semiformula n) :
    (p ⭤ q).val = L.iff p.val q.val := rfl

lemma val_inj {p q : L.Semiformula n} :
    p.val = q.val ↔ p = q := by rcases p; rcases q; simp

@[ext] lemma ext {p q : L.Semiformula n} (h : p.val = q.val) : p = q := val_inj.mp h

@[simp] lemma and_inj {p₁ p₂ q₁ q₂ : L.Semiformula n} :
    p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [Semiformula.ext_iff]

@[simp] lemma or_inj {p₁ p₂ q₁ q₂ : L.Semiformula n} :
    p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [Semiformula.ext_iff]

@[simp] lemma all_inj {p q : L.Semiformula (n + 1)} :
    p.all = q.all ↔ p = q := by simp [Semiformula.ext_iff]

@[simp] lemma ex_inj {p q : L.Semiformula (n + 1)} :
    p.ex = q.ex ↔ p = q := by simp [Semiformula.ext_iff]

@[simp] lemma val_verums : (verums k : L.Semiformula n).val = qqVerums k := rfl

@[simp] lemma verums_zero : (verums 0 : L.Semiformula n) = ⊤ := by ext; simp

@[simp] lemma verums_succ (k : V) : (verums (k + 1) : L.Semiformula n) = ⊤ ⋏ verums k := by ext; simp

@[simp] lemma neg_verum : ∼(⊤ : L.Semiformula n) = ⊥ := by ext; simp
@[simp] lemma neg_falsum : ∼(⊥ : L.Semiformula n) = ⊤ := by ext; simp
@[simp] lemma neg_and (p q : L.Semiformula n) : ∼(p ⋏ q) = ∼p ⋎ ∼q := by ext; simp
@[simp] lemma neg_or (p q : L.Semiformula n) : ∼(p ⋎ q) = ∼p ⋏ ∼q := by ext; simp
@[simp] lemma neg_all (p : L.Semiformula (n + 1)) : ∼p.all = (∼p).ex := by ext; simp
@[simp] lemma neg_ex (p : L.Semiformula (n + 1)) : ∼p.ex = (∼p).all := by ext; simp

lemma imp_def (p q : L.Semiformula n) : p ➝ q = ∼p ⋎ q := by ext; simp [imp]

@[simp] lemma neg_neg (p : L.Semiformula n) : ∼∼p = p := by
  ext; simp [shift, Language.IsUFormula.neg_neg]

noncomputable def shift (p : L.Semiformula n) : L.Semiformula n := ⟨L.shift p.val, p.prop.shift⟩

noncomputable def substs (p : L.Semiformula n) (w : L.SemitermVec n m) : L.Semiformula m :=
  ⟨L.substs w.val p.val, p.prop.substs w.prop⟩

@[simp] lemma val_shift (p : L.Semiformula n) : p.shift.val = L.shift p.val := rfl
@[simp] lemma val_substs (p : L.Semiformula n) (w : L.SemitermVec n m) : (p.substs w).val = L.substs w.val p.val := rfl

@[simp] lemma shift_verum : (⊤ : L.Semiformula n).shift = ⊤ := by ext; simp [shift]
@[simp] lemma shift_falsum : (⊥ : L.Semiformula n).shift = ⊥ := by ext; simp [shift]
@[simp] lemma shift_and (p q : L.Semiformula n) : (p ⋏ q).shift = p.shift ⋏ q.shift := by ext; simp [shift]
@[simp] lemma shift_or (p q : L.Semiformula n) : (p ⋎ q).shift = p.shift ⋎ q.shift := by ext; simp [shift]
@[simp] lemma shift_all (p : L.Semiformula (n + 1)) : p.all.shift = p.shift.all := by ext; simp [shift]
@[simp] lemma shift_ex (p : L.Semiformula (n + 1)) : p.ex.shift = p.shift.ex := by ext; simp [shift]

@[simp] lemma neg_inj {p q : L.Semiformula n} :
    ∼p = ∼q ↔ p = q :=
  ⟨by intro h; simpa using congr_arg (∼·) h, by rintro rfl; rfl⟩

@[simp] lemma imp_inj {p₁ p₂ q₁ q₂ : L.Semiformula n} :
    p₁ ➝ p₂ = q₁ ➝ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [imp_def]

@[simp] lemma shift_neg (p : L.Semiformula n) : (∼p).shift = ∼(p.shift) := by
  ext; simp [shift, val_neg, SemitermVec.prop]; simp [Metamath.shift_neg p.prop]

@[simp] lemma shift_imp (p q : L.Semiformula n) : (p ➝ q).shift = p.shift ➝ q.shift := by
  simp [imp_def]

@[simp] lemma substs_verum (w : L.SemitermVec n m) : (⊤ : L.Semiformula n).substs w = ⊤ := by ext; simp [substs]
@[simp] lemma substs_falsum (w : L.SemitermVec n m) : (⊥ : L.Semiformula n).substs w = ⊥ := by ext; simp [substs]
@[simp] lemma substs_and (w : L.SemitermVec n m) (p q : L.Semiformula n) :
    (p ⋏ q).substs w = p.substs w ⋏ q.substs w := by ext; simp [substs]
@[simp] lemma substs_or (w : L.SemitermVec n m) (p q : L.Semiformula n) :
    (p ⋎ q).substs w = p.substs w ⋎ q.substs w := by ext; simp [substs]
@[simp] lemma substs_all (w : L.SemitermVec n m) (p : L.Semiformula (n + 1)) :
    p.all.substs w = (p.substs w.q).all := by
  ext; simp [substs, Language.bvar, Language.qVec, Language.SemitermVec.bShift, Language.SemitermVec.q, w.prop.lh]
@[simp] lemma substs_ex (w : L.SemitermVec n m) (p : L.Semiformula (n + 1)) :
    p.ex.substs w = (p.substs w.q).ex := by
  ext; simp [substs, Language.bvar, Language.qVec, Language.SemitermVec.bShift, Language.SemitermVec.q, w.prop.lh]

@[simp] lemma substs_neg (w : L.SemitermVec n m) (p : L.Semiformula n) : (∼p).substs w = ∼(p.substs w) := by
  ext; simp [substs, val_neg, SemitermVec.prop, Metamath.substs_neg p.prop w.prop]
@[simp] lemma substs_imp (w : L.SemitermVec n m) (p q : L.Semiformula n) : (p ➝ q).substs w = p.substs w ➝ q.substs w := by
  simp [imp_def]
@[simp] lemma substs_imply (w : L.SemitermVec n m) (p q : L.Semiformula n) : (p ⭤ q).substs w = p.substs w ⭤ q.substs w := by
  simp [LogicalConnective.iff]

end Language.Semiformula

notation p:max "^/[" w "]" => Language.Semiformula.substs p w

structure Language.SemiformulaVec (n : V) where
  val : V
  prop : ∀ i < len val, L.IsSemiformula n val.[i]

namespace Language.SemiformulaVec

noncomputable def conj (ps : L.SemiformulaVec n) : L.Semiformula n := ⟨^⋀ ps.val, by simpa using ps.prop⟩

noncomputable def disj (ps : L.SemiformulaVec n) : L.Semiformula n := ⟨^⋁ ps.val, by simpa using ps.prop⟩

noncomputable def nth (ps : L.SemiformulaVec n) (i : V) (hi : i < len ps.val) : L.Semiformula n :=
  ⟨ps.val.[i], ps.prop i hi⟩

@[simp] lemma val_conj (ps : L.SemiformulaVec n) : ps.conj.val = ^⋀ ps.val := rfl

@[simp] lemma val_disj (ps : L.SemiformulaVec n) : ps.disj.val = ^⋁ ps.val := rfl

@[simp] lemma val_nth (ps : L.SemiformulaVec n) (i : V) (hi : i < len ps.val) :
    (ps.nth i hi).val = ps.val.[i] := rfl

end Language.SemiformulaVec

namespace Language.TSemifromula

lemma subst_eq_self {n : V} (w : L.SemitermVec n n) (p : L.Semiformula n) (H : ∀ i, (hi : i < n) → w.nth i hi = L.bvar i hi) :
    p^/[w] = p := by
  suffices ∀ i < n, w.val.[i] = ^#i by
    ext; simp only [Semiformula.val_substs]; rw [Metamath.subst_eq_self p.prop w.prop]; simpa
  intro i hi
  simpa using congr_arg Language.Semiterm.val (H i hi)

@[simp] lemma subst_eq_self₁ (p : L.Semiformula (0 + 1)) :
    p^/[(L.bvar 0 (by simp)).sing] = p := by
  apply subst_eq_self
  simp only [zero_add, lt_one_iff_eq_zero]
  rintro _ rfl
  simp

@[simp] lemma subst_nil_eq_self (w : L.SemitermVec 0 0) :
    p^/[w] = p := subst_eq_self _ _ (by simp)

lemma shift_substs {n m : V} (w : L.SemitermVec n m) (p : L.Semiformula n) :
    (p^/[w]).shift = p.shift^/[w.shift] := by ext; simp [Metamath.shift_substs p.prop w.prop]

lemma substs_substs {n m l : V} (v : L.SemitermVec m l) (w : L.SemitermVec n m) (p : L.Semiformula n) :
    (p^/[w])^/[v] = p^/[w.substs v] := by ext; simp [Metamath.substs_substs p.prop v.prop w.prop]

end Language.TSemifromula

end typed_formula

/-
section typed_isfvfree

namespace Language.Semiformula

def FVFree (p : L.Semiformula n) : Prop := L.IsFVFree n p.val

lemma FVFree.iff {p : L.Semiformula n} : p.FVFree ↔ p.shift = p := by
  simp [FVFree, Language.IsFVFree, ext_iff]

@[simp] lemma Fvfree.verum : (⊤ : L.Semiformula n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.falsum : (⊥ : L.Semiformula n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.and {p q : L.Semiformula n} :
    (p ⋏ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff, FVFree.iff]

@[simp] lemma Fvfree.or {p q : L.Semiformula n} : (p ⋎ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.neg {p : L.Semiformula n} : (∼p).FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.all {p : L.Semiformula (n + 1)} : p.all.FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.ex {p : L.Semiformula (n + 1)} : p.ex.FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.imp {p q : L.Semiformula n} : (p ➝ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff]

end Language.Semiformula

end typed_isfvfree
-/

open InternalArithmetic

noncomputable def Language.Semiterm.equals {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiformula n := ⟨t.val ^= u.val, by simp [qqEQ]⟩

noncomputable def Language.Semiterm.notEquals {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiformula n := ⟨t.val ^≠ u.val, by simp [qqNEQ]⟩

noncomputable def Language.Semiterm.lessThan {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiformula n := ⟨t.val ^< u.val, by simp [qqLT]⟩

noncomputable def Language.Semiterm.notLessThan {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiformula n := ⟨t.val ^≮ u.val, by simp [qqNLT]⟩

scoped infix:75 " =' " => Language.Semiterm.equals

scoped infix:75 " ≠' " => Language.Semiterm.notEquals

scoped infix:75 " <' " => Language.Semiterm.lessThan

scoped infix:75 " ≮' " => Language.Semiterm.notLessThan

noncomputable def Language.Semiformula.ball {n : V} (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) : ⌜ℒₒᵣ⌝.Semiformula n :=
  (⌜ℒₒᵣ⌝.bvar 0 ≮' t.bShift ⋎ p).all

noncomputable def Language.Semiformula.bex {n : V} (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) : ⌜ℒₒᵣ⌝.Semiformula n :=
  (⌜ℒₒᵣ⌝.bvar 0 <' t.bShift ⋏ p).ex

namespace InternalArithmetic

variable {n m : V}

@[simp] lemma val_equals {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : (t =' u).val = t.val ^= u.val := rfl
@[simp] lemma val_notEquals {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : (t ≠' u).val = t.val ^≠ u.val := rfl
@[simp] lemma val_lessThan {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : (t <' u).val = t.val ^< u.val := rfl
@[simp] lemma val_notLessThan {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : (t ≮' u).val = t.val ^≮ u.val := rfl

@[simp] lemma equals_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    (t₁ =' u₁) = (t₂ =' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Language.Semiformula.ext_iff, Language.Semiterm.ext_iff, qqEQ]

@[simp] lemma notequals_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    (t₁ ≠' u₁) = (t₂ ≠' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Language.Semiformula.ext_iff, Language.Semiterm.ext_iff, qqNEQ]

@[simp] lemma lessThan_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    (t₁ <' u₁) = (t₂ <' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Language.Semiformula.ext_iff, Language.Semiterm.ext_iff, qqLT]

@[simp] lemma notLessThan_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    (t₁ ≮' u₁) = (t₂ ≮' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Language.Semiformula.ext_iff, Language.Semiterm.ext_iff, qqNLT]

@[simp] lemma neg_equals (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    ∼(t₁ =' t₂) = (t₁ ≠' t₂) := by
  ext; simp [Language.Semiterm.equals, Language.Semiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_notEquals (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    ∼(t₁ ≠' t₂) = (t₁ =' t₂) := by
  ext; simp [Language.Semiterm.equals, Language.Semiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_lessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    ∼(t₁ <' t₂) = (t₁ ≮' t₂) := by
  ext; simp [Language.Semiterm.lessThan, Language.Semiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma neg_notLessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    ∼(t₁ ≮' t₂) = (t₁ <' t₂) := by
  ext; simp [Language.Semiterm.lessThan, Language.Semiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma shift_equals (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ =' t₂).shift = (t₁.shift =' t₂.shift) := by
  ext; simp [Language.Semiterm.equals, Language.Semiterm.shift, Language.Semiformula.shift, qqEQ]

@[simp] lemma shift_notEquals (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ ≠' t₂).shift = (t₁.shift ≠' t₂.shift) := by
  ext; simp [Language.Semiterm.notEquals, Language.Semiterm.shift, Language.Semiformula.shift, qqNEQ]

@[simp] lemma shift_lessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ <' t₂).shift = (t₁.shift <' t₂.shift) := by
  ext; simp [Language.Semiterm.lessThan, Language.Semiterm.shift, Language.Semiformula.shift, qqLT]

@[simp] lemma shift_notLessThan (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ ≮' t₂).shift = (t₁.shift ≮' t₂.shift) := by
  ext; simp [Language.Semiterm.notLessThan, Language.Semiterm.shift, Language.Semiformula.shift, qqNLT]

@[simp] lemma substs_equals (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ =' t₂).substs w = (t₁.substs w =' t₂.substs w) := by
  ext; simp [Language.Semiterm.equals, Language.Semiterm.substs, Language.Semiformula.substs, qqEQ]

@[simp] lemma substs_notEquals (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ ≠' t₂).substs w = (t₁.substs w ≠' t₂.substs w) := by
  ext; simp [Language.Semiterm.notEquals, Language.Semiterm.substs, Language.Semiformula.substs, qqNEQ]

@[simp] lemma substs_lessThan (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ <' t₂).substs w = (t₁.substs w <' t₂.substs w) := by
  ext; simp [Language.Semiterm.lessThan, Language.Semiterm.substs, Language.Semiformula.substs, qqLT]

@[simp] lemma substs_notLessThan (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ ≮' t₂).substs w = (t₁.substs w ≮' t₂.substs w) := by
  ext; simp [Language.Semiterm.notLessThan, Language.Semiterm.substs, Language.Semiformula.substs, qqNLT]

@[simp] lemma val_ball {n : V} (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.ball t).val = ^∀ (^#0 ^≮ ⌜ℒₒᵣ⌝.termBShift t.val) ^⋎ p.val := by
  simp [Language.Semiformula.ball]

@[simp] lemma val_bex {n : V} (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.bex t).val = ^∃ (^#0 ^< ⌜ℒₒᵣ⌝.termBShift t.val) ^⋏ p.val := by
  simp [Language.Semiformula.bex]

lemma neg_ball (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    ∼(p.ball t) = (∼p).bex t := by
  ext; simp [neg_all, neg_or, qqNLT, qqLT, t.prop.termBShift.isUTerm]

lemma neg_bex (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    ∼(p.bex t) = (∼p).ball t := by
  ext; simp [neg_ex, neg_and, qqNLT, qqLT, t.prop.termBShift.isUTerm]

@[simp] lemma shifts_ball (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.ball t).shift = p.shift.ball t.shift := by
  simp [Language.Semiformula.ball, Language.Semiterm.bShift_shift_comm]

@[simp] lemma shifts_bex (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.bex t).shift = p.shift.bex t.shift := by
  simp [Language.Semiformula.bex, Language.Semiterm.bShift_shift_comm]

@[simp] lemma substs_ball (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.ball t)^/[w] = (p^/[w.q]).ball (t^ᵗ/[w]) := by
  simp [Language.Semiformula.ball]

@[simp] lemma substs_bex (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    (p.bex t)^/[w] = (p^/[w.q]).bex (t^ᵗ/[w]) := by
  simp [Language.Semiformula.bex]

noncomputable def tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    ⌜ℒₒᵣ⌝.SemiformulaVec m := ⟨substItr w.val p.val k, by
  intro i hi
  have : i < k := by simpa using hi
  simp only [gt_iff_lt, this, substItr_nth]
  exact p.prop.substs (w.prop.cons (by simp))⟩

@[simp] lemma val_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    (tSubstItr w p k).val = substItr w.val p.val k := by simp [tSubstItr]

@[simp] lemma len_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    len (tSubstItr w p k).val = k := by simp

lemma nth_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth i (by simp [hi]) = p.substs (↑(k - (i + 1)) ∷ᵗ w) := by ext; simp [tSubstItr, Language.Semiformula.substs, hi]

lemma nth_tSubstItr' {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth (k - (i + 1)) (by simpa using sub_succ_lt_self hi) = p.substs (↑i ∷ᵗ w) := by
  ext; simp [tSubstItr, Language.Semiformula.substs, hi, sub_succ_lt_self hi, sub_succ_lt_selfs hi]

@[simp] lemma neg_conj_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    ∼(tSubstItr w p k).conj = (tSubstItr w (∼p) k).disj := by
  ext; simp [neg_conj_substItr p.prop w.prop]

@[simp] lemma neg_disj_tSubstItr {n m : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    ∼(tSubstItr w p k).disj = (tSubstItr w (∼p) k).conj := by
  ext; simp [neg_disj_substItr p.prop w.prop]

@[simp] lemma substs_conj_tSubstItr {n m l : V} (v : ⌜ℒₒᵣ⌝.SemitermVec m l) (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    (tSubstItr w p k).conj.substs v = (tSubstItr (w.substs v) p k).conj := by
  ext; simp [Language.Semiformula.substs, Language.SemitermVec.substs, substs_conj_substItr p.prop w.prop v.prop]

@[simp] lemma substs_disj_tSubstItr {n m l : V} (v : ⌜ℒₒᵣ⌝.SemitermVec m l) (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) (k : V) :
    (tSubstItr w p k).disj.substs v = (tSubstItr (w.substs v) p k).disj := by
  ext; simp [Language.Semiformula.substs, Language.SemitermVec.substs, substs_disj_substItr p.prop w.prop v.prop]

end InternalArithmetic

lemma Language.Semiformula.ball_eq_imp {n : V} (t : ⌜ℒₒᵣ⌝.Semiterm n) (p : ⌜ℒₒᵣ⌝.Semiformula (n + 1)) :
    p.ball t = (⌜ℒₒᵣ⌝.bvar 0 <' t.bShift ➝ p).all := by simp [Language.Semiformula.ball, imp_def]

end LO.ISigma1.Metamath
