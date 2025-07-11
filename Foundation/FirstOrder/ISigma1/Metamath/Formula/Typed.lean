import Foundation.FirstOrder.ISigma1.Metamath.Term.Typed
import Foundation.FirstOrder.ISigma1.Metamath.Formula.Iteration

/-!
# Typed Formalized Semiformula/Formula
-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma sub_succ_lt_self {a b : V} (h : b < a) : a - (b + 1) < a := by
  simp [tsub_lt_iff_left (succ_le_iff_lt.mpr h)]

lemma sub_succ_lt_selfs {a b : V} (h : b < a) : a - (a - (b + 1) + 1) = b := by
  rw [←PeanoMinus.sub_sub]
  apply sub_remove_left
  apply sub_remove_left
  rw [←add_sub_of_le (succ_le_iff_lt.mpr h)]
  simp

section typed_formula

variable (V L)

structure Semiformula (n : V) where
  val : V
  prop : IsSemiformula L n val

attribute [simp] Semiformula.prop

abbrev Formula := Semiformula (V := V) L 0

variable {L V}

variable {n : V}

@[simp] lemma Semiformula.isUFormula (p : Semiformula V L n) : IsUFormula L p.val := p.prop.isUFormula

noncomputable scoped instance : LogicalConnective (Semiformula V L n) where
  top := ⟨^⊤, by simp⟩
  bot := ⟨^⊥, by simp⟩
  wedge (p q) := ⟨p.val ^⋏ q.val, by simp⟩
  vee (p q) := ⟨p.val ^⋎ q.val, by simp⟩
  tilde (p) := ⟨neg L p.val, by simp⟩
  arrow (p q) := ⟨imp L p.val q.val, by simp⟩

def Semiformula.cast (p : Semiformula V L n) (eq : n = n' := by simp) : Semiformula V L n' := eq ▸ p

def Semiformula.sCast {n : ℕ} (p : Semiformula V L ↑(n + 1)) : Semiformula V L (↑n + 1) := p.cast

noncomputable def verums (k : V) : Semiformula V L n := ⟨qqVerums k, by simp⟩

@[simp] lemma Semiformula.val_cast (p : Semiformula V L n) (eq : n = n') :
    (p.cast eq).val = p.val := by rcases eq; simp [Semiformula.cast]

@[simp] lemma Semiformula.val_sCast {n : ℕ} (p : Semiformula V L ↑(n + 1)) :
    (p.sCast).val = p.val := by simp [sCast]

noncomputable def Semiformula.all (p : Semiformula V L (n + 1)) : Semiformula V L n := ⟨^∀ p.val, by simp⟩

noncomputable def Semiformula.ex (p : Semiformula V L (n + 1)) : Semiformula V L n := ⟨^∃ p.val, by simp⟩

namespace Semiformula

@[simp] lemma val_verum : (⊤ : Semiformula V L n).val = ^⊤ := rfl

@[simp] lemma val_falsum : (⊥ : Semiformula V L n).val = ^⊥ := rfl

@[simp] lemma val_and (p q : Semiformula V L n) :
    (p ⋏ q).val = p.val ^⋏ q.val := rfl

@[simp] lemma val_or (p q : Semiformula V L n) :
    (p ⋎ q).val = p.val ^⋎ q.val := rfl

@[simp] lemma val_neg (p : Semiformula V L n) :
    (∼p).val = neg L p.val := rfl

@[simp] lemma val_imp (p q : Semiformula V L n) :
    (p ➝ q).val = imp L p.val q.val := rfl

@[simp] lemma val_all (p : Semiformula V L (n + 1)) :
    p.all.val = ^∀ p.val := rfl

@[simp] lemma val_ex (p : Semiformula V L (n + 1)) :
    p.ex.val = ^∃ p.val := rfl

@[simp] lemma val_iff (p q : Semiformula V L n) :
    (p ⭤ q).val = iff L p.val q.val := rfl

lemma val_inj {p q : Semiformula V L n} :
    p.val = q.val ↔ p = q := by rcases p; rcases q; simp

@[ext] lemma ext {p q : Semiformula V L n} (h : p.val = q.val) : p = q := val_inj.mp h

@[simp] lemma and_inj {p₁ p₂ q₁ q₂ : Semiformula V L n} :
    p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [Semiformula.ext_iff]

@[simp] lemma or_inj {p₁ p₂ q₁ q₂ : Semiformula V L n} :
    p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [Semiformula.ext_iff]

@[simp] lemma all_inj {p q : Semiformula V L (n + 1)} :
    p.all = q.all ↔ p = q := by simp [Semiformula.ext_iff]

@[simp] lemma ex_inj {p q : Semiformula V L (n + 1)} :
    p.ex = q.ex ↔ p = q := by simp [Semiformula.ext_iff]

@[simp] lemma val_verums : (verums k : Semiformula V L n).val = qqVerums k := rfl

@[simp] lemma verums_zero : (verums 0 : Semiformula V L n) = ⊤ := by ext; simp

@[simp] lemma verums_succ (k : V) : (verums (k + 1) : Semiformula V L n) = ⊤ ⋏ verums k := by ext; simp

@[simp] lemma neg_verum : ∼(⊤ : Semiformula V L n) = ⊥ := by ext; simp
@[simp] lemma neg_falsum : ∼(⊥ : Semiformula V L n) = ⊤ := by ext; simp
@[simp] lemma neg_and (p q : Semiformula V L n) : ∼(p ⋏ q) = ∼p ⋎ ∼q := by ext; simp
@[simp] lemma neg_or (p q : Semiformula V L n) : ∼(p ⋎ q) = ∼p ⋏ ∼q := by ext; simp
@[simp] lemma neg_all (p : Semiformula V L (n + 1)) : ∼p.all = (∼p).ex := by ext; simp
@[simp] lemma neg_ex (p : Semiformula V L (n + 1)) : ∼p.ex = (∼p).all := by ext; simp

lemma imp_def (p q : Semiformula V L n) : p ➝ q = ∼p ⋎ q := by ext; simp [imp]

@[simp] lemma neg_neg (p : Semiformula V L n) : ∼∼p = p := by
  ext; simp [IsUFormula.neg_neg]

noncomputable def shift (p : Semiformula V L n) : Semiformula V L n := ⟨Metamath.shift L p.val, p.prop.shift⟩

noncomputable def substs (p : Semiformula V L n) (w : SemitermVec V L n m) : Semiformula V L m :=
  ⟨Metamath.substs L w.val p.val, p.prop.substs w.prop⟩

@[simp] lemma val_shift (p : Semiformula V L n) : p.shift.val = Metamath.shift L p.val := rfl
@[simp] lemma val_substs (p : Semiformula V L n) (w : SemitermVec V L n m) : (p.substs w).val = Metamath.substs L w.val p.val := rfl

@[simp] lemma shift_verum : (⊤ : Semiformula V L n).shift = ⊤ := by ext; simp [shift]
@[simp] lemma shift_falsum : (⊥ : Semiformula V L n).shift = ⊥ := by ext; simp [shift]
@[simp] lemma shift_and (p q : Semiformula V L n) : (p ⋏ q).shift = p.shift ⋏ q.shift := by ext; simp [shift]
@[simp] lemma shift_or (p q : Semiformula V L n) : (p ⋎ q).shift = p.shift ⋎ q.shift := by ext; simp [shift]
@[simp] lemma shift_all (p : Semiformula V L (n + 1)) : p.all.shift = p.shift.all := by ext; simp [shift]
@[simp] lemma shift_ex (p : Semiformula V L (n + 1)) : p.ex.shift = p.shift.ex := by ext; simp [shift]

@[simp] lemma neg_inj {p q : Semiformula V L n} :
    ∼p = ∼q ↔ p = q :=
  ⟨by intro h; simpa using congr_arg (∼·) h, by rintro rfl; rfl⟩

@[simp] lemma imp_inj {p₁ p₂ q₁ q₂ : Semiformula V L n} :
    p₁ ➝ p₂ = q₁ ➝ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [imp_def]

@[simp] lemma shift_neg (p : Semiformula V L n) : (∼p).shift = ∼(p.shift) := by
  ext; simp [shift, val_neg]; simp [Metamath.shift_neg p.prop]

@[simp] lemma shift_imp (p q : Semiformula V L n) : (p ➝ q).shift = p.shift ➝ q.shift := by
  simp [imp_def]

@[simp] lemma substs_verum (w : SemitermVec V L n m) : (⊤ : Semiformula V L n).substs w = ⊤ := by ext; simp [substs]
@[simp] lemma substs_falsum (w : SemitermVec V L n m) : (⊥ : Semiformula V L n).substs w = ⊥ := by ext; simp [substs]
@[simp] lemma substs_and (w : SemitermVec V L n m) (p q : Semiformula V L n) :
    (p ⋏ q).substs w = p.substs w ⋏ q.substs w := by ext; simp [substs]
@[simp] lemma substs_or (w : SemitermVec V L n m) (p q : Semiformula V L n) :
    (p ⋎ q).substs w = p.substs w ⋎ q.substs w := by ext; simp [substs]
@[simp] lemma substs_all (w : SemitermVec V L n m) (p : Semiformula V L (n + 1)) :
    p.all.substs w = (p.substs w.q).all := by
  ext; simp [substs, Semiterm.bvar, qVec, SemitermVec.bShift, SemitermVec.q, w.prop.lh]
@[simp] lemma substs_ex (w : SemitermVec V L n m) (p : Semiformula V L (n + 1)) :
    p.ex.substs w = (p.substs w.q).ex := by
  ext; simp [substs, Semiterm.bvar, qVec, SemitermVec.bShift, SemitermVec.q, w.prop.lh]

@[simp] lemma substs_neg (w : SemitermVec V L n m) (p : Semiformula V L n) : (∼p).substs w = ∼(p.substs w) := by
  ext; simp [substs, val_neg, Metamath.substs_neg p.prop w.prop]
@[simp] lemma substs_imp (w : SemitermVec V L n m) (p q : Semiformula V L n) : (p ➝ q).substs w = p.substs w ➝ q.substs w := by
  simp [imp_def]
@[simp] lemma substs_imply (w : SemitermVec V L n m) (p q : Semiformula V L n) : (p ⭤ q).substs w = p.substs w ⭤ q.substs w := by
  simp [LogicalConnective.iff]

end Semiformula

notation p:max "^/[" w "]" => Semiformula.substs p w

variable (L)

structure SemiformulaVec (n : V) where
  val : V
  prop : ∀ i < len val, IsSemiformula L n val.[i]

variable {L}

namespace SemiformulaVec

noncomputable def conj (ps : SemiformulaVec L n) : Semiformula V L n := ⟨^⋀ ps.val, by simpa using ps.prop⟩

noncomputable def disj (ps : SemiformulaVec L n) : Semiformula V L n := ⟨^⋁ ps.val, by simpa using ps.prop⟩

noncomputable def nth (ps : SemiformulaVec L n) (i : V) (hi : i < len ps.val) : Semiformula V L n :=
  ⟨ps.val.[i], ps.prop i hi⟩

@[simp] lemma val_conj (ps : SemiformulaVec L n) : ps.conj.val = ^⋀ ps.val := rfl

@[simp] lemma val_disj (ps : SemiformulaVec L n) : ps.disj.val = ^⋁ ps.val := rfl

@[simp] lemma val_nth (ps : SemiformulaVec L n) (i : V) (hi : i < len ps.val) :
    (ps.nth i hi).val = ps.val.[i] := rfl

end SemiformulaVec

namespace Language.TSemifromula

lemma subst_eq_self {n : V} (w : SemitermVec V L n n) (p : Semiformula V L n) (H : ∀ i, (hi : i < n) → w.nth i hi = Semiterm.bvar L i hi) :
    p^/[w] = p := by
  suffices ∀ i < n, w.val.[i] = ^#i by
    ext; simp only [Semiformula.val_substs]; rw [Metamath.subst_eq_self p.prop w.prop]; simpa
  intro i hi
  simpa using congr_arg Semiterm.val (H i hi)

@[simp] lemma subst_eq_self₁ (p : Semiformula V L (0 + 1)) :
    p^/[(Semiterm.bvar L 0 (by simp)).sing] = p := by
  apply subst_eq_self
  simp only [zero_add, lt_one_iff_eq_zero]
  rintro _ rfl
  simp

@[simp] lemma subst_nil_eq_self (w : SemitermVec V L 0 0) :
    p^/[w] = p := subst_eq_self _ _ (by simp)

lemma shift_substs {n m : V} (w : SemitermVec V L n m) (p : Semiformula V L n) :
    (p^/[w]).shift = p.shift^/[w.shift] := by ext; simp [Metamath.shift_substs p.prop w.prop]

lemma substs_substs {n m l : V} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (p : Semiformula V L n) :
    (p^/[w])^/[v] = p^/[w.substs v] := by ext; simp [Metamath.substs_substs p.prop v.prop w.prop]

end Language.TSemifromula

end typed_formula

/-
section typed_isfvfree

namespace Semiformula

def FVFree (p : Semiformula V L n) : Prop := L.IsFVFree n p.val

lemma FVFree.iff {p : Semiformula V L n} : p.FVFree ↔ p.shift = p := by
  simp [FVFree, Language.IsFVFree, ext_iff]

@[simp] lemma Fvfree.verum : (⊤ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.falsum : (⊥ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.and {p q : Semiformula V L n} :
    (p ⋏ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff, FVFree.iff]

@[simp] lemma Fvfree.or {p q : Semiformula V L n} : (p ⋎ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.neg {p : Semiformula V L n} : (∼p).FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.all {p : Semiformula V L (n + 1)} : p.all.FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.ex {p : Semiformula V L (n + 1)} : p.ex.FVFree ↔ p.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.imp {p q : Semiformula V L n} : (p ➝ q).FVFree ↔ p.FVFree ∧ q.FVFree := by
  simp [FVFree.iff]

end Semiformula

end typed_isfvfree
-/

open InternalArithmetic

noncomputable def Semiterm.equals {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^= u.val, by simp [qqEQ]⟩

noncomputable def Semiterm.notEquals {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≠ u.val, by simp [qqNEQ]⟩

noncomputable def Semiterm.lessThan {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^< u.val, by simp [qqLT]⟩

noncomputable def Semiterm.notLessThan {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≮ u.val, by simp [qqNLT]⟩

scoped infix:46 " ≐ " => Semiterm.equals

scoped infix:46 " ≉ " => Semiterm.notEquals

scoped infix:46 " <' " => Semiterm.lessThan

scoped infix:46 " ≮' " => Semiterm.notLessThan

noncomputable def Semiformula.ball {n : V} (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ((Semiterm.bvar ℒₒᵣ 0 ≮' t.bShift) ⋎ p).all

noncomputable def Semiformula.bex {n : V} (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ((Semiterm.bvar ℒₒᵣ 0 <' t.bShift) ⋏ p).ex

namespace InternalArithmetic

variable {n m : V}

@[simp] lemma val_equals {n : V} (t u : Semiterm V ℒₒᵣ n) : (t ≐ u).val = t.val ^= u.val := rfl
@[simp] lemma val_notEquals {n : V} (t u : Semiterm V ℒₒᵣ n) : (t ≉ u).val = t.val ^≠ u.val := rfl
@[simp] lemma val_lessThan {n : V} (t u : Semiterm V ℒₒᵣ n) : (t <' u).val = t.val ^< u.val := rfl
@[simp] lemma val_notLessThan {n : V} (t u : Semiterm V ℒₒᵣ n) : (t ≮' u).val = t.val ^≮ u.val := rfl

@[simp] lemma equals_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≐ u₁) = (t₂ ≐ u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqEQ]

@[simp] lemma notequals_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≉ u₁) = (t₂ ≉ u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqNEQ]

@[simp] lemma lessThan_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ <' u₁) = (t₂ <' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqLT]

@[simp] lemma notLessThan_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≮' u₁) = (t₂ ≮' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqNLT]

@[simp] lemma neg_equals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≐ t₂) = (t₁ ≉ t₂) := by
  ext; simp [Semiterm.equals, Semiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_notEquals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≉ t₂) = (t₁ ≐ t₂) := by
  ext; simp [Semiterm.equals, Semiterm.notEquals, qqEQ, qqNEQ]

@[simp] lemma neg_lessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ <' t₂) = (t₁ ≮' t₂) := by
  ext; simp [Semiterm.lessThan, Semiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma neg_notLessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≮' t₂) = (t₁ <' t₂) := by
  ext; simp [Semiterm.lessThan, Semiterm.notLessThan, qqLT, qqNLT]

@[simp] lemma shift_equals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≐ t₂).shift = (t₁.shift ≐ t₂.shift) := by
  ext; simp [Semiterm.equals, Semiterm.shift, Semiformula.shift, qqEQ]

@[simp] lemma shift_notEquals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≉ t₂).shift = (t₁.shift ≉ t₂.shift) := by
  ext; simp [Semiterm.notEquals, Semiterm.shift, Semiformula.shift, qqNEQ]

@[simp] lemma shift_lessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ <' t₂).shift = (t₁.shift <' t₂.shift) := by
  ext; simp [Semiterm.lessThan, Semiterm.shift, Semiformula.shift, qqLT]

@[simp] lemma shift_notLessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≮' t₂).shift = (t₁.shift ≮' t₂.shift) := by
  ext; simp [Semiterm.notLessThan, Semiterm.shift, Semiformula.shift, qqNLT]

@[simp] lemma substs_equals (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≐ t₂).substs w = (t₁.substs w ≐ t₂.substs w) := by
  ext; simp [Semiterm.equals, Semiterm.substs, Semiformula.substs, qqEQ]

@[simp] lemma substs_notEquals (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≉ t₂).substs w = (t₁.substs w ≉ t₂.substs w) := by
  ext; simp [Semiterm.notEquals, Semiterm.substs, Semiformula.substs, qqNEQ]

@[simp] lemma substs_lessThan (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ <' t₂).substs w = (t₁.substs w <' t₂.substs w) := by
  ext; simp [Semiterm.lessThan, Semiterm.substs, Semiformula.substs, qqLT]

@[simp] lemma substs_notLessThan (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≮' t₂).substs w = (t₁.substs w ≮' t₂.substs w) := by
  ext; simp [Semiterm.notLessThan, Semiterm.substs, Semiformula.substs, qqNLT]

@[simp] lemma val_ball {n : V} (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.ball t).val = ^∀ (^#0 ^≮ termBShift ℒₒᵣ t.val) ^⋎ p.val := by
  simp [Semiformula.ball]

@[simp] lemma val_bex {n : V} (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.bex t).val = ^∃ (^#0 ^< termBShift ℒₒᵣ t.val) ^⋏ p.val := by
  simp [Semiformula.bex]

lemma neg_ball (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(p.ball t) = (∼p).bex t := by
  ext; simp [neg_all, neg_or, qqNLT, qqLT, t.prop.termBShift.isUTerm]

lemma neg_bex (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(p.bex t) = (∼p).ball t := by
  ext; simp [neg_ex, neg_and, qqNLT, qqLT, t.prop.termBShift.isUTerm]

@[simp] lemma shifts_ball (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.ball t).shift = p.shift.ball t.shift := by
  simp [Semiformula.ball, Semiterm.bShift_shift_comm]

@[simp] lemma shifts_bex (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.bex t).shift = p.shift.bex t.shift := by
  simp [Semiformula.bex, Semiterm.bShift_shift_comm]

@[simp] lemma substs_ball (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.ball t)^/[w] = (p^/[w.q]).ball (t^ᵗ/[w]) := by
  simp [Semiformula.ball]

@[simp] lemma substs_bex (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    (p.bex t)^/[w] = (p^/[w.q]).bex (t^ᵗ/[w]) := by
  simp [Semiformula.bex]

noncomputable def tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    SemiformulaVec ℒₒᵣ m := ⟨substItr w.val p.val k, by
  intro i hi
  have : i < k := by simpa using hi
  simp only [this, substItr_nth]
  exact p.prop.substs (w.prop.cons (by simp))⟩

@[simp] lemma val_tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    (tSubstItr w p k).val = substItr w.val p.val k := by simp [tSubstItr]

@[simp] lemma len_tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    len (tSubstItr w p k).val = k := by simp

lemma nth_tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth i (by simp [hi]) = p.substs (↑(k - (i + 1)) ∷ᵗ w) := by ext; simp [tSubstItr, Semiformula.substs, hi]

lemma nth_tSubstItr' {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) {i} (hi : i < k) :
    (tSubstItr w p k).nth (k - (i + 1)) (by simpa using sub_succ_lt_self hi) = p.substs (↑i ∷ᵗ w) := by
  ext; simp [tSubstItr, Semiformula.substs, sub_succ_lt_self hi, sub_succ_lt_selfs hi]

@[simp] lemma neg_conj_tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    ∼(tSubstItr w p k).conj = (tSubstItr w (∼p) k).disj := by
  ext; simp [neg_conj_substItr p.prop w.prop]

@[simp] lemma neg_disj_tSubstItr {n m : V} (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    ∼(tSubstItr w p k).disj = (tSubstItr w (∼p) k).conj := by
  ext; simp [neg_disj_substItr p.prop w.prop]

@[simp] lemma substs_conj_tSubstItr {n m l : V} (v : SemitermVec V ℒₒᵣ m l) (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    (tSubstItr w p k).conj.substs v = (tSubstItr (w.substs v) p k).conj := by
  ext; simp [Semiformula.substs, SemitermVec.substs, substs_conj_substItr p.prop w.prop v.prop]

@[simp] lemma substs_disj_tSubstItr {n m l : V} (v : SemitermVec V ℒₒᵣ m l) (w : SemitermVec V ℒₒᵣ n m) (p : Semiformula V ℒₒᵣ (n + 1)) (k : V) :
    (tSubstItr w p k).disj.substs v = (tSubstItr (w.substs v) p k).disj := by
  ext; simp [Semiformula.substs, SemitermVec.substs, substs_disj_substItr p.prop w.prop v.prop]

end InternalArithmetic

lemma Semiformula.ball_eq_imp {n : V} (t : Semiterm V ℒₒᵣ n) (p : Semiformula V ℒₒᵣ (n + 1)) :
    p.ball t = ((Semiterm.bvar ℒₒᵣ 0 <' t.bShift) ➝ p).all := by simp [Semiformula.ball, imp_def]

end LO.ISigma1.Metamath
