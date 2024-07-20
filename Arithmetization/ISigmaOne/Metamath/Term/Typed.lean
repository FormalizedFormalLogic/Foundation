import Arithmetization.ISigmaOne.Metamath.Term.Functions

/-!

# Typed Formalized Semiterm/Term

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

/-
section typed_fin

structure TFin (n : V) where
  val : V
  prop : val < n

attribute [simp] TFin.prop

namespace TFin

variable {n : V}

lemma ext_iff {i j : TFin n} : i = j ↔ i.val = j.val := by rcases i; rcases j; simp

@[ext] lemma ext {i j : TFin n} (h : i.val = j.val) : i = j := ext_iff.mpr h

end TFin

end typed_fin
-/

section typed_term

variable (L)

structure Language.TSemiterm (n : V) where
  val : V
  prop : L.Semiterm n val

structure Language.TSemitermVec (m n : V) where
  val : V
  prop : L.SemitermVec m n val

attribute [simp] Language.TSemiterm.prop Language.TSemitermVec.prop

abbrev Language.TTerm := L.TSemiterm 0

@[ext]
lemma Language.TSemiterm.ext {t u : L.TSemiterm n}
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

@[ext]
lemma Language.TSemitermVec.ext {v w : L.TSemitermVec k n}
    (h : v.val = w.val) : v = w := by rcases v; rcases w; simpa using h

def Language.bvar {n : V} (z : V) (hz : z < n := by simp) : L.TSemiterm n := ⟨^#z, by simp [hz]⟩

def Language.fvar {n : V} (x : V) : L.TSemiterm n := ⟨^&x, by simp⟩

def Language.func {n k f : V} (hf : L.Func k f) (v : L.TSemitermVec k n) :
    L.TSemiterm n := ⟨^func k f v.val , by simp [hf]⟩

variable {L}

def Language.TSemiterm.cons {m n} (t : L.TSemiterm n) (v : L.TSemitermVec m n) :
    L.TSemitermVec (m + 1) n := ⟨t.val ∷ v.val, v.prop.cons t.prop⟩

scoped infixr:67 " ∷ᵗ " => Language.TSemiterm.cons

@[simp] lemma Language.TSemitermvec.val_cons {m n : V} (t : L.TSemiterm n) (v : L.TSemitermVec m n) :
    (t ∷ᵗ v).val = t.val ∷ v.val := by simp [Language.TSemiterm.cons]

variable (L)

def Language.TSemitermVec.nil (n) : L.TSemitermVec 0 n := ⟨0, by simp⟩

variable {L}

@[simp] lemma Language.TSemitermvec.val_nil (n : V) :
    (Language.TSemitermVec.nil L n).val = 0 := rfl

abbrev Language.TSemiterm.sing {n} (t : L.TSemiterm n) : L.TSemitermVec (0 + 1) n := t ∷ᵗ .nil L n

namespace Language.TSemiterm

def shift (t : L.TSemiterm n) : L.TSemiterm n :=
  ⟨L.termShift n t.val, Language.Semiterm.termShift t.prop⟩

def bShift (t : L.TSemiterm n) : L.TSemiterm (n + 1) :=
  ⟨L.termBShift n t.val, Language.Semiterm.termBShift t.prop⟩

def substs (t : L.TSemiterm n) (w : L.TSemitermVec n m) : L.TSemiterm m :=
  ⟨L.termSubst n m w.val t.val, termSubst_rng_semiterm w.prop t.prop⟩

end Language.TSemiterm

namespace Language.TSemitermVec

def shift (v : L.TSemitermVec k n) : L.TSemitermVec k n :=
  ⟨L.termShiftVec k n v.val, Language.SemitermVec.termShiftVec v.prop⟩

def bShift (v : L.TSemitermVec k n) : L.TSemitermVec k (n + 1) :=
  ⟨L.termBShiftVec k n v.val, Language.SemitermVec.termBShiftVec v.prop⟩

def substs (v : L.TSemitermVec k n) (w : L.TSemitermVec n m) : L.TSemitermVec k m :=
  ⟨L.termSubstVec k n m w.val v.val, Language.SemitermVec.termSubstVec w.prop v.prop⟩


@[simp] lemma bShift_nil (n : V) :
    (nil L n).bShift = nil L (n + 1) := by
  ext; simp [bShift]

@[simp] lemma bShift_cons (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).bShift = t.bShift ∷ᵗ v.bShift := by
  ext; simp [bShift, Language.TSemiterm.bShift, termBShiftVec_cons t.prop v.prop]

@[simp] lemma shift_nil (n : V) :
    (nil L n).shift = nil L n := by
  ext; simp [shift]

@[simp] lemma shift_cons (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).shift = t.shift ∷ᵗ v.shift := by
  ext; simp [shift, Language.TSemiterm.shift, termShiftVec_cons t.prop v.prop]

@[simp] lemma substs_nil (w : L.TSemitermVec n m) :
    (nil L n).substs w = nil L m := by
  ext; simp [substs]

@[simp] lemma substs_cons (w : L.TSemitermVec n m) (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).substs w = t.substs w ∷ᵗ v.substs w := by
  ext; simp [substs, Language.TSemiterm.substs, termSubstVec_cons t.prop v.prop]

def nth (t : L.TSemitermVec k n) (i : V) (hi : i < k := by simp) : L.TSemiterm n :=
  ⟨t.val.[i], t.prop.prop hi⟩

@[simp] lemma nth_zero (t : L.TSemiterm n) (v : L.TSemitermVec k n) : (t ∷ᵗ v).nth 0 = t := by ext; simp [nth]

@[simp] lemma nth_succ (t : L.TSemiterm n) (v : L.TSemitermVec k n) (i : V) (hi : i < k) :
    (t ∷ᵗ v).nth (i + 1) (by simp [hi]) = v.nth i hi := by ext; simp [nth]

@[simp] lemma nth_one (t : L.TSemiterm n) (v : L.TSemitermVec (k + 1) n)  :
    (t ∷ᵗ v).nth 1 (by simp) = v.nth 0 (by simp) := by ext; simp [nth]

lemma nth_of_pos (t : L.TSemiterm n) (v : L.TSemitermVec k n) (i : V) (ipos : 0 < i) (hi : i < k + 1) :
    (t ∷ᵗ v).nth i (by simp [hi]) = v.nth (i - 1) (tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi) := by
  ext; simp only [nth, TSemitermvec.val_cons]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp

def q (w : L.TSemitermVec k n) : L.TSemitermVec (k + 1) (n + 1) := L.bvar (0 : V) ∷ᵗ w.bShift

@[simp] lemma q_zero (w : L.TSemitermVec k n) : w.q.nth 0 = L.bvar 0 := by simp [q]

@[simp] lemma q_succ (w : L.TSemitermVec k n) {i} (hi : i < k) :
    w.q.nth (i + 1) (by simp [hi]) = (w.nth i hi).bShift := by
  simp only [q, gt_iff_lt, hi, nth_succ]
  ext; simp [bShift, nth, Language.TSemiterm.bShift, hi]

lemma q_of_pos (w : L.TSemitermVec k n) (i) (ipos : 0 < i) (hi : i < k + 1) :
    w.q.nth i (by simp [hi]) = (w.nth (i - 1) (tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi)).bShift := by
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp [q_succ w (by simpa using hi)]

@[simp] lemma q_val_eq_qVec (w : L.TSemitermVec k n) : w.q.val = L.qVec k n w.val := by simp [q, Language.qVec, Language.bvar, bShift]

end Language.TSemitermVec

namespace Language.TSemiterm

@[simp] lemma shift_bvar {z n : V} (hz : z < n) :
    shift (L.bvar z hz) = L.bvar z hz := by ext; simp [Language.bvar, shift, hz]

@[simp] lemma shift_fvar (x : V) :
    shift (L.fvar x : L.TSemiterm n) = L.fvar (x + 1) := by ext; simp [Language.fvar, shift]

@[simp] lemma shift_func {k f} (hf : L.Func k f) (v : L.TSemitermVec k n) :
    shift (L.func hf v) = L.func hf v.shift := by ext; simp [Language.func, shift, TSemitermVec.shift, hf]

@[simp] lemma bShift_bvar {z n : V} (hz : z < n) :
    bShift (L.bvar z hz) = L.bvar (z + 1) (by simpa using hz) := by ext; simp [Language.bvar, bShift, hz]

@[simp] lemma bShift_fvar (x : V) :
    bShift (L.fvar x : L.TSemiterm n) = L.fvar x := by ext; simp [Language.fvar, bShift]

@[simp] lemma bShift_func {k f} (hf : L.Func k f) (v : L.TSemitermVec k n) :
    bShift (L.func hf v) = L.func hf v.bShift := by ext; simp [Language.func, bShift, TSemitermVec.bShift, hf]

@[simp] lemma substs_bvar {z m : V} (w : L.TSemitermVec n m) (hz : z < n) :
    (L.bvar z hz).substs w = w.nth z hz := by ext; simp [Language.bvar, substs, hz, Language.TSemitermVec.nth]

@[simp] lemma substs_fvar (w : L.TSemitermVec n m) (x : V) :
    (L.fvar x : L.TSemiterm n).substs w = L.fvar x := by ext; simp [Language.fvar, substs]

@[simp] lemma substs_func {k f} (w : L.TSemitermVec n m) (hf : L.Func k f) (v : L.TSemitermVec k n) :
    (L.func hf v).substs w = L.func hf (v.substs w) := by
  ext; simp [Language.func, substs, TSemitermVec.substs, hf]

@[simp] lemma bShift_substs_q (t : L.TSemiterm n) (w : L.TSemitermVec n m) :
    t.bShift.substs w.q = (t.substs w).bShift := by
  ext; simp only [substs, TSemitermVec.q_val_eq_qVec, bShift, prop, TSemitermVec.prop, substs_qVec_bShift]

@[simp] lemma bShift_substs_sing (t u : L.TTerm) :
    t.bShift.substs u.sing = t := by
  ext; simp [substs, bShift]
  rw [show (1 : V) = 0 + 1 by simp, substs_cons_bShift] <;> simp

end Language.TSemiterm

end typed_term

namespace Formalized

def typedNumeral (n m : V) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨numeral m, by simp⟩

def add {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩

def mul {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨t.val ^* u.val, by simp [qqMul]⟩

instance (n : V) : Add (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨add⟩

instance (n : V) : Mul (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨mul⟩

instance (n : V) : Coe V (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨typedNumeral n⟩

variable {n : V}

@[simp] lemma val_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).val = numeral x := rfl

@[simp] lemma val_add (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl

@[simp] lemma val_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl

@[simp] lemma subst_numeral {m n : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (x : V) :
    (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).substs w = ↑x := by
  ext; simp [Language.TSemiterm.substs]

@[simp] lemma subst_add {m n : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ + t₂).substs w = t₁.substs w + t₂.substs w := by
  ext; simp [qqAdd, Language.TSemiterm.substs]

@[simp] lemma subst_mul {m n : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ * t₂).substs w = t₁.substs w * t₂.substs w := by
  ext; simp [qqMul, Language.TSemiterm.substs]

@[simp] lemma shift_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).shift = ↑x := by
  ext; simp [Language.TSemiterm.shift]

@[simp] lemma shift_add (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ + t₂).shift = t₁.shift + t₂.shift := by
  ext; simp [qqAdd, Language.TSemiterm.shift]

@[simp] lemma shift_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ * t₂).shift = t₁.shift * t₂.shift := by
  ext; simp [qqMul, Language.TSemiterm.shift]

@[simp] lemma bShift_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).bShift = ↑x := by
  ext; simp [Language.TSemiterm.bShift]

@[simp] lemma bShift_add (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ + t₂).bShift = t₁.bShift + t₂.bShift := by
  ext; simp [qqAdd, Language.TSemiterm.bShift]

@[simp] lemma bShift_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ * t₂).bShift = t₁.bShift * t₂.bShift := by
  ext; simp [qqMul, Language.TSemiterm.bShift]

end Formalized

end LO.Arith
