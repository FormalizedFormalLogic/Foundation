import Arithmetization.ISigmaOne.Metamath.Term.Functions

/-!

# Typed Formalized IsSemiterm/Term

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

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
  prop : L.IsSemiterm n val

structure Language.TSemitermVec (m n : V) where
  val : V
  prop : L.IsSemitermVec m n val

attribute [simp] Language.TSemiterm.prop Language.TSemitermVec.prop

abbrev Language.TTerm := L.TSemiterm 0

@[ext]
lemma Language.TSemiterm.ext {t u : L.TSemiterm n}
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

lemma Language.TSemiterm.ext_iff {t u : L.TSemiterm n} : t = u ↔ t.val = u.val := by rcases t; rcases u; simp

@[simp] lemma Language.TSemiterm.isUTerm (t : L.TSemiterm n) : L.IsUTerm t.val := t.prop.isUTerm

@[simp] lemma Language.TSemitermVec.isUTerm (v : L.TSemitermVec k n) : L.IsUTermVec k v.val := v.prop.isUTerm

@[ext]
lemma Language.TSemitermVec.ext {v w : L.TSemitermVec k n}
    (h : v.val = w.val) : v = w := by rcases v; rcases w; simpa using h

def Language.bvar {n : V} (z : V) (hz : z < n := by simp) : L.TSemiterm n := ⟨^#z, by simp [hz]⟩

def Language.fvar {n : V} (x : V) : L.TSemiterm n := ⟨^&x, by simp⟩

def Language.func {n k f : V} (hf : L.Func k f) (v : L.TSemitermVec k n) :
    L.TSemiterm n := ⟨^func k f v.val , by simp [hf]⟩

variable {L}

abbrev bv {n : V} (x : V) (h : x < n := by simp) : L.TSemiterm n := L.bvar x h
abbrev fv {n : V} (x : V) : L.TSemiterm n := L.fvar x

scoped prefix:max "#'" => bv
scoped prefix:max "&'" => fv

@[simp] lemma Language.val_bvar {n : V} (z : V) (hz : z < n) : (L.bvar z hz).val = ^#z := rfl
@[simp] lemma Language.val_fvar {n : V} (x : V) : (L.fvar x : L.TSemiterm n).val = ^&x := rfl

def Language.TSemiterm.cons {m n} (t : L.TSemiterm n) (v : L.TSemitermVec m n) :
    L.TSemitermVec (m + 1) n := ⟨t.val ∷ v.val, by simp⟩

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
  ⟨L.termShift t.val, Language.IsSemiterm.termShift t.prop⟩

def bShift (t : L.TSemiterm n) : L.TSemiterm (n + 1) :=
  ⟨L.termBShift t.val, Language.IsSemiterm.termBShift t.prop⟩

def substs (t : L.TSemiterm n) (w : L.TSemitermVec n m) : L.TSemiterm m :=
  ⟨L.termSubst w.val t.val, w.prop.termSubst t.prop⟩

@[simp] lemma val_shift (t : L.TSemiterm n) : t.shift.val = L.termShift t.val := rfl
@[simp] lemma val_bShift (t : L.TSemiterm n) : t.bShift.val = L.termBShift t.val := rfl
@[simp] lemma val_substs (w : L.TSemitermVec n m) (t : L.TSemiterm n) : (t.substs w).val = L.termSubst w.val t.val := rfl

end Language.TSemiterm

notation t:max "^ᵗ/[" w "]" => Language.TSemiterm.substs t w

namespace Language.TSemitermVec

def shift (v : L.TSemitermVec k n) : L.TSemitermVec k n :=
  ⟨L.termShiftVec k v.val, Language.IsSemitermVec.termShiftVec v.prop⟩

def bShift (v : L.TSemitermVec k n) : L.TSemitermVec k (n + 1) :=
  ⟨L.termBShiftVec k v.val, Language.IsSemitermVec.termBShiftVec v.prop⟩

def substs (v : L.TSemitermVec k n) (w : L.TSemitermVec n m) : L.TSemitermVec k m :=
  ⟨L.termSubstVec k w.val v.val, Language.IsSemitermVec.termSubstVec w.prop v.prop⟩

@[simp] lemma val_shift (v : L.TSemitermVec k n) : v.shift.val = L.termShiftVec k v.val := rfl
@[simp] lemma val_bShift (v : L.TSemitermVec k n) : v.bShift.val = L.termBShiftVec k v.val := rfl
@[simp] lemma val_substs (v : L.TSemitermVec k n) (w : L.TSemitermVec n m) : (v.substs w).val = L.termSubstVec k w.val v.val := rfl

@[simp] lemma bShift_nil (n : V) :
    (nil L n).bShift = nil L (n + 1) := by
  ext; simp [bShift]

@[simp] lemma bShift_cons (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).bShift = t.bShift ∷ᵗ v.bShift := by
  ext; simp [bShift, Language.TSemiterm.bShift, termBShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma shift_nil (n : V) :
    (nil L n).shift = nil L n := by
  ext; simp [shift]

@[simp] lemma shift_cons (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).shift = t.shift ∷ᵗ v.shift := by
  ext; simp [shift, Language.TSemiterm.shift, termShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma substs_nil (w : L.TSemitermVec n m) :
    (nil L n).substs w = nil L m := by
  ext; simp [substs]

@[simp] lemma substs_cons (w : L.TSemitermVec n m) (t : L.TSemiterm n) (v : L.TSemitermVec k n) :
    (t ∷ᵗ v).substs w = t.substs w ∷ᵗ v.substs w := by
  ext; simp [substs, Language.TSemiterm.substs, termSubstVec_cons t.prop.isUTerm v.prop.isUTerm]

def nth (t : L.TSemitermVec k n) (i : V) (hi : i < k := by simp) : L.TSemiterm n :=
  ⟨t.val.[i], t.prop.nth hi⟩

@[simp] lemma nth_val (v : L.TSemitermVec k n) (i : V) (hi : i < k) : (v.nth i hi).val = v.val.[i] := by simp [nth]

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

@[simp] lemma q_one (w : L.TSemitermVec k n) (h : 0 < k) : w.q.nth 1 (by simp [h]) = (w.nth 0 h).bShift := by
  simpa using q_succ w h

lemma q_of_pos (w : L.TSemitermVec k n) (i) (ipos : 0 < i) (hi : i < k + 1) :
    w.q.nth i (by simp [hi]) = (w.nth (i - 1) (tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi)).bShift := by
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp [q_succ w (by simpa using hi)]

@[simp] lemma q_val_eq_qVec (w : L.TSemitermVec k n) : w.q.val = L.qVec k w.val := by simp [q, Language.qVec, Language.bvar, bShift]

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
  ext; simp only [substs, TSemitermVec.q_val_eq_qVec, bShift, prop, TSemitermVec.prop, substs_qVec_bShift t.prop w.prop]

@[simp] lemma bShift_substs_sing (t u : L.TTerm) :
    t.bShift.substs u.sing = t := by
  ext; simp [substs, bShift]
  rw [substs_cons_bShift t.prop]; simp

lemma bShift_shift_comm (t : L.TSemiterm n) :
    t.shift.bShift = t.bShift.shift := by
  ext; simp [termBShift_termShift t.prop]

end Language.TSemiterm

end typed_term

section typed_isfvfree

namespace Language.TSemiterm

def FVFree (t : L.TSemiterm n) : Prop := L.IsTermFVFree n t.val

lemma FVFree.iff {t : L.TSemiterm n} : t.FVFree ↔ t.shift = t := by
  simp [FVFree, Language.IsTermFVFree, ext_iff]

@[simp] lemma FVFree.bvar (z : V) (h : z < n) : (L.bvar z h).FVFree := by simp [FVFree, h]

@[simp] lemma FVFree.bShift (t : L.TSemiterm n) (ht : t.FVFree) :
    t.bShift.FVFree := by simp [FVFree.iff, ←bShift_shift_comm, FVFree.iff.mp ht]

end Language.TSemiterm

end typed_isfvfree

namespace Formalized

def typedNumeral (n m : V) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨numeral m, by simp⟩

def add {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩

def mul {n : V} (t u : ⌜ℒₒᵣ⌝.TSemiterm n) : ⌜ℒₒᵣ⌝.TSemiterm n := ⟨t.val ^* u.val, by simp [qqMul]⟩

instance (n : V) : Add (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨add⟩

instance (n : V) : Mul (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨mul⟩

instance coeNumeral (n : V) : Coe V (⌜ℒₒᵣ⌝.TSemiterm n) := ⟨typedNumeral n⟩

variable {n : V}

@[simp] lemma val_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).val = numeral x := rfl

@[simp] lemma val_add (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl

@[simp] lemma val_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl

@[simp] lemma add_inj_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TSemiterm n} :
    t₁ + t₂ = u₁ + u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Language.TSemiterm.ext_iff, qqAdd]

@[simp] lemma mul_inj_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TSemiterm n} :
    t₁ * t₂ = u₁ * u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Language.TSemiterm.ext_iff, qqMul]

@[simp] lemma subst_numeral {m n : V} (w : ⌜ℒₒᵣ⌝.TSemitermVec n m) (x : V) :
    (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).substs w = ↑x := by
  ext; simp [Language.TSemiterm.substs, numeral_substs w.prop]

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

@[simp] lemma fvFree_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.TSemiterm n).FVFree := by simp [Language.TSemiterm.FVFree.iff]

@[simp] lemma fvFree_add (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ + t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Language.TSemiterm.FVFree.iff]

@[simp] lemma fvFree_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.TSemiterm n) :
    (t₁ * t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Language.TSemiterm.FVFree.iff]

/-
lemma replace {P : α → Prop} {x y} (hx : P x) (h : x = y) : P y := h ▸ hx

lemma semiterm_induction (Γ) {n : V} {P : ⌜ℒₒᵣ⌝.TSemiterm n → Prop}
    (hP : Γ-[1]-Predicate (fun x ↦ (h : ⌜ℒₒᵣ⌝.IsSemiterm n x) → P ⟨x, h⟩))
    (hBvar : ∀ (z : V) (h : z < n), P (⌜ℒₒᵣ⌝.bvar z h))
    (hFvar : ∀ x, P (⌜ℒₒᵣ⌝.fvar x))
    (hZero : P ((0 : V) : ⌜ℒₒᵣ⌝.TSemiterm n))
    (hOne : P ((1 : V) : ⌜ℒₒᵣ⌝.TSemiterm n))
    (hAdd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂))
    (hMul : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ * t₂)) :
    ∀ (t : ⌜ℒₒᵣ⌝[V].TSemiterm n), P t := by
  let Q := fun x ↦ (h : ⌜ℒₒᵣ⌝.IsSemiterm n x) → P ⟨x, h⟩
  suffices ∀ t, ⌜ℒₒᵣ⌝.IsSemiterm n t → Q t by intro t; exact this t.val t.prop t.prop
  apply Language.IsSemiterm.induction Γ hP
  case hbvar => intro z hz _; exact hBvar z hz
  case hfvar => intro x _; exact hFvar x
  case hfunc =>
    intro k f v hf hv ih _
    rcases (by simpa [func_iff] using hf) with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases (by simpa using hv)
      exact replace hZero (by ext; simp [Formalized.zero, qqFunc_absolute])
    · rcases (by simpa using hv)
      exact replace hOne (by ext; simp [Formalized.one, qqFunc_absolute])
    · rcases Language.IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hAdd ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
    · rcases Language.IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hMul ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
-/

end Formalized

end LO.Arith
