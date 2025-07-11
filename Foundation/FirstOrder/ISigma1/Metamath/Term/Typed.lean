import Foundation.FirstOrder.ISigma1.Metamath.Term.Functions

/-!

# Typed Formalized IsSemiterm/Term

-/

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

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

variable (V L)

structure Semiterm (n : V) where
  val : V
  prop : IsSemiterm L n val

structure SemitermVec (m n : V) where
  val : V
  prop : IsSemitermVec L m n val

attribute [simp] Semiterm.prop SemitermVec.prop

abbrev Term := Semiterm (V := V) L 0

variable {V} {n k : V}

@[ext]
lemma Semiterm.ext {n : V} {t u : Semiterm V L n}
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

@[simp] lemma Semiterm.isUTerm {n : V} (t : Semiterm V L n) : IsUTerm L t.val := t.prop.isUTerm

@[simp] lemma SemitermVec.isUTerm {k n : V} (v : SemitermVec V L k n) : IsUTermVec L k v.val := v.prop.isUTerm

@[ext]
lemma SemitermVec.ext {v w : SemitermVec V L k n}
    (h : v.val = w.val) : v = w := by rcases v; rcases w; simpa using h

noncomputable def Semiterm.bvar {n : V} (z : V) (hz : z < n := by simp) : Semiterm V L n := ⟨^#z, by simp [hz]⟩

noncomputable def Semiterm.fvar {n : V} (x : V) : Semiterm V L n := ⟨^&x, by simp⟩

variable {L}

noncomputable def Semiterm.func {n k f : V} (hf : L.IsFunc k f) (v : SemitermVec V L k n) :
    Semiterm V L n := ⟨^func k f v.val , by simp [hf]⟩

noncomputable abbrev Semiterm.bv {n : V} (x : V) (h : x < n := by simp) : Semiterm V L n := Semiterm.bvar L x h
noncomputable abbrev Semiterm.fv {n : V} (x : V) : Semiterm V L n := Semiterm.fvar L x

@[simp] lemma Semiterm.val_bvar {n : V} (z : V) (hz : z < n) : (Semiterm.bvar L z hz).val = ^#z := rfl
@[simp] lemma Semiterm.val_fvar {n : V} (x : V) : (Semiterm.fvar L x : Semiterm V L n).val = ^&x := rfl

noncomputable def Semiterm.cons {m n : V} (t : Semiterm V L n) (v : SemitermVec V L m n) :
    SemitermVec V L (m + 1) n := ⟨t.val ∷ v.val, by simp⟩

scoped infixr:67 " ∷ᵗ " => Semiterm.cons

@[simp] lemma SemitermVec.val_cons {m n : V} (t : Semiterm V L n) (v : SemitermVec V L m n) :
    (t ∷ᵗ v).val = t.val ∷ v.val := by simp [Semiterm.cons]

variable (L)

def SemitermVec.nil (n : V) : SemitermVec V L 0 n := ⟨0, by simp⟩

variable {L}

@[simp] lemma SemitermVec.val_nil (n : V) :
    (SemitermVec.nil L n).val = 0 := rfl

noncomputable abbrev Semiterm.sing {n : V} (t : Semiterm V L n) : SemitermVec V L (0 + 1) n := t ∷ᵗ .nil L n

namespace Semiterm

noncomputable def shift (t : Semiterm V L n) : Semiterm V L n :=
  ⟨termShift L t.val, IsSemiterm.termShift t.prop⟩

noncomputable def bShift (t : Semiterm V L n) : Semiterm V L (n + 1) :=
  ⟨termBShift L t.val, IsSemiterm.termBShift t.prop⟩

noncomputable def substs (t : Semiterm V L n) (w : SemitermVec V L n m) : Semiterm V L m :=
  ⟨termSubst L w.val t.val, w.prop.termSubst t.prop⟩

@[simp] lemma val_shift (t : Semiterm V L n) : t.shift.val = termShift L t.val := rfl
@[simp] lemma val_bShift (t : Semiterm V L n) : t.bShift.val = termBShift L t.val := rfl
@[simp] lemma val_substs (w : SemitermVec V L n m) (t : Semiterm V L n) : (t.substs w).val = termSubst L w.val t.val := rfl

end Semiterm

notation t:max "^ᵗ/[" w "]" => Semiterm.substs t w

namespace SemitermVec

noncomputable def shift (v : SemitermVec V L k n) : SemitermVec V L k n :=
  ⟨termShiftVec L k v.val, IsSemitermVec.termShiftVec v.prop⟩

noncomputable def bShift (v : SemitermVec V L k n) : SemitermVec V L k (n + 1) :=
  ⟨termBShiftVec L k v.val, IsSemitermVec.termBShiftVec v.prop⟩

noncomputable def substs (v : SemitermVec V L k n) (w : SemitermVec V L n m) : SemitermVec V L k m :=
  ⟨termSubstVec L k w.val v.val, IsSemitermVec.termSubstVec w.prop v.prop⟩

@[simp] lemma val_shift (v : SemitermVec V L k n) : v.shift.val = termShiftVec L k v.val := rfl
@[simp] lemma val_bShift (v : SemitermVec V L k n) : v.bShift.val = termBShiftVec L k v.val := rfl
@[simp] lemma val_substs (v : SemitermVec V L k n) (w : SemitermVec V L n m) : (v.substs w).val = termSubstVec L k w.val v.val := rfl

@[simp] lemma bShift_nil (n : V) :
    (nil L n).bShift = nil L (n + 1) := by
  ext; simp [bShift]

@[simp] lemma bShift_cons (t : Semiterm V L n) (v : SemitermVec V L k n) :
    (t ∷ᵗ v).bShift = t.bShift ∷ᵗ v.bShift := by
  ext; simp [bShift, Semiterm.bShift, termBShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma shift_nil (n : V) :
    (nil L n).shift = nil L n := by
  ext; simp [shift]

@[simp] lemma shift_cons (t : Semiterm V L n) (v : SemitermVec V L k n) :
    (t ∷ᵗ v).shift = t.shift ∷ᵗ v.shift := by
  ext; simp [shift, Semiterm.shift, termShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma substs_nil (w : SemitermVec V L n m) :
    (nil L n).substs w = nil L m := by
  ext; simp [substs]

@[simp] lemma substs_cons (w : SemitermVec V L n m) (t : Semiterm V L n) (v : SemitermVec V L k n) :
    (t ∷ᵗ v).substs w = t.substs w ∷ᵗ v.substs w := by
  ext; simp [substs, Semiterm.substs, termSubstVec_cons t.prop.isUTerm v.prop.isUTerm]

noncomputable def nth (t : SemitermVec V L k n) (i : V) (hi : i < k := by simp) : Semiterm V L n :=
  ⟨t.val.[i], t.prop.nth hi⟩

@[simp] lemma nth_val (v : SemitermVec V L k n) (i : V) (hi : i < k) : (v.nth i hi).val = v.val.[i] := by simp [nth]

@[simp] lemma nth_zero (t : Semiterm V L n) (v : SemitermVec V L k n) : (t ∷ᵗ v).nth 0 = t := by ext; simp [nth]

@[simp] lemma nth_succ (t : Semiterm V L n) (v : SemitermVec V L k n) (i : V) (hi : i < k) :
    (t ∷ᵗ v).nth (i + 1) (by simp [hi]) = v.nth i hi := by ext; simp [nth]

@[simp] lemma nth_one (t : Semiterm V L n) (v : SemitermVec V L (k + 1) n)  :
    (t ∷ᵗ v).nth 1 (by simp) = v.nth 0 (by simp) := by ext; simp [nth]

lemma nth_of_pos (t : Semiterm V L n) (v : SemitermVec V L k n) (i : V) (ipos : 0 < i) (hi : i < k + 1) :
    (t ∷ᵗ v).nth i (by simp [hi]) = v.nth (i - 1) (PeanoMinus.tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi) := by
  ext; simp only [nth, SemitermVec.val_cons]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp

noncomputable def q (w : SemitermVec V L k n) : SemitermVec V L (k + 1) (n + 1) := Semiterm.bvar L (0 : V) ∷ᵗ w.bShift

@[simp] lemma q_zero (w : SemitermVec V L k n) : w.q.nth 0 = Semiterm.bvar L 0 := by simp [q]

@[simp] lemma q_succ (w : SemitermVec V L k n) {i} (hi : i < k) :
    w.q.nth (i + 1) (by simp [hi]) = (w.nth i hi).bShift := by
  simp only [q, hi, nth_succ]
  ext; simp [bShift, nth, Semiterm.bShift, hi]

@[simp] lemma q_one (w : SemitermVec V L k n) (h : 0 < k) : w.q.nth 1 (by simp [h]) = (w.nth 0 h).bShift := by
  simpa using q_succ w h

lemma q_of_pos (w : SemitermVec V L k n) (i) (ipos : 0 < i) (hi : i < k + 1) :
    w.q.nth i (by simp [hi]) = (w.nth (i - 1) (PeanoMinus.tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi)).bShift := by
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp [q_succ w (by simpa using hi)]

@[simp] lemma q_val_eq_qVec (w : SemitermVec V L k n) : w.q.val = qVec L w.val := by simp [q, qVec, Semiterm.bvar, bShift, w.prop.lh]

end SemitermVec

namespace Semiterm

@[simp] lemma shift_bvar {z n : V} (hz : z < n) :
    shift (Semiterm.bvar L z hz) = Semiterm.bvar L z hz := by ext; simp [Semiterm.bvar, shift]

@[simp] lemma shift_fvar (x : V) :
    shift (Semiterm.fvar L x : Semiterm V L n) = Semiterm.fvar L (x + 1) := by ext; simp [Semiterm.fvar, shift]

@[simp] lemma shift_func {k f : V} (hf : L.IsFunc k f) (v : SemitermVec V L k n) :
    shift (func hf v) = func hf v.shift := by ext; simp [Semiterm.func, shift, SemitermVec.shift, hf]

@[simp] lemma bShift_bvar {z n : V} (hz : z < n) :
    bShift (Semiterm.bvar L z hz) = Semiterm.bvar L (z + 1) (by simpa using hz) := by ext; simp [Semiterm.bvar, bShift]

@[simp] lemma bShift_fvar (x : V) :
    bShift (Semiterm.fvar L x : Semiterm V L n) = Semiterm.fvar L x := by ext; simp [Semiterm.fvar, bShift]

@[simp] lemma bShift_func {k f : V} (hf : L.IsFunc k f) (v : SemitermVec V L k n) :
    bShift (func hf v) = func hf v.bShift := by ext; simp [Semiterm.func, bShift, SemitermVec.bShift, hf]

@[simp] lemma substs_bvar {z m : V} (w : SemitermVec V L n m) (hz : z < n) :
    (Semiterm.bvar L z hz).substs w = w.nth z hz := by ext; simp [Semiterm.bvar, substs, SemitermVec.nth]

@[simp] lemma substs_fvar (w : SemitermVec V L n m) (x : V) :
    (Semiterm.fvar L x : Semiterm V L n).substs w = Semiterm.fvar L x := by ext; simp [Semiterm.fvar, substs]

@[simp] lemma substs_func {k f : V} (w : SemitermVec V L n m) (hf : L.IsFunc k f) (v : SemitermVec V L k n) :
    (func hf v).substs w = func hf (v.substs w) := by
  ext; simp [Semiterm.func, substs, SemitermVec.substs, hf]

@[simp] lemma bShift_substs_q (t : Semiterm V L n) (w : SemitermVec V L n m) :
    t.bShift.substs w.q = (t.substs w).bShift := by
  ext; simp only [substs, SemitermVec.q_val_eq_qVec, bShift, substs_qVec_bShift t.prop w.prop]

@[simp] lemma bShift_substs_sing (t u : Term V L) :
    t.bShift.substs u.sing = t := by
  ext; simp [substs, bShift, substs_cons_bShift t.prop]

lemma bShift_shift_comm (t : Semiterm V L n) :
    t.shift.bShift = t.bShift.shift := by
  ext; simp [termBShift_termShift t.prop]

end Semiterm

end typed_term

section typed_isfvfree

namespace Semiterm

variable {n k : V}

def FVFree (t : Semiterm V L n) : Prop := IsTermFVFree L n t.val

lemma FVFree.iff {t : Semiterm V L n} : t.FVFree ↔ t.shift = t := by
  simp [FVFree, IsTermFVFree, Semiterm.ext_iff]

@[simp] lemma FVFree.bvar (z : V) (h : z < n) : (Semiterm.bvar L z h).FVFree := by simp [FVFree, h]

@[simp] lemma FVFree.bShift (t : Semiterm V L n) (ht : t.FVFree) :
    t.bShift.FVFree := by simp [FVFree.iff, ←bShift_shift_comm, FVFree.iff.mp ht]

end Semiterm

end typed_isfvfree

namespace InternalArithmetic

noncomputable def typedNumeral (n m : V) : Semiterm V ℒₒᵣ n := ⟨numeral m, by simp⟩

noncomputable def add {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩

noncomputable def mul {n : V} (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^* u.val, by simp [qqMul]⟩

noncomputable instance (n : V) : Add (Semiterm V ℒₒᵣ n) := ⟨add⟩

noncomputable instance (n : V) : Mul (Semiterm V ℒₒᵣ n) := ⟨mul⟩

noncomputable instance coeNumeral (n : V) : Coe V (Semiterm V ℒₒᵣ n) := ⟨typedNumeral n⟩

variable {n : V}

@[simp] lemma val_numeral (x : V) : (↑x : Semiterm V ℒₒᵣ n).val = numeral x := rfl

@[simp] lemma val_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl

@[simp] lemma val_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl

@[simp] lemma add_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ + t₂ = u₁ + u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqAdd]

@[simp] lemma mul_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ * t₂ = u₁ * u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqMul]

@[simp] lemma numeral_add_two' (x : V) :
    typedNumeral n (x + 1 + 1) = typedNumeral n (x + 1) + typedNumeral n 1 := by
  ext; simp [numeral]

lemma numeral_succ_pos' {x : V} (pos : 0 < x) :
    typedNumeral n (x + 1) = typedNumeral n x + typedNumeral n 1 := by
  ext; simp [numeral_succ_pos pos]

@[simp] lemma subst_numeral {m n : V} (w : SemitermVec V ℒₒᵣ n m) (x : V) :
    (↑x : Semiterm V ℒₒᵣ n).substs w = ↑x := by
  ext; simp [Semiterm.substs, numeral_substs w.prop]

@[simp] lemma subst_add {m n : V} (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).substs w = t₁.substs w + t₂.substs w := by
  ext; simp [qqAdd, Semiterm.substs]

@[simp] lemma subst_mul {m n : V} (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).substs w = t₁.substs w * t₂.substs w := by
  ext; simp [qqMul, Semiterm.substs]

@[simp] lemma shift_numeral (x : V) : (↑x : Semiterm V ℒₒᵣ n).shift = ↑x := by
  ext; simp [Semiterm.shift]

@[simp] lemma shift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).shift = t₁.shift + t₂.shift := by
  ext; simp [qqAdd, Semiterm.shift]

@[simp] lemma shift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).shift = t₁.shift * t₂.shift := by
  ext; simp [qqMul, Semiterm.shift]

@[simp] lemma bShift_numeral (x : V) : (↑x : Semiterm V ℒₒᵣ n).bShift = ↑x := by
  ext; simp [Semiterm.bShift]

@[simp] lemma bShift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).bShift = t₁.bShift + t₂.bShift := by
  ext; simp [qqAdd, Semiterm.bShift]

@[simp] lemma bShift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).bShift = t₁.bShift * t₂.bShift := by
  ext; simp [qqMul, Semiterm.bShift]

@[simp] lemma fvFree_numeral (x : V) : (↑x : Semiterm V ℒₒᵣ n).FVFree := by simp [Semiterm.FVFree.iff]

@[simp] lemma fvFree_add (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]

@[simp] lemma fvFree_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]

/-
lemma replace {P : α → Prop} {x y} (hx : P x) (h : x = y) : P y := h ▸ hx

lemma semiterm_induction (Γ) {n : V} {P : Semiterm V ℒₒᵣ n → Prop}
    (hP : Γ-[1]-Predicate (fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩))
    (hBvar : ∀ (z : V) (h : z < n), P (bvar ℒₒᵣ z h))
    (hFvar : ∀ x, P (⌜ℒₒᵣ⌝.fvar x))
    (hZero : P ((0 : V) : Semiterm V ℒₒᵣ n))
    (hOne : P ((1 : V) : Semiterm V ℒₒᵣ n))
    (hAdd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂))
    (hMul : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ * t₂)) :
    ∀ (t : ⌜ℒₒᵣ⌝[V].Semiterm n), P t := by
  let Q := fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩
  suffices ∀ t, IsSemiterm ℒₒᵣ n t → Q t by intro t; exact this t.val t.prop t.prop
  apply IsSemiterm.induction Γ hP
  case hbvar => intro z hz _; exact hBvar z hz
  case hfvar => intro x _; exact hFvar x
  case hfunc =>
    intro k f v hf hv ih _
    rcases (by simpa [func_iff] using hf) with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases (by simpa using hv)
      exact replace hZero (by ext; simp [Formalized.zero, qqFunc_absolute])
    · rcases (by simpa using hv)
      exact replace hOne (by ext; simp [Formalized.one, qqFunc_absolute])
    · rcases IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hAdd ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
    · rcases IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hMul ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
-/

end LO.ISigma1.Metamath.InternalArithmetic
