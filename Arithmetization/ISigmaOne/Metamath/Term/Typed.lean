import Arithmetization.ISigmaOne.Metamath.Term.Functions

/-!

# Typed Formalized Semiterm/Term

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section typed_term

variable (L)

structure Language.TSemiterm (n : V) where
  val : V
  prop : L.Semiterm n val

structure Language.TSemitermVec (m n : V) where
  val : V
  prop : L.SemitermVec m n val

attribute [simp] Language.TSemiterm.prop Language.TSemitermVec.prop

abbrev Language.FTerm := L.TSemiterm 0

@[ext]
lemma Language.TSemiterm.ext {t u : L.TSemiterm n}
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

@[ext]
lemma Language.TSemitermVec.ext {v w : L.TSemitermVec k n}
    (h : v.val = w.val) : v = w := by rcases v; rcases w; simpa using h

def Language.bvar {n : V} (z : V) (hz : z < n) : L.TSemiterm n := ⟨^#z, by simp [hz]⟩

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

def nth (t : L.TSemitermVec k n) (i : V) (hi : i < k) : L.TSemiterm n :=
  ⟨t.val.[i], t.prop.prop hi⟩

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
