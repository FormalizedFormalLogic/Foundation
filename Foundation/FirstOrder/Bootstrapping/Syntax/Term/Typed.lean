module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Functions

@[expose] public section
/-!

# Typed Formalized IsSemiterm/Term

-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def matrixToVec (v : Fin k → V) : V := Matrix.foldr (fun t w ↦ t ∷ w) 0 v

@[simp] lemma matrixToVec_nil (v : Fin 0 → V) : matrixToVec v = 0 := rfl

@[simp] lemma matrixToVec_succ (v : Fin (k + 1) → V) : matrixToVec v = Matrix.vecHead v ∷ matrixToVec (Matrix.vecTail v) := rfl

@[simp] lemma matrixToVec_len (v : Fin k → V) : len (matrixToVec v) = k := by
  induction k <;> simp [*]

@[simp] lemma matrixToVec_nth (v : Fin k → V) (i : Fin k) : (matrixToVec v).[↑i] = v i := by
  induction k
  · exact i.elim0
  · cases i using Fin.cases
    · simp; rfl
    · simp [*]; rfl

namespace Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]

section typed_term

variable (V L)

structure Semiterm (n : ℕ) where
  val : V
  isSemiterm : IsSemiterm (V := V) L n val

abbrev SemitermVec (m n : ℕ) := Fin m → Semiterm V L (n : ℕ)

attribute [simp] Semiterm.isSemiterm

abbrev Term := Semiterm (V := V) L 0

abbrev TermVec (m : ℕ) := SemitermVec (V := V) L m 0

variable {V L} {k n m : ℕ}

@[ext]
lemma Semiterm.ext (t u : Semiterm V L n)
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

@[simp] lemma Semiterm.isSemiterm_zero (t : Term V L) :
   IsSemiterm L 0 t.val := by simpa using t.isSemiterm

@[simp] lemma Semiterm.isSemiterm_one (t : Semiterm V L 1) :
   IsSemiterm L 1 t.val := by simpa using t.isSemiterm

@[simp] lemma Semiterm.isSemiterm_succ (t : Semiterm V L (n + 1)) :
    IsSemiterm L (↑n + 1 : V) t.val := by simpa using t.isSemiterm

@[simp] lemma Semiterm.isUTerm (t : Semiterm V L n) : IsUTerm L t.val := t.isSemiterm.isUTerm

noncomputable def SemitermVec.val (v : SemitermVec V L k n) : V := matrixToVec ((fun t ↦ t.val)⨟ v)

@[simp] lemma SemitermVec.val_nil (v : SemitermVec V L 0 n) : v.val = 0 := rfl

@[simp] lemma SemitermVec.val_cons (t : Semiterm V L n) (v : SemitermVec V L k n) :
    SemitermVec.val (t :> v : SemitermVec V L (k + 1) n) = t.val ∷ v.val := by rfl

@[simp] lemma SemitermVec.val_succ (v : SemitermVec V L (k + 1) n) :
    SemitermVec.val (v : SemitermVec V L (k + 1) n) = (Matrix.vecHead v).val ∷ SemitermVec.val (Matrix.vecTail v) := by rfl

lemma SemitermVec.val_inj (v₁ v₂ : SemitermVec V L k n) : v₁ = v₂ ↔ v₁.val = v₂.val := by
    induction k
    · simp [Matrix.empty_eq]
    case succ k ih =>
      simp [← Semiterm.ext_iff, ←ih, Matrix.eq_iff_eq_vecHead_of_eq_vecTail]

@[simp] lemma SemitermVec.isSemitermVec {k} (v : SemitermVec V L k n) : IsSemitermVec (V := V) L k n v.val := by
  induction k <;> simp [*]

@[simp] lemma SemitermVec.isUTermVec {k} (v : SemitermVec V L k n) : IsUTermVec (V := V) L k v.val := by
  induction k <;> simp [*]

@[simp] lemma SemitermVec.len_eq (v : SemitermVec V L k n) : len v.val = ↑k := by
  induction k <;> simp [*]

@[simp] lemma SemitermVec.val_nth_eq (v : SemitermVec V L k n) (i : Fin k) :
    v.val.[(i : V)] = (v i).val := by
  induction k
  · apply finZeroElim i
  · cases i using Fin.cases
    · simp; rfl
    · simp [*]; rfl

noncomputable def Semiterm.bvar (z : Fin n) : Semiterm V L n := ⟨^#z, by simp⟩

noncomputable def Semiterm.fvar (x : V) : Semiterm V L n := ⟨^&x, by simp⟩

noncomputable def Semiterm.func (f : L.Func k) (v : SemitermVec V L k n) :
    Semiterm V L n := ⟨^func ↑k ⌜f⌝ v.val , by simp⟩
noncomputable abbrev Semiterm.bv (x : Fin n) : Semiterm V L n := Semiterm.bvar x
noncomputable abbrev Semiterm.fv (x : V) : Semiterm V L n := Semiterm.fvar x

@[simp] lemma Semiterm.bvar_val (z : Fin n) : (Semiterm.bvar z : Semiterm V L n).val = ^#(z : V) := rfl
@[simp] lemma Semiterm.fvar_val (x : V) : (Semiterm.fvar x : Semiterm V L n).val = ^&x := rfl
@[simp] lemma Semiterm.func_val (f : L.Func k) (v : SemitermVec V L k n) :
    (Semiterm.func f v).val = ^func ↑k ⌜f⌝ v.val := rfl


namespace Semiterm

@[simp] lemma bvar_inj_iff (z x : Fin n) :
    (bvar z : Semiterm V L n) = bvar x ↔ z = x := ⟨by simpa [bvar] using Fin.eq_of_val_eq, by rintro rfl; rfl⟩

@[simp] lemma fvar_inj_iff (z x : V) : (fvar z : Semiterm V L n) = fvar x ↔ z = x := by simp [fvar]

@[simp] lemma func_inj_iff (f₁ f₂ : L.Func k) (v₁ v₂ : SemitermVec V L k n) : func f₁ v₁ = func f₂ v₂ ↔ f₁ = f₂ ∧ v₁ = v₂ := by
  simp only [func, Semiterm.ext_iff, qqFunc_inj, quote_func_inj, true_and, and_congr_right_iff]
  rintro rfl
  symm; exact SemitermVec.val_inj v₁ v₂

noncomputable def shift (t : Semiterm V L n) : Semiterm V L n :=
  ⟨termShift L t.val, IsSemiterm.termShift t.isSemiterm⟩

noncomputable def bShift (t : Semiterm V L n) : Semiterm V L (n + 1) :=
  ⟨termBShift L t.val, IsSemiterm.termBShift t.isSemiterm⟩

noncomputable def subst (w : SemitermVec V L n m) (t : Semiterm V L n) : Semiterm V L m :=
  ⟨termSubst L w.val t.val, w.isSemitermVec.termSubst t.isSemiterm⟩

noncomputable def free (t : Semiterm V L 1) : Semiterm V L 0 :=
  t.shift.subst ![fvar 0]

@[simp] lemma val_shift (t : Semiterm V L n) : t.shift.val = termShift L t.val := rfl
@[simp] lemma val_bShift (t : Semiterm V L n) : t.bShift.val = termBShift L t.val := rfl
@[simp] lemma val_substs (w : SemitermVec V L n m) (t : Semiterm V L n) : (t.subst w).val = termSubst L w.val t.val := rfl

end Semiterm

namespace SemitermVec

@[simp] lemma val_shift (v : SemitermVec V L k n) : val (Semiterm.shift⨟ v) = termShiftVec L ↑k v.val := by
  induction k <;> simp [termShiftVec_cons, *]

@[simp] lemma val_bShift (v : SemitermVec V L k n) : val (Semiterm.bShift⨟ v) = termBShiftVec L ↑k v.val := by
  induction k <;> simp [termBShiftVec_cons, *]

@[simp] lemma val_substs (v : SemitermVec V L k n) (w : SemitermVec V L n m) :
    val ((Semiterm.subst w)⨟ v) = termSubstVec L ↑k w.val v.val := by
  induction k <;> simp [termSubstVec_cons, *]

noncomputable def q (w : SemitermVec V L k n) : SemitermVec V L (k + 1) (n + 1) := Semiterm.bvar 0 :> Semiterm.bShift⨟ w

@[simp] lemma q_zero (w : SemitermVec V L k n) : w.q 0 = Semiterm.bvar 0 := rfl

@[simp] lemma q_succ (w : SemitermVec V L k n) (i : Fin k) : w.q i.succ = Semiterm.bShift (w i) := rfl

@[simp] lemma q_val_eq_qVec (w : SemitermVec V L k n) : w.q.val = qVec L w.val := by simp [q, qVec]

@[simp] lemma q_vecHead (w : SemitermVec V L k n) : Matrix.vecHead w.q = Semiterm.bvar 0 := rfl

@[simp] lemma q_vecTail (w : SemitermVec V L k n) : Matrix.vecTail w.q = Semiterm.bShift⨟ w := rfl

end SemitermVec

namespace Semiterm

@[simp] lemma shift_bvar (z : Fin n) :
    shift (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z := by ext; simp [Semiterm.bvar, shift]

@[simp] lemma shift_fvar (x : V) :
    shift (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar (x + 1) := by ext; simp [Semiterm.fvar, shift]

@[simp] lemma shift_func (f : L.Func k) (v : SemitermVec V L k n) :
    shift (func f v) = func f (shift⨟ v) := by ext; simp [Semiterm.func, shift]

@[simp] lemma bShift_bvar (z : Fin n) :
    bShift (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z.succ := by ext; simp [Semiterm.bvar, bShift]

@[simp] lemma bShift_fvar (x : V) :
    bShift (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar x := by ext; simp [Semiterm.fvar, bShift]

@[simp] lemma bShift_func (f : L.Func k) (v : SemitermVec V L k n) :
    bShift (func f v) = func f (bShift⨟ v) := by ext; simp [Semiterm.func, bShift]

@[simp] lemma substs_bvar (z : Fin n) (w : SemitermVec V L n m) :
    (Semiterm.bvar z).subst w = w z := by ext; simp [subst]

@[simp] lemma substs_fvar (w : SemitermVec V L n m) (x : V) :
    (Semiterm.fvar x : Semiterm V L n).subst w = Semiterm.fvar x := by ext; simp [Semiterm.fvar, subst]

@[simp] lemma substs_func (f : L.Func k) (w : SemitermVec V L n m) (v : SemitermVec V L k n) :
    (func f v).subst w = func f ((subst w)⨟ v) := by ext; simp [Semiterm.func, subst]

@[simp] lemma free_bvar (z : Fin 1) : free (bvar z : Semiterm V L 1) = fvar 0 := by simp [free]

@[simp] lemma free_fvar (x : V) : free (Semiterm.fvar x : Semiterm V L 1) = fvar (x + 1) := by simp [free]

@[simp] lemma bShift_substs_q (t : Semiterm V L n) (w : SemitermVec V L n m) :
    t.bShift.subst w.q = (t.subst w).bShift := by
  ext; simp only [subst, SemitermVec.q_val_eq_qVec, bShift, substs_qVec_bShift t.isSemiterm w.isSemitermVec]

@[simp] lemma bShift_substs_sing (t u : Term V L) :
    t.bShift.subst ![u] = t := by
  ext; simp [subst, bShift, substs_cons_bShift t.isSemiterm, substs_nil t.isSemiterm]

lemma bShift_substs_succ (w : SemitermVec V L (n + 1) m) (t : Semiterm V L n) :
    t.bShift.subst w = t.subst (Matrix.vecTail w) := by
  ext; simp [subst, bShift, substs_cons_bShift t.isSemiterm]

@[simp] lemma bShift_substs_zero (t : Term V L) :
    t.subst ![] = t := by
  ext; simp [subst]

lemma bShift_shift_comm (t : Semiterm V L n) :
    t.shift.bShift = t.bShift.shift := by
  ext; simp [termBShift_termShift t.isSemiterm]

lemma shift_substs (w : SemitermVec V L n m) (t : Semiterm V L n) :
    (t.subst w).shift = t.shift.subst (Semiterm.shift⨟ w) := by ext; simp [Bootstrapping.termShift_termSubsts t.isSemiterm w.isSemitermVec]

lemma substs_substs {n m l : ℕ} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (t : Semiterm V L n) :
    (t.subst w).subst v = t.subst ((Semiterm.subst v)⨟ w) := by
  ext;simp [Bootstrapping.termSubst_termSubst w.isSemitermVec t.isSemiterm]

end Semiterm

end typed_term

section typed_isfvfree

variable {k n m : ℕ}

namespace Semiterm

def FVFree (t : Semiterm V L n) : Prop := IsTermFVFree L ↑n t.val

lemma FVFree.iff {t : Semiterm V L n} : t.FVFree ↔ t.shift = t := by
  simp [FVFree, IsTermFVFree, Semiterm.ext_iff]

@[simp] lemma FVFree.bvar (i : Fin n) : (Semiterm.bvar i : Semiterm V L n).FVFree := by simp [FVFree]

@[simp] lemma FVFree.bShift (t : Semiterm V L n) (ht : t.FVFree) :
    t.bShift.FVFree := by simp [FVFree.iff, ←bShift_shift_comm, FVFree.iff.mp ht]

end Semiterm

end typed_isfvfree

namespace Arithmetic

variable {k n m : ℕ}

noncomputable def typedNumeral (m : V) : Semiterm V ℒₒᵣ n := ⟨numeral m, by simp⟩

scoped prefix:max "𝕹" => typedNumeral

noncomputable def add (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩

noncomputable def mul (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^* u.val, by simp [qqMul]⟩

noncomputable instance (n : ℕ) : Add (Semiterm V ℒₒᵣ n) := ⟨add⟩

noncomputable instance (n : ℕ) : Mul (Semiterm V ℒₒᵣ n) := ⟨mul⟩

@[simp] lemma val_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).val = numeral x := rfl

@[simp] lemma val_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl

@[simp] lemma val_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl

@[simp] lemma zero_eq (v) :
    Semiterm.func (V := V) (n := n) (Language.Zero.zero : (ℒₒᵣ).Func 0) v = typedNumeral 0 := by
  ext; simp [coe_zero_eq]

@[simp] lemma one_eq (v) :
    Semiterm.func (V := V) (n := n) (Language.One.one : (ℒₒᵣ).Func 0) v = typedNumeral 1 := by
  ext; simp [coe_one_eq]

@[simp] lemma add_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiterm.func (Language.Add.add : (ℒₒᵣ).Func 2) v = v 0 + v 1 := by
  ext; rfl

@[simp] lemma mul_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiterm.func (Language.Mul.mul : (ℒₒᵣ).Func 2) v = v 0 * v 1 := by
  ext; rfl

@[simp] lemma add_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ + t₂ = u₁ + u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqAdd]

@[simp] lemma mul_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ * t₂ = u₁ * u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqMul]

@[simp] lemma numeral_add_two' (x : V) :
    (typedNumeral (x + 1 + 1) : Semiterm V ℒₒᵣ n) = typedNumeral (x + 1) + typedNumeral 1 := by
  ext; simp [numeral]

lemma numeral_succ_pos' {x : V} (pos : 0 < x) :
    (typedNumeral (x + 1) : Semiterm V ℒₒᵣ n) = typedNumeral x + typedNumeral 1 := by
  ext; simp [numeral_succ_pos pos]

@[simp] lemma subst_numeral (w : SemitermVec V ℒₒᵣ n m) (x : V) :
    (𝕹 x : Semiterm V ℒₒᵣ n).subst w = 𝕹 x := by
  ext; simp [Semiterm.subst, numeral_substs w.isSemitermVec]

@[simp] lemma subst_add (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).subst w = t₁.subst w + t₂.subst w := by
  ext; simp [qqAdd, Semiterm.subst]

@[simp] lemma subst_mul (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).subst w = t₁.subst w * t₂.subst w := by
  ext; simp [qqMul, Semiterm.subst]

@[simp] lemma shift_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).shift = 𝕹 x := by
  ext; simp [Semiterm.shift]

@[simp] lemma shift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).shift = t₁.shift + t₂.shift := by
  ext; simp [qqAdd, Semiterm.shift]

@[simp] lemma shift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).shift = t₁.shift * t₂.shift := by
  ext; simp [qqMul, Semiterm.shift]

@[simp] lemma bShift_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).bShift = 𝕹 x := by
  ext; simp [Semiterm.bShift]

@[simp] lemma bShift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).bShift = t₁.bShift + t₂.bShift := by
  ext; simp [qqAdd, Semiterm.bShift]

@[simp] lemma bShift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).bShift = t₁.bShift * t₂.bShift := by
  ext; simp [qqMul, Semiterm.bShift]

@[simp] lemma fvFree_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).FVFree := by simp [Semiterm.FVFree.iff]

@[simp] lemma fvFree_add (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]

@[simp] lemma fvFree_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]

@[simp] lemma free_add (t₁ t₂ : Semiterm V ℒₒᵣ 1) : (t₁ + t₂).free = t₁.free + t₂.free := by
  simp [Semiterm.free]

@[simp] lemma free_mul (t₁ t₂ : Semiterm V ℒₒᵣ 1) : (t₁ * t₂).free = t₁.free * t₂.free := by
  simp [Semiterm.free]

@[simp] lemma free_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ 1).free = 𝕹 x := by simp [Semiterm.free]

/-
lemma replace {P : α → isSemiterm} {x y} (hx : P x) (h : x = y) : P y := h ▸ hx

lemma semiterm_induction (Γ) {n : V} {P : Semiterm V ℒₒᵣ n → isSemiterm}
    (hP : Γ-[1]-Predicate (fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩))
    (hBvar : ∀ (z : V) (h : z < n), P (bvar ℒₒᵣ z h))
    (hFvar : ∀ x, P (⌜ℒₒᵣ⌝.fvar x))
    (hZero : P ((0 : V) : Semiterm V ℒₒᵣ n))
    (hOne : P ((1 : V) : Semiterm V ℒₒᵣ n))
    (hAdd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂))
    (hMul : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ * t₂)) :
    ∀ (t : ⌜ℒₒᵣ⌝[V].Semiterm n), P t := by
  let Q := fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩
  suffices ∀ t, IsSemiterm ℒₒᵣ n t → Q t by intro t; exact this t.val t.isSemiterm t.isSemiterm
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

end LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
