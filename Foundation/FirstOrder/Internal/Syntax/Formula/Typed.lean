import Foundation.FirstOrder.Internal.Term.Typed
import Foundation.FirstOrder.Internal.Formula.Iteration

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

structure Semiformula (n : ℕ) where
  val : V
  isSemiformula : IsSemiformula L ↑n val

attribute [simp] Semiformula.isSemiformula

abbrev Formula := Semiformula (V := V) L 0

variable {L V}

variable {k n m : ℕ}

@[simp] lemma Semiformula.isSemiformula_zero (φ : Formula V L) :
    IsSemiformula L 0 φ.val := by simpa using φ.isSemiformula

@[simp] lemma Semiformula.isSemiformula_one (φ : Semiformula V L 1) :
    IsSemiformula L 1 φ.val := by simpa using φ.isSemiformula

@[simp] lemma Semiformula.isSemiformula_succ (φ : Semiformula V L (n + 1)) :
    IsSemiformula L (↑n + 1 : V) φ.val := by simpa using φ.isSemiformula

@[simp] lemma Semiformula.isUFormula (φ : Semiformula V L n) : IsUFormula L φ.val := φ.isSemiformula.isUFormula

noncomputable def Semiformula.rel (R : L.Rel k) (v : SemitermVec V L k n) : Semiformula V L n := ⟨^rel ↑k ⌜R⌝ v.val, by simp⟩

noncomputable def Semiformula.nrel (R : L.Rel k) (v : SemitermVec V L k n) : Semiformula V L n := ⟨^nrel ↑k ⌜R⌝ v.val, by simp⟩

@[simp] lemma Semiformula.rel_val (R : L.Rel k) (v : SemitermVec V L k n) :
    (Semiformula.rel R v).val = ^rel ↑k ⌜R⌝ v.val := rfl

@[simp] lemma Semiformula.nrel_val (R : L.Rel k) (v : SemitermVec V L k n) :
    (Semiformula.nrel R v).val = ^nrel ↑k ⌜R⌝ v.val := rfl

noncomputable scoped instance : LogicalConnective (Semiformula V L n) where
  top := ⟨^⊤, by simp⟩
  bot := ⟨^⊥, by simp⟩
  wedge (φ ψ) := ⟨φ.val ^⋏ ψ.val, by simp⟩
  vee (φ ψ) := ⟨φ.val ^⋎ ψ.val, by simp⟩
  tilde (φ) := ⟨neg L φ.val, by simp⟩
  arrow (φ ψ) := ⟨imp L φ.val ψ.val, by simp⟩

noncomputable instance : LCWQ (Semiformula V L) where
  connectives := inferInstance
  univ φ := ⟨^∀ φ.val, by simp⟩
  ex φ := ⟨^∃ φ.val, by simp⟩

noncomputable def verums (k : V) : Semiformula V L n := ⟨qqVerums k, by simp⟩

namespace Semiformula

@[simp] lemma val_verum : (⊤ : Semiformula V L n).val = ^⊤ := rfl

@[simp] lemma val_falsum : (⊥ : Semiformula V L n).val = ^⊥ := rfl

@[simp] lemma val_and (φ ψ : Semiformula V L n) :
    (φ ⋏ ψ).val = φ.val ^⋏ ψ.val := rfl

@[simp] lemma val_or (φ ψ : Semiformula V L n) :
    (φ ⋎ ψ).val = φ.val ^⋎ ψ.val := rfl

@[simp] lemma val_neg (φ : Semiformula V L n) :
    (∼φ).val = neg L φ.val := rfl

@[simp] lemma val_imp (φ ψ : Semiformula V L n) :
    (φ ➝ ψ).val = imp L φ.val ψ.val := rfl

@[simp] lemma val_all (φ : Semiformula V L (n + 1)) :
    (∀' φ).val = ^∀ φ.val := rfl

@[simp] lemma val_ex (φ : Semiformula V L (n + 1)) :
    (∃' φ).val = ^∃ φ.val := rfl

@[simp] lemma val_iff (φ ψ : Semiformula V L n) :
    (φ ⭤ ψ).val = iff L φ.val ψ.val := rfl

lemma val_inj {φ ψ : Semiformula V L n} :
    φ.val = ψ.val ↔ φ = ψ := by rcases φ; rcases ψ; simp

@[ext] lemma ext {φ ψ : Semiformula V L n} (h : φ.val = ψ.val) : φ = ψ := val_inj.mp h

@[simp] lemma and_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Semiformula.ext_iff]

@[simp] lemma or_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Semiformula.ext_iff]

@[simp] lemma all_inj {φ ψ : Semiformula V L (n + 1)} :
    ∀' φ = ∀' ψ ↔ φ = ψ := by simp [Semiformula.ext_iff]

@[simp] lemma ex_inj {φ ψ : Semiformula V L (n + 1)} :
    ∃' φ = ∃' ψ ↔ φ = ψ := by simp [Semiformula.ext_iff]

@[simp] lemma val_verums (k : V) : (verums k : Semiformula V L n).val = qqVerums k := rfl

@[simp] lemma verums_zero : (verums 0 : Semiformula V L n) = ⊤ := by ext; simp

@[simp] lemma verums_succ (k : V) : (verums (k + 1) : Semiformula V L n) = ⊤ ⋏ verums k := by ext; simp

instance : DeMorgan (Semiformula V L n) where
  verum := by ext; simp
  falsum := by ext; simp
  and _ _ := by ext; simp
  or _ _ := by ext; simp
  imply _ _ := by ext; simp; rfl
  neg _ := by ext; simp

@[simp] lemma neg_all (φ : Semiformula V L (n + 1)) : ∼(∀' φ) = ∃' (∼φ) := by ext; simp
@[simp] lemma neg_ex (φ : Semiformula V L (n + 1)) : ∼(∃' φ) = ∀' (∼φ) := by ext; simp

@[simp] lemma neg_rel (R : L.Rel k) (v : SemitermVec V L k n) :
    ∼Semiformula.rel R v = Semiformula.nrel R v := by ext; simp
@[simp] lemma neg_nrel (R : L.Rel k) (v : SemitermVec V L k n) :
    ∼Semiformula.nrel R v = Semiformula.rel R v := by ext; simp

lemma imp_def (φ ψ : Semiformula V L n) : φ ➝ ψ = ∼φ ⋎ ψ := by ext; simp [imp]

noncomputable def shift (φ : Semiformula V L n) : Semiformula V L n := ⟨Metamath.shift L φ.val, φ.isSemiformula.shift⟩

noncomputable def substs (w : SemitermVec V L n m) (φ : Semiformula V L n) : Semiformula V L m :=
  ⟨Metamath.substs L w.val φ.val, φ.isSemiformula.substs w.isSemitermVec⟩

@[simp] lemma val_shift (φ : Semiformula V L n) : φ.shift.val = Metamath.shift L φ.val := rfl
@[simp] lemma val_substs (φ : Semiformula V L n) (w : SemitermVec V L n m) : (φ.substs w).val = Metamath.substs L w.val φ.val := rfl

@[simp] lemma shift_verum : (⊤ : Semiformula V L n).shift = ⊤ := by ext; simp [shift]
@[simp] lemma shift_falsum : (⊥ : Semiformula V L n).shift = ⊥ := by ext; simp [shift]
@[simp] lemma shift_and (φ ψ : Semiformula V L n) : (φ ⋏ ψ).shift = φ.shift ⋏ ψ.shift := by ext; simp [shift]
@[simp] lemma shift_or (φ ψ : Semiformula V L n) : (φ ⋎ ψ).shift = φ.shift ⋎ ψ.shift := by ext; simp [shift]
@[simp] lemma shift_all (φ : Semiformula V L (n + 1)) : (∀' φ).shift = ∀' φ.shift := by ext; simp [shift]
@[simp] lemma shift_ex (φ : Semiformula V L (n + 1)) : (∃' φ).shift = ∃' φ.shift := by ext; simp [shift]
@[simp] lemma shift_rel (R : L.Rel k) (v : SemitermVec V L k n) : (rel R v).shift = rel R (Semiterm.shift⨟ v) := by ext; simp
@[simp] lemma shift_nrel (R : L.Rel k) (v : SemitermVec V L k n) : (nrel R v).shift = nrel R (Semiterm.shift⨟ v) := by ext; simp

@[simp] lemma neg_inj {φ ψ : Semiformula V L n} :
    ∼φ = ∼ψ ↔ φ = ψ :=
  ⟨by intro h; simpa using congr_arg (∼·) h, by rintro rfl; rfl⟩

@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_def]

@[simp] lemma shift_neg (φ : Semiformula V L n) : (∼φ).shift = ∼(φ.shift) := by
  ext; simp [shift, val_neg]; simp [Metamath.shift_neg φ.isSemiformula]

@[simp] lemma shift_imp (φ ψ : Semiformula V L n) : (φ ➝ ψ).shift = φ.shift ➝ ψ.shift := by
  simp [imp_def]
@[simp] lemma shift_iff (φ ψ : Semiformula V L n) : (φ ⭤ ψ).shift = φ.shift ⭤ ψ.shift := by
  simp [LogicalConnective.iff]

@[simp] lemma substs_verum (w : SemitermVec V L n m) : (⊤ : Semiformula V L n).substs w = ⊤ := by ext; simp [substs]
@[simp] lemma substs_falsum (w : SemitermVec V L n m) : (⊥ : Semiformula V L n).substs w = ⊥ := by ext; simp [substs]
@[simp] lemma substs_and (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) :
    (φ ⋏ ψ).substs w = φ.substs w ⋏ ψ.substs w := by ext; simp [substs]
@[simp] lemma substs_or (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) :
    (φ ⋎ ψ).substs w = φ.substs w ⋎ ψ.substs w := by ext; simp [substs]
@[simp] lemma substs_all (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∀' φ).substs w = ∀' (φ.substs w.q) := by
  ext; simp [substs, Semiterm.bvar, qVec, SemitermVec.q, w.isSemitermVec.lh]
@[simp] lemma substs_ex (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∃' φ).substs w = ∃' (φ.substs w.q) := by
  ext; simp [substs, Semiterm.bvar, qVec, SemitermVec.q, w.isSemitermVec.lh]
@[simp] lemma substs_rel (w : SemitermVec V L n m) (R : L.Rel k) (v : SemitermVec V L k n) :
    (rel R v).substs w = rel R ((Semiterm.substs w)⨟ v) := by ext; simp
@[simp] lemma substs_nrel (w : SemitermVec V L n m) (R : L.Rel k) (v : SemitermVec V L k n) :
    (nrel R v).substs w = nrel R ((Semiterm.substs w)⨟ v) := by ext; simp

@[simp] lemma substs_neg (w : SemitermVec V L n m) (φ : Semiformula V L n) : (∼φ).substs w = ∼(φ.substs w) := by
  ext; simp [substs, val_neg, Metamath.substs_neg φ.isSemiformula w.isSemitermVec]
@[simp] lemma substs_imp (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) : (φ ➝ ψ).substs w = φ.substs w ➝ ψ.substs w := by
  simp [imp_def]
@[simp] lemma substs_imply (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) : (φ ⭤ ψ).substs w = φ.substs w ⭤ ψ.substs w := by
  simp [LogicalConnective.iff]

@[simp] lemma substs_ball (t) (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∀[t] φ).substs w = ∀[t.substs w.q] (φ.substs w.q) := by
  simp [ball]
@[simp] lemma substs_bex (t) (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∃[t] φ).substs w = ∃[t.substs w.q] (φ.substs w.q) := by
  simp [bex]

lemma subst_eq_self {n : ℕ} (w : SemitermVec V L n n) (φ : Semiformula V L n) (H : ∀ i, w i = Semiterm.bvar i) :
    φ.substs w = φ := by
  suffices ∀ i < ↑n, w.val.[i] = ^#i by
    ext; simp only [Semiformula.val_substs]; rw [Metamath.subst_eq_self φ.isSemiformula w.isSemitermVec]; simpa
  intro i hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simpa using congr_arg Semiterm.val <| H i

@[simp] lemma subst_eq_self₁ (φ : Semiformula V L 1) :
    φ.substs ![Semiterm.bvar 0] = φ := by
  apply subst_eq_self
  simp [Fin.fin_one_eq_zero]

@[simp] lemma subst_nil_eq_self (w : SemitermVec V L 0 0) (φ : Semiformula V L 0) :
    φ.substs w = φ := subst_eq_self _ _ (by simp)

lemma shift_substs (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    (φ.substs w).shift = φ.shift.substs (Semiterm.shift⨟ w) := by ext; simp [Metamath.shift_substs φ.isSemiformula w.isSemitermVec]

lemma substs_substs {n m l : ℕ} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    (φ.substs w).substs v = φ.substs ((Semiterm.substs v)⨟ w) := by
  ext; simp [Metamath.substs_substs φ.isSemiformula v.isSemitermVec w.isSemitermVec]

noncomputable def free (φ : Semiformula V L 1) : Formula V L := φ.shift.substs ![Semiterm.fvar 0]

@[simp] lemma free_val (φ : Semiformula V L 1) : φ.free.val = Metamath.free L φ.val := by
  simp [free]; rfl

noncomputable def free1 (φ : Semiformula V L 2) : Semiformula V L 1 := φ.shift.substs ![Semiterm.fvar 0, Semiterm.bvar 0]

@[simp] lemma free1_val (φ : Semiformula V L 2) : φ.free1.val = Metamath.free1 L φ.val := by
  simp [free1]; rfl

open InternalArithmetic

noncomputable def substItrConj (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) : Semiformula V ℒₒᵣ n :=
  ⟨^⋀ InternalArithmetic.substItr w.val φ.val z, by
    have : IsSemiformula ℒₒᵣ (↑m + 1 : V) φ.val := by simp
    exact this.substItrConj w.isSemitermVec z⟩

noncomputable def substItrDisj (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) : Semiformula V ℒₒᵣ n :=
  ⟨^⋁ InternalArithmetic.substItr w.val φ.val z, by
    have : IsSemiformula ℒₒᵣ (↑m + 1 : V) φ.val := by simp
    exact this.substItrDisj w.isSemitermVec z⟩

@[simp] lemma substItrConj_val (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).val = ^⋀ InternalArithmetic.substItr w.val φ.val z := rfl

@[simp] lemma substItrDisj_val (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).val = ^⋁ InternalArithmetic.substItr w.val φ.val z := rfl

@[simp] lemma substItrConj_zero (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrConj w 0 = ⊤ := by ext; simp

@[simp] lemma substItrConj_succ (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    φ.substItrConj w (z + 1) = φ.substs (typedNumeral z :> w) ⋏ φ.substItrConj w z := by ext; simp

@[simp] lemma substItrConj_one (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrConj w 1 = φ.substs (typedNumeral 0 :> w) ⋏ ⊤ := by
  simpa using substItrConj_succ w φ 0

@[simp] lemma substItrDisj_zero (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrDisj w 0 = ⊥ := by ext; simp

@[simp] lemma substItrDisj_succ (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    φ.substItrDisj w (z + 1) = φ.substs (typedNumeral z :> w) ⋎ φ.substItrDisj w z := by ext; simp

@[simp] lemma substItrDisj_one (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrDisj w 1 = φ.substs (typedNumeral 0 :> w) ⋎ ⊥ := by
  simpa using substItrDisj_succ w φ 0

@[simp] lemma substItrConj_neg (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    ∼(φ.substItrConj w z) = (∼φ).substItrDisj w z := by
  ext; simp [substItrConj, substItrDisj, neg_conj_substItr φ.isSemiformula w.isSemitermVec]

@[simp] lemma substItrDisj_neg (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    ∼(φ.substItrDisj w z) = (∼φ).substItrConj w z := by
  ext; simp [substItrConj, substItrDisj, neg_disj_substItr φ.isSemiformula w.isSemitermVec]

@[simp] lemma substItrConj_substs (v : SemitermVec V ℒₒᵣ n k) (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).substs v = φ.substItrConj ((Semiterm.substs v)⨟ w) z := by
  ext; simp only [substItrConj, val_substs, SemitermVec.val_substs]
  rw [substs_conj_substItr φ.isSemiformula w.isSemitermVec v.isSemitermVec]; rfl

@[simp] lemma substItrDisj_substs (v : SemitermVec V ℒₒᵣ n k) (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).substs v = φ.substItrDisj ((Semiterm.substs v)⨟ w) z := by
  ext; simp only [substItrDisj, val_substs, SemitermVec.val_substs]
  rw [substs_disj_substItr φ.isSemiformula w.isSemitermVec v.isSemitermVec]; rfl

@[simp] lemma substItrConj_shift (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).shift = φ.shift.substItrConj (Semiterm.shift⨟ w) z := by
  ext; simp only [substItrConj, val_shift, SemitermVec.val_shift]
  rw [shift_conj_substItr φ.isSemiformula w.isSemitermVec]; rfl

@[simp] lemma substItrDisj_shift (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).shift = φ.shift.substItrDisj (Semiterm.shift⨟ w) z := by
  ext; simp only [substItrDisj, val_shift, SemitermVec.val_shift]
  rw [shift_disj_substItr φ.isSemiformula w.isSemitermVec]; rfl

@[simp] lemma substItrConj_free (w : SemitermVec V ℒₒᵣ m 1) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).free = φ.shift.substItrConj (Semiterm.free⨟ w) z := by
  unfold free; simp [Matrix.map_map_comp']; rfl

@[simp] lemma substItrDisj_free (w : SemitermVec V ℒₒᵣ m 1) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).free = φ.shift.substItrDisj (Semiterm.free⨟ w) z := by
  unfold free; simp [Matrix.map_map_comp']; rfl

end Semiformula

end typed_formula

/-
section typed_isfvfree

namespace Semiformula

def FVFree (φ : Semiformula V L n) : Prop := L.IsFVFree n φ.val

lemma FVFree.iff {φ : Semiformula V L n} : φ.FVFree ↔ φ.shift = φ := by
  simp [FVFree, Language.IsFVFree, ext_iff]

@[simp] lemma Fvfree.verum : (⊤ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.falsum : (⊥ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.and {φ ψ : Semiformula V L n} :
    (φ ⋏ ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff, FVFree.iff]

@[simp] lemma Fvfree.or {φ ψ : Semiformula V L n} : (φ ⋎ ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.neg {φ : Semiformula V L n} : (∼φ).FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.all {φ : Semiformula V L (n + 1)} : ∀' φ.FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.ex {φ : Semiformula V L (n + 1)} : ∃' φ.FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.imp {φ ψ : Semiformula V L n} : (φ ➝ ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff]

end Semiformula

end typed_isfvfree
-/

open InternalArithmetic

variable {k n m : ℕ}

noncomputable def Semiterm.equals (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^= u.val, by simp [qqEQ]⟩

noncomputable def Semiterm.notEquals (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≠ u.val, by simp [qqNEQ]⟩

noncomputable def Semiterm.lessThan (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^< u.val, by simp [qqLT]⟩

noncomputable def Semiterm.notLessThan (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≮ u.val, by simp [qqNLT]⟩

scoped infix:46 " ≐ " => Semiterm.equals

scoped infix:46 " ≉ " => Semiterm.notEquals

scoped infix:46 " <' " => Semiterm.lessThan

scoped infix:46 " ≮' " => Semiterm.notLessThan

noncomputable def Semiformula.ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ∀' ((Semiterm.bvar 0 ≮' t.bShift) ⋎ φ)

noncomputable def Semiformula.bex (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ∃' ((Semiterm.bvar 0 <' t.bShift) ⋏ φ)

namespace InternalArithmetic

variable {n m : ℕ}

@[simp] lemma rel_eq_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.rel (Language.Eq.eq : (ℒₒᵣ).Rel 2) v = (v 0 ≐ v 1) := by
  ext; rfl

@[simp] lemma nrel_eq_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.nrel (Language.Eq.eq : (ℒₒᵣ).Rel 2) v = (v 0 ≉ v 1) := by
  ext; rfl

@[simp] lemma rel_lt_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.rel (Language.LT.lt : (ℒₒᵣ).Rel 2) v = (v 0 <' v 1) := by
  ext; rfl

@[simp] lemma nrel_lt_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.nrel (Language.LT.lt : (ℒₒᵣ).Rel 2) v = (v 0 ≮' v 1) := by
  ext; rfl

@[simp] lemma val_equals (t u : Semiterm V ℒₒᵣ n) : (t ≐ u).val = t.val ^= u.val := rfl
@[simp] lemma val_notEquals (t u : Semiterm V ℒₒᵣ n) : (t ≉ u).val = t.val ^≠ u.val := rfl
@[simp] lemma val_lessThan (t u : Semiterm V ℒₒᵣ n) : (t <' u).val = t.val ^< u.val := rfl
@[simp] lemma val_notLessThan (t u : Semiterm V ℒₒᵣ n) : (t ≮' u).val = t.val ^≮ u.val := rfl

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

@[simp] lemma val_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).val = ^∀ (^#0 ^≮ termBShift ℒₒᵣ t.val) ^⋎ φ.val := by
  simp [Semiformula.ball]

@[simp] lemma val_bex (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bex t).val = ^∃ (^#0 ^< termBShift ℒₒᵣ t.val) ^⋏ φ.val := by
  simp [Semiformula.bex]

lemma neg_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(φ.ball t) = (∼φ).bex t := by
  ext; simp [neg_all, neg_or, qqNLT, qqLT, t.isSemiterm.termBShift.isUTerm]

lemma neg_bex (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(φ.bex t) = (∼φ).ball t := by
  ext; simp [neg_ex, neg_and, qqNLT, qqLT, t.isSemiterm.termBShift.isUTerm]

@[simp] lemma shifts_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).shift = φ.shift.ball t.shift := by
  simp [Semiformula.ball, Semiterm.bShift_shift_comm]

@[simp] lemma shifts_bex (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bex t).shift = φ.shift.bex t.shift := by
  simp [Semiformula.bex, Semiterm.bShift_shift_comm]

@[simp] lemma substs_ball (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).substs w = (φ.substs w.q).ball (t.substs w) := by
  simp [Semiformula.ball]

@[simp] lemma substs_bex (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bex t).substs w = (φ.substs w.q).bex (t.substs w) := by
  simp [Semiformula.bex]

end InternalArithmetic

lemma Semiformula.ball_eqss_imp (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    φ.ball t = ∀' ((Semiterm.bvar 0 <' t.bShift) ➝ φ) := by simp [Semiformula.ball, imp_def]

end LO.ISigma1.Metamath
