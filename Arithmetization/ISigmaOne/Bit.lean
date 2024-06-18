import Arithmetization.ISigmaZero.Exponential.Exp
import Arithmetization.ISigmaZero.Exponential.Log

namespace LO.FirstOrder.Arith

noncomputable section

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M]

variable [M ⊧ₘ* 𝐈𝚺₁]

namespace Model

def Bit (i a : M) : Prop := LenBit (exp i) a

instance : Membership M M := ⟨Bit⟩

def _root_.LO.FirstOrder.Arith.bitDef : 𝚺₀-Semisentence 2 := .mkSigma
  “x y | ∃ z <⁺ y, !expDef z x ∧ !lenbitDef z y” (by simp)

lemma bit_defined : 𝚺₀-Relation ((· ∈ ·) : M → M → Prop) via bitDef := by
  intro v; simp [bitDef, ←le_iff_lt_succ]
  constructor
  · intro h; exact ⟨exp (v 0), by simp [h.le], rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma bit_defined_iff (v) :
    Semiformula.Evalbm M v bitDef.val ↔ v 0 ∈ v 1 := bit_defined.df.iff v

@[instance, definability] def mem_definable : DefinableRel ℒₒᵣ 𝚺₀ ((· ∈ ·) : M → M → Prop) := Defined.to_definable _ bit_defined

@[simp, instance, definability] def mem_definable' : DefinableRel ℒₒᵣ Γ ((· ∈ ·) : M → M → Prop) := .of_zero mem_definable _

lemma mem_absolute (i a : ℕ) : i ∈ a ↔ (i : M) ∈ (a : M) := by
  simpa using Defined.shigmaZero_absolute M bit_defined bit_defined ![i, a]

lemma mem_iff_bit {i a : M} : i ∈ a ↔ Bit i a := iff_of_eq rfl

lemma exp_le_of_mem {i a : M} (h : i ∈ a) : exp i ≤ a := LenBit.le h

lemma lt_of_mem {i a : M} (h : i ∈ a) : i < a := lt_of_lt_of_le (lt_exp i) (exp_le_of_mem h)

lemma not_mem_of_lt_exp {i a : M} (h : a < exp i) : i ∉ a := fun H ↦ by have := lt_of_le_of_lt (exp_le_of_mem H) h; simp at this

section

@[definability] lemma Definable.ball_mem (Γ m) {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction ℒₒᵣ (𝚺, m + 1) f) (h : Definable ℒₒᵣ (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable ℒₒᵣ (Γ, m + 1) (fun v ↦ ∀ x ∈ f v, P v x) := by
  have : Definable ℒₒᵣ (Γ, m + 1) (fun v ↦ ∀ x < f v, x ∈ f v → P v x) :=
    .ball_lt hf (.imp (by simpa using Definable.comp₂ (by simp) (hf.retraction _) (by simp)) h)
  exact this.of_iff <| by intro v; exact ⟨fun h x _ hxv ↦ h x hxv, fun h x hx ↦ h x (lt_of_mem hx) hx⟩

@[definability] lemma Definable.ball_mem' (Γ m) {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction ℒₒᵣ (𝚺, m + 1) f) (h : Definable ℒₒᵣ (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable ℒₒᵣ (Γ, m + 1) (fun v ↦ ∀ {x}, x ∈ f v → P v x) := Definable.ball_mem Γ m hf h

@[definability] lemma Definable.bex_mem (Γ m) {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableFunction ℒₒᵣ (𝚺, m + 1) f) (h : Definable ℒₒᵣ (Γ, m + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable ℒₒᵣ (Γ, m + 1) (fun v ↦ ∃ x ∈ f v, P v x) := by
  have : Definable ℒₒᵣ (Γ, m + 1) (fun v ↦ ∃ x < f v, x ∈ f v ∧ P v x) :=
    .bex_lt hf (.and (by simpa using Definable.comp₂ (by simp) (hf.retraction _) (by simp)) h)
  exact this.of_iff <| by
    intro v; exact ⟨by rintro ⟨x, hx, hxv⟩; exact ⟨x, lt_of_mem hx, hx, hxv⟩, by rintro ⟨x, _, hx, hvx⟩; exact ⟨x, hx, hvx⟩⟩

end

end Model

end

section

open Model

variable {ξ : Type*} {n}

instance : Semiformula.Operator.Mem ℒₒᵣ := ⟨⟨bitDef.val⟩⟩

lemma operator_mem_def : Semiformula.Operator.Mem.mem.sentence = bitDef.val := by
  simp [Semiformula.Operator.Mem.mem, Semiformula.Operator.operator]

def ballIn (t : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n + 1)) : Semiformula ℒₒᵣ ξ n := “∀ x < !!t, x ∈ !!(Rew.bShift t) → !p x ⋯”

def bexIn (t : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n + 1)) : Semiformula ℒₒᵣ ξ n := “∃ x < !!t, x ∈ !!(Rew.bShift t) ∧ !p x ⋯”

@[simp] lemma Hierarchy.bit {t u : Semiterm ℒₒᵣ μ n} : Hierarchy Γ s “!!t ∈ !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂, operator_mem_def]

@[simp] lemma Hieralchy.ballIn {Γ m} (t : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n + 1)) :
    Hierarchy Γ m (ballIn t p) ↔ Hierarchy Γ m p := by
  simp only [Arith.ballIn, Rew.bshift_positive, Hierarchy.ball_iff, Hierarchy.imp_iff, and_iff_right_iff_imp]
  intros
  simp [Semiformula.Operator.operator, operator_mem_def]

@[simp] lemma Hieralchy.bexIn {Γ m} (t : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n + 1)) :
    Hierarchy Γ m (bexIn t p) ↔ Hierarchy Γ m p := by
  simp only [Arith.bexIn, Rew.bshift_positive, Hierarchy.bex_iff, Hierarchy.and_iff, and_iff_right_iff_imp]
  intros
  simp [Semiformula.Operator.operator, operator_mem_def]

def memRel : 𝚺₀-Semisentence 3 := .mkSigma
  “R x y | ∃ p <⁺ (x + y + 1)², !pairDef p x y ∧ p ∈ R” (by simp)

def memRelOpr : Semiformula.Operator ℒₒᵣ 3 := ⟨memRel.val⟩

section

open Lean PrettyPrinter Delaborator

syntax:max "∀ " ident " ∈' " first_order_term ", " first_order_formula:0 : first_order_formula
syntax:max "∃ " ident " ∈' " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(“ $binders* | ∀ $x ∈' $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(ballIn ‘ $binders* | $t ’ “ $binders'* | $p ”)
  | `(“ $binders* | ∃ $x ∈' $t, $p ”) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertAt 0 x
    `(bexIn ‘ $binders* | $t ’ “ $binders'* | $p ”)

syntax:45 first_order_term:45 " ~[" first_order_term "]" first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≁[" first_order_term "]" first_order_term:0 : first_order_formula

macro_rules
  | `(“ $binders* | $t₁:first_order_term ~[ $u:first_order_term ] $t₂:first_order_term ”) =>
    `(memRelOpr.operator ![‘$binders* | $u’, ‘$binders* | $t₁’, ‘$binders* | $t₂’])
  | `(“ $binders* | $t₁:first_order_term ≁[ $u:first_order_term ] $t₂:first_order_term ”) =>
    `(~memRelOpr.operator ![‘$binders* | $u’, ‘$binders* | $t₁’, ‘$binders* | $t₂’])

end

@[simp] lemma Hierarchy.memRel {t₁ t₂ u : Semiterm ℒₒᵣ μ n} : Hierarchy Γ s “!!t₁ ~[ !!u ] !!t₂” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂, operator_mem_def, memRelOpr]

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

scoped instance : Structure.Mem ℒₒᵣ M := ⟨by intro a b; simp [Semiformula.Operator.val, operator_mem_def, Model.bit_defined.df.iff]⟩

@[simp] lemma eval_ballIn {t : Semiterm ℒₒᵣ ξ n} {p : Semiformula ℒₒᵣ ξ (n + 1)} {e ε} :
    Semiformula.Evalm M e ε (ballIn t p) ↔ ∀ x ∈ t.valm M e ε, Semiformula.Evalm M (x :> e) ε p := by
  simp [ballIn]
  constructor
  · intro h x hx; exact h x (lt_of_mem hx) hx
  · intro h x _ hx; exact h x hx

@[simp] lemma eval_bexIn {t : Semiterm ℒₒᵣ ξ n} {p : Semiformula ℒₒᵣ ξ (n + 1)} {e ε} :
    Semiformula.Evalm M e ε (bexIn t p) ↔ ∃ x ∈ t.valm M e ε, Semiformula.Evalm M (x :> e) ε p := by
  simp [bexIn]
  constructor
  · rintro ⟨x, _, hx, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨x, lt_of_mem hx, hx, h⟩

lemma Model.memRel_defined : 𝚺₀-Relation₃ ((fun r x y ↦ ⟪x, y⟫ ∈ r) : M → M → M → Prop) via memRel := by
  intro v; simp [memRel, pair_defined.df.iff, lt_succ_iff_le]
  constructor
  · intro h; exact ⟨⟪v 1, v 2⟫, by simp, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

@[simp] lemma eval_memRel {x y r : M} :
    memRelOpr.val ![r, x, y] ↔ ⟪x, y⟫ ∈ r := by
  unfold Semiformula.Operator.val
  simp [memRelOpr, pair_defined.df.iff, memRel_defined.df.iff]

end

noncomputable section

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M]

variable [M ⊧ₘ* 𝐈𝚺₁]

namespace Model

lemma mem_iff_mul_exp_add_exp_add {i a : M} : i ∈ a ↔ ∃ k, ∃ r < exp i, a = k * exp (i + 1) + exp i + r := by
  simp [mem_iff_bit, exp_succ]
  exact lenbit_iff_add_mul (exp_pow2 i) (a := a)

lemma not_mem_iff_mul_exp_add {i a : M} : i ∉ a ↔ ∃ k, ∃ r < exp i, a = k * exp (i + 1) + r := by
  simp [mem_iff_bit, exp_succ]
  exact not_lenbit_iff_add_mul (exp_pow2 i) (a := a)

section empty

scoped instance : EmptyCollection M := ⟨0⟩

lemma emptyset_def : (∅ : M) = 0 := rfl

@[simp] lemma not_mem_empty (i : M) : i ∉ (∅ : M) := by simp [emptyset_def, mem_iff_bit, Bit]

@[simp] lemma not_mem_zero (i : M) : i ∉ (0 : M) := by simp [mem_iff_bit, Bit]

end empty

section singleton

scoped instance : Singleton M M := ⟨fun a ↦ exp a⟩

lemma singleton_def (a : M) : {a} = exp a := rfl

end singleton

section insert

open Classical in
noncomputable def bitInsert (i a : M) : M := if i ∈ a then a else a + exp i

open Classical in
noncomputable def bitRemove (i a : M) : M := if i ∈ a then a - exp i else a

scoped instance : Insert M M := ⟨bitInsert⟩

lemma insert_eq {i a : M} : insert i a = bitInsert i a := rfl

lemma singleton_eq_insert (i : M) : ({i} : M) = insert i ∅ := by simp [singleton_def, insert, bitInsert, emptyset_def]

@[simp] lemma mem_bitInsert_iff {i j a : M} :
    i ∈ insert j a ↔ i = j ∨ i ∈ a := by
  by_cases h : j ∈ a <;> simp [h, insert_eq, bitInsert]
  · by_cases e : i = j <;> simp [h, e]
  · simpa [exp_inj.eq_iff] using
      lenbit_add_pow2_iff_of_not_lenbit (exp_pow2 i) (exp_pow2 j) h

@[simp] lemma mem_bitRemove_iff {i j a : M} :
    i ∈ bitRemove j a ↔ i ≠ j ∧ i ∈ a := by
  by_cases h : j ∈ a <;> simp [h, bitRemove]
  · simpa [exp_inj.eq_iff] using
      lenbit_sub_pow2_iff_of_lenbit (exp_pow2 i) (exp_pow2 j) h
  · rintro _ rfl; contradiction

@[simp] lemma not_mem_bitRemove_self (i a : M) : i ∉ bitRemove i a := by simp

lemma insert_graph (b i a : M) :
    b = insert i a ↔ (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e ≤ b, e = exp i ∧ b = a + e) :=
  ⟨by rintro rfl; by_cases hi : i ∈ a <;> simp [hi, insert, bitInsert],
   by by_cases hi : i ∈ a <;> simp only [hi, true_and, not_true_eq_false, false_and,
        or_false, insert, bitInsert, ↓reduceIte, imp_self,
        not_false_eq_true, true_and, false_or, forall_exists_index, and_imp]
      rintro x _ rfl rfl; rfl ⟩

def _root_.LO.FirstOrder.Arith.insertDef : 𝚺₀-Semisentence 3 := .mkSigma
  “b i a | (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e <⁺ b, !expDef e i ∧ b = a + e)” (by simp)

lemma insert_defined : 𝚺₀-Function₂ (insert : M → M → M) via insertDef := by
  intro v; simp [insertDef, insert_graph]

@[simp] lemma insert_defined_iff (v) :
    Semiformula.Evalbm M v insertDef.val ↔ v 0 = insert (v 1) (v 2) := insert_defined.df.iff v

instance insert_definable : 𝚺₀-Function₂ (insert : M → M → M) := Defined.to_definable _ insert_defined

instance insert_definable' (Γ) : Γ-Function₂ (insert : M → M → M) := .of_zero insert_definable _

lemma insert_le_of_le_of_le {i j a b : M} (hij : i ≤ j) (hab : a ≤ b) : insert i a ≤ b + exp j := by
  simp [insert, bitInsert]
  by_cases hi : i ∈ a <;> simp [hi]
  · exact le_trans hab (by simp)
  · exact add_le_add hab (exp_monotone_le.mpr hij)

end insert

lemma one_eq_singleton : (1 : M) = {∅} := by simp [singleton_eq_insert, insert, bitInsert, emptyset_def]

@[simp] lemma mem_singleton_iff {i j : M} :
    i ∈ ({j} : M) ↔ i = j := by simp [singleton_eq_insert]

lemma bitRemove_lt_of_mem {i a : M} (h : i ∈ a) : bitRemove i a < a := by
  simp [h, bitRemove, tsub_lt_iff_left (exp_le_of_mem h)]

lemma pos_of_nonempty {i a : M} (h : i ∈ a) : 0 < a := by
  by_contra A; simp at A; rcases A; simp_all

@[simp] lemma mem_insert (i a : M) : i ∈ insert i a := by simp

lemma log_mem_of_pos {a : M} (h : 0 < a) : log a ∈ a :=
  mem_iff_mul_exp_add_exp_add.mpr
    ⟨0, a - exp log a,
      (tsub_lt_iff_left (exp_log_le_self h)).mpr (by rw [←two_mul]; exact lt_two_mul_exponential_log h),
      by simp; exact Eq.symm <| add_tsub_self_of_le (exp_log_le_self h)⟩

lemma le_log_of_mem {i a : M} (h : i ∈ a) : i ≤ log a := (exp_le_iff_le_log (pos_of_nonempty h)).mp (exp_le_of_mem h)

lemma succ_mem_iff_mem_div_two {i a : M} : i + 1 ∈ a ↔ i ∈ a / 2 := by simp [mem_iff_bit, Bit, LenBit.iff_rem, exp_succ, div_mul]

lemma lt_length_of_mem {i a : M} (h : i ∈ a) : i < ‖a‖ := by
  simpa [length_of_pos (pos_of_nonempty h), ←le_iff_lt_succ] using le_log_of_mem h

lemma lt_exp_iff {a i : M} : a < exp i ↔ ∀ j ∈ a, j < i :=
  ⟨fun h j hj ↦ exp_monotone.mp <| lt_of_le_of_lt (exp_le_of_mem hj) h,
   by contrapose; simp
      intro (h : exp i ≤ a)
      have pos : 0 < a := lt_of_lt_of_le (by simp) h
      exact ⟨log a, log_mem_of_pos pos, (exp_le_iff_le_log pos).mp h⟩⟩

instance : HasSubset M := ⟨fun a b ↦ ∀ ⦃i⦄, i ∈ a → i ∈ b⟩

def _root_.LO.FirstOrder.Arith.bitSubsetDef : 𝚺₀-Semisentence 2 := .mkSigma
  “a b | ∀ i < a, i ∈ a → i ∈ b” (by simp)

lemma bitSubset_defined : 𝚺₀-Relation ((· ⊆ ·) : M → M → Prop) via bitSubsetDef := by
  intro v; simp [bitSubsetDef]
  exact ⟨by intro h x _ hx; exact h hx, by intro h x hx; exact h x (lt_of_mem hx) hx⟩

@[simp] lemma bitSubset_defined_iff (v) :
    Semiformula.Evalbm M v bitSubsetDef.val ↔ v 0 ⊆ v 1 := bitSubset_defined.df.iff v

instance bitSubset_definable : DefinableRel ℒₒᵣ 𝚺₀ ((· ⊆ ·) : M → M → Prop) := Defined.to_definable₀ _ bitSubset_defined

@[simp, definability] instance bitSubset_definable' : DefinableRel ℒₒᵣ Γ ((· ⊆ ·) : M → M → Prop) := Defined.to_definable₀ _ bitSubset_defined

lemma subset_iff {a b : M} : a ⊆ b ↔ (∀ x ∈ a, x ∈ b) := by simp [HasSubset.Subset]

@[refl, simp] lemma subset_refl (a : M) : a ⊆ a := by intro x; simp

@[trans] lemma subset_trans {a b c : M} (hab : a ⊆ b) (hbc : b ⊆ c) : a ⊆ c := by
  intro x hx; exact hbc (hab hx)

lemma mem_exp_add_succ_sub_one (i j : M) : i ∈ exp (i + j + 1) - 1 := by
  have : exp (i + j + 1) - 1 = (exp j - 1) * exp (i + 1) + exp i + (exp i - 1) := calc
    exp (i + j + 1) - 1 = exp j * exp (i + 1) - 1                             := by simp [exp_add, ←mul_assoc, mul_comm]
    _                   = exp j * exp (i + 1) - exp (i + 1) + exp (i + 1) - 1 := by rw [sub_add_self_of_le]; exact le_mul_of_pos_left (exp_pos j)
    _                   = (exp j - 1) * exp (i + 1) + exp (i + 1) - 1         := by simp [sub_mul]
    _                   = (exp j - 1) * exp (i + 1) + (exp i + exp i) - 1     := by simp [←two_mul, ←exp_succ i]
    _                   = (exp j - 1) * exp (i + 1) + (exp i + exp i - 1)     := by rw [add_tsub_assoc_of_le]; simp [←two_mul, ←pos_iff_one_le]
    _                   = (exp j - 1) * exp (i + 1) + exp i + (exp i - 1)     := by simp [add_assoc, add_tsub_assoc_of_le]
  exact mem_iff_mul_exp_add_exp_add.mpr ⟨exp j - 1, exp i - 1, (tsub_lt_iff_left (by simp)).mpr $ by simp, this⟩

/-- under a = {0, 1, 2, ..., a - 1} -/
def under (a : M) : M := exp a - 1

@[simp] lemma le_under (a : M) : a ≤ under a :=
  le_iff_lt_succ.mpr (by simp [under, show exp a - 1 + 1 = exp a from sub_add_self_of_le (by simp)])

@[simp] lemma mem_under_iff {i j : M} : i ∈ under j ↔ i < j := by
  constructor
  · intro h
    have : exp i < exp j := calc
      exp i ≤ exp j - 1 := exp_le_of_mem h
      _     < exp j     := pred_lt_self_of_pos (exp_pos j)
    exact exp_monotone.mp this
  · intro lt
    have := lt_iff_succ_le.mp lt
    let k := j - (i + 1)
    have : j = i + k + 1 := by
      simp [add_assoc, ←sub_sub, k]; rw [sub_add_self_of_le, add_tsub_self_of_le]
      · exact le_of_lt lt
      · exact le_tsub_of_add_le_left this
    rw [this]; exact mem_exp_add_succ_sub_one i k

@[simp] lemma not_mem_under_self (i : M) : i ∉ under i := by simp

private lemma under_graph (x y : M) : y = under x ↔ y + 1 = exp x :=
  ⟨by rintro rfl; simp [under, sub_add_self_of_le], by intro h; have := congr_arg (· - 1) h; simp [under] at this ⊢; exact this⟩

def _root_.LO.FirstOrder.Arith.underDef : 𝚺₀-Semisentence 2 := .mkSigma
  “y x | !expDef.val (y + 1) x” (by simp)

lemma under_defined : 𝚺₀-Function₁ (under : M → M) via underDef := by
  intro v; simp [underDef, under_graph]

@[simp] lemma under_defined_iff (v) :
    Semiformula.Evalbm M v underDef.val ↔ v 0 = under (v 1) := under_defined.df.iff v

instance under_definable : 𝚺₀-Function₁ (under : M → M) := Defined.to_definable _ under_defined

instance under_definable' (Γ) : Γ-Function₁ (under : M → M) := .of_zero under_definable _

lemma eq_zero_of_subset_zero {a : M} : a ⊆ 0 → a = 0 := by
  intro h; by_contra A
  have : log a ∈ (0 : M) := h (log_mem_of_pos (pos_iff_ne_zero.mpr A))
  simp_all

lemma subset_div_two {a b : M} : a ⊆ b → a / 2 ⊆ b / 2 := by
  intro ss i hi
  have : i + 1 ∈ a := succ_mem_iff_mem_div_two.mpr hi
  exact succ_mem_iff_mem_div_two.mp <| ss this

lemma zero_mem_iff {a : M} : 0 ∉ a ↔ 2 ∣ a := by simp [mem_iff_bit, Bit, LenBit]

@[simp] lemma zero_not_mem (a : M) : 0 ∉ 2 * a := by simp [mem_iff_bit, Bit, LenBit]

lemma le_of_subset {a b : M} (h : a ⊆ b) : a ≤ b := by
  induction b using hierarchy_polynomial_induction_oRing_pi₁ generalizing a
  · definability
  case zero =>
    simp [eq_zero_of_subset_zero h]
  case even b _ IH =>
    have IH : a / 2 ≤ b := IH (by simpa using subset_div_two h)
    have : 2 * (a / 2) = a :=
      mul_div_self_of_dvd.mpr (zero_mem_iff.mp $ by intro ha; have : 0 ∈ 2 * b := h ha; simp_all)
    simpa [this] using mul_le_mul_left (a := 2) IH
  case odd b IH =>
    have IH : a / 2 ≤ b := IH (by simpa [div_mul_add' b 2 one_lt_two] using subset_div_two h)
    exact le_trans (le_two_mul_div_two_add_one a) (by simpa using IH)

lemma mem_ext {a b : M} (h : ∀ i, i ∈ a ↔ i ∈ b) : a = b :=
  le_antisymm (le_of_subset fun i hi ↦ (h i).mp hi) (le_of_subset fun i hi ↦ (h i).mpr hi)

lemma pos_iff_nonempty {s : M} : 0 < s ↔ s ≠ ∅ := pos_iff_ne_zero

lemma nonempty_of_pos {a : M} (h : 0 < a) : ∃ i, i ∈ a := by
  by_contra A
  have : a = 0 := mem_ext (by simpa using A)
  simp [this] at h

lemma eq_empty_or_nonempty (a : M) : a = ∅ ∨ ∃ i, i ∈ a := by
  rcases zero_le a with (rfl | pos)
  · simp [emptyset_def]
  · right; exact nonempty_of_pos pos

lemma nonempty_iff {s : M} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  rcases eq_empty_or_nonempty s with ⟨rfl, hy⟩ <;> simp
  simp [show s ≠ ∅ from by rintro rfl; simp_all]; assumption

lemma isempty_iff {s : M} : s = ∅ ↔ ∀ x, x ∉ s := by
  simpa using not_iff_not.mpr (nonempty_iff (s := s))

lemma lt_of_lt_log {a b : M} (pos : 0 < b) (h : ∀ i ∈ a, i < log b) : a < b := by
  rcases zero_le a with (rfl | apos)
  · exact pos
  by_contra A
  exact not_lt_of_le (log_monotone <| show b ≤ a by simpa using A) (h (log a) (log_mem_of_pos apos))

@[simp] lemma under_inj {i j : M} : under i = under j ↔ i = j := ⟨fun h ↦ by
  by_contra ne
  wlog lt : i < j
  · exact this (Eq.symm h) (Ne.symm ne) (lt_of_le_of_ne (by simpa using lt) (Ne.symm ne))
  have : i ∉ under i := by simp
  have : i ∈ under i := by rw [h]; simp [mem_under_iff, lt]
  contradiction, by rintro rfl; simp⟩

@[simp] lemma under_zero : under (0 : M) = ∅ := mem_ext (by simp [mem_under_iff])

@[simp] lemma under_succ (i : M) : under (i + 1) = insert i (under i) :=
  mem_ext (by simp [mem_under_iff, lt_succ_iff_le, le_iff_eq_or_lt])

lemma insert_remove {i a : M} (h : i ∈ a) : insert i (bitRemove i a) = a := mem_ext <| by
  simp; intro j
  constructor
  · rintro (rfl | ⟨_, hj⟩) <;> assumption
  · intro hj; simp [hj, eq_or_ne j i]

section

variable {m : ℕ} [Fact (1 ≤ m)] [M ⊧ₘ* 𝐈𝐍𝐃𝚺 m]

private lemma finset_comprehension_aux (Γ : Polarity) {P : M → Prop} (hP : (Γ, m)-Predicate P) (a : M) :
    haveI : M ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
    ∃ s < exp a, ∀ i < a, i ∈ s ↔ P i := by
  haveI : M ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
  have : ∃ s < exp a, ∀ i < a, P i → i ∈ s :=
    ⟨under a, pred_lt_self_of_pos (by simp), fun i hi _ ↦ by simpa [mem_under_iff] using hi⟩
  rcases this with ⟨s, hsn, hs⟩
  have : (Γ.alt, m)-Predicate (fun s : M ↦ ∀ i < a, P i → i ∈ s) := by
    apply Definable.ball_lt₀; simp; apply Definable.imp <;> definability
  have : ∃ t, (∀ i < a, P i → i ∈ t) ∧ ∀ t' < t, ∃ x < a, P x ∧ x ∉ (t' : M) := by
    simpa using least_number_h (L := ℒₒᵣ) Γ.alt m this hs
  rcases this with ⟨t, ht, t_minimal⟩
  have t_le_s : t ≤ s := not_lt.mp (by
    intro lt
    rcases t_minimal s lt with ⟨i, hin, hi, his⟩
    exact his (hs i hin hi))
  have : ∀ i < a, i ∈ t → P i := by
    intro i _ hit
    by_contra Hi
    have : ∃ j < a, P j ∧ (j ∈ t → j = i) := by
      simpa [not_imp_not] using t_minimal (bitRemove i t) (bitRemove_lt_of_mem hit)
    rcases this with ⟨j, hjn, Hj, hm⟩
    rcases hm (ht j hjn Hj); contradiction
  exact ⟨t, lt_of_le_of_lt t_le_s hsn, fun i hi ↦ ⟨this i hi, ht i hi⟩⟩

theorem finset_comprehension {Γ} {P : M → Prop} (hP : (Γ, m)-Predicate P) (a : M) :
    haveI : M ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
    ∃ s < exp a, ∀ i < a, i ∈ s ↔ P i :=
  match Γ with
  | 𝚺 => finset_comprehension_aux 𝚺 hP a
  | 𝚷 => finset_comprehension_aux 𝚷 hP a
  | 𝚫 => finset_comprehension_aux 𝚺 hP.of_delta a

theorem finset_comprehension_exists_unique {P : M → Prop} (hP : (Γ, m)-Predicate P) (a : M) :
    haveI : M ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
    ∃! s, s < exp a ∧ ∀ i < a, i ∈ s ↔ P i := by
  haveI : M ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
  rcases finset_comprehension hP a with ⟨s, hs, Hs⟩
  exact ExistsUnique.intro s ⟨hs, Hs⟩ (by
    intro t ⟨ht, Ht⟩
    apply mem_ext
    intro i
    constructor
    · intro hi
      have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) ht)
      exact (Hs i hin).mpr ((Ht i hin).mp hi)
    · intro hi
      have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) hs)
      exact (Ht i hin).mpr ((Hs i hin).mp hi))

end

section ISigma₁

instance : Fact (1 ≤ 1) := ⟨by rfl⟩

theorem finset_comprehension₁ {P : M → Prop} (hP : (Γ, 1)-Predicate P) (a : M) :
    ∃ s < exp a, ∀ i < a, i ∈ s ↔ P i :=
  finset_comprehension hP a

theorem finset_comprehension₁! {P : M → Prop} (hP : (Γ, 1)-Predicate P) (a : M) :
    ∃! s, s < exp a ∧ (∀ i < a, i ∈ s ↔ P i) := by
  rcases finset_comprehension₁ hP a with ⟨s, hs, Ha⟩
  exact ExistsUnique.intro s ⟨hs, Ha⟩
    (by
      rintro b ⟨hb, Hb⟩
      apply mem_ext
      intro x
      constructor
      · intro hx
        have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hb
        exact (Ha x this).mpr <| (Hb x this).mp hx
      · intro hx
        have : x < a := exp_monotone.mp <| LE.le.trans_lt (exp_le_of_mem hx) hs
        exact (Hb x this).mpr <| (Ha x this).mp hx)

theorem finite_comprehension₁! {P : M → Prop} (hP : (Γ, 1)-Predicate P) (fin : ∃ m, ∀ i, P i → i < m)  :
    ∃! s : M, ∀ i, i ∈ s ↔ P i := by
  rcases fin with ⟨m, mh⟩
  rcases finset_comprehension₁ hP m with ⟨s, hs, Hs⟩
  have H : ∀ i, i ∈ s ↔ P i :=
    fun i ↦ ⟨
      fun h ↦ (Hs i (exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem h) hs))).mp h,
      fun h ↦ (Hs i (mh i h)).mpr h⟩
  exact ExistsUnique.intro s H (fun s' H' ↦ mem_ext <| fun i ↦ by simp [H, H'])

/-
def setExt {Γ} (p : 𝚫₁-Semisentence (n + 1)) : Γ-Semisentence (n + 1) :=
  match Γ with
  | (𝚺, m) => .mkSigma “u | ∀ x < u, x ∈ u ↔ !p x ⋯” (by {  })

lemma set_iff {n} {f : (Fin n → M) → M} {R : (Fin (n + 1) → M) → Prop}
    (hf : ∀ v x, x ∈ f v ↔ R (x :> v)) {Γ} (p : (Γ, 1)-Semisentence (n + 1)) : DefinedFunction ℒₒᵣ (Γ, 1) f p := by {

     }
-/

end ISigma₁

end Model

end

end Arith

end LO.FirstOrder
