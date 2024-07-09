import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

section

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

variable (M)

structure _root_.LO.FirstOrder.Arith.LDef where
  func : HSemisentence ℒₒᵣ 2 𝚺₀
  rel : HSemisentence ℒₒᵣ 2 𝚺₀

protected structure Language where
  Func (arity : M) : M → Prop
  Rel (arity : M) : M → Prop

variable {M}

namespace Language

protected class Defined (L : Arith.Language M) (pL : outParam LDef) where
  func : 𝚺₀-Relation L.Func via pL.func
  rel : 𝚺₀-Relation L.Rel via pL.rel

variable {L : Arith.Language M} {pL : LDef} [L.Defined pL]

@[simp] lemma Defined.eval_func (v) :
    Semiformula.Evalbm M v pL.func.val ↔ L.Func (v 0) (v 1) := Defined.func.df.iff v

@[simp] lemma Defined.eval_rel_iff (v) :
    Semiformula.Evalbm M v pL.rel.val ↔ L.Rel (v 0) (v 1) := Defined.rel.df.iff v

instance Defined.func_definable : 𝚺₀-Relation L.Func := Defined.to_definable _ Defined.func

instance Defined.rel_definable : 𝚺₀-Relation L.Rel := Defined.to_definable _ Defined.rel

@[simp, definability] instance Defined.func_definable' (Γ) : Γ-Relation L.Func :=
  Definable.of_zero Defined.func_definable _

@[simp, definability] instance Defined.rel_definable' (Γ) : Γ-Relation L.Rel :=
  Definable.of_zero Defined.rel_definable _

end Language

end

section

variable {L₀ : Language} [L₀.ORing]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Func k) := ⟨fun f ↦ Semiterm.Operator.numeral L₀ (Encodable.encode f)⟩

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Rel k) := ⟨fun r ↦ Semiterm.Operator.numeral L₀ (Encodable.encode r)⟩

variable (L)

class DefinableLanguage extends Arith.LDef where
  func_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Func k → ℕ) ↔
    𝐏𝐀⁻ ⊢₌! func.val/[Semiterm.Operator.numeral ℒₒᵣ k, Semiterm.Operator.numeral ℒₒᵣ c]
  rel_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Rel k → ℕ) ↔
    𝐏𝐀⁻ ⊢₌! rel.val/[Semiterm.Operator.numeral ℒₒᵣ k, Semiterm.Operator.numeral ℒₒᵣ c]

def _root_.LO.FirstOrder.Language.lDef [d : DefinableLanguage L] : LDef := d.toLDef

variable {L}

variable [DefinableLanguage L]

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

variable (L M)

def _root_.LO.FirstOrder.Language.codeIn : Arith.Language M where
  Func := fun x y ↦ Semiformula.Evalbm M ![x, y] L.lDef.func.val
  Rel := fun x y ↦ Semiformula.Evalbm M ![x, y] L.lDef.rel.val

variable {L M}

instance : (L.codeIn M).Defined L.lDef where
  func := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]
  rel := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]

@[simp] lemma codeIn_func_encode {k : ℕ} (f : L.Func k) : (L.codeIn M).Func k (Encodable.encode f) := by
  simpa [models_iff, numeral_eq_natCast] using
    consequence_iff_add_eq.mp (sound! <| DefinableLanguage.func_iff.mp ⟨f, rfl⟩) M
      (models_of_subtheory (T := 𝐏𝐀⁻) inferInstance)

@[simp] lemma codeIn_rel_encode {k : ℕ} (r : L.Rel k) : (L.codeIn M).Rel k (Encodable.encode r) := by
  simpa [models_iff, numeral_eq_natCast] using
    consequence_iff_add_eq.mp (sound! <| DefinableLanguage.rel_iff.mp ⟨r, rfl⟩) M
      (models_of_subtheory (T := 𝐏𝐀⁻) inferInstance)

end

/-- TODO: move to Basic/Syntax/Language.lean-/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_func {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : FirstOrder.Language.Func ℒₒᵣ k → ℕ) ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    match k, f with
    | 0, Language.ORing.Func.zero => simp; rfl
    | 0, Language.ORing.Func.one => simp; rfl
    | 2, Language.ORing.Func.add => simp; rfl
    | 2, Language.ORing.Func.mul => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Func.zero, rfl⟩
    · exact ⟨Language.ORing.Func.one, rfl⟩
    · exact ⟨Language.ORing.Func.add, rfl⟩
    · exact ⟨Language.ORing.Func.mul, rfl⟩

/-- TODO: move to Basic/Syntax/Language.lean-/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_rel {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : FirstOrder.Language.Rel ℒₒᵣ k → ℕ) ↔
    (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨r, rfl⟩
    match k, r with
    | 2, Language.ORing.Rel.eq => simp; rfl
    | 2, Language.ORing.Rel.lt => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Rel.eq, rfl⟩
    · exact ⟨Language.ORing.Rel.lt, rfl⟩

instance : DefinableLanguage ℒₒᵣ where
  func := .mkSigma “k f | (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” (by simp)
  rel  := .mkSigma “k r | (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” (by simp)
  func_iff {k c} := by
    rw [←sigma_one_completeness_iff]
    · simpa [models_iff] using Language.ORing.of_mem_range_encode_func
    · simp
  rel_iff {k c} := by
    rw [←sigma_one_completeness_iff]
    · simpa [models_iff] using Language.ORing.of_mem_range_encode_rel
    · simp

end LO.Arith

end
