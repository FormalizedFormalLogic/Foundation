import Arithmetization.ISigmaOne.HFS

noncomputable section

namespace LO.FirstOrder

namespace Arith.Model

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

class Defined (L : Model.Language M) (pL : outParam LDef) where
  func : 𝚺₀-Relation L.Func via pL.func
  rel : 𝚺₀-Relation L.Rel via pL.rel

variable {L : Model.Language M} {pL : LDef} [Defined L pL]

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

end Model

section

variable {L₀ : Language} [L₀.ORing]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Func k) := ⟨fun f ↦ Semiterm.Operator.numeral L₀ (Encodable.encode f)⟩

instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Rel k) := ⟨fun r ↦ Semiterm.Operator.numeral L₀ (Encodable.encode r)⟩

variable (L)

class DefinableLanguage (T : Theory ℒₒᵣ) where
  func_def : HSemisentence ℒₒᵣ 2 𝚺₀
  rel_def : HSemisentence ℒₒᵣ 2 𝚺₀
  func_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Func k → ℕ) ↔
    T ⊢! func_def.val/[Semiterm.Operator.numeral ℒₒᵣ k, Semiterm.Operator.numeral ℒₒᵣ c]
  rel_iff {k c : ℕ} :
    c ∈ Set.range (Encodable.encode : L.Rel k → ℕ) ↔
    T ⊢! rel_def.val/[Semiterm.Operator.numeral ℒₒᵣ k, Semiterm.Operator.numeral ℒₒᵣ c]

end

/-
instance : DefinableLanguage ℒₒᵣ 𝐏𝐀⁻⁼ where
  func_def := .mkSigma “k f | (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” (by simp)
  rel_def  := .mkSigma “k r | (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” (by simp)
  func_iff {k c} := by {  }
-/

end Arith


end LO.FirstOrder
