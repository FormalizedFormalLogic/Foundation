import Logic.FirstOrder.Order.Le

namespace LO

class ORingSymbol (α : Type*) extends
  Zero α, One α, Add α, Mul α, LT α

attribute [instance] ORingSymbol.mk

namespace ORingSymbol

variable {α : Type*} [ORingSymbol α]

def numeral : ℕ → α
  | 0     => 0
  | 1     => 1
  | n + 2 => numeral (n + 1) + 1

 @[simp] lemma zero_eq_zero : (numeral 0 : α) = 0 := rfl

 @[simp] lemma one_eq_one : (numeral 1 : α) = 1 := rfl

end ORingSymbol

@[simp] lemma Nat.numeral_eq : (n : ℕ) → ORingSymbol.numeral n = n
  | 0     => rfl
  | 1     => rfl
  | n + 2 => by simp[ORingSymbol.numeral, Nat.numeral_eq (n + 1)]; rfl

namespace FirstOrder

open Semiterm Semiformula

class ORing (L : Language) extends
  Operator.Zero L, Operator.One L, Operator.Add L, Operator.Mul L, Operator.Eq L, Operator.LT L

class Structure.ORing (L : Language) [ORing L] (M : Type w) [ORingSymbol M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M, Structure.LT L M

attribute [instance] Structure.ORing.mk

namespace Structure

variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingSymbol M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingSymbol.numeral z : M)
  | 0     => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_add_two,
                  Semiterm.Operator.val_comp, Matrix.fun_eq_vec₂, numeral_eq_numeral (z + 1)]

end Structure

namespace Arith

class Sound {L : Language} [Structure L ℕ]
    (T : Theory L) (F : Sentence L → Prop) where
  sound : ∀ {σ}, F σ → T ⊢! σ → ℕ ⊧ₘ σ

section

variable {L : Language} [Structure L ℕ] (T : Theory L) (F : Set (Sentence L))

lemma consistent_of_sound [Sound T F] (hF : F ⊥) : System.Consistent T :=
  ⟨fun b => by simpa using Sound.sound hF ⟨b⟩⟩

end

variable [ORing L] (T : Theory L) [𝐄𝐪 ≾ T]

lemma consequence_of (σ : Sentence L)
  (H : ∀ (M : Type u)
         [Inhabited M]
         [ORingSymbol M]
         [Structure L M]
         [Structure.ORing L M]
         [Theory.Mod M T],
         M ⊧ₘ σ) :
    T ⊨ σ := consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Theory.Mod (Structure.Model L M) T :=
    ⟨((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)⟩
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
    (H (Structure.Model L M))

end Arith

end FirstOrder

end LO
