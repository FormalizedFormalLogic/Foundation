import Logic.FirstOrder.Order.Le



namespace LO

namespace ORingSymbol

variable {α : Type*} [Zero α] [One α] [Add α] [Mul α] [LT α]

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

namespace Language

variable {L : Language} [L.ORing]

def oringEmb : ℒₒᵣ →ᵥ L where
  func := fun {k} f ↦
    match k, f with
    | _, Zero.zero => Zero.zero
    | _, One.one   => One.one
    | _, Add.add   => Add.add
    | _, Mul.mul   => Mul.mul
  rel := fun {k} r ↦
    match k, r with
    | _, Eq.eq => Eq.eq
    | _, LT.lt => LT.lt

@[simp] lemma oringEmb_zero : (oringEmb : ℒₒᵣ →ᵥ L).func Zero.zero = Zero.zero := rfl

@[simp] lemma oringEmb_one : (oringEmb : ℒₒᵣ →ᵥ L).func One.one = One.one := rfl

@[simp] lemma oringEmb_add : (oringEmb : ℒₒᵣ →ᵥ L).func Add.add = Add.add := rfl

@[simp] lemma oringEmb_mul : (oringEmb : ℒₒᵣ →ᵥ L).func Mul.mul = Mul.mul := rfl

@[simp] lemma oringEmb_eq : (oringEmb : ℒₒᵣ →ᵥ L).rel Eq.eq = Eq.eq := rfl

@[simp] lemma oringEmb_lt : (oringEmb : ℒₒᵣ →ᵥ L).rel LT.lt = LT.lt := rfl

end Language

open Semiterm Semiformula

abbrev Polynomial (n : ℕ) : Type := Semiterm ℒₒᵣ Empty n

class Structure.ORing (L : Language) [L.ORing] (M : Type w) [Zero M] [One M] [Add M] [Mul M] [LT M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M, Structure.LT L M

attribute [instance] Structure.ORing.mk

namespace Structure

variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [Zero M] [One M] [Add M] [Mul M] [LT M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingSymbol.numeral z : M)
  | 0     => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp[ORingSymbol.numeral, Semiterm.Operator.numeral_add_two,
                  Semiterm.Operator.val_comp, Matrix.fun_eq_vec₂, numeral_eq_numeral (z + 1)]

end Structure

namespace Arith

class SoundOn {L : Language} [Structure L ℕ]
    (T : Theory L) (F : Sentence L → Prop) where
  sound : ∀ {σ}, F σ → T ⊢! σ → ℕ ⊧ₘ σ

section

variable {L : Language} [Structure L ℕ] (T : Theory L) (F : Set (Sentence L))

lemma consistent_of_sound [SoundOn T F] (hF : F ⊥) : System.Consistent T :=
  fun b => by simpa using SoundOn.sound hF b

end

variable {L : Language} [L.ORing] (T : Theory L) [𝐄𝐪 ≾ T]

lemma consequence_of (σ : Sentence L)
  (H : ∀ (M : Type u)
         [Zero M] [One M] [Add M] [Mul M] [LT M]
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
