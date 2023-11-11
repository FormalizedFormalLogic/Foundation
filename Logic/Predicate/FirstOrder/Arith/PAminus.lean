import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Arith.Model
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

--import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [ORing L] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace Arith

namespace PAminus

noncomputable section

namespace Model
open Language
variable
  {M : Type} [DecidableEq M] [ORingSymbol M]
  [Structure Language.oRing M] [Structure.ORing Language.oRing M]
  [Theory.Mod M (Theory.PAminus Language.oRing)]

instance : LE M := ⟨fun x y => x = y ∨ x < y⟩

lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl

lemma add_zero : ∀ x : M, x + 0 = x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.addZero oRing _)

lemma add_assoc : ∀ x y z : M, (x + y) + z = x + (y + z) := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.addAssoc oRing _)

lemma add_comm : ∀ x y : M, x + y = y + x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.addComm oRing _)

lemma add_eq_of_lt : ∀ x y : M, x < y → ∃ z, x + z = y := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.addEqOfLt oRing _)

lemma zero_le : ∀ x : M, 0 ≤ x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.zeroLe oRing _)

lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.zeroLtOne oRing _)

lemma one_le_of_zero_lt : ∀ x : M, 0 < x → 1 ≤ x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.oneLeOfZeroLt oRing _)

lemma add_lt_add : ∀ x y z : M, x < y → x + z < y + z := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.addLtAdd oRing _)

lemma mul_zero : ∀ x : M, x * 0 = 0 := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.mulZero oRing _)

lemma mul_one : ∀ x : M, x * 1 = x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.mulOne oRing _)

lemma mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z) := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.mulAssoc oRing _)

lemma mul_comm : ∀ x y : M, x * y = y * x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.mulComm oRing _)

lemma mul_lt_mul : ∀ x y z : M, x < y → 0 < z → x * z < y * z := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.mulLtMul oRing _)

lemma distr : ∀ x y z : M, x * (y + z) = x * y + x * z := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.distr oRing _)

lemma lt_irrefl : ∀ x : M, ¬x < x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.ltIrrefl oRing _)

lemma lt_trans : ∀ x y z : M, x < y → y < z → x < z := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.ltTrans oRing _)

lemma lt_tri : ∀ x y : M, x < y ∨ x = y ∨ y < x := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.ltTri oRing _)

instance : AddCommMonoid M where
  add_assoc := Model.add_assoc
  zero_add  := fun x => Model.add_comm x 0 ▸ Model.add_zero x
  add_zero  := Model.add_zero
  add_comm  := Model.add_comm

instance : CommMonoid M where
  mul_assoc := Model.mul_assoc
  one_mul   := fun x => Model.mul_comm x 1 ▸ Model.mul_one x
  mul_one   :=  Model.mul_one
  mul_comm  := Model.mul_comm

instance : LinearOrder M where
  le_refl := fun x => Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy) <;> simp[*, le_def]
    · exact Or.inr (Model.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) <;> simp
    rintro (rfl | hy) <;> try simp
    exact False.elim $ Model.lt_irrefl _ (Model.lt_trans _ _ _ hx hy)
  le_total := by
    intro x y
    rcases Model.lt_tri x y with (h | rfl | h) <;> simp[*, le_def]
  lt_iff_le_not_le := fun x y =>
    ⟨fun h => ⟨Or.inr h, by
      simp[le_def]; rintro (rfl | h'); { exact lt_irrefl y h }; { exact lt_irrefl _ (lt_trans _ _ _ h h') }⟩,
     by simp[not_or, le_def]; rintro (rfl | h) <;> simp[*] ⟩
  decidableLE := fun _ _ => Classical.dec _

lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa[mul_comm] using mul_zero x

instance : LinearOrderedCommSemiring M where
  left_distrib := distr
  right_distrib := fun x y z => by simp[mul_comm _ z]; exact distr z x y
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := Model.mul_assoc
  mul_comm := mul_comm
  one_mul   := fun x => Model.mul_comm x 1 ▸ Model.mul_one x
  mul_one   :=  Model.mul_one
  add_le_add_left := by rintro x y (rfl | h) z <;> simp[add_comm z]; exact Or.inr (add_lt_add x y z h)
  zero_le_one := Or.inr zero_lt_one
  le_of_add_le_add_left := by
    rintro x y z h
    have : y ≤ z ∨ z < y := le_or_lt y z
    rcases this with (hyz | hyz)
    · exact hyz
    · have : x + z < x + y := by simpa[add_comm] using add_lt_add z y x hyz
      exact False.elim ((lt_iff_not_ge _ _).mp this h)
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
  mul_lt_mul_of_pos_left := by
    rintro x y z h hz; simp[mul_zero]; { simpa[mul_comm z] using mul_lt_mul x y z h hz }
  mul_lt_mul_of_pos_right := by
    rintro x y z h hz; simp[mul_zero]; { simpa using mul_lt_mul x y z h hz }
  le_total := le_total
  decidableLE := fun _ _ => Classical.dec _

@[simp] lemma numeral_eq_natCast : (n : ℕ) → (ORingSymbol.numeral n : M) = n
  | 0     => rfl
  | 1     => by simp
  | n + 2 => by simp[ORingSymbol.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]

lemma natCast_add (n m : ℕ) : (↑n : M) + (↑m : M) = ↑(n + m) := by symm; exact Nat.cast_add n m

lemma natCast_mul (n m : ℕ) : (↑n : M) * (↑m : M) = ↑(n * m) := by symm; exact Nat.cast_mul n m

lemma natCast_lt {n m : ℕ} (h : n < m) : (↑n : M) < (↑m : M) := by exact Iff.mpr Nat.cast_lt h



end Model

end

end PAminus

end Arith
