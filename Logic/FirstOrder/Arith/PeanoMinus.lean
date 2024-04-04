import Logic.FirstOrder.Arith.Model
import Logic.Vorspiel.ExistsUnique
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Associated

namespace LO

namespace FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

open Language

namespace Model

instance : LE M := ⟨fun x y => x = y ∨ x < y⟩

lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl

protected lemma add_zero : ∀ x : M, x + 0 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addZero

protected lemma add_assoc : ∀ x y z : M, (x + y) + z = x + (y + z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addAssoc

protected lemma add_comm : ∀ x y : M, x + y = y + x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addComm

lemma add_eq_of_lt : ∀ x y : M, x < y → ∃ z, x + z = y := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addEqOfLt

@[simp] lemma zero_le : ∀ x : M, 0 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M Theory.peanoMinus.zeroLe

lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.zeroLtOne

lemma one_le_of_zero_lt : ∀ x : M, 0 < x → 1 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M Theory.peanoMinus.oneLeOfZeroLt

lemma add_lt_add : ∀ x y z : M, x < y → x + z < y + z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addLtAdd

protected lemma mul_zero : ∀ x : M, x * 0 = 0 := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulZero

protected lemma mul_one : ∀ x : M, x * 1 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulOne

protected lemma mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulAssoc

protected lemma mul_comm : ∀ x y : M, x * y = y * x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulComm

lemma mul_lt_mul : ∀ x y z : M, x < y → 0 < z → x * z < y * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulLtMul

lemma distr : ∀ x y z : M, x * (y + z) = x * y + x * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.distr

lemma lt_irrefl : ∀ x : M, ¬x < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltIrrefl

lemma lt_trans : ∀ x y z : M, x < y → y < z → x < z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltTrans

lemma lt_tri : ∀ x y : M, x < y ∨ x = y ∨ y < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltTri

instance : AddCommMonoid M where
  add_assoc := Model.add_assoc
  zero_add  := fun x => Model.add_comm x 0 ▸ Model.add_zero x
  add_zero  := Model.add_zero
  add_comm  := Model.add_comm
  nsmul := nsmulRec

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

protected lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa[mul_comm] using Model.mul_zero x

instance : LinearOrderedCommSemiring M where
  left_distrib := distr
  right_distrib := fun x y z => by simp[mul_comm _ z]; exact distr z x y
  zero_mul := Model.zero_mul
  mul_zero := Model.mul_zero
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

instance : CanonicallyOrderedAddCommMonoid M where
  bot := 0
  bot_le := by simp
  exists_add_of_le := by
    rintro x y (rfl | h)
    · exact ⟨0, by simp⟩
    · simpa[eq_comm] using add_eq_of_lt x y h
  le_self_add := by intro x y; simp

lemma numeral_eq_natCast : (n : ℕ) → (ORingSymbol.numeral n : M) = n
  | 0     => rfl
  | 1     => by simp
  | n + 2 => by simp[ORingSymbol.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]

lemma not_neg (x : M) : ¬x < 0 := by simp

lemma eq_succ_of_pos {x : M} (h : 0 < x) : ∃ y, x = y + 1 := by
  rcases le_iff_exists_add.mp (one_le_of_zero_lt x h) with ⟨y, rfl⟩
  exact ⟨y, add_comm 1 y⟩

lemma le_iff_lt_succ {x y : M} : x ≤ y ↔ x < y + 1 :=
  ⟨by intro h; exact lt_of_le_of_lt h (lt_add_one y),
   fun h => by
    rcases lt_iff_exists_add.mp h with ⟨z, hz, h⟩
    rcases eq_succ_of_pos hz with ⟨z', rfl⟩
    have : y = x + z' := by simpa[←add_assoc] using h
    simp[this]⟩

lemma eq_nat_of_lt_nat : ∀ {n : ℕ} {x : M}, x < n → ∃ m : ℕ, x = m
  | 0,     x, hx => by simp[not_neg] at hx
  | n + 1, x, hx => by
    have : x ≤ n := by simpa[le_iff_lt_succ] using hx
    rcases this with (rfl | hx)
    · exact ⟨n, rfl⟩
    · exact eq_nat_of_lt_nat hx

open Hierarchy

lemma val_numeral {n} : ∀ (t : Semiterm ℒₒᵣ Empty n),
    ∀ v, Semiterm.val! M (v ·) Empty.elim t = (Semiterm.val! ℕ v Empty.elim t)
  | #_,                                _ => by simp
  | Semiterm.func Language.Zero.zero _, e => by simp
  | Semiterm.func Language.One.one _,   e => by simp
  | Semiterm.func Language.Add.add v,   e => by simp[Semiterm.val_func, val_numeral (v 0), val_numeral (v 1)]
  | Semiterm.func Language.Mul.mul v,   e => by simp[Semiterm.val_func, val_numeral (v 0), val_numeral (v 1)]

lemma pval_of_pval_nat_of_sigma_one : ∀ {n} {σ : Semisentence ℒₒᵣ n},
    Hierarchy Σ 1 σ → ∀ {e}, Semiformula.PVal! ℕ e σ → Semiformula.PVal! M (e ·) σ
  | _, _, Hierarchy.verum _ _ _,               _ => by simp
  | _, _, Hierarchy.falsum _ _ _,              _ => by simp
  | _, _, Hierarchy.rel _ _ Language.Eq.eq v,  e => by simp[Semiformula.eval_rel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.nrel _ _ Language.Eq.eq v, e => by simp[Semiformula.eval_nrel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.rel _ _ Language.LT.lt v,  e => by simp[Semiformula.eval_rel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.nrel _ _ Language.LT.lt v, e => by simp[Semiformula.eval_nrel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.and hp hq,                 e => by
    simp; intro ep eq; exact ⟨pval_of_pval_nat_of_sigma_one hp ep, pval_of_pval_nat_of_sigma_one hq eq⟩
  | _, _, Hierarchy.or hp hq,                  e => by
    simp; rintro (h | h)
    · left; exact pval_of_pval_nat_of_sigma_one hp h
    · right; exact pval_of_pval_nat_of_sigma_one hq h
  | _, _, Hierarchy.ball pt hp,                e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro h x hx
    rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
    simpa[Matrix.comp_vecCons'] using pval_of_pval_nat_of_sigma_one hp (h x (by simpa using hx))
  | _, _, Hierarchy.bex pt hp,                 e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro x hx h
    exact ⟨x, by simpa using hx, by simpa[Matrix.comp_vecCons'] using pval_of_pval_nat_of_sigma_one hp h⟩
  | _, _, Hierarchy.sigma (p := p) hp,         e => by
    simp; intro x h
    have : Hierarchy Σ 1 p := hp.accum _
    exact ⟨x, by simpa[Matrix.comp_vecCons'] using pval_of_pval_nat_of_sigma_one this h⟩
  | _, _, Hierarchy.ex hp,                     e => by
    simp; intro x hx; exact ⟨x, by simpa[Matrix.comp_vecCons'] using pval_of_pval_nat_of_sigma_one hp hx⟩

end Model

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≾ T] [𝐏𝐀⁻ ≾ T]

theorem sigma_one_completeness {σ : Sentence ℒₒᵣ} (hσ : Hierarchy Σ 1 σ) :
    ℕ ⊧ₘ σ → T ⊢ σ := fun H =>
  Complete.complete (oRing_consequence_of _ _ (fun M _ _ _ _ _ _ => by
    haveI : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_subtheory (T₁ := T) inferInstance (Semantics.ofSystemSubtheory _ _)
    simpa [Matrix.empty_eq] using Model.pval_of_pval_nat_of_sigma_one (M := M) hσ H))

end

end Arith

end FirstOrder

end LO
