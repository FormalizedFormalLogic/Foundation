import Logic.FirstOrder.Completeness.Corollaries
import Logic.FirstOrder.Arith.Model
import Logic.Vorspiel.ExistsUnique
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

noncomputable section

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

open Language

scoped instance : LE M := ⟨fun x y => x = y ∨ x < y⟩

lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl

protected lemma add_zero (x : M) : x + 0 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addZero (fun _ ↦ x)

protected lemma add_assoc (x y z : M) : (x + y) + z = x + (y + z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma add_comm (x y : M) : x + y = y + x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addComm (x :>ₙ fun _ ↦ y)

lemma add_eq_of_lt (x y : M) : x < y → ∃ z, x + z = y := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addEqOfLt (x :>ₙ fun _ ↦ y)

@[simp] lemma zero_le (x : M) : 0 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M Theory.peanoMinus.zeroLe (fun _ ↦ x)

lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.zeroLtOne

lemma one_le_of_zero_lt (x : M) : 0 < x → 1 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M Theory.peanoMinus.oneLeOfZeroLt (fun _ ↦ x)

lemma add_lt_add (x y z : M) : x < y → x + z < y + z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.addLtAdd (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_zero (x : M) : x * 0 = 0 := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulZero (fun _ ↦ x)

protected lemma mul_one (x : M) : x * 1 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulOne (fun _ ↦ x)

protected lemma mul_assoc (x y z : M) : (x * y) * z = x * (y * z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_comm (x y : M) : x * y = y * x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulComm (x :>ₙ fun _ ↦ y)

lemma mul_lt_mul (x y z : M) : x < y → 0 < z → x * z < y * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.mulLtMul (x :>ₙ y :>ₙ fun _ ↦ z)

lemma distr (x y z : M) : x * (y + z) = x * y + x * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.distr (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_irrefl (x : M) : ¬x < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltIrrefl (fun _ ↦ x)

protected lemma lt_trans (x y z : M) : x < y → y < z → x < z := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltTrans (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_tri (x y : M) : x < y ∨ x = y ∨ y < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.peanoMinus.ltTri (x :>ₙ fun _ ↦ y)

scoped instance : AddCommMonoid M where
  add_assoc := Arith.add_assoc
  zero_add  := fun x => Arith.add_comm x 0 ▸ Arith.add_zero x
  add_zero  := Arith.add_zero
  add_comm  := Arith.add_comm
  nsmul := nsmulRec

scoped instance : CommMonoid M where
  mul_assoc := Arith.mul_assoc
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one
  mul_comm  := Arith.mul_comm

scoped instance : LinearOrder M where
  le_refl := fun x => Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy) <;> simp[*, le_def]
    · exact Or.inr (Arith.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) <;> simp
    rintro (rfl | hy) <;> try simp
    exact False.elim $ Arith.lt_irrefl _ (Arith.lt_trans _ _ _ hx hy)
  le_total := by
    intro x y
    rcases Arith.lt_tri x y with (h | rfl | h) <;> simp[*, le_def]
  lt_iff_le_not_le := fun x y =>
    ⟨fun h => ⟨Or.inr h, by
      simp only [le_def]; rintro (rfl | h'); { exact lt_irrefl y h }; { exact lt_irrefl _ (Arith.lt_trans _ _ _ h h') }⟩,
     by simp[not_or, le_def]; rintro (rfl | h) <;> simp[*] ⟩
  decidableLE := fun _ _ => Classical.dec _

protected lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa[mul_comm] using Arith.mul_zero x

scoped instance : LinearOrderedCommSemiring M where
  left_distrib := distr
  right_distrib := fun x y z => by simp[mul_comm _ z]; exact distr z x y
  zero_mul := Arith.zero_mul
  mul_zero := Arith.mul_zero
  mul_assoc := Arith.mul_assoc
  mul_comm := mul_comm
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one
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

scoped instance : CanonicallyOrderedAddCommMonoid M where
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

lemma val_numeral {n} : ∀ (t : Semiterm ℒₒᵣ ξ n),
    ∀ v f, Semiterm.valm M (v ·) (f ·) t = (Semiterm.valm ℕ v f t)
  | #_,                                 _ => by simp
  | &x,                                 _ => by simp
  | Semiterm.func Language.Zero.zero _, e => by simp
  | Semiterm.func Language.One.one _,   e => by simp
  | Semiterm.func Language.Add.add v,   e => by simp[Semiterm.val_func, val_numeral (v 0), val_numeral (v 1)]
  | Semiterm.func Language.Mul.mul v,   e => by simp[Semiterm.val_func, val_numeral (v 0), val_numeral (v 1)]

lemma bold_sigma_one_completeness {n} {p : Semiformula ℒₒᵣ ξ n} (hp : Hierarchy 𝚺 1 p) {e f} :
    Semiformula.Evalm ℕ e f p → Semiformula.Evalm M (e ·) (f ·) p := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hNEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hLT => intro n t₁ t₂ e; simp [val_numeral]
  case hNLT => intro n t₁ t₂ e; simp [val_numeral]
  case hAnd =>
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, and_imp]
    intro n p q _ _ ihp ihq e hp hq
    exact ⟨ihp hp, ihq hq⟩
  case hOr =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rintro n p q _ _ ihp ihq e (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq
  case hBall =>
    simp only [Semiformula.eval_ball, Nat.succ_eq_add_one, Semiformula.eval_operator₂,
      Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Structure.LT.lt, val_numeral]
    intro n t p _ ihp e hp x hx
    rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
    simpa [Matrix.comp_vecCons'] using ihp (hp x (by simpa using hx))
  case hEx =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one, forall_exists_index]
    intro n p _ ihp e x hp
    exact ⟨x, by simpa [Matrix.comp_vecCons'] using ihp hp⟩

lemma sigma_one_completeness {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ → M ⊧ₘ₀ σ := by
  simp [models₀_iff]; intro h
  simpa [Matrix.empty_eq, Empty.eq_elim] using bold_sigma_one_completeness hσ h

end Arith

namespace FirstOrder.Arith

open LO.Arith

variable {T : Theory ℒₒᵣ}

theorem sigma_one_completeness [𝐄𝐐 ≼ T] [𝐏𝐀⁻ ≼ T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ → T ⊢! ↑σ := fun H =>
  complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by
    haveI : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_provably_subtheory M 𝐏𝐀⁻ T inferInstance (by assumption)
    exact LO.Arith.sigma_one_completeness hσ H

theorem sigma_one_completeness_iff [𝐏𝐀⁻ ≼ T] [ℕ ⊧ₘ* T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ ↔ T ⊢₌! ↑σ :=
  haveI : 𝐏𝐀⁻ ≼ T⁼ := System.Subtheory.comp (𝓣 := T) inferInstance inferInstance
  ⟨fun h ↦ sigma_one_completeness (T := T⁼) hσ h, fun h ↦ consequence_iff_add_eq.mp (sound₀! h) ℕ inferInstance⟩

end FirstOrder.Arith

end LO

end
