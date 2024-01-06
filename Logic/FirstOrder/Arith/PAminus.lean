import Logic.FirstOrder.Arith.Model
import Logic.Vorspiel.ExistsUnique
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Associated
--import Logic.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder

namespace Arith

namespace PAminus

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

open Language

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

@[simp] lemma zero_le : ∀ x : M, 0 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using Theory.Mod.models M (@Theory.PAminus.zeroLe oRing _)

lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using Theory.Mod.models M (@Theory.PAminus.zeroLtOne oRing _)

lemma one_le_of_zero_lt : ∀ x : M, 0 < x → 1 ≤ x := by
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using Theory.Mod.models M (@Theory.PAminus.oneLeOfZeroLt oRing _)

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

instance : CanonicallyOrderedAddCommMonoid M where
  bot := 0
  bot_le := by simp
  exists_add_of_le := by
    rintro x y (rfl | h)
    · exact ⟨0, by simp⟩
    · simpa[eq_comm] using add_eq_of_lt x y h
  le_self_add := by intro x y; simp

@[simp] lemma numeral_eq_natCast : (n : ℕ) → (ORingSymbol.numeral n : M) = n
  | 0     => rfl
  | 1     => by simp
  | n + 2 => by simp[ORingSymbol.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]

lemma not_neg (x : M) : ¬x < 0 := by simp

lemma eq_succ_of_pos {x : M} (h : 0 < x) : ∃ y, x = y + 1 := by
  rcases le_iff_exists_add.mp (one_le_of_zero_lt x h) with ⟨y, rfl⟩
  exact ⟨y, add_comm 1 y⟩

lemma le_of_lt_succ {x y : M} : x < y + 1 ↔ x ≤ y :=
  ⟨fun h => by
    rcases lt_iff_exists_add.mp h with ⟨z, hz, h⟩
    rcases eq_succ_of_pos hz with ⟨z', rfl⟩
    have : y = x + z' := by simpa[←add_assoc] using h
    simp[this],
   by intro h; exact lt_of_le_of_lt h (lt_add_one y)⟩

lemma eq_nat_of_lt_nat : ∀ {n : ℕ} {x : M}, x < n → ∃ m : ℕ, x = m
  | 0,     x, hx => by simp[not_neg] at hx
  | n + 1, x, hx => by
    have : x ≤ n := by simpa[le_of_lt_succ] using hx
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

lemma sigma_zero_completeness : ∀ {n} {σ : Semisentence ℒₒᵣ n},
    Hierarchy Σ 0 σ → ∀ {e}, Semiformula.PVal! ℕ e σ → Semiformula.PVal! M (e ·) σ
  | _, _, Hierarchy.verum _ _ _,               _ => by simp
  | _, _, Hierarchy.falsum _ _ _,              _ => by simp
  | _, _, Hierarchy.rel _ _ Language.Eq.eq v,  e => by simp[Semiformula.eval_rel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.nrel _ _ Language.Eq.eq v, e => by simp[Semiformula.eval_nrel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.rel _ _ Language.LT.lt v,  e => by simp[Semiformula.eval_rel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.nrel _ _ Language.LT.lt v, e => by simp[Semiformula.eval_nrel, Matrix.comp_vecCons', val_numeral]
  | _, _, Hierarchy.and hp hq,                 e => by
    simp; intro ep eq; exact ⟨sigma_zero_completeness hp ep, sigma_zero_completeness hq eq⟩
  | _, _, Hierarchy.or hp hq,                  e => by
    simp; rintro (h | h)
    · left; exact sigma_zero_completeness hp h
    · right; exact sigma_zero_completeness hq h
  | _, _, Hierarchy.ball pt hp,                 e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro h x hx
    rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
    simpa[Matrix.comp_vecCons'] using sigma_zero_completeness hp (h x (by simpa using hx))
  | _, _, Hierarchy.bex pt hp,                  e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro x hx h
    exact ⟨x, by simpa using hx, by simpa[Matrix.comp_vecCons'] using sigma_zero_completeness hp h⟩

lemma sigma_one_completeness : ∀ {n} {σ : Semisentence ℒₒᵣ n},
    Hierarchy Σ 1 σ → ∀ {e}, Semiformula.PVal! ℕ e σ → Semiformula.PVal! M (e ·) σ
  | _, _, Hierarchy.verum _ _ _,               _ => by simp
  | _, _, Hierarchy.falsum _ _ _,              _ => by simp
  | _, _, Hierarchy.rel _ _ r v,               e => sigma_zero_completeness (by simp)
  | _, _, Hierarchy.nrel _ _ r v,              e => sigma_zero_completeness (by simp)
  | _, _, Hierarchy.and hp hq,                 e => by
    simp; intro ep eq; exact ⟨sigma_one_completeness hp ep, sigma_one_completeness hq eq⟩
  | _, _, Hierarchy.or hp hq,                  e => by
    simp; rintro (h | h)
    · left; exact sigma_one_completeness hp h
    · right; exact sigma_one_completeness hq h
  | _, _, Hierarchy.ball pt hp,                 e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro h x hx
    rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
    simpa[Matrix.comp_vecCons'] using sigma_one_completeness hp (h x (by simpa using hx))
  | _, _, Hierarchy.bex pt hp,                  e => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    simp[val_numeral]; intro x hx h
    exact ⟨x, by simpa using hx, by simpa[Matrix.comp_vecCons'] using sigma_one_completeness hp h⟩
  | _, _, Hierarchy.sigma (p := p) hp,         e => by
    simp; intro x h
    have : Hierarchy Σ 1 p := hp.accum _
    exact ⟨x, by simpa[Matrix.comp_vecCons'] using sigma_one_completeness this h⟩
  | _, _, Hierarchy.ex hp,                     e => by
    simp; intro x hx; exact ⟨x, by simpa[Matrix.comp_vecCons'] using sigma_one_completeness hp hx⟩
  | _, _, Hierarchy.accum _ hp,                e => sigma_zero_completeness (by simpa [Hierarchy.zero_iff_sigma_zero] using hp)

end Model

section sigma_one_completeness

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T]

theorem sigma_one_completeness {σ : Sentence ℒₒᵣ} (hσ : Hierarchy Σ 1 σ) :
    ℕ ⊧ₘ σ → T ⊢ σ := fun H =>
  Complete.complete (consequence_of _ _ (fun M _ _ _ _ _ => by
    haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_subtheory (T₁ := T) M (Semantics.ofSystemSubtheory _ _)
    simpa[Matrix.empty_eq] using @Model.sigma_one_completeness M _ _ _ _ _ _ _ hσ ![] (by simpa[models_iff] using H)))

end sigma_one_completeness

namespace Model

variable {x y z : M}

section msub

lemma msub_existsUnique (x y : M) : ∃! z, (x ≥ y → x = y + z) ∧ (x < y → z = 0) := by
  have : y ≤ x ∨ x < y := le_or_lt y x
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simp [show ¬x < y from not_lt.mpr hxy]
    have : ∃ z, x = y + z := exists_add_of_le hxy
    rcases this with ⟨z, rfl⟩
    exact ExistsUnique.intro z rfl (fun x h => (add_left_cancel h).symm)
  · simp [show ¬y ≤ x from not_le.mpr hxy]

def msub (x y : M) : M := Classical.choose! (msub_existsUnique x y)

infix:65 " -̇ " => msub

lemma msub_spec_of_ge (h : x ≥ y) : x = y + (x -̇ y) := (Classical.choose!_spec (msub_existsUnique x y)).1 h

lemma msub_spec_of_lt (h : x < y) : x -̇ y = 0 := (Classical.choose!_spec (msub_existsUnique x y)).2 h

lemma msub_eq_iff : z = x -̇ y ↔ ((x ≥ y → x = y + z) ∧ (x < y → z = 0)) := Classical.choose!_eq_iff _

lemma msub_definable : Σᴬ[0]-Function₂ (λ x y : M ↦ x -̇ y) :=
  ⟨“(#2 ≤ #1 → #1 = #2 + #0) ∧ (#1 < #2 → #0 = 0)”,
    by simp[Hierarchy.zero_iff_sigma_zero], by intro v; simp[msub_eq_iff]; rfl⟩

@[simp] lemma msub_le_self (x y : M) : x -̇ y ≤ x := by
  have : y ≤ x ∨ x < y := le_or_lt y x
  rcases this with (hxy | hxy) <;> simp[hxy]
  · simpa [← msub_spec_of_ge hxy] using show x -̇ y ≤ y + (x -̇ y) from le_add_self
  · simp[msub_spec_of_lt hxy]

lemma msub_polybounded : PolyBounded₂ (λ x y : M ↦ x -̇ y) := ⟨#0, λ _ ↦ by simp⟩

end msub

section Dvd

lemma le_mul_self_of_pos_left (hy : 0 < y) : x ≤ y * x := by
  have : 1 * x ≤ y * x := mul_le_mul_of_nonneg_right (one_le_of_zero_lt y hy) (by simp)
  simpa using this

lemma le_mul_self_of_pos_right (hy : 0 < y) : x ≤ x * y := by
  simpa [mul_comm x y] using le_mul_self_of_pos_left hy

lemma dvd_iff_bounded {x y : M} : x ∣ y ↔ ∃ z ≤ y, y = x * z := by
  by_cases hx : x = 0
  · simp[hx]; rintro rfl; exact ⟨0, by simp⟩
  · constructor
    · rintro ⟨z, rfl⟩; exact ⟨z, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact dvd_mul_right x z

lemma dvd_definable : Σᴬ[0]-Relation (λ x y : M ↦ x ∣ y) :=
  ⟨∃[“#0 < #2 + 1”] “#2 = #1 * #0”, by simp,
  λ v ↦ by simp[dvd_iff_bounded, Matrix.vecHead, Matrix.vecTail, le_of_lt_succ]⟩

end Dvd

@[simp] lemma lt_one_iff_eq_zero : x < 1 ↔ x = 0 := ⟨by
  intro hx
  have : x ≤ 0 := by exact le_of_lt_succ.mp (show x < 0 + 1 from by simpa using hx)
  exact nonpos_iff_eq_zero.mp this,
  by rintro rfl; exact zero_lt_one⟩

lemma le_one_iff_eq_zero_or_one : x ≤ 1 ↔ x = 0 ∨ x = 1 :=
  ⟨by intro h; rcases h with (rfl | ltx)
      · simp
      · simp [show x = 0 from by simpa using ltx],
   by rintro (rfl | rfl) <;> simp⟩

lemma le_of_dvd (h : 0 < y) : x ∣ y → x ≤ y := by
  rintro ⟨z, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show z ≠ 0 from by rintro rfl; simp at h))

lemma dvd_antisymm : x ∣ y → y ∣ x → x = y := by
  intro hx hy
  rcases show x = 0 ∨ 0 < x from eq_zero_or_pos x with (rfl | ltx)
  · simp [show y = 0 from by simpa using hx]
  · rcases show y = 0 ∨ 0 < y from eq_zero_or_pos y with (rfl | lty)
    · simp [show x = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)

lemma dvd_one : x ∣ 1 ↔ x = 1 := ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩

section Prime

lemma eq_one_or_eq_of_dvd_of_prime {p x : M} (pp : Prime p) (hxp : x ∣ p) : x = 1 ∨ x = p := by
  have : p ∣ x ∨ x ∣ 1 := pp.left_dvd_or_dvd_right_of_dvd_mul (show x ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one.mp hx

/-
lemma prime_iff_bounded {x : M} : Prime x ↔ 1 < x ∧ ∀ y ≤ x, (y ∣ x → y = 1 ∨ y = x) := by
  constructor
  · intro prim
    have : 1 < x := by
      by_contra A; simp at A
      rcases le_one_iff_eq_zero_or_one.mp A with (rfl | rfl)
      · exact not_prime_zero prim
      · exact not_prime_one prim
    exact ⟨this, fun y hy hyx ↦ eq_one_or_eq_of_dvd_of_prime prim hyx⟩
  · intro H; constructor
    · sorry
    · constructor
      · sorry
      · intro y z h
-/

def IsPrime (x : M) : Prop := 1 < x ∧ ∀ y ≤ x, (y ∣ x → y = 1 ∨ y = x)
-- TODO: prove IsPrime x ↔ Prime x

lemma isPrime_definable : Σᴬ[0]-Predicate (λ x : M ↦ IsPrime x) := by
  have : Σᴬ[0]-Relation (λ x y : M ↦ x ∣ y) := dvd_definable
  rcases this with ⟨dvd, hdvd, sdvd⟩
  let prime : Semisentence ℒₒᵣ 1 := “1 < #0” ⋏ (∀[“#0 < #1 + 1”] dvd ⟶ “#0 = 1 ∨ #0 = #1”)
  exact ⟨prime, by simp[prime, hdvd, Hierarchy.zero_iff_sigma_zero],
    fun v ↦ by
      simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.vecHead, Matrix.constant_eq_singleton,
        IsPrime, ← sdvd, le_of_lt_succ]⟩

end Prime

end Model

end

end PAminus

end Arith
