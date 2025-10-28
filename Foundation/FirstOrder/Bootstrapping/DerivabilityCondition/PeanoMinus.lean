import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory

/-!
# Bootstrapping theory $\mathsf{PA}^-$, $\mathsf{R_0}$ in $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗣𝗔⁻]

lemma lt_add_self_add_one (a b : V) : a < b + a + 1 := lt_succ_iff_le.mpr <| le_add_self

lemma lt_succ_iff_eq_or_succ {a b : V} : a < b + 1 ↔ a = b ∨ a < b := by
  simp [lt_succ_iff_le, le_iff_eq_or_lt]

end LO.FirstOrder.Arithmetic

namespace LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

open Classical LO.Entailment

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

local prefix:max "#'" => Semiterm.bvar  (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

local postfix:max "⇞" => Semiterm.shift

local postfix:max "⤉" => Semiformula.shift

variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝗣𝗔⁻ ⪯ T]

open Entailment Entailment.FiniteContext Semiformula

instance : 𝗘𝗤 ⪯ T := WeakerThan.trans inferInstance (inferInstanceAs (𝗣𝗔⁻ ⪯ T))

lemma term_add_assoc (t₁ t₂ t₃ : Term V ℒₒᵣ) :
    T.internalize V ⊢ t₁ + (t₂ + t₃) ≐ (t₁ + t₂) + t₃ := by
  have : T ⊢ “∀ x y z, x + (y + z) = (x + y) + z” :=
    provable_of_models.{0} _ _ fun M _ hM ↦ by
      have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
      simp [models_iff, add_assoc]
  have : T.internalize V ⊢ ∀' ∀' ∀' (#'2 + (#'1 + #'0) ≐ #'2 + #'1 + #'0) := by
    simpa using internal_provable_of_outer_provable (V := V) this
  simpa using TProof.specialize₃! this t₃ t₂ t₁

lemma numeral_add (n m : V) :
    T.internalize V ⊢ (𝕹 n + 𝕹 m) ≐ 𝕹 (n + m) := by
  induction m using sigma1_pos_succ_induction
  · simp only [tprovable_iff_provable, val_equals, val_add, val_numeral]
    definability
  case zero =>
    have : T.internalize V ⊢ ∀' ((#'0 + 𝕹 0) ≐ #'0) := by
      have : T ⊢ “∀ x, x + 0 = x” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specialize! this <| 𝕹 n
  case one =>
    rcases eq_zero_or_pos n with (rfl | pos)
    · have : T.internalize V ⊢ (𝕹 0 + 𝕹 1) ≐ 𝕹 1 := by
        have : T ⊢ “0 + 1 = 1” :=
          provable_of_models.{0} _ _ fun M _ hM ↦ by
            have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
            simp [models_iff]
        simpa using internal_provable_of_outer_provable (V := V) this
      simpa using this
    · simp [numeral_succ_pos' pos]
  case succ m ih =>
    suffices
      T.internalize V ⊢ 𝕹 n + (𝕹 (m + 1) + 𝕹 1) ≐ 𝕹 (n + m + 1) + 𝕹 1 by simpa [←one_add_one_eq_two, ←add_assoc]
    have e1 : T.internalize V ⊢ 𝕹 n + (𝕹 (m + 1) + 𝕹 1) ≐ (𝕹 n + 𝕹 (m + 1)) + 𝕹 1 := term_add_assoc T _ _ _
    have e2 : T.internalize V ⊢ (𝕹 n + 𝕹 (m + 1)) + 𝕹 1 ≐ 𝕹 (n + (m + 1)) + 𝕹 1 :=
      subst_add_eq_add T _ _ _ _ ⨀! ih ⨀! (eq_refl T (𝕹 1))
    simpa [add_assoc] using eq_trans e1 e2

lemma numeral_mul (n m : V) :
    T.internalize V ⊢ 𝕹 n * 𝕹 m ≐ 𝕹 (n * m) := by
  induction m using sigma1_pos_succ_induction
  · simp only [tprovable_iff_provable, val_equals, val_mul, val_numeral]
    definability
  case zero =>
    have : T.internalize V ⊢ ∀' ((#'0 * 𝕹 0) ≐ 𝕹 0) := by
      have : T ⊢ “∀ x, x * 0 = 0” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specialize! this (𝕹 n)
  case one =>
    have : T.internalize V ⊢ ∀' ((#'0 * 𝕹 1) ≐ #'0) := by
      have : T ⊢ “∀ x, x * 1 = x” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff]
      have := internal_provable_of_outer_provable (V := V) this
      simpa using this
    simpa using TProof.specialize! this (𝕹 n)
  case succ m ih =>
    suffices
        T.internalize V ⊢ 𝕹 n * (𝕹(m + 1) + 𝕹 1) ≐ 𝕹(n * (m + 1) + n) by
      simpa [←one_add_one_eq_two, ←add_assoc, mul_add]
    have e1 : T.internalize V ⊢ 𝕹 n * (𝕹(m + 1) + 𝕹 1) ≐ 𝕹 n * 𝕹(m + 1) + 𝕹 n := by
      have : T ⊢ “∀ x y, x * (y + 1) = x * y + x” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff, mul_add]
      have := by simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂! this 𝕹(m + 1) (𝕹 n)
    have e2 : T.internalize V ⊢ 𝕹 n * 𝕹(m + 1) + 𝕹 n ≐ 𝕹 (n * (m + 1)) + 𝕹 n :=
      subst_add_eq_add T _ _ _ _ ⨀! ih ⨀! (eq_refl T (𝕹 n))
    have e3 : T.internalize V ⊢ 𝕹 (n * (m + 1)) + 𝕹 n ≐ 𝕹 (n * (m + 1) + n) := numeral_add T _ _
    exact eq_trans (eq_trans e1 e2) e3

lemma numeral_eq {n m : V} :
    n = m → T.internalize V ⊢ 𝕹 n ≐ 𝕹 m := by
  rintro rfl; exact eq_refl T (𝕹 n)

lemma numeral_lt {n m : V} :
    n < m → T.internalize V ⊢ 𝕹 n <' 𝕹 m := fun h ↦ by
  let d := m - (n + 1)
  have hm : m = d + n + 1 := by
    simpa [d, add_assoc] using Eq.symm <| sub_add_self_of_le <| succ_le_iff_lt.mpr h
  suffices T.internalize V ⊢ 𝕹 n <' 𝕹 (d + n + 1) by simpa [hm]
  have l₁ : T.internalize V ⊢ 𝕹 n <' 𝕹 d + 𝕹 n + 𝕹 1 := by
    have : T ⊢ “∀ x y, x < y + x + 1” :=
      provable_of_models.{0} _ _ fun M _ hM ↦ by
        have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
        simp [models_iff, Arithmetic.lt_add_self_add_one]
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize₂! this (𝕹 d) (𝕹 n)
  have l₂ : T.internalize V ⊢ 𝕹 d + 𝕹 n + 𝕹 1 ≐ 𝕹 (d + n + 1) := by
    have e₁ : T.internalize V ⊢ 𝕹 d + 𝕹 n + 𝕹 1 ≐ 𝕹 (d + n) + 𝕹 1 :=
      subst_add_eq_add T _ _ _ _ ⨀ numeral_add T d n ⨀ eq_refl T (𝕹 1)
    have e₂ : T.internalize V ⊢ 𝕹 (d + n) + 𝕹 1 ≐ 𝕹 (d + n + 1) :=
      numeral_add T (d + n) 1
    exact eq_trans e₁ e₂
  exact subst_lt T (𝕹 n) (𝕹 n) (𝕹 d + 𝕹 n + 𝕹 1) (𝕹(d + n + 1)) ⨀ eq_refl T (𝕹 n) ⨀ l₂ ⨀ l₁

lemma numeral_ne {n m : V} :
    n ≠ m → T.internalize V ⊢ 𝕹 n ≉ 𝕹 m := fun h ↦ by
  wlog hnm : n < m
  · have hmn : m < n := by exact lt_of_le_of_ne (by simpa using hnm) (Ne.symm h)
    exact ne_symm T _ _ ⨀ (this T (Ne.symm h) hmn)
  have l₁ : T.internalize V ⊢ 𝕹 n <' 𝕹 m := numeral_lt T hnm
  have l₂ : T.internalize V ⊢ (𝕹 n <' 𝕹 m) ➝ (𝕹 n ≉ 𝕹 m) := by
    have : T ⊢ “∀ x y, x < y → x ≠ y” :=
      provable_of_models.{0} _ _ fun M _ hM ↦ by
        have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
        simpa [models_iff] using fun _ _ ↦ ne_of_lt
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize₂! this (𝕹 m) (𝕹 n)
  exact l₂ ⨀ l₁

lemma numeral_nlt {n m : V} :
    n ≥ m → T.internalize V ⊢ 𝕹 n ≮' 𝕹 m := fun h ↦ by
  rcases eq_or_lt_of_le h with (rfl | lt)
  · have : T ⊢ “∀ x, x ≮ x” :=
      provable_of_models.{0} _ _ fun M _ hM ↦ by
        have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
        simp [models_iff]
    have := by simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize! this (𝕹 m)
  · have l₁ : T.internalize V ⊢ 𝕹 m <' 𝕹 n := numeral_lt T lt
    have l₂ : T.internalize V ⊢ (𝕹 m <' 𝕹 n) ➝ (𝕹 n ≮' 𝕹 m) := by
      have : T ⊢ “∀ x y, x < y → y ≮ x” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simpa [models_iff] using fun _ _ ↦ le_of_lt
      have := by simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂! this (𝕹 n) (𝕹 m)
    exact l₂ ⨀ l₁

lemma lt_iff_substItrDisj (t : Term V ℒₒᵣ) (m : V) :
    T.internalize V ⊢ (t <' 𝕹 m) ⭤ substItrDisj ![t] (#'1 ≐ #'0) m := by
  induction m using sigma1_pos_succ_induction
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, tprovable_iff_provable,
      val_iff, val_lessThan, val_numeral, substItrDisj_val, SemitermVec.val_succ, Matrix.head_cons,
      Matrix.tail_cons, SemitermVec.val_nil, val_equals, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, Nat.cast_one, Nat.zero_mod, Nat.cast_zero]
    definability
  case zero =>
    suffices T.internalize V ⊢ (t <' 𝕹 0) ⭤ ⊥ by simpa
    have : T.internalize V ⊢ ∀' ((#'0 <' 𝕹 0) ⭤ ⊥) := by
      have : T ⊢ “∀ x, x < 0 ↔ ⊥” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff]
      simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize! this t
  case one =>
    suffices T.internalize V ⊢ (t <' 𝕹 1) ⭤ (t ≐ 𝕹 0) ⋎ ⊥ by simpa
    have : T.internalize V ⊢ ∀' ((#'0 <' 𝕹 1) ⭤ (#'0 ≐ 𝕹 0) ⋎ ⊥) := by
      have : T ⊢ “∀ x, x < 1 ↔ x = 0 ∨ ⊥” :=
        provable_of_models.{0} _ _ fun M _ hM ↦ by
          have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
          simp [models_iff]
      simpa using internal_provable_of_outer_provable (V := V) this
    simpa using TProof.specialize! this t
  case succ m ih =>
    suffices
        T.internalize V ⊢
          (t <' 𝕹(m + 1) + 𝕹 1) ⭤ (t ≐ 𝕹(m + 1)) ⋎ substItrDisj ![t] (#'1 ≐ #'0) (m + 1) by
      simpa [←one_add_one_eq_two, ←add_assoc]
    have : T.internalize V ⊢ (t <' 𝕹(m + 1) + 𝕹 1) ⭤ (t ≐ 𝕹(m + 1)) ⋎ (t <' 𝕹(m + 1)) := by
      have : T.internalize V ⊢ ∀' ∀' ((#'0 <' #'1 + 𝕹 1) ⭤ (#'0 ≐ #'1) ⋎ (#'0 <' #'1)) := by
        have : T ⊢ “∀ m x, x < m + 1 ↔ x = m ∨ x < m” :=
          provable_of_models.{0} _ _ fun M _ hM ↦ by
            have : M ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory hM
            simp [models_iff, Arithmetic.lt_succ_iff_eq_or_succ]
        simpa using internal_provable_of_outer_provable (V := V) this
      simpa using TProof.specialize₂! this t 𝕹(m + 1)
    cl_prover [ih, this]

lemma ball_intro (φ : Semiformula V ℒₒᵣ 1) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢ φ.subst ![𝕹 i]) :
    T.internalize V ⊢ φ.ball (𝕹 n) := by
  apply TProof.all!
  suffices T.internalize V ⊢ (&'0 <' 𝕹 n) ➝ φ⤉.subst ![&'0] by
    simpa [imp_def, Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  suffices T.internalize V ⊢ substItrDisj ![&'0] (#'1 ≐ #'0) n ➝ φ⤉.subst ![&'0] from
    C!_trans (K!_left (lt_iff_substItrDisj T &'0 n)) this
  apply TProof.substItrDisj_left_intro
  · intro i hi
    suffices T.internalize V ⊢ (&'0 ≐ 𝕹 i) ➝ φ⤉.subst ![&'0] by simpa
    have hi : T.internalize V ⊢ φ⤉.subst ![𝕹 i] := by
      simpa [Semiformula.shift_substs] using TProof.shift! (bs i hi)
    have rl : T.internalize V ⊢ (𝕹 i ≐ &'0) ➝ φ⤉.subst ![𝕹 i] ➝ φ⤉.subst ![&'0] :=
      replace T φ.shift (𝕹 i) (&'0)
    have ec : T.internalize V ⊢ (&'0 ≐ 𝕹 i) ➝ (𝕹 i ≐ &'0) := eq_symm T (Semiterm.fvar 0) (𝕹 i)
    cl_prover [hi, rl, ec]

lemma bex_intro (φ : Semiformula V ℒₒᵣ 1) (n : V) {i}
    (hi : i < n) (b : T.internalize V ⊢ φ.subst ![𝕹 i]) :
    T.internalize V ⊢ φ.bex (𝕹 n) := by
  apply TProof.ex! (𝕹 i)
  suffices T.internalize V ⊢ (𝕹 i <' 𝕹 n) ⋏ φ.subst ![𝕹 i] by simpa
  apply K!_intro
  · exact numeral_lt T hi
  · exact b

lemma ball_replace (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ (t ≐ u) ➝ φ.ball t ➝ φ.ball u := by
  simpa [SemitermVec.q, Semiformula.substs_substs] using replace T ((φ.subst ![#'0]).ball #'0) t u

lemma bex_replace (φ : Semiformula V ℒₒᵣ 1) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ (t ≐ u) ➝ φ.bex t ➝ φ.bex u := by
  simpa [SemitermVec.q, Semiformula.substs_substs] using replace T ((φ.subst ![#'0]).bex #'0) t u

end LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
