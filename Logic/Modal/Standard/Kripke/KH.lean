import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

variable [DecidableEq α] [Inhabited α]

namespace Kripke

open System
open Kripke
open Formula Formula.Kripke

variable (a : α) {F : Kripke.Frame}

lemma valid_H_of_valid_L : F# ⊧ Axioms.L (atom a) → F# ⊧ Axioms.H (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ⟶ a)) := by intro y Rxy; exact hx Rxy |>.1;
  exact @h V x this;


lemma valid_L_of_valid_H : F# ⊧ Axioms.H (atom a) → F# ⊧ Axioms.L (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro hH V x hx;

  let M : Kripke.Model α := ⟨F#, V⟩;
  let V' : Valuation F α := λ w a => ∀ n : ℕ, Satisfies ⟨F#, V⟩ w (□^[n] a);

  let M' : Kripke.Model α := ⟨F, V'⟩;

  have h₁ : Satisfies M' x (□(□a ⟷ a)) := by
    intro y Rxy;
    have : Satisfies M' y a ↔ Satisfies M' y (□a) := calc
      _ ↔ ∀ n, Satisfies M y (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ n, Satisfies M y (□^[(n + 1)]a) := by
        constructor;
        . intro h n; apply h;
        . intro h n;
          have h₁ : Satisfies M y (□□^[n](atom a) ⟶ □^[n](atom a)) := by
            induction n with
            | zero => apply hx Rxy;
            | succ n => intro _; apply h;
          apply h₁;
          simpa using h n;
      _ ↔ ∀ n, ∀ z, y ≺ z → Satisfies M z (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ z, y ≺ z → ∀ n : ℕ, Satisfies M z (□^[n]a) := by aesop;
      _ ↔ ∀ z, y ≺ z → Satisfies M' z (atom a) := by simp [Satisfies];
      _ ↔ Satisfies M' y (□(atom a)) := by simp [Satisfies];
    exact ⟨this.2, this.1⟩;

  have H : Satisfies M' x (□atom a) := @hH M'.Valuation x h₁;

  intro w hxw;
  exact H hxw 0;

lemma iff_valid_L_valid_H : F# ⊧ Axioms.L (atom a) ↔ F# ⊧ Axioms.H (atom a) := by
  constructor;
  . exact valid_H_of_valid_L a;
  . exact valid_L_of_valid_H a;


section

abbrev CresswellFrame : Kripke.Frame where
  World := ℕ × Bool
  Rel n m :=
    match n, m with
    | (n, true), (m, true) => n ≤ m + 1
    | (n, false), (m, false) => n > m
    | (_, true), (_, false) => True
    | _, _ => False

namespace CresswellFrame

variable {n m : ℕ}

@[match_pattern]
abbrev sharp (n : ℕ) : CresswellFrame.World := (n, true)
postfix:max "♯" => sharp

abbrev SharpWorld := { w : CresswellFrame.World // w.2 = true }
instance : LE CresswellFrame.SharpWorld := ⟨λ x y => x.1 ≤ y.1⟩


@[match_pattern]
abbrev flat (n : ℕ) : CresswellFrame.World := (n, false)
postfix:max "♭" => flat

abbrev FlatWorld := { w : CresswellFrame.World // w.2 = false }
instance : LE CresswellFrame.SharpWorld := ⟨λ x y => x.1 ≤ y.1⟩


lemma sharp_cresc (h : n ≤ m) : n♯ ≺ m♯ := by omega;

lemma sharp_refl : n♯ ≺ n♯ := by omega;

lemma flat_irrefl : ¬(n♭ ≺ n♭) := by omega;

lemma flat_iff : n > m ↔ n♭ ≺ m♭ := by omega;


lemma bridge : n♯ ≺ m♭ := by simp [Frame.Rel'];

/-
  `0♯ ≺ 1♯ ≺ 2# ≺ ⋯ ≺ n♯ ≺ ⋯ ≺ n♭ ⋯ ≺ 2♭ ≺ 1♭ ≺ 0♭`

  - reflexive in `♯`
  - irreflexive in `♭`
-/

end CresswellFrame

abbrev CresswellModel (α) : Kripke.Model α := ⟨CresswellFrame, λ w _ => w ≠ 0♯⟩

namespace CresswellModel

@[reducible]
instance : Semantics (Formula α) (CresswellModel α).World := Formula.Kripke.Satisfies.semantics (M := CresswellModel α)

lemma not_satisfies_Four : ¬(Satisfies (CresswellModel α) 2♯ (Axioms.Four (atom a))) := by
  simp [Satisfies, Axioms.Four];
  constructor;
  . intro x h;
    by_contra hC; subst hC;
    simp [Frame.Rel'] at h;
  . use 1;

abbrev Truthset (p : Formula α) := { w : (CresswellModel α).World | w ⊧ p }
scoped prefix:80 "𝒯 " => CresswellModel.Truthset

namespace Truthset

variable (p q : Formula α)

@[simp] lemma top : 𝒯 (⊤ : Formula α) = Set.univ := by simp [Truthset, Satisfies];
@[simp] lemma bot : 𝒯 (⊥ : Formula α) = ∅ := by simp [Truthset, Satisfies];
@[simp] lemma and : 𝒯 (p ⋏ q) = 𝒯 p ∩ 𝒯 q := by simp [Truthset]; rfl;
@[simp] lemma or  : 𝒯 (p ⋎ q) = 𝒯 p ∪ 𝒯 q := by simp [Truthset]; rfl;
@[simp] lemma neg : 𝒯 (~p) = (𝒯 p)ᶜ := by simp [Truthset, Satisfies]; aesop;
@[simp] lemma imp : 𝒯 (p ⟶ q) = (𝒯 p)ᶜ ∪ 𝒯 q := by simp_all [Truthset, Satisfies, imp_iff_not_or]; rfl;

end Truthset


abbrev _root_.Set.Cofinite (s : Set α) := sᶜ.Finite

@[simp]
lemma _root_.Set.cofinite_compl (s : Set α) : sᶜ.Cofinite ↔ s.Finite := by simp [Set.Cofinite];

lemma _root_.Set.comp_finite (s : Set α) : s.Finite → sᶜ.Cofinite := by
  intro h;
  simp [Set.Cofinite];
  exact h;

lemma either_finite_cofinite (p : Formula α) : (𝒯 p).Finite ∨ (𝒯 p)ᶜ.Finite := by
  induction p using Formula.rec' with
  | hatom a => simp [Truthset, Satisfies];
  | hverum => simp;
  | hfalsum => simp;
  | hneg p ih => rcases ih with (_ | _) <;> simp_all;
  | hor p q ihp ihq =>
    simp [Set.compl_union];
    rcases ihp with (_ | _) <;> rcases ihq with (_ | _);
    . left; simp_all;
    . right; apply Set.Finite.inter_of_right; assumption;
    . right; apply Set.Finite.inter_of_left; assumption;
    . right; apply Set.Finite.inter_of_left; assumption;
  | hand p q ihp ihq =>
    simp [Set.compl_inter];
    rcases ihp with (_ | _) <;> rcases ihq with (_ | _);
    . left; apply Set.Finite.inter_of_left; assumption;
    . left; apply Set.Finite.inter_of_left; assumption;
    . left; apply Set.Finite.inter_of_right; assumption;
    . right; simp_all;
  | himp p q ihp ihq =>
    simp [Set.compl_union];
    rcases ihp with (_ | _) <;> rcases ihq with (_ | _);
    . right; apply Set.Finite.inter_of_left; assumption;
    . right; apply Set.Finite.inter_of_left; assumption;
    . left; simp_all;
    . right; apply Set.Finite.inter_of_right; assumption;
  | hbox p ih =>
    by_cases H : ∀ n, Satisfies (CresswellModel α) n♭ p;
    . have : ¬((𝒯 p).Finite) := by
        simp [Truthset];
        sorry;
      have : (𝒯 p)ᶜ.Finite := by aesop;
      sorry;
    . push_neg at H;
      obtain ⟨n, h⟩ := H;
      have h_sharp : ∀ m : ℕ, ¬Satisfies (CresswellModel α) m♯ (□p) := by
        intro m;
        simp only [Satisfies]; push_neg;
        use n♭;
      have h_flat : ∀ m : ℕ, m > n → ¬Satisfies (CresswellModel α) m♭ (□p) := by
        intro m hmn;
        simp only [Satisfies]; push_neg;
        use n♭;
      have : ∀ w, w ≺ n♭ → ¬Satisfies (CresswellModel α) w (□p) := by
        intro w hmn;
        match w with
        | w♯ => apply h_sharp;
        | w♭ =>
          apply h_flat;
          apply CresswellFrame.flat_iff.mpr;
          assumption;
      left;
      simp [Truthset, Set.Finite];
      sorry;

open CresswellFrame

lemma valid_H : (CresswellModel α) ⊧* (𝗛 : AxiomSet α) := by
  simp; intro p;

  wlog H : ∃ w, ¬(Satisfies (CresswellModel α) w p);
  case inr =>
    simp at H;
    intro x h₁ y Rxy;
    apply h₁ Rxy |>.1;
    intro z Ryz;
    match z with
    | z♯ => exact H z |>.2;
    | z♭ => exact H z |>.1;

  by_cases h : ∀ n, n♭ ∈ (𝒯 p);
  . have : ¬((𝒯 p).Finite) := by
      simp [Truthset];
      sorry;
    have : (𝒯 p).Cofinite := by
      have := @either_finite_cofinite α p
      aesop;
    sorry;
  . sorry;


end CresswellModel

lemma _root_.LO.Modal.Standard.KH_not_Four : 𝐊𝐇 ⊬! Axioms.Four (atom a) := by
  sorry;

lemma _root_.LO.Modal.Standard.KH_not_Loeb : 𝐊𝐇 ⊬! Axioms.L (atom a) := by
  by_contra hC;
  have : System.HasAxiomL 𝐊𝐇 := ⟨by
    intro p;
    simpa [subst] using KH_deduct_substitution a p hC |>.some;
  ⟩;
  have : 𝐊𝐇 ⊢! Axioms.Four (atom a) := axiomFour!;
  exact KH_not_Four a this;

end

notation "Thm(" Λ:90 ")" => System.theory Λ

/-- Set of frame that every theorems of `Λ` are valid on. -/
abbrev TheoremsFrameClass (Λ : DeductionParameter α) : FrameClass.Dep α := { F : Frame | F# ⊧* Thm(Λ) }
notation "𝔽(" Λ:90 ")" => TheoremsFrameClass Λ

variable [Inhabited α]

lemma KH_incompleteAux (𝔽 : FrameClass) (hFH : 𝔽# ⊧* (𝗛 : AxiomSet α)) : ∃ p : Formula α, (𝔽# ⊧ p ∧ 𝐊𝐇 ⊬! p) := by
  by_contra hC;
  push_neg at hC;
  have := hC (Axioms.L (atom default)) ?h;
  have := KH_not_Loeb (α := α) default;
  contradiction;

  intro F hF;
  apply iff_valid_L_valid_H (default) |>.mpr;
  simp at hFH;
  exact hFH _ hF;

theorem KH_incomplete : ∃ p : Formula α, 𝔽(𝐊𝐇) ⊧ p ∧ 𝐊𝐇 ⊬! p := by
  obtain ⟨p, hs, hp⟩ := KH_incompleteAux (α := α) 𝔽(𝐊𝐇) $ by
    simp;
    intro p F hp;
    exact Semantics.realizeSet_iff.mp hp (by simp [System.theory]);
  use p;

/--
  Type class for _"`Λ` is incomplete for Kripke semantics"_
-/
class Incomplete (Λ : DeductionParameter α) : Prop where
  incomplete : ∃ p, 𝔽(Λ) ⊧ p ∧ Λ ⊬! p

instance : Incomplete (α := α) 𝐊𝐇 := ⟨KH_incomplete⟩

end Kripke

end LO.Modal.Standard
