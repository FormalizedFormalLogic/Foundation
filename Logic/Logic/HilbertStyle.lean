import Logic.Logic.System

namespace LO

namespace System

variable (F : Type u) [LogicSymbol F] [System F]

class Intuitionistic where
  modus_ponens {T : Set F} {p q : F}   : T ⊢! p ⟶ q → T ⊢! p → T ⊢! q
  verum       (T : Set F)             : T ⊢! ⊤
  falsum      (T : Set F) (p : F)     : T ⊢! ⊥ ⟶ p
  imply₁      (T : Set F) (p q : F)   : T ⊢! p ⟶ q ⟶ p
  imply₂      (T : Set F) (p q r : F) : T ⊢! (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁       (T : Set F) (p q : F)   : T ⊢! p ⋏ q ⟶ p
  conj₂       (T : Set F) (p q : F)   : T ⊢! p ⋏ q ⟶ q
  conj₃       (T : Set F) (p q : F)   : T ⊢! p ⟶ q ⟶ p ⋏ q
  disj₁       (T : Set F) (p q : F)   : T ⊢! p ⟶ p ⋎ q
  disj₂       (T : Set F) (p q : F)   : T ⊢! q ⟶ p ⋎ q
  disj₃       (T : Set F) (p q r : F) : T ⊢! (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r
  neg₁        (T : Set F) (p q : F)   : T ⊢! (p ⟶ q) ⟶ (p ⟶ ~q) ⟶ ~p
  neg₂        (T : Set F) (p q : F)   : T ⊢! p ⟶ ~p ⟶ q

class Deduction where
  deduction {T : Set F} {p q : F} : T ⊢! p ⟶ q ↔ T ∪ {p} ⊢! q

variable {F}
variable {Struc : Type w → Type v} [𝓢 : Semantics F Struc]

namespace Intuitionistic

variable [Intuitionistic F] {T : Set F}

scoped infixl:90 " ⨀ " => modus_ponens

@[simp] lemma imp_id (p : F) : T ⊢! p ⟶ p := (imply₂ T p (p ⟶ p) p) ⨀ (imply₁ T p (p ⟶ p)) ⨀ (imply₁ T p p)

@[simp] lemma hyp_right {p : F} (h : T ⊢! p) (q) : T ⊢! q ⟶ p := imply₁ T p q ⨀ h

lemma imp_trans {p q r : F} (hp : T ⊢! p ⟶ q) (hq : T ⊢! q ⟶ r) : T ⊢! p ⟶ r :=
  imply₂ T p q r ⨀ hyp_right hq p ⨀ hp

lemma and_split {p q : F} (hp : T ⊢! p) (hq : T ⊢! q) : T ⊢! p ⋏ q := (conj₃ T p q) ⨀ hp ⨀ hq

lemma and_left {p q : F} (h : T ⊢! p ⋏ q) : T ⊢! p := conj₁ T p q ⨀ h

lemma and_right {p q : F} (h : T ⊢! p ⋏ q) : T ⊢! q := conj₂ T p q ⨀ h

lemma and_symm {p q : F} (h : T ⊢! p ⋏ q) : T ⊢! q ⋏ p := and_split (and_right h) (and_left h)

lemma or_left {p q : F} (h : T ⊢! p) : T ⊢! p ⋎ q := disj₁ T p q ⨀ h

lemma or_right {p q : F} (h : T ⊢! q) : T ⊢! p ⋎ q := disj₂ T p q ⨀ h

lemma or_symm {p q : F} (h : T ⊢! p ⋎ q) : T ⊢! q ⋎ p := (disj₃ T _ _ _) ⨀ (disj₂ _ _ _) ⨀ (disj₁ _ _ _) ⨀ h

lemma iff_refl (p : F) : T ⊢! p ⟷ p := and_split (imp_id p) (imp_id p)

lemma iff_symm {p q : F} (h : T ⊢! p ⟷ q) : T ⊢! q ⟷ p := and_split (and_right h) (and_left h)

lemma iff_trans {p q r : F} (hp : T ⊢! p ⟷ q) (hq : T ⊢! q ⟷ r) : T ⊢! p ⟷ r :=
  and_split (imp_trans (and_left hp) (and_left hq)) (imp_trans (and_right hq) (and_right hp))

lemma iff_mp {p q : F} (h : T ⊢! p ⟷ q) : T ⊢! p ⟶ q := and_left h

lemma iff_mpr {p q : F} (h : T ⊢! p ⟷ q) : T ⊢! q ⟶ p := and_right h

lemma iff_unprov {p q : F} (h₁ : T ⊢! p ⟷ q) (h₂ : T ⊬! p) : T ⊬! q := by
  by_contra hC;
  suffices : T ⊢! p; aesop;
  exact (iff_mpr h₁) ⨀ (by simpa using hC);

lemma unprov_imp_left_iff (h₁ : T ⊬! σ ⟶ π) (h₂ : T ⊢! σ ⟷ ρ): (T ⊬! ρ ⟶ π) := by
  by_contra HC;
  suffices : T ⊢! σ ⟶ π; simp_all only [not_isEmpty_of_nonempty];
  exact imp_trans (iff_mp h₂) (by simpa using HC);

lemma unprov_imp_right_iff (h₁ : T ⊬! σ ⟶ π) (h₂ : T ⊢! π ⟷ ρ): (T ⊬! σ ⟶ ρ) := by
  by_contra HC;
  suffices : T ⊢! σ ⟶ π; simp_all only [not_isEmpty_of_nonempty];
  exact imp_trans (by simpa using HC) (iff_mpr h₂);

class BotDef (F : Type u) [LogicSymbol F] where
  bot_def : (⊥ : F) = ~(⊤ : F)
open BotDef

variable [BotDef F]

lemma no_contradiction {p : F} (h₁ : T ⊢! p) (h₂ : T ⊢! ~p) : T ⊢! ⊥ := by
  have hl := imply₁ T p ⊤ ⨀ h₁;
  have hr := imply₁ T (~p) ⊤ ⨀ h₂;
  simpa [bot_def] using (neg₁ T ⊤ p) ⨀ hl ⨀ hr;

lemma neg_imply_bot' {p : F} (h : T ⊢! ~p) : T ⊢! ~~p ⟶ ⊥ := by
  exact neg₂ T (~p) ⊥ ⨀ h;

lemma efq (p : F) : T ⊢! ⊥ ⟶ p := by
  simpa [bot_def] using neg₂ T ⊤ p ⨀ verum T;

class DoubleNeg (F : Type u) [LogicSymbol F] where
  double_neg : ∀ (p : F), ~~p = p
open DoubleNeg

variable [DoubleNeg F]

lemma neg_imply_bot (p : F) (h : T ⊢! ~p) : (T ⊢! p ⟶ ⊥) := by
  simpa [double_neg] using (neg₂ T (~p) ⊥ ⨀ h);

-- TODO: DoubleNegを仮定する必要は確か無い（直観主義論理で示せる）はず
lemma negneg_intro (p : F) : T ⊢! p ⟶ ~~p := by simp [double_neg];

lemma negneg_elim (p : F) : T ⊢! p ⟶ ~~p := by simp [double_neg];

class ImpDef (F : Type u) [LogicSymbol F] where
  imp_def {p q : F} : (p ⟶ q) = ~p ⋎ q

variable [ImpDef F]

lemma imp_contra₀ {p q} (h : T ⊢! p ⟶ q) : (T ⊢! ~q ⟶ ~p) := by
  simp_all [ImpDef.imp_def, DoubleNeg.double_neg, or_symm];

lemma imp_contra₁ {p q} (h : T ⊢! p ⟶ ~q) : (T ⊢! q ⟶ ~p) := by simpa [double_neg] using (imp_contra₀ h);

lemma imp_contra₂ {p q} (h : T ⊢! ~p ⟶ q) : (T ⊢! ~q ⟶ p) := by simpa [double_neg] using (imp_contra₀ h);

lemma imp_contra₃ {p q} (h : T ⊢! ~p ⟶ ~q) : (T ⊢! q ⟶ p) := by simpa [double_neg] using (imp_contra₀ h);

lemma iff_intro : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ σ) → (T ⊢! σ ⟷ π) := λ H₁ H₂ => conj₃ _ _ _ ⨀ H₁ ⨀ H₂

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := λ H => iff_intro (imp_contra₀ $ iff_mpr H) (imp_contra₀ $ iff_mp H)

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := λ H => iff_symm $ iff_contra H

end Intuitionistic

section complete

variable [Complete F]

instance : Intuitionistic F where
  modus_ponens := fun {T p q} b₁ b₂ =>
    Complete.consequence_iff_provable.mp (fun M _ s hM => by
      rcases b₁ with ⟨b₁⟩; rcases b₂ with ⟨b₂⟩
      have : s ⊧ₛ p → s ⊧ₛ q := by simpa using Sound.models_of_proof hM b₁
      exact this (Sound.models_of_proof hM b₂))
  verum  := fun T => Complete.consequence_iff_provable.mp (fun M _ _ _ => by simp)
  falsum := fun T p => Complete.consequence_iff_provable.mp (fun M _ _ _ => by simp)
  imply₁ := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a _ => a)
  imply₂ := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b c => a c (b c))
  conj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a _ => a)
  conj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp)
  conj₃  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b => ⟨a, b⟩)
  disj₁  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.inl)
  disj₂  := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.inr)
  disj₃  := fun T p q r => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simpa using Or.rec)
  neg₁   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b c => (b c) (a c))
  neg₂   := fun T p q => Complete.consequence_iff_provable.mp (fun _ _ _ _ => by simp; exact fun a b => (b a).elim)

instance : Deduction F where
  deduction := fun {T p q} =>
    ⟨ fun b => Complete.consequence_iff_provable.mp (fun M _ s hM => by
        rcases b with ⟨b⟩
        have hM : s ⊧ₛ p ∧ s ⊧ₛ* T := by simpa using hM
        have : s ⊧ₛ p → s ⊧ₛ q := by simpa using Sound.models_of_proof hM.2 b
        exact this hM.1),
      fun b =>
      Complete.consequence_iff_provable.mp (fun M _ s hM => by
        rcases b with ⟨b⟩
        simp; intro hp; exact Sound.models_of_proof (s := s) (by simp[*]) b) ⟩

end complete

end System

end LO
