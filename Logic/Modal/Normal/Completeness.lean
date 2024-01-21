import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Soundness

/-!
# Completeness of Normal Modal Logic

## References
- <https://builds.openlogicproject.org/open-logic-complete.pdf>
-/

namespace LO.Modal.Normal

open Finset Set
open Formula Theory
open Deduction

attribute [simp] Finset.subset_union_right Finset.subset_union_left
attribute [simp] Set.insert_subset_iff

variable {α β : Type u} [Inhabited α] [DecidableEq β]

def Formula.FrameConsequence (F : Frame α) (Γ : Theory β) (p : Formula β) := ∀ V w, (⊧ᴹ[⟨F, V⟩, w] Γ) → (⊧ᴹ[⟨F, V⟩, w] p)
notation Γ " ⊨ᴹ[" F "] " p => Formula.FrameConsequence F Γ p
notation Γ " ⊭ᴹ[" F "] " p => ¬(Γ ⊨ᴹ[F] p)

lemma Formula.FrameConsequence.modus_ponens {F : Frame α} {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴹ[F] p ⟶ q) → (Γ ⊨ᴹ[F] p) → (Γ ⊨ᴹ[F] q) := by
  intro hpq hp V w h;
  have hpq := by simpa using hpq V w h;
  have hp := by simpa using hp V w h;
  exact hpq hp;

def Formula.FrameClassConsequence (𝔽 : FrameClass α) (Γ : Theory β) (p : Formula β) := ∀ F ∈ 𝔽, Γ ⊨ᴹ[F] p
notation Γ " ⊨ᴹ[" 𝔽 "] " p => Formula.FrameClassConsequence 𝔽 Γ p
notation Γ " ⊭ᴹ[" 𝔽 "] " p => ¬(Γ ⊨ᴹ[𝔽] p)

namespace Formula.FrameClassConsequence

lemma modus_ponens {𝔽 : FrameClass α} {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴹ[𝔽] p ⟶ q) → (Γ ⊨ᴹ[𝔽] p) → (Γ ⊨ᴹ[𝔽] q) := by
  simp [Formula.FrameClassConsequence];
  intro hpq hp F hF;
  exact (hpq F hF).modus_ponens (hp F hF);

/-
lemma neg {𝔽 : FrameClass α} {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴹ[𝔽] p) ↔ (Γ ⊭ᴹ[𝔽] ~p) := by
  constructor;
  . intro h₁;
    by_contra h₂;
    have := h₂.modus_ponens h₁;
    simp [FrameClassConsequence, FrameConsequence, Satisfies] at this;
  . intro h;
    simp [Formula.FrameClassConsequence];
    intro F hF;
-/

end Formula.FrameClassConsequence

@[simp]
def ExtendedDeducible (Λ) (Γ : Theory β) (p) := ∃ (Δ : Context β), (↑Δ ⊆ Γ) ∧ (Δ ⊢ᴹ[Λ]! p)
notation:40 Γ " ⊢ᴹ[" Λ "]! " p => ExtendedDeducible Λ Γ p

namespace ExtendedDeducible

variable {Λ : AxiomSet β}

lemma axm {Γ : Theory β} {p} : (p ∈ Γ) → (Γ ⊢ᴹ[Λ]! p) := by
  intro hp;
  existsi {p}, (by aesop);
  exact ⟨(Deduction.axm (by simp))⟩;

lemma maxm {Γ : Theory β} {p} : (p ∈ Λ) → (Γ ⊢ᴹ[Λ]! p) := by
  intro hp;
  existsi ∅, (by aesop);
  exact ⟨(Deduction.maxm hp)⟩;

lemma modus_ponens {Γ : Theory β} {p q : Formula β} : (Γ ⊢ᴹ[Λ]! (p ⟶ q)) → (Γ ⊢ᴹ[Λ]! p) → (Γ ⊢ᴹ[Λ]! q) := by
  intro h₁ h₂;
  simp [ExtendedDeducible] at h₁ h₂;
  have ⟨Δ₁, ⟨hΔ₁₁, ⟨hΔ₁₂⟩⟩⟩ := h₁;
  have ⟨Δ₂, ⟨hΔ₂₁, ⟨hΔ₂₂⟩⟩⟩ := h₂;

  have hpq : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] (p ⟶ q) := hΔ₁₂.weakening' (by simp);
  have hp : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] p := hΔ₂₂.weakening' (by simp);

  existsi (Δ₁ ∪ Δ₂), (by aesop);
  exact ⟨(hpq.modus_ponens hp)⟩

lemma monotone : Monotone (λ (Γ : Theory β) => Γ ⊢ᴹ[Λ]! p) := by
  rintro _ _ h ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩;
  existsi Δ;
  constructor;
  . apply Set.Subset.trans hΔ₁ h;
  . exact ⟨hΔ₂⟩;

lemma conj₁ (Γ : Theory β) (p q : Formula β) : (Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ p) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₁ ∅ p q;

lemma conj₁' {Γ : Theory β} {p q : Formula β } (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! p := (conj₁ _ _ _).modus_ponens d

lemma conj₂ (Γ : Theory β) (p q : Formula β) : (Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ q) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₂ ∅ p q;

lemma conj₂' {Γ : Theory β} {p q : Formula β } (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! q := (conj₂ _ _ _).modus_ponens d

lemma conj₃ (Γ : Theory β) (p q : Formula β) : (Γ ⊢ᴹ[Λ]! p ⟶ q ⟶ (p ⋏ q)) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₃ ∅ p q;

lemma conj₃' {Γ : Theory β} {p q : Formula β } (d₁ : Γ ⊢ᴹ[Λ]! p) (d₂ : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) :=
  (conj₃ _ _ _).modus_ponens d₁
    |>.modus_ponens d₂

lemma disj₁ (Γ : Theory β) (p q : Formula β) : (Γ ⊢ᴹ[Λ]! p ⟶ (p ⋎ q)) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₁ ∅ p q;

lemma disj₁' {Γ : Theory β} {p q : Formula β } (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := (disj₁ _ _ _).modus_ponens d

lemma disj₂ (Γ : Theory β) (p q : Formula β) : (Γ ⊢ᴹ[Λ]! q ⟶ (p ⋎ q)) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₂ ∅ p q;

lemma disj₂' {Γ : Theory β} {p q : Formula β } (d : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := (disj₂ _ _ _).modus_ponens d

lemma disj₃ (Γ : Theory β) (p q r : Formula β) : (Γ ⊢ᴹ[Λ]! (p ⟶ r) ⟶ (q ⟶ r) ⟶ ((p ⋎ q) ⟶ r)) := by
  simp [ExtendedDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₃ ∅ p q r;

lemma disj₃' {Γ : Theory β} {p q r : Formula β } (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ r)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ r)) (d₃ : Γ ⊢ᴹ[Λ]! (p ⋎ q)) : Γ ⊢ᴹ[Λ]! r :=
  (disj₃ _ _ _ _)
    |>.modus_ponens d₁
    |>.modus_ponens d₂
    |>.modus_ponens d₃

end ExtendedDeducible

@[simp]
abbrev ExtendedUndeducible (Λ) (Γ : Theory β) (p) := ¬(Γ ⊢ᴹ[Λ]! p)
notation:40 Γ " ⊬ᴹ[" Λ "]! " p => ExtendedUndeducible Λ Γ p

def Theory.FrameSatisfiable (F : Frame α) (Γ : Theory β) := ∃ V w, ⊧ᴹ[⟨F, V⟩, w] Γ

def Theory.FrameClassSatisfiable (𝔽 : FrameClass α) (Γ : Theory β) := ∃ F ∈ 𝔽, Γ.FrameSatisfiable F

section

variable (Λ : AxiomSet β) (Γ : Theory β)

def Maximal := ∀ p, (p ∈ Γ) ∨ (~p ∈ Γ)

def Theory.Inconsistent (Γ : Theory β) := Γ ⊢ᴹ[Λ]! ⊥

def Theory.Consistent (Γ : Theory β) := ¬(Inconsistent Λ Γ)

def Formula.Inconsistent (p : Formula β) := Theory.Inconsistent {p}

def Formula.Consistent (p : Formula β) := Theory.Consistent {p}

def WeakCompleteness := ∀ (p : Formula β), (⊧ᴹ[(𝔽(Λ) : FrameClass α)] p) → (⊢ᴹ[Λ] p)

def Completeness (𝔽 : FrameClass α) := ∀ (Γ : Theory β) (p : Formula β), (Γ ⊨ᴹ[𝔽] p) → (Γ ⊢ᴹ[Λ]! p)

end

variable {Λ : AxiomSet β}
variable {Γ : Set (Formula β)} (hConsisΓ : Theory.Consistent Λ Γ)

@[simp]
lemma inconsistent_insert_falsum : Theory.Inconsistent Λ (insert ⊥ Γ) := by
  simp [Theory.Inconsistent];
  existsi {⊥};
  exact ⟨(by simp), ⟨axm (by simp)⟩⟩;

@[simp]
lemma consistent_isempty_falsum (Δ : Context β) (hΔ : ↑Δ ⊆ Γ) : IsEmpty (Δ ⊢ᴹ[Λ] ⊥) := by
  simp [Theory.Inconsistent, Theory.Consistent] at hConsisΓ;
  exact hConsisΓ Δ (by assumption);

lemma consistent_no_falsum : ∀ (Δ : Context β), ↑Δ ⊆ Γ → ⊥ ∉ Δ := by
  intro Δ hΔ;
  by_contra hC;
  have h₁ : Δ ⊢ᴹ[Λ] ⊥ := axm hC;
  have h₂ : IsEmpty (Δ ⊢ᴹ[Λ] ⊥) := consistent_isempty_falsum hConsisΓ Δ hΔ;
  exact h₂.false h₁;

lemma consistent_no_falsum' : ⊥ ∉ Γ := by
  by_contra;
  apply consistent_no_falsum hConsisΓ {⊥} (by aesop);
  simp;

lemma consistent_neither_provable (p) : (Γ ⊬ᴹ[Λ]! p) ∨ (Γ ⊬ᴹ[Λ]! ~p) := by
  by_contra hC; simp only [not_or] at hC;

  have h₁ := hC.1; simp at h₁;
  have h₂ := hC.2; simp at h₂;

  have ⟨x, ⟨hx₁, ⟨hx₂⟩⟩⟩ := h₁;
  have ⟨y, ⟨hy₁, ⟨hy₂⟩⟩⟩ := h₂;

  simp [Theory.Inconsistent, Theory.Consistent] at hConsisΓ;
  exact hConsisΓ (x ∪ y) (by aesop) |>.false
    $ modus_ponens (hy₂.weakening' (by simp)) (hx₂.weakening' (by simp));

lemma consistent_subset {Γ₁ Γ₂ : Theory β} : (Γ₁ ⊆ Γ₂) → (Consistent Λ Γ₂) → (Consistent Λ Γ₁) := by
  intro hs hConsisΓ₂ hInconsisΓ₁;
  simp [Theory.Consistent, Theory.Inconsistent] at hConsisΓ₂ hInconsisΓ₁;
  have ⟨Δ, hΔ₁, hΔ₂⟩ := hInconsisΓ₁;
  exact hConsisΓ₂ Δ (Set.Subset.trans hΔ₁ hs) |>.false hΔ₂.some;

lemma consistent_insert {Γ : Theory β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_subset (by simp)

lemma frameclass_satisfiable_neg {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊨ᴹ[𝔽] p) ↔ (Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

lemma inconsistent_insert_neg {Γ : Theory β} : (Γ ⊢ᴹ[Λ]! p) ↔ (Inconsistent Λ (insert (~p) Γ)) := by
  constructor;
  . intro h;
    simp only [Theory.Inconsistent];
    have ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩ := h;
    existsi (insert (~p) Δ);
    constructor;
    . simp only [coe_insert];
      apply Set.insert_subset_insert;
      simpa;
    . exact ⟨(axm (by simp)).modus_ponens (hΔ₂.weakening' (by simp))⟩;
  . intro h;
    simp only [Theory.Inconsistent] at h;
    have ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩ := h;
    existsi (Δ.erase (~p));
    constructor;
    . aesop;
    . admit;

lemma consistent_insert_neg {Γ : Theory β} : (Γ ⊬ᴹ[Λ]! p) ↔ (Consistent Λ (insert (~p) Γ)) := inconsistent_insert_neg.not

lemma completeness_def {𝔽 : FrameClass α} : (Completeness Λ 𝔽) ↔ (∀ Γ, Consistent Λ Γ → Theory.FrameClassSatisfiable 𝔽 Γ) := by
  constructor;
  . contrapose;
    admit;
  . contrapose;
    admit;

lemma consistent_false (Δ : Context β) (h : ↑Δ ⊆ Γ) : (Undeducible Λ Δ ⊥) := by
  simp [Theory.Consistent, Theory.Inconsistent] at hConsisΓ;
  simpa using (hConsisΓ Δ h);

def Theory.MaximalConsistent (Λ) (Γ : Theory β) := Theory.Consistent Λ Γ ∧ Maximal Γ

section MaximalConsistent

variable (hMCΓ : MaximalConsistent Λ Γ)

lemma axiomset_include : Λ ⊆ Γ := by
  intro p hp;
  by_contra hC;
  apply consistent_false hMCΓ.1 {~p} (by have := hMCΓ.2 p; aesop) ⟨(axm (by simp)).modus_ponens (maxm hp)⟩;

lemma member_of_maximal_consistent : (p ∈ Γ) ↔ (Γ ⊢ᴹ[Λ]! p) := by
  constructor;
  . intros; existsi {p}; aesop;
  . intro h;
    suffices ~p ∉ Γ by have := hMCΓ.2 p; aesop;
    by_contra hC;
    have ⟨Δ, ⟨hΔ₁, ⟨hΔ₂⟩⟩⟩ := h;
    have : (insert (~p) Δ) ⊢ᴹ[Λ] ⊥ := (axm (by simp)).modus_ponens (hΔ₂.weakening' (by simp));
    have : ↑(insert (~p) Δ) ⊆ Γ := by simp_all [coe_insert, Set.insert_subset_iff];
    apply consistent_false hMCΓ.1 _ (by assumption) ⟨(by assumption)⟩;

lemma not_member_of_maximal_consistent : (p ∉ Γ) ↔ (Γ ⊬ᴹ[Λ]! p) := by
  simpa using (member_of_maximal_consistent hMCΓ).not;

lemma maximal_consistent_modus_ponens {p q : Formula β} : (p ∈ Γ) → ((p ⟶ q) ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq;
  have dp  := (member_of_maximal_consistent hMCΓ).mp hp;
  have dpq := (member_of_maximal_consistent hMCΓ).mp hpq;
  exact (member_of_maximal_consistent hMCΓ).mpr $ dpq.modus_ponens dp;

lemma maximal_neg_include : (~p ∈ Γ) ↔ (p ∉ Γ) := by
  constructor;
  . intros;
    by_contra hC;
    have hp : ({p, ~p}) ⊢ᴹ[Λ] p := axm (by simp);
    have hnp : ({p, ~p}) ⊢ᴹ[Λ] ~p := axm (by simp);
    apply consistent_false hMCΓ.1 {p, ~p} (by aesop;) ⟨hnp.modus_ponens hp⟩;
  . have := hMCΓ.2 p; aesop;

lemma maximal_imp_include : (p ⟶ q ∈ Γ) ↔ (p ∉ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . simp [or_iff_not_imp_left];
    intros;
    apply (member_of_maximal_consistent hMCΓ).mpr;
    have hp : ({p, p ⟶ q}) ⊢ᴹ[Λ] p := axm (by simp);
    have hpq : ({p, p ⟶ q}) ⊢ᴹ[Λ] p ⟶ q := axm (by simp);
    have := hpq.modus_ponens hp;
    existsi {p, p ⟶ q}, (by aesop)
    exact ⟨hpq.modus_ponens hp⟩;
  . intros h;
    cases h;
    case inl h =>
      have := (maximal_neg_include hMCΓ).mpr h;
      have d₁ : Γ ⊢ᴹ[Λ]! (~p ⟶ (p ⟶ q)) := by admit;
      have d₂ : Γ ⊢ᴹ[Λ]! ~p := by existsi {~p}; aesop;
      apply (member_of_maximal_consistent hMCΓ).mpr;
      exact d₁.modus_ponens d₂;
    case inr h =>
      have d₁ : Γ ⊢ᴹ[Λ]! (q ⟶ (p ⟶ q)) := by
        existsi ∅, by simp;
        exact ⟨imply₁ _ _ _⟩;
      have d₂ : Γ ⊢ᴹ[Λ]! q := by existsi {q}; aesop;
      apply (member_of_maximal_consistent hMCΓ).mpr;
      exact d₁.modus_ponens d₂;

lemma maximal_imp_include' : (p ⟶ q ∈ Γ) ↔ ((p ∈ Γ) → (q ∈ Γ)) := by
  constructor;
  . intro hpq hp;
    have := (maximal_imp_include hMCΓ).mp hpq;
    aesop;
  . intro hp;
    apply (maximal_imp_include hMCΓ).mpr;
    simp [or_iff_not_imp_left];
    aesop;

lemma maximal_and_include : (p ⋏ q ∈ Γ) ↔ (p ∈ Γ) ∧ (q ∈ Γ) := by
  constructor;
  . intros h;
    simp_all only [(member_of_maximal_consistent hMCΓ)];
    constructor;
    . exact h.conj₁';
    . exact h.conj₂';
  . rintro ⟨hp, hq⟩;
    simp_all only [(member_of_maximal_consistent hMCΓ)];
    exact ExtendedDeducible.conj₃' hp hq;

lemma maximal_or_include : (p ⋎ q ∈ Γ) ↔ (p ∈ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . intros h;
    -- simp_all only [(member_of_maximal_consistent hMCΓ)];
    have hpq : ({p ⋎ q}) ⊢ᴹ[Λ] (p ⋎ q) := axm (by simp);
    have hpp : ({p ⋎ q}) ⊢ᴹ[Λ] (p ⟶ p ⋎ q) := by admit;
    have hqq : ({p ⋎ q}) ⊢ᴹ[Λ] (q ⟶ p ⋎ q) := by admit;
    admit;
  . intro h;
    simp_all only [(member_of_maximal_consistent hMCΓ)];
    cases h;
    case inl h => exact ExtendedDeducible.disj₁' h;
    case inr h => exact ExtendedDeducible.disj₂' h;

end MaximalConsistent

structure MaximalConsistentTheory (Λ : AxiomSet β) where
  theory : Theory β
  consistent : Consistent Λ theory
  maximal : Maximal theory

namespace MaximalConsistentTheory

variable (Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ)

@[simp]
def membership (p : Formula β) (Ω : MaximalConsistentTheory Λ) := p ∈ Ω.theory
instance : Membership (Formula β) (MaximalConsistentTheory Λ) := ⟨membership⟩

@[simp]
def subset := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (MaximalConsistentTheory Λ) := ⟨subset⟩

@[simp]
def subset' (Γ : Theory β) (Ω : MaximalConsistentTheory Λ) := Γ ⊆ Ω.theory
infix:50 " ⊆ " => subset'

lemma mc : MaximalConsistent Λ Ω.theory := by
  constructor;
  . exact Ω.consistent;
  . exact Ω.maximal;

def box := □Ω.theory
prefix:73  "□" => box

def dia := ◇Ω.theory
prefix:73  "◇" => dia

def unbox := □⁻¹Ω.theory
prefix:73  "□⁻¹" => unbox

def undia := ◇⁻¹Ω.theory
prefix:73  "◇⁻¹" => undia

end MaximalConsistentTheory

section Lindenbaum

variable (Λ : AxiomSet β)
variable [∀ Γ p, Decidable (Consistent Λ (insert p Γ))]
variable [Denumerable (Formula β)]

open Encodable Denumerable

def lindenbaum_step (Γ : Theory β) (p : Formula β) : Theory β :=
  if Consistent Λ (insert p Γ) then (insert p Γ) else insert (~p) Γ

lemma lindenbaum_step_include (Γ : Theory β) : ∀ p, (p ∈ lindenbaum_step Λ Γ p) ∨ (~p ∈ lindenbaum_step Λ Γ p) := by
  intro p;
  simp [lindenbaum_step];
  by_cases hConsis : Consistent Λ (insert p Γ) <;> aesop;

@[simp]
lemma lindenbaum_step_subset (Γ : Theory β) (p : Formula β) : Γ ⊆ lindenbaum_step Λ Γ p := by
  simp only [lindenbaum_step];
  by_cases hConsis : Consistent Λ (insert p Γ) <;> aesop;

def lindenbaum_set (Γ : Theory β) : ℕ → (Theory β)
  | .zero => Γ
  | .succ n => lindenbaum_step Λ (lindenbaum_set Γ n) (ofNat _ n)

notation Γ "[" Λ ", " i "]" => lindenbaum_set Λ Γ i

@[simp]
lemma lindenbaum_set_zero (Γ : Theory β) : Γ[Λ, 0] = Γ := rfl

@[simp]
lemma lindenbaum_set_succ (Γ : Theory β) (n : ℕ) : Γ[Λ, n + 1] = lindenbaum_step Λ (Γ[Λ, n]) (ofNat _ n) := rfl

lemma lindenbaum_set_subset_next (Γ : Theory β) : ∀ n, Γ[Λ, n] ⊆ Γ[Λ, n + 1] := by aesop;

lemma lindenbaum_set_consistent (Γ : Theory β) (hConsisΓ : Consistent Λ Γ) : ∀ n, Consistent Λ (Γ[Λ, n]) := by
  intro n;
  induction n with
  | zero => simpa;
  | succ n ih =>
    simp only [lindenbaum_set, lindenbaum_step];
    split;
    case inl => assumption;
    case inr hInconsis₁ => sorry
      /-
      by_contra hInconsis₂;
      simp [Consistent, Inconsistent, -NegDefinition.neg] at hInconsis₁ hInconsis₂;
      have ⟨Δ₁, ⟨hΔ₁₁, ⟨hΔ₁₂⟩⟩⟩ := hInconsis₁;
      have ⟨Δ₂, ⟨hΔ₂₁, ⟨hΔ₂₂⟩⟩⟩ := hInconsis₂;
      -/

lemma lindenbaum_set_maximal (Γ : Theory β) : ∀ (p : Formula β), p ∈ Γ[Λ, (encode p)] ∨ (~p ∈ Γ[Λ, (encode p)]) := by
  intro p;
  sorry;

def lindenbaum_set_iUnion (Γ : Theory β) := iUnion (lindenbaum_set Λ Γ)
notation Γ "[" Λ "]⁺" => lindenbaum_set_iUnion Λ Γ

lemma lindenbaum_set_iUnion_maximal (Γ : Theory β) : ∀ (p : Formula β), p ∈ Γ[Λ]⁺ ∨ ~p ∈ Γ[Λ]⁺ := by
  intro p;
  simp [lindenbaum_set_iUnion, -NegDefinition.neg];
  cases lindenbaum_set_maximal Λ Γ p;
  case inl h => left; existsi (encode p); assumption;
  case inr h => right; existsi (encode p); assumption;

lemma lindenbaum_set_iUnion_subset_original (Γ : Theory β) : Γ ⊆ Γ[Λ]⁺ := by
  intro p hp;
  simp [lindenbaum_set_iUnion];
  existsi 0;
  simpa;

lemma lindenbaum (hConsisΓ : Consistent Λ Γ) : ∃ (Ω : Theory β), (Γ ⊆ Ω) ∧ (MaximalConsistent Λ Ω) := by
  existsi Γ[Λ]⁺;
  constructor;
  . apply lindenbaum_set_iUnion_subset_original;
  . constructor;
    . admit;
    . apply lindenbaum_set_iUnion_maximal;

lemma lindenbaum' (hConsisΓ : Consistent Λ Γ) : ∃ (Ω : MaximalConsistentTheory Λ), (Γ ⊆ Ω) := by
  have ⟨Ω, hΩ⟩ := lindenbaum Λ hConsisΓ;
  existsi ⟨Ω, hΩ.2.1, hΩ.2.2⟩;
  exact hΩ.1;

end Lindenbaum

/-
@[simp]
lemma Context.box_subset_theory {Γ : Context β} {Δ : Theory β} : (↑Γ ⊆ Δ) → (↑(Γ.box) ⊆ □Δ) := by
  intros;
  simp only [Context.box, Theory.box];
-/

variable (hK : 𝐊 ⊆ Λ)

lemma boxed_context_deducible {Γ : Theory β} (h : Γ ⊢ᴹ[Λ]! p) : (□Γ ⊢ᴹ[Λ]! □p) := by
  have ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩ := h;
  existsi □Δ;
  constructor
  . simpa using box_subset hΔ₁;
  . exact ⟨LogicK.Hilbert.deduction_by_boxed_context hK hΔ₂⟩;

lemma unbox_prov {Γ : Theory β} (h : □⁻¹Γ ⊢ᴹ[Λ]! p) : (Γ ⊢ᴹ[Λ]! □p) := by
  have := boxed_context_deducible hK h;
  simp [MaximalConsistent, Theory.Consistent, Theory.Inconsistent] at this;
  have ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩ := this;
  existsi Δ;
  constructor;
  . exact Set.Subset.trans hΔ₁ (by aesop);
  . exact ⟨hΔ₂⟩;

variable [∀ Γ p, Decidable (Consistent Λ (insert p Γ))]
variable [Denumerable (Formula β)]

lemma mct_mem_box_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (□p ∈ Ω) ↔ (∀ (Ω' : MaximalConsistentTheory Λ), □⁻¹Ω ⊆ Ω' → p ∈ Ω') := by
  constructor;
  . aesop;
  . contrapose;
    intro hC;
    have := (not_member_of_maximal_consistent Ω.mc).mp hC;
    have := consistent_insert_neg.mp $ not_imp_not.mpr (unbox_prov hK) this;
    have ⟨Ω', hΩ'⟩ := lindenbaum' Λ this;
    simp;
    existsi Ω';
    constructor;
    . aesop;
    . exact maximal_neg_include (Ω'.mc) |>.mp (by aesop);

def CanonicalModel (Λ : AxiomSet β) : Model (MaximalConsistentTheory Λ) β where
  frame (Ω₁ Ω₂) := (□⁻¹Ω₁) ⊆ Ω₂
  val (Ω a) := (atom a) ∈ Ω

@[simp]
lemma CanonicalModel.frame_def {Λ : AxiomSet β} {Ω₁ Ω₂ : MaximalConsistentTheory Λ} :
  (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (□⁻¹Ω₁) ⊆ Ω₂
  := by rfl

@[simp]
lemma CanonicalModel.val_def {Λ : AxiomSet β} {Ω : MaximalConsistentTheory Λ} {a : β} :
  a ∈ (CanonicalModel Λ).val Ω ↔ (atom a) ∈ Ω
  := by rfl

variable [∀ Λ Γ p, Decidable (Consistent (Λ : AxiomSet β) (insert p Γ))] [Denumerable (Formula β)]

lemma truthlemma {p : Formula β} : ∀ {Ω}, (⊧ᴹ[CanonicalModel Λ, Ω] p) ↔ (p ∈ Ω) := by
  induction p using rec' with
  | hatom => aesop;
  | hfalsum =>
    intro Ω;
    simpa [Satisfies.bot_def] using consistent_no_falsum' Ω.consistent;
  | himp =>
    intro Ω;
    constructor;
    . intros; apply maximal_imp_include' (Ω.mc) |>.mpr; aesop;
    . intro h; have := maximal_imp_include' (Ω.mc) |>.mp h; aesop;
  | hor =>
    intro Ω;
    constructor;
    . intros; apply maximal_or_include (Ω.mc) |>.mpr; aesop;
    . intro h; have := maximal_or_include (Ω.mc) |>.mp h; aesop;
  | hand =>
    intro Ω;
    constructor;
    . intros; apply maximal_and_include (Ω.mc) |>.mpr; aesop;
    . intro h; have := maximal_and_include (Ω.mc) |>.mp h; aesop;
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply (mct_mem_box_iff hK).mpr;
      intro Ω' hΩ';
      apply ih.mp;
      simp [Satisfies.box_def] at h;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      simp [Set.subset_def] at hΩ';
      exact hΩ' p (by aesop);

lemma truthlemma' {Γ : Theory β} : ∀ {Ω : MaximalConsistentTheory Λ}, (⊧ᴹ[CanonicalModel Λ, Ω] Γ) ↔ (Γ ⊆ Ω) := by
  intro Ω;
  constructor;
  . simp [Set.subset_def];
    intro h p hp;
    exact truthlemma hK |>.mp $ h p hp;
  . intro h p hp;
    apply truthlemma hK |>.mpr;
    aesop;

theorem LogicK.Hilbert.completes : Completeness (𝐊 : AxiomSet β) (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := lindenbaum' (𝐊 : AxiomSet β) hConsisΓ;
  existsi (CanonicalModel 𝐊).frame;
  constructor;
  . apply LogicK.def_FrameClass;
  . existsi (CanonicalModel 𝐊).val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

end LO.Modal.Normal
