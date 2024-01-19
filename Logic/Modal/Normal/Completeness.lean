import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Soundness

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
def ExtendedDeducible (Λ) (Γ : Theory β) (p) := ∃ (Δ : Finset (Formula β)), (↑Δ ⊆ Γ) ∧ (Δ ⊢ᴹ[Λ]! p)
notation:40 Γ " ⊢ᴹ[" Λ "]! " p => ExtendedDeducible Λ Γ p

namespace ExtendedDeducible

lemma axm {Λ : AxiomSet β} {Γ : Theory β} {p} : (p ∈ Γ) → (Γ ⊢ᴹ[Λ]! p) := by
  intro hp;
  existsi {p}, (by aesop);
  exact ⟨(Deduction.axm (by simp))⟩;

lemma modus_ponens {Λ : AxiomSet β} {Γ : Theory β} {p q : Formula β} : (Γ ⊢ᴹ[Λ]! (p ⟶ q)) → (Γ ⊢ᴹ[Λ]! p) → (Γ ⊢ᴹ[Λ]! q) := by
  intro h₁ h₂;
  simp [ExtendedDeducible] at h₁ h₂;
  have ⟨Δ₁, ⟨hΔ₁₁, ⟨hΔ₁₂⟩⟩⟩ := h₁;
  have ⟨Δ₂, ⟨hΔ₂₁, ⟨hΔ₂₂⟩⟩⟩ := h₂;

  have hpq : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] (p ⟶ q) := hΔ₁₂.weakening' (by simp);
  have hp : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] p := hΔ₂₂.weakening' (by simp);

  existsi (Δ₁ ∪ Δ₂), (by aesop);
  exact ⟨(hpq.modus_ponens hp)⟩

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
lemma consistent_isempty_falsum (Δ : Finset (Formula β)) (hΔ : ↑Δ ⊆ Γ) : IsEmpty (Δ ⊢ᴹ[Λ] ⊥) := by
  simp [Theory.Inconsistent, Theory.Consistent] at hConsisΓ;
  exact hConsisΓ Δ (by assumption);

lemma consistent_no_falsum : ∀ (Δ : Finset (Formula β)), ↑Δ ⊆ Γ → ⊥ ∉ Δ := by
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

lemma not_consequence_iff {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊨ᴹ[𝔽] p) ↔ (Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

lemma not_deducible_iff {Γ : Theory β} : (Γ ⊬ᴹ[Λ]! p) ↔ (Consistent Λ (insert (~p) Γ)) := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

lemma completeness_def {𝔽 : FrameClass α} : (Completeness Λ 𝔽) ↔ (∀ Γ, Consistent Λ Γ → Theory.FrameClassSatisfiable 𝔽 Γ) := by
  constructor;
  . contrapose;
    admit;
  . contrapose;
    admit;

lemma consistent_false (Δ : Finset (Formula β)) (h : ↑Δ ⊆ Γ) : (Undeducible Λ Δ ⊥) := by
  simp [Theory.Consistent, Theory.Inconsistent] at hConsisΓ;
  simpa using (hConsisΓ Δ h);

def MaximalConsistent (Λ) (Γ : Theory β) := Theory.Consistent Λ Γ ∧ Maximal Γ

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

end MaximalConsistent

structure MaximalConsistentTheory (Λ : AxiomSet β) where
  theory : Theory β
  consistent : Consistent Λ theory
  maximal : Maximal theory

namespace MaximalConsistentTheory

@[simp]
def membership (p : Formula β) (Ω : MaximalConsistentTheory Λ) := p ∈ Ω.theory
instance : Membership (Formula β) (MaximalConsistentTheory Λ) := ⟨membership⟩

@[simp]
def subset (Ω₁ Ω₂ : MaximalConsistentTheory Λ) := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (MaximalConsistentTheory Λ) := ⟨subset⟩

@[simp]
def subset' (Γ : Theory β) (Ω : MaximalConsistentTheory Λ) := Γ ⊆ Ω.theory
infix:50 "⊆" => subset'

@[simp]
lemma mc (Ω : MaximalConsistentTheory Λ) : MaximalConsistent Λ Ω.theory := by
  constructor;
  . exact Ω.consistent;
  . exact Ω.maximal;

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

def CanonicalModel (Λ : AxiomSet β) : Model (MaximalConsistentTheory Λ) β where
  frame (Ω₁ Ω₂) := ∀ (p : Formula β), (□p ∈ Ω₁) → (p ∈ Ω₂)
  val (Ω a) := (atom a) ∈ Ω

@[simp]
lemma CanonicalModel_frame {Λ : AxiomSet β} {Ω₁ Ω₂ : MaximalConsistentTheory Λ} :
  (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (∀ (p : Formula β), (□p ∈ Ω₁) → (p ∈ Ω₂))
  := by rfl

@[simp]
lemma CanonicalModel_val {Λ : AxiomSet β} {Ω : MaximalConsistentTheory Λ} {a : β} :
  a ∈ (CanonicalModel Λ).val Ω ↔ (atom a) ∈ Ω
  := by rfl

lemma truthlemma {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (⊧ᴹ[CanonicalModel Λ, Ω] p) ↔ (p ∈ Ω) := by
  induction p using rec' with
  | hatom a => aesop;
  | hfalsum => simpa [Satisfies.bot_def] using consistent_no_falsum' Ω.consistent;
  | himp p q ihp ihq =>
    -- simp [ihp, ihq];
    constructor;
    . intro h;
      admit
    . intros;
      sorry;
  | hor p q ih =>
    constructor;
    . intro h; sorry;
    . intro h; sorry;
  | hand p q ihp ihq =>
    constructor;
    . intro h; sorry;
    . intro h; sorry;
  | hbox p ih =>
    constructor;
    . contrapose;
      intro h;
      sorry;
    . intro h Δ h₂;
      have b := h₂ _ h;
      sorry;

lemma truthlemma' {Ω : MaximalConsistentTheory Λ} {Γ : Theory β} : (⊧ᴹ[CanonicalModel Λ, Ω] Γ) ↔ (Γ ⊆ Ω) := by
  constructor;
  . simp [Set.subset_def];
    intro h p hp;
    exact truthlemma.mp $ h p hp;
  . intro h p hp;
    apply truthlemma.mpr;
    aesop;

variable [∀ Λ Γ p, Decidable (Consistent (Λ : AxiomSet β) (insert p Γ))] [Denumerable (Formula β)]

theorem LogicK.Hilbert.completes : Completeness (𝐊 : AxiomSet β) (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β)) ) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := lindenbaum' (𝐊 : AxiomSet β) hConsisΓ;
  existsi (CanonicalModel 𝐊).frame;
  constructor;
  . apply LogicK.def_FrameClass;
  . existsi (CanonicalModel 𝐊).val, Ω;
    apply truthlemma'.mpr;
    assumption;

end LO.Modal.Normal
