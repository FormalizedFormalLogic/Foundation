import Logic.Propositional.Basic.Completeness
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Soundness

namespace LO.Modal.Normal

open Finset
open Formula Context Deduction

variable {α β : Type u} [DecidableEq β]

namespace Formula

/-
@[simp] def FrameConsequence (f : Frame α) (Γ : Context β) (p : Formula β) := ∀ V w, (w ⊧ᴹˢ[⟨f, V⟩] Γ) → (w ⊧ᴹˢ[⟨f, V⟩] p)

notation Γ " ⊨ᴹᶠ[" f "] " p => Formula.FrameConsequence f Γ p
notation Γ " ⊭ᴹᶠ[" f "] " p => ¬(Γ ⊨ᴹᶠ[f] p)

namespace FrameConsequence

variable {f : Frame α} {Γ Γ' : Context β} {p q : Formula β}

@[simp] lemma def_emptyctx : (∅ ⊨ᴹᶠ[f] p) ↔ (⊧ᴹᶠ[f] p) := by aesop;
@[simp] lemma axiomK : (Γ ⊨ᴹᶠ[f] AxiomK p q) := by aesop;
@[simp] lemma weakening : (Γ ⊆ Γ') → (Γ ⊨ᴹᶠ[f] p) → (Γ' ⊨ᴹᶠ[f] p) := by aesop;
@[simp] lemma modus_ponens : (Γ ⊨ᴹᶠ[f] p ⟶ q) → (Γ ⊨ᴹᶠ[f] p) → (Γ ⊨ᴹᶠ[f] q) := by aesop;

end FrameConsequence
-/

def Consequence (α) (Λ : AxiomSet β) (Γ : Context β) (p : Formula β) := ∀ f ∈ FrameClass α β Λ, ∀ V w, (w ⊧ᴹˢ[⟨f, V⟩] Γ) → (w ⊧ᴹˢ[⟨f, V⟩] p)

notation Γ " ⊨ᴹ[" Λ "," α "] " p => Consequence α Λ Γ p
notation Γ " ⊭ᴹ[" Λ "," α "] " p => ¬(Γ ⊨ᴹ[Λ, α] p)

end Formula

section

variable (Λ : AxiomSet β) (Γ : Context β)

def Maximal := ∀ p, p ∈ Γ ∨ ~p ∈ Γ

def Inconsistent (Γ : Set (Formula β)) := ∃ (Δ : Finset (Formula β)), (↑Δ ⊆ Γ) ∧ (Δ ⊢ᴹ[Λ]! ⊥)

def Consistent (Γ : Set (Formula β)) := ¬(Inconsistent Λ Γ)

def WeakCompleteness := ∀ (f : Frame α) (p : Formula β), (⊧ᴹᶠ[f] p) → (⊢ᴹ[Λ] p)

def Completeness (Λ α) := ∀ Γ (p : Formula β), (Γ ⊨ᴹ[Λ, α] p) → (∃ (Δ : Finset (Formula β)), (↑Δ ⊆ Γ) → (Δ ⊢ᴹ[Λ]! p))

def FrameClassSatisfiable (Λ α) (Γ : Context β) := ∃ f ∈ FrameClass α β Λ, ∃ V w, w ⊧ᴹˢ[⟨f, V⟩] Γ

end

variable {Λ : AxiomSet β}
variable {Γ : Set (Formula β)} (hConsisΓ : Consistent Λ Γ)

@[simp]
lemma inconsistent_insert_falsum : Inconsistent Λ (insert ⊥ Γ) := by
  simp [Inconsistent];
  existsi {⊥};
  exact ⟨(by simp), ⟨axm (by simp)⟩⟩;

@[simp]
lemma consistent_isempty_falsum (Δ : Finset (Formula β)) (hΔ : ↑Δ ⊆ Γ) : IsEmpty (Δ ⊢ᴹ[Λ] ⊥) := by
  simp [Inconsistent, Consistent] at hConsisΓ;
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

lemma consistent_neither_provable : ∀ (Δ : Finset (Formula β)), ↑Δ ⊆ Γ → ¬((Δ ⊢ᴹ[Λ]! p) ∧ (Δ ⊢ᴹ[Λ]! ~p)) := by
  intro Δ hΔ;
  by_contra hC;
  have := consistent_isempty_falsum hConsisΓ Δ hΔ;
  exact this.false (modus_ponens hC.2.some hC.1.some);

lemma consistent_neg_undeducible : ∀ (Δ : Finset (Formula β)), ↑Δ ⊆ Γ → (Δ ⊢ᴹ[Λ]! p) → (Δ ⊬ᴹ[Λ]! ~p) := by
  intro Δ hΔ hp hn;
  exact consistent_neither_provable hConsisΓ Δ hΔ ⟨hp, hn⟩;

lemma consistent_neither_included : ∀ (Δ : Finset (Formula β)), ↑Δ ⊆ Γ → ∀ p, ¬(p ∈ Δ ∧ ~p ∈ Δ) := by
  intro Δ hΔ p;
  by_contra hC;
  exact consistent_neither_provable hConsisΓ Δ hΔ ⟨⟨axm hC.1⟩, ⟨axm hC.2⟩⟩;

lemma consistent_subset {Γ₁ Γ₂ : Context β} : (Γ₁ ⊆ Γ₂) → (Consistent Λ Γ₂) → (Consistent Λ Γ₁) := by
  intro hs hConsisΓ₂ hInconsisΓ₁;
  simp [Consistent, Inconsistent] at hConsisΓ₂ hInconsisΓ₁;
  have ⟨Δ, hΔ₁, hΔ₂⟩ := hInconsisΓ₁;
  exact (hConsisΓ₂ Δ (Set.Subset.trans hΔ₁ hs)).false hΔ₂.some;

lemma consistent_insert {Γ : Context β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_subset (by simp)

lemma neg_consistent_intro_undeducible (hConsis : Consistent Λ (insert (~p) Γ)) : ∀ (Δ : Finset (Formula β)), ↑Δ ⊆ Γ → (Δ ⊬ᴹ[Λ]! p) := by
  simp [Inconsistent, Consistent] at hConsis;
  intro Δ hΔ;
  by_contra hC;
  suffices (insert (~p) Δ ⊢ᴹ[Λ] ⊥) by
    have : insert (~p) Δ ⊢ᴹ[Λ]! ⊥ := ⟨this⟩;
    have : insert (~p) Δ ⊬ᴹ[Λ]! ⊥ := by simpa using hConsis (insert (~p) Δ) (by simpa using Set.insert_subset_insert hΔ);
    aesop;
  have h₁ : insert (~p) Δ ⊢ᴹ[Λ] p := weakening' (by simp) hC.some;
  have h₂ : insert (~p) Δ ⊢ᴹ[Λ] p ⟶ ⊥ := by {
    have : insert (~p) Δ ⊢ᴹ[Λ] ~p := axm (by simp);
    simpa [Formula.neg_eq] using this;
  };
  exact modus_ponens h₂ h₁;

lemma undeducible_intro_neg_consistent {Γ} (h : Γ ⊬ᴹ[Λ]! p) : (Consistent Λ (insert (~p) Γ)) := by
  by_contra hC;

  simp [Consistent, Inconsistent] at hC;
  have ⟨Δ, hΔ₁, hΔ₂⟩ := hC;
  admit;

  /-
  by_cases hp : (~p) ∈ Δ;
  . have hΔ : Δ = insert (~p) (Δ.erase (~p)) := by aesop;
    rw [hΔ] at hΔ₁ hΔ₂;
    have : Γ ⊢ᴹ[Λ] p := modus_ponens (dne Γ p) (by
      rw [neg_eq, neg];
      have : Γ ⊢ᴹ[Λ] (~p) ⟶ ⊥ := hΔ₂.some.drop.weakening' (by
        have := Finset.erase_subset_erase (~p) hΔ₁;
        have := Finset.erase_ssubset_insert Γ (~p);
      );

      simpa using hC.some.drop;
    );

  have : Γ ⊢ᴹ[Λ] p := modus_ponens (dne Γ p) (by
    rw [neg_eq, neg];
    simpa using hC.some.drop;
  );
  exact h ⟨this⟩;
  -/

lemma def_not_FrameclassSatisfiable : (Γ ⊭ᴹ[Λ, α] p) ↔ (FrameClassSatisfiable Λ α (insert (~p) Γ)) := by
  simp only [FrameClassSatisfiable, Consequence];
  aesop;

lemma intro_Completeness : (∀ (Γ : Context β), Consistent Λ Γ → FrameClassSatisfiable Λ α Γ) → (Completeness Λ α) := by
  simp [Completeness];
  intro h₁ Γ p h₂;
  have := h₁ Γ;
  sorry;

  /-
  intro h f hf Γ p hΓp;
  suffices Γ ⊭ᴹᶠ[f] p by have := this hΓp; contradiction;
  exact (def_not_FrameclassSatisfiable ht).mpr (h (insert (~p) Γ) (by sorry)) f hf;
  -/

/-
lemma maximal_consistent_modus_ponens (hConsisΓ : Consistent Λ Γ) (hMaximalΓ : Maximal Γ) : (p ∈ Γ) → ((p ⟶ q) ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq; by_contra hnq;
  apply consistent_neither_provable hConsisΓ;
  /-
  exact consistent_neither_provable hConsisΓ ⟨
    ⟨modus_ponens (axm hpq) (axm hp)⟩,
    ⟨axm (show ~q ∈ Γ from have := hMaximalΓ q; by simp_all)⟩
  ⟩;
  -/
-/

structure MaximalConsistentTheory (Λ : AxiomSet β) where
  theory : Context β
  consistent : Consistent Λ theory
  maximal : ∀ Δ, Consistent Λ Δ → theory ⊆ Δ → Δ = theory

lemma mct_maximality (Ω : MaximalConsistentTheory Λ) : ∀ p, p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  intro p;
  by_cases hConsis₁ : Consistent Λ (insert p Ω.theory);
  . have h := Ω.maximal (insert p Ω.theory) hConsis₁ (by simp);
    rw [←h];
    simp;
  . have h := Ω.maximal (insert (~p) Ω.theory) (by
      by_contra hConsis₂;
      simp [Consistent, Inconsistent] at hConsis₁ hConsis₂;
      have ⟨Δ₁, h₁₁, h₁₂⟩ := hConsis₁;
      have ⟨Δ₂, h₂₁, h₂₂⟩ := hConsis₂;
      have : Inconsistent Λ Ω.theory := by sorry;
      apply Ω.consistent this;
    ) (by simp);
    rw [←h];
    simp;
  -- have := Ω.maximal (insert p Ω.theory);

lemma axiomset_include (Ω : MaximalConsistentTheory Λ) : Λ ⊆ Ω.theory := by
  intro p hp;
  by_contra hC;
  have hConsis := by simpa [Consistent, Inconsistent] using Ω.consistent;
  have : ~p ∈ Ω.theory := by simpa [hC] using mct_maximality Ω p;
  have h₂ : {~p} ⊬ᴹ[Λ]! ⊥ := by simpa using hConsis {~p} (by aesop);
  have h₃ : ⊢ᴹ[Λ] ~~p := by {
    have : ⊢ᴹ[Λ] p := maxm hp;
    admit
  }
  have : {~p} ⊢ᴹ[Λ] ⊥ := by sorry;
  exact h₂ ⟨this⟩;

lemma exists_maximal_consistent_theory (hConsisΓ : Consistent Λ Γ) :
  ∃ Γ', Consistent Λ Γ' ∧ Γ ⊆ Γ' ∧ ∀ Δ, Consistent Λ Δ → Γ' ⊆ Δ → Δ = Γ' :=
  zorn_subset_nonempty { Γ' | Consistent Λ Γ' } (by
    intro c hc chain hnc;
    existsi ⋃₀ c;
    constructor;
    . simp;
      by_contra hC;
      suffices Consistent Λ (⋃₀ c) by aesop;
      admit;
    . apply Set.subset_sUnion_of_mem
  ) Γ hConsisΓ

lemma lindenbaum (hConsisΓ : Consistent Λ Γ) : ∃ (Ω : MaximalConsistentTheory Λ), (Γ ⊆ Ω.theory) := by
  have ⟨Γ', ⟨hConsisΓ', hΓΓ', hMaximalΓ'⟩⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi ⟨Γ', (by assumption), (by assumption)⟩;
  assumption;

def CanonicalModel (Λ : AxiomSet β) : Model (MaximalConsistentTheory Λ) β where
  frame (Γ Δ) := ∀ (p : Formula β), (□p ∈ Γ.theory) → (p ∈ Δ.theory)
  val (Γ a) := (atom a) ∈ Γ.theory

@[simp]
lemma CanonicalModel_frame {Λ : AxiomSet β} {Ω MΔ : MaximalConsistentTheory Λ} :
  (CanonicalModel Λ).frame Ω MΔ ↔ (∀ (p : Formula β), (□p ∈ Ω.theory) → (p ∈ MΔ.theory))
  := by rfl

@[simp]
lemma CanonicalModel_val {Λ : AxiomSet β} {Ω : MaximalConsistentTheory Λ} {a : β} :
  a ∈ (CanonicalModel Λ).val Ω ↔ (atom a) ∈ Ω.theory
  := by rfl

lemma mem_maximalConsistentTheory_iff
  {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (Ω ⊧ᴹˢ[CanonicalModel Λ] p) ↔ (p ∈ Ω.theory) := by
  induction p using rec' with
  | hatom a => simp;
  | hfalsum => simpa [Satisfies.bot_def] using consistent_no_falsum' Ω.consistent;
  | himp p q ihp ihq =>
    simp [ihp, ihq];
    constructor;
    . intro h;
      sorry;
    . intro hpq hp;
      sorry;
  | hor p q ih => sorry;
  | hand p q ihp ihq => sorry;
  | hbox p ih =>
    constructor;
    . contrapose;
      intro h;
      sorry;
    . intro h Δ h₂;
      have b := h₂ _ h;
      sorry;


lemma mem_maximalConsistentTheory_iff'
  {Ω : MaximalConsistentTheory Λ} {Γ : Context β} : (Ω ⊧ᴹˢ[CanonicalModel Λ] Γ) ↔ (Γ ⊆ Ω.theory) := by
  simp [Set.subset_def];
  constructor;
  . intro h p hp; exact (mem_maximalConsistentTheory_iff).mp (h p hp);
  . intro h p hp; exact (mem_maximalConsistentTheory_iff).mpr (h p hp);

theorem LogicK.Hilbert.completes : Completeness (𝐊 : AxiomSet β) (MaximalConsistentTheory (𝐊 : AxiomSet β)) := by
  apply intro_Completeness;

  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := lindenbaum hConsisΓ;

  existsi (CanonicalModel 𝐊).frame;
  constructor;
  . apply LogicK.def_FrameClass;
  . existsi (CanonicalModel 𝐊).val, Ω;
    apply mem_maximalConsistentTheory_iff'.mpr hΩ;

end LO.Modal.Normal
