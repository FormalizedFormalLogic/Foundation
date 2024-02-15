import Logic.Propositional.Basic.Completeness
import Logic.Modal.Normal.Deduction
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Hilbert
open Finset Set
open Formula Theory

attribute [simp] Finset.subset_union_right Finset.subset_union_left
attribute [simp] Set.Subset.rfl Set.insert_subset_iff

variable {α β : Type u} [Inhabited α] [DecidableEq β] [Inhabited β]

section

variable (Λ : AxiomSet β) (Γ : Theory β)

def Theory.Maximal := ∀ p, (p ∈ Γ) ∨ (~p ∈ Γ)

def WeakCompleteness := ∀ (p : Formula β), (⊧ᴹ[(𝔽(Λ) : FrameClass α)] p) → (⊢ᴹ[Λ]! p)

def Completeness (𝔽 : FrameClass α) := ∀ (Γ : Theory β) (p : Formula β), (Γ ⊨ᴹ[𝔽] p) → (Γ ⊢ᴹ[Λ]! p)

end

variable {Λ : AxiomSet β}
variable {Γ : Theory β} (hConsisΓ : Consistent Λ Γ)

@[simp]
lemma inconsistent_insert_falsum : Inconsistent Λ (insert ⊥ Γ) := Hilbert.inconsistent_insert_falsum (· ⊢ᴹ[Λ] ·) Γ

lemma consistent_iff_undeducible_falsum : Consistent Λ Γ ↔ (Γ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_iff_undeducible_falsum (· ⊢ᴹ[Λ] ·) Γ

@[simp]
lemma consistent_undeducible_falsum : Γ ⊬ᴹ[Λ]! ⊥ := consistent_iff_undeducible_falsum.mp hConsisΓ

lemma consistent_subset_undeducible_falsum (Δ) (hΔ : Δ ⊆ Γ) : (Δ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_subset_undeducible_falsum (· ⊢ᴹ[Λ] ·) hConsisΓ hΔ

lemma consistent_no_falsum : ⊥ ∉ Γ := Hilbert.consistent_no_falsum (· ⊢ᴹ[Λ] ·) hConsisΓ

lemma consistent_no_falsum_subset (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := Hilbert.consistent_no_falsum_subset (· ⊢ᴹ[Λ] ·) hConsisΓ hΔ

lemma consistent_neither_undeducible (p) : (Γ ⊬ᴹ[Λ]! p) ∨ (Γ ⊬ᴹ[Λ]! ~p) := Hilbert.consistent_neither_undeducible (· ⊢ᴹ[Λ] ·) hConsisΓ p

lemma consistent_of_subset (h : Γ₁ ⊆ Γ₂) : (Consistent Λ Γ₂) → (Consistent Λ Γ₁) := Hilbert.consistent_of_subset (· ⊢ᴹ[Λ] ·) h

lemma consistent_insert {Γ : Theory β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_of_subset (by simp)

lemma consistent_empty (hConsisΛ : Theory.Consistent Λ Λ) : Theory.Consistent Λ ∅ := consistent_of_subset (by simp) hConsisΛ

lemma inconsistent_insert (h : Inconsistent Λ (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢ᴹ[Λ]! ⊥)) := Hilbert.inconsistent_insert (· ⊢ᴹ[Λ] ·) h

lemma consistent_iff_insert_neg  : (Consistent Λ (insert (~p) Γ)) ↔ (Γ ⊬ᴹ[Λ]! p)  := Hilbert.consistent_iff_insert_neg (· ⊢ᴹ[Λ] ·)

lemma consistent_either (hConsisΓ : Consistent Λ Γ) : ∀ p, (Consistent Λ (insert p Γ)) ∨ (Consistent Λ (insert (~p) Γ)) := Hilbert.consistent_either (· ⊢ᴹ[Λ] ·) hConsisΓ

lemma frameclass_unsatisfiable_insert_neg {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊭ᴹ[𝔽] p) ↔ (Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by
  constructor;
  . intro hCon;
    simp [FrameClassConsequence, FrameConsequence] at hCon;
    simp [FrameClassSatisfiable, FrameSatisfiable];
    have ⟨F, hF, V, w, ⟨h₁, h₂⟩⟩ := hCon;
    existsi F, hF, V, w;
    exact ⟨h₂, h₁⟩;
  . intro hSat hCon;
    simp [FrameClassConsequence, FrameConsequence] at hCon;
    simp [FrameClassSatisfiable, FrameSatisfiable] at hSat;
    have ⟨F, hF, V, w, ⟨h₁, h₂⟩⟩ := hSat;
    exact h₁ $ hCon F hF V w h₂;

lemma frameclass_satisfiable_insert_neg {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊨ᴹ[𝔽] p) ↔ ¬(Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by simpa using frameclass_unsatisfiable_insert_neg.not

lemma completeness_def {𝔽 : FrameClass α} : (Completeness Λ 𝔽) ↔ (∀ Γ, Consistent Λ Γ → FrameClassSatisfiable 𝔽 Γ) := by
  constructor;
  . contrapose;
    simp [Completeness];
    intro Δ h₁ h₂;
    existsi Δ, ⊥;
    constructor;
    . intro F hF V w h;
      simp [FrameClassSatisfiable, FrameSatisfiable] at h₂;
      have ⟨p, ⟨hp₁, hp₂⟩⟩ := h₂ F hF V w;
      have := h p hp₁;
      contradiction;
    . simpa [Theory.Consistent, Theory.Inconsistent] using h₁;
  . contrapose;
    simp [Completeness];
    intro Δ p h₁ h₂;
    existsi (insert (~p) Δ);
    constructor;
    . apply consistent_iff_insert_neg.mpr;
      simpa using h₂;
    . apply frameclass_satisfiable_insert_neg.mp;
      exact h₁;


def Theory.MaximalConsistent (Λ) (Γ : Theory β) := Theory.Consistent Λ Γ ∧ Maximal Γ

section MaximalConsistent

variable (hMCΓ : MaximalConsistent Λ Γ)

lemma maximal_consistent_include_axiomset : Λ ⊆ Γ := by
  intro p hp;
  by_contra hC;
  have h₁ : {~p} ⊬ᴹ[Λ]! ⊥ := consistent_subset_undeducible_falsum hMCΓ.1 {~p} (by have := hMCΓ.2 p; aesop)
  have h₂ : {~p} ⊢ᴹ[Λ]! ⊥ := by simpa using dtl! $ dni'! (show ∅ ⊢ᴹ[Λ]! p by exact Deducible.maxm! hp);
  contradiction;

lemma maximal_consistent_iff_membership_deducible : (p ∈ Γ) ↔ (Γ ⊢ᴹ[Λ]! p) := by
  constructor;
  . intro h; exact (Hilbert.axm! h)
  . intro h;
    suffices ~p ∉ Γ by have := hMCΓ.2 p; aesop;
    by_contra hC;
    have h₂ : Γ ⊢ᴹ[Λ]! ~p := Hilbert.axm! hC;
    exact consistent_subset_undeducible_falsum hMCΓ.1 Γ (by simp) (modus_ponens'! h₂ h);

lemma maximal_consistent_iff_not_membership_undeducible : (p ∉ Γ) ↔ (Γ ⊬ᴹ[Λ]! p) := by
  simpa using (maximal_consistent_iff_membership_deducible hMCΓ).not;

lemma maximal_consistent_modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Γ) → (p ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq;
  have dp  := (maximal_consistent_iff_membership_deducible hMCΓ).mp hp;
  have dpq := (maximal_consistent_iff_membership_deducible hMCΓ).mp hpq;
  exact (maximal_consistent_iff_membership_deducible hMCΓ).mpr $ modus_ponens'! dp dpq;

lemma maximal_consistent_neg_membership_iff : (~p ∈ Γ) ↔ (p ∉ Γ) := by
  constructor;
  . intros;
    by_contra hC;
    have hp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hnp : ({p, ~p}) ⊢ᴹ[Λ]! ~p := axm! (by simp);
    apply consistent_subset_undeducible_falsum hMCΓ.1 {p, ~p} (by aesop;) (modus_ponens'! hnp hp);
  . have := hMCΓ.2 p; aesop;

lemma maximal_consistent_imp_membership_iff : (p ⟶ q ∈ Γ) ↔ (p ∉ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . simp [or_iff_not_imp_left];
    intros;
    apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
    have hp : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hpq : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p ⟶ q := axm! (by simp);
    exact weakening! (by aesop) $ modus_ponens'! hpq hp;
  . intros h;
    cases h;
    case inl h =>
      have := (maximal_consistent_neg_membership_iff hMCΓ).mpr h;
      have d₁ : Γ ⊢ᴹ[Λ]! (~p ⟶ (p ⟶ q)) := by
        have dp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
        have dnp : ({p, ~p}) ⊢ᴹ[Λ]! (~p) := axm! (by simp);
        have h₂ : ({p, ~p}) ⊢ᴹ[Λ]! q := efq'! $ modus_ponens'! (by simpa using dnp) dp;
        have h₃ : ∅ ⊢ᴹ[Λ]! ~p ⟶ (p ⟶ q) := dtr! (by simpa using dtr! h₂);
        exact weakening! (by simp) h₃;
      have d₂ : Γ ⊢ᴹ[Λ]! ~p := axm! (by simpa)
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact modus_ponens'! d₁ d₂;
    case inr h =>
      have d₁ : Γ ⊢ᴹ[Λ]! (q ⟶ (p ⟶ q)) := imply₁! _ _ _;
      have d₂ : Γ ⊢ᴹ[Λ]! q := axm! h;
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact modus_ponens'! d₁ d₂;

lemma maximal_consistent_imp_membership_iff' : (p ⟶ q ∈ Γ) ↔ ((p ∈ Γ) → (q ∈ Γ)) := by
  constructor;
  . intro hpq hp;
    have := (maximal_consistent_imp_membership_iff hMCΓ).mp hpq;
    aesop;
  . intro hp;
    apply (maximal_consistent_imp_membership_iff hMCΓ).mpr;
    simp [or_iff_not_imp_left];
    aesop;

lemma maximal_consistent_and_membership_iff : (p ⋏ q ∈ Γ) ↔ (p ∈ Γ) ∧ (q ∈ Γ) := by
  constructor;
  . intros h;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    constructor;
    . exact conj₁'! h;
    . exact conj₂'! h;
  . rintro ⟨hp, hq⟩;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    exact conj₃'! hp hq;

lemma maximal_consistent_or_membership_iff : (p ⋎ q ∈ Γ) ↔ (p ∈ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . intros h;
    by_contra hC; simp [not_or] at hC;
    have : Γ ⊢ᴹ[Λ]! ⊥ := disj₃'!
      (show Γ ⊢ᴹ[Λ]! (p ⟶ ⊥) by exact axm! (by apply maximal_consistent_neg_membership_iff hMCΓ |>.mpr; aesop;))
      (show Γ ⊢ᴹ[Λ]! (q ⟶ ⊥) by exact axm! (by apply maximal_consistent_neg_membership_iff hMCΓ |>.mpr; aesop;))
      (show Γ ⊢ᴹ[Λ]! (p ⋎ q) by exact axm! h);
    exact consistent_undeducible_falsum hMCΓ.1 this;
  . intro h;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    cases h;
    case inl h => exact disj₁'! h;
    case inr h => exact disj₂'! h;

end MaximalConsistent

structure MaximalConsistentTheory (Λ : AxiomSet β) where
  theory : Theory β
  mc : MaximalConsistent Λ theory

namespace MaximalConsistentTheory

variable (Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ)

@[simp] def membership (p : Formula β) (Ω : MaximalConsistentTheory Λ) := p ∈ Ω.theory
instance : Membership (Formula β) (MaximalConsistentTheory Λ) := ⟨membership⟩

@[simp] def subset := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (MaximalConsistentTheory Λ) := ⟨subset⟩

lemma consitent : Consistent Λ Ω.theory := Ω.mc.1

lemma maximal : Maximal Ω.theory := Ω.mc.2

abbrev box := □Ω.theory
prefix:73  "□" => box

abbrev dia := ◇Ω.theory
prefix:73  "◇" => dia

abbrev prebox := □⁻¹Ω.theory
prefix:73  "□⁻¹" => prebox

abbrev predia := ◇⁻¹Ω.theory
prefix:73  "◇⁻¹" => predia

variable  {Ω : MaximalConsistentTheory Λ}

lemma modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Ω) → (p ∈ Ω) → (q ∈ Ω) := by
  apply maximal_consistent_modus_ponens' (Ω.mc);

lemma membership_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (p ∈ Ω) ↔ (Ω.theory ⊢ᴹ[Λ]! p) := by
  apply maximal_consistent_iff_membership_deducible (Ω.mc);

lemma iff_congr : (Ω.theory ⊢ᴹ[Λ]! (p ⟷ q)) → ((p ∈ Ω) ↔ (q ∈ Ω)) := by
  intro hpq;
  simp only [LogicSymbol.iff] at hpq;
  constructor;
  . intro hp;
    exact membership_iff.mpr $ modus_ponens'! (conj₁'! hpq) (membership_iff.mp hp)
  . intro hq;
    exact membership_iff.mpr $ modus_ponens'! (conj₂'! hpq) (membership_iff.mp hq)

lemma dn_membership_iff : (p ∈ Ω) ↔ (~~p ∈ Ω) := iff_congr (equiv_dn! Ω.theory p)

lemma neg_membership_iff : (~p ∈ Ω) ↔ (p ∉ Ω) := maximal_consistent_neg_membership_iff (Ω.mc)

lemma imp_membership_iff' : (p ⟶ q ∈ Ω) ↔ ((p ∈ Ω) → (q ∈ Ω)) := maximal_consistent_imp_membership_iff' (Ω.mc)

lemma and_membership_iff : (p ⋏ q ∈ Ω) ↔ (p ∈ Ω) ∧ (q ∈ Ω) := maximal_consistent_and_membership_iff (Ω.mc)

lemma or_membership_iff : (p ⋎ q ∈ Ω) ↔ (p ∈ Ω) ∨ (q ∈ Ω) := maximal_consistent_or_membership_iff (Ω.mc)

@[simp]
lemma no_falsum : ⊥ ∉ Ω := consistent_no_falsum Ω.consitent

@[simp]
lemma neither_mem : ¬((p ∈ Ω) ∧ (~p ∈ Ω)) := by
  by_contra hC;
  exact Ω.no_falsum $ Ω.modus_ponens' hC.2 hC.1;

end MaximalConsistentTheory

section Lindenbaum

lemma exists_maximal_consistent_theory' :
  ∃ m ∈ {Γ | Theory.Consistent Λ Γ}, Γ ⊆ m ∧ ∀ a ∈ {Γ | Theory.Consistent Λ Γ}, m ⊆ a → a = m
  := zorn_subset_nonempty { Γ : Theory β | Consistent Λ Γ } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp;
    constructor;
    . by_contra hC;
      replace hC : ⋃₀ c ⊢ᴹ[Λ]! ⊥ := by simpa [Theory.Consistent, Theory.Inconsistent] using hC;
      rcases hC.compact with ⟨s, hs, s_consis⟩;
      rcases Set.subset_mem_chain_of_finite c hnc chain (s := s) (Finset.finite_toSet s) hs with ⟨U, hUc, hsU⟩
      exact (consistent_of_subset hsU (by apply hc; simpa)) s_consis;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) Γ hConsisΓ

/--
  a.k.a. Lindenbaum Lemma
-/
lemma exists_maximal_consistent_theory : ∃ (Ω : MaximalConsistentTheory Λ), (Γ ⊆ Ω.theory) := by
  have ⟨Ω, ⟨h₁, ⟨h₂, h₃⟩⟩⟩ := exists_maximal_consistent_theory' hConsisΓ;
  existsi ⟨Ω, h₁, (by
    intro p;
    cases (consistent_either h₁ p) with
    | inl h => have := h₃ (insert p Ω) h (by simp); left; simpa;
    | inr h => have := h₃ (insert (~p) Ω) h (by simp); right; simpa;
  )⟩;
  exact h₂;

end Lindenbaum

open MaximalConsistentTheory

variable (hK : 𝐊 ⊆ Λ)

lemma mct_mem_box_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (□p ∈ Ω) ↔ (∀ (Ω' : MaximalConsistentTheory Λ), (□⁻¹Ω ⊆ Ω'.theory) → (p ∈ Ω')) := by
  have := Deduction.instBoxedNecessitation hK;
  constructor;
  . aesop;
  . contrapose;
    intro hC;
    have := (maximal_consistent_iff_not_membership_undeducible Ω.mc).mp hC;
    have := consistent_iff_insert_neg.mpr $ not_imp_not.mpr preboxed_necessitation! this;
    have ⟨Ω', hΩ'⟩ := exists_maximal_consistent_theory this;
    simp;
    existsi Ω';
    constructor;
    . aesop;
    . exact neg_membership_iff.mp (by aesop);

def CanonicalModel (Λ : AxiomSet β) : Model (MaximalConsistentTheory Λ) β where
  frame (Ω₁ Ω₂) := (□⁻¹Ω₁) ⊆ Ω₂.theory
  val (Ω a) := (atom a) ∈ Ω


namespace CanonicalModel

variable {Λ : AxiomSet β} (hK : 𝐊 ⊆ Λ) {Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ}

lemma frame_def: (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (□⁻¹Ω₁) ⊆ Ω₂.theory := by rfl

lemma frame_def': (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (◇Ω₂ ⊆ Ω₁.theory) := by
  have := Deduction.instBoxedNecessitation hK;
  have := Deduction.ofKSubset hK;

  simp only [frame_def];
  constructor;
  . intro h p hp;
    have ⟨q, hq₁, hq₂⟩ := Set.dia_mem_iff.mp hp;
    rw [←hq₂, ModalDuality.dia];
    apply (Ω₁.neg_membership_iff).mpr;
    by_contra hC;
    have : ~q ∈ Ω₂ := by aesop;
    exact Ω₂.neither_mem ⟨hq₁, (by simpa)⟩;
  . intro h p;
    contrapose;
    intro hnp;
    have : ◇(~p) ∈ Ω₁ := by simpa using h $ dia_mem_intro $ neg_membership_iff.mpr hnp;
    have : ~(□p) ∈ Ω₁ := by
      suffices h : Ω₁.theory ⊢ᴹ[Λ]! ((◇~p) ⟷ ~(□p)) by exact MaximalConsistentTheory.iff_congr h |>.mp this;
      apply equiv_dianeg_negbox!;
    have := neg_membership_iff.mp this;
    aesop;

@[simp]
lemma val_def {a : β} :
  a ∈ (CanonicalModel Λ).val Ω ↔ (atom a) ∈ Ω
  := by rfl

lemma axiomT (hT : 𝐓 ⊆ Λ) : Reflexive (CanonicalModel Λ).frame := by
  intro Ω p hp;
  have d₁ : Ω.theory ⊢ᴹ[Λ]! (□p ⟶ p) := Deducible.maxm! (hT $ (by apply AxiomT.set.include));
  apply Ω.modus_ponens' (membership_iff.mpr d₁) hp;

lemma axiomD (hD : 𝐃 ⊆ Λ) : Serial (CanonicalModel Λ).frame := by
  have := Deduction.instBoxedNecessitation hK; -- TODO: it can be removed?

  intro Ω;
  simp [frame_def];
  suffices h : Consistent Λ (□⁻¹Ω.theory) by exact exists_maximal_consistent_theory h;
  by_contra hC;
  simp [Theory.Consistent, Theory.Inconsistent] at hC;
  have d₁ : Ω.theory ⊢ᴹ[Λ]! □⊥ := preboxed_necessitation! hC;
  have d₂ : Ω.theory ⊢ᴹ[Λ]! (□⊥ ⟶ ◇⊥) := Deducible.maxm! (hD $ (by apply AxiomD.set.include));
  have d₃ : Ω.theory ⊢ᴹ[Λ]! ~(◇⊥) := dni'! $ boxverum! Ω.theory;
  have d₄ : Ω.theory ⊢ᴹ[Λ]! ◇⊥ := modus_ponens'! d₂ d₁;
  have d₅ : Ω.theory ⊢ᴹ[Λ]! ⊥ := modus_ponens'! d₃ d₄;
  exact consistent_undeducible_falsum Ω.consitent d₅;

lemma axiomB (hB : 𝐁 ⊆ Λ) : Symmetric (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ h;
  simp [frame_def] at h;
  simp [(frame_def' hK)];
  intro p hp;
  have ⟨q, hq, _⟩ := Set.dia_mem_iff.mp hp;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! q := membership_iff.mp hq;
  have d₂ : Ω₁.theory ⊢ᴹ[Λ]! (q ⟶ □◇q) := Deducible.maxm! (hB $ (by apply AxiomB.set.include));
  have d₃ : Ω₁.theory ⊢ᴹ[Λ]! □◇q := modus_ponens'! d₂ d₁;
  have := membership_iff.mpr d₃;
  aesop

lemma axiom4 (h4 : 𝟒 ⊆ Λ) : Transitive (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ Ω₃ h₁₂ h₂₃ p hp;
  apply h₂₃;
  apply h₁₂;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! (□p ⟶ □□p) := Deducible.maxm! (h4 $ (by apply Axiom4.set.include));
  exact Ω₁.modus_ponens' (membership_iff.mpr d₁) hp;

lemma axiom5 (h5 : 𝟓 ⊆ Λ) : Euclidean (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ Ω₃ h₁₂ h₁₃;
  simp [frame_def] at h₁₂;
  simp [(frame_def' hK)] at h₁₃;
  simp [(frame_def' hK)];
  intro p hp;
  have ⟨q, _, _⟩ := Set.dia_mem_iff.mp hp;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! ◇q := axm! (by aesop)
  have d₂ : Ω₁.theory ⊢ᴹ[Λ]! ◇q ⟶ □◇q := Deducible.maxm! (h5 $ (by apply Axiom5.set.include));
  have d₃ : Ω₁.theory ⊢ᴹ[Λ]! □◇q := modus_ponens'! d₂ d₁;
  have := membership_iff.mpr d₃;
  aesop;

end CanonicalModel

lemma truthlemma {p : Formula β} : ∀ {Ω}, (⊧ᴹ[CanonicalModel Λ, Ω] p) ↔ (p ∈ Ω) := by
  induction p using rec' with
  | hatom => aesop;
  | hfalsum => simp;
  | himp => simp_all [imp_membership_iff'];
  | hor => simp_all [or_membership_iff];
  | hand => simp_all [and_membership_iff];
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
      simp [Set.subset_def, CanonicalModel.frame_def] at hΩ';
      exact hΩ' p h;

lemma truthlemma' {Γ : Theory β} : ∀ {Ω}, (⊧ᴹ[CanonicalModel Λ, Ω] Γ) ↔ (Γ ⊆ Ω.theory) := by
  intro Ω;
  constructor;
  . simp [Set.subset_def];
    intro h p hp;
    exact truthlemma hK |>.mp $ h p hp;
  . intro h p hp;
    apply truthlemma hK |>.mpr;
    apply h hp;

-- TODO: ほとんど同じ記述なのでどうにかして共通化したい．

theorem LogicK.Hilbert.completes : Completeness (𝐊 : AxiomSet β) (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel 𝐊).frame;
  constructor;
  . apply LogicK.def_FrameClass;
  . existsi (CanonicalModel 𝐊).val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

theorem LogicS4.Hilbert.completes : Completeness (𝐒𝟒 : AxiomSet β) (𝔽((𝐒𝟒 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐒𝟒 : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel 𝐒𝟒).frame;
  constructor;
  . apply (LogicS4.def_FrameClass _).mp;
    constructor;
    . apply CanonicalModel.axiomT (by simp);
    . apply CanonicalModel.axiom4 (by simp);
  . existsi (CanonicalModel 𝐒𝟒).val, Ω;
    apply truthlemma' (by exact subset_K) |>.mpr;
    assumption;

theorem LogicS5.Hilbert.completes : Completeness (𝐒𝟓 : AxiomSet β) (𝔽((𝐒𝟓 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐒𝟓 : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel 𝐒𝟓).frame;
  constructor;
  . apply (LogicS5.def_FrameClass _).mp;
    constructor;
    . apply CanonicalModel.axiomT (by simp);
    . apply CanonicalModel.axiom5 (by simp) (by simp);
  . existsi (CanonicalModel 𝐒𝟓).val, Ω;
    apply truthlemma' (by exact subset_K) |>.mpr;
    assumption;

end LO.Modal.Normal
