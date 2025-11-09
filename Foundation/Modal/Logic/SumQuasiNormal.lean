import Foundation.Modal.Logic.SumNormal

namespace LO.Modal

namespace Logic

variable {L L₁ L₂ : Logic α} {φ ψ : Formula α} {s : Substitution α}

inductive sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : L₁ ⊢ φ → sumQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : L₂ ⊢ φ → sumQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ ➝ ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
  | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

namespace sumQuasiNormal


lemma mem₁! (hφ : L₁ ⊢ φ) : sumQuasiNormal L₁ L₂ ⊢ φ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₁ hφ;

lemma mem₂! (hφ : L₂ ⊢ φ) : sumQuasiNormal L₁ L₂ ⊢ φ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₂ hφ;

instance : Entailment.ModusPonens (sumQuasiNormal L₁ L₂) where
  mdp hφψ hφ := by
    constructor;
    apply sumQuasiNormal.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;

instance : (sumQuasiNormal L₁ L₂).Substitution where
  subst s hφ := by
    rw [iff_provable] at ⊢ hφ;
    apply sumQuasiNormal.subst;
    assumption;

lemma rec!
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢ φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢ φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢ φ ➝ ψ} → {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  (subst : ∀ {φ s}, {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} → (motive φ hφ) → motive (φ⟦s⟧) (Logic.subst _ hφ))
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢ φ) → motive φ h := by
  intro _ hφ;
  induction (iff_provable.mp $ hφ) with
  | mem₁ h => apply mem₁ h;
  | mem₂ h => apply mem₂ h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;
    . apply iff_provable.mpr; assumption;
  | subst hφ ihφ =>
    apply subst;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;

lemma symm : sumQuasiNormal L₁ L₂ = sumQuasiNormal L₂ L₁ := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact sumQuasiNormal.mem₂ h;
    | mem₂ h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumQuasiNormal.subst ihφ;
  . intro h;
    induction h with
    | mem₁ h => exact sumQuasiNormal.mem₂ h;
    | mem₂ h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumQuasiNormal.subst ihφ;

variable [DecidableEq α]

instance [Entailment.Cl L₁] : Entailment.Lukasiewicz (sumQuasiNormal L₁ L₂) where
  implyK {_ _} := by constructor; apply sumQuasiNormal.mem₁; simp;
  implyS {_ _ _} := by constructor; apply sumQuasiNormal.mem₁; simp;
  elimContra {_ _} := by constructor; apply sumQuasiNormal.mem₁; simp;

instance [L₁.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal where
  K _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  subst s hφ := by
    rw [iff_provable] at ⊢ hφ;
    apply sumQuasiNormal.subst;
    assumption;

instance [L₂.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal := by
  rw [sumQuasiNormal.symm];
  infer_instance;

instance : L₁ ⪯ sumQuasiNormal L₁ L₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  exact mem₁! hφ;

instance : L₂ ⪯ sumQuasiNormal L₁ L₂ := by
  rw [sumQuasiNormal.symm];
  infer_instance;

omit [DecidableEq α] in
lemma iff_subset {X Y} : L.sumQuasiNormal Y ⊆ L.sumQuasiNormal X ↔ ∀ ψ ∈ Y, L.sumQuasiNormal X ⊢ ψ := by
  constructor;
  . intro h ψ hψ;
    apply Logic.iff_provable.mpr $ @h ψ ?_;
    apply Logic.sumQuasiNormal.mem₂;
    grind;
  . intro h ψ;
    suffices L.sumQuasiNormal Y ⊢ ψ → L.sumQuasiNormal X ⊢ ψ by grind;
    intro hψ;
    induction hψ using Logic.sumQuasiNormal.rec! with
    | mem₁ hψ => apply Logic.sumQuasiNormal.mem₁! hψ;
    | mem₂ hψ => apply h; grind;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | subst ihφ => apply Logic.subst; assumption;

section

variable [L₁.IsQuasiNormal]

open LO.Entailment

lemma provable_of_finite_provable : (∃ X : Finset _, (X.toSet ⊆ L₂) ∧ L₁ ⊢ X.conj ➝ φ) → sumQuasiNormal L₁ L₂ ⊢ φ := by
  rintro ⟨X, hX₂, hφ⟩;
  apply (WeakerThan.pbl (𝓣 := sumQuasiNormal L₁ L₂) hφ) ⨀ ?_;
  apply FConj!_iff_forall_provable.mpr;
  intro χ hχ;
  apply mem₂!;
  apply iff_provable.mpr;
  apply hX₂ hχ;

lemma finite_provable_of_provable (h : ∀ ξ ∈ L₂, ∀ s : Substitution _, ξ⟦s⟧ ∈ L₂) :
  sumQuasiNormal L₁ L₂ ⊢ φ → ∃ X : Finset _, (↑X ⊆ L₂) ∧ L₁ ⊢ X.conj ➝ φ := by
  intro h;
  induction h using sumQuasiNormal.rec! with
  | mem₁ h =>
    use ∅;
    constructor;
    . tauto;
    . cl_prover [h];
  | @mem₂ φ h =>
    use {φ};
    constructor;
    . simp only [Finset.coe_singleton, Set.singleton_subset_iff]; grind;
    . simp;
  | @mdp φ ψ _ _ ihφψ ihφ =>
    obtain ⟨X₁, _, hφψ⟩ := ihφψ;
    obtain ⟨X₂, _, hφ⟩ := ihφ;
    use X₁ ∪ X₂;
    constructor;
    . simp_all;
    . suffices L₁ ⊢ (X₁.conj ⋏ X₂.conj) ➝ ψ by exact C!_trans CFconjUnionKFconj! this;
      cl_prover [hφψ, hφ];
  | @subst _ s _ ihφ =>
    obtain ⟨X, hX, hφ⟩ := ihφ;
    use X.image (·⟦s⟧);
    constructor;
    . intro ξ hξ;
      obtain ⟨ξ, _, rfl⟩ : ∃ x ∈ X, x⟦s⟧ = ξ := by simpa using hξ;
      apply h;
      apply hX;
      assumption;
    . apply C!_trans ?_ (Logic.subst s hφ);
      exact fconj_subst;

lemma iff_provable_finite_provable (h : ∀ ξ ∈ L₂, ∀ s : Substitution _, ξ⟦s⟧ ∈ L₂)  :
  sumQuasiNormal L₁ L₂ ⊢ φ ↔ ∃ X : Finset _, (↑X ⊆ L₂) ∧ L₁ ⊢ X.conj ➝ φ := ⟨finite_provable_of_provable h, provable_of_finite_provable⟩

omit [DecidableEq α] in
lemma iff_provable_finite_provable_letterless [DecidableEq α] {L₁ L₂ : Logic α} {φ : Formula _} [L₁.IsQuasiNormal] (L₂_letterless : FormulaSet.Letterless L₂)
  : sumQuasiNormal L₁ L₂ ⊢ φ ↔ ∃ X : Finset _, (↑X ⊆ L₂) ∧ L₁ ⊢ X.conj ➝ φ := by
  apply iff_provable_finite_provable;
  rintro ξ hξ s;
  simpa [Formula.subst.subst_letterless (L₂_letterless _ hξ)];

end

omit [DecidableEq α] in
@[simp]
lemma with_empty [DecidableEq α] {L₁ : Logic α} [L₁.IsQuasiNormal] : L₁.sumQuasiNormal ∅ = L₁ := by
  ext φ;
  suffices L₁.sumQuasiNormal ∅ ⊢ φ ↔ L₁ ⊢ φ by simpa [Logic.iff_provable];
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | mem₁ => assumption;
    | mem₂ => simp_all [Logic.iff_provable];
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => exact Logic.subst _ ihφ;
  . intro h;
    exact Entailment.WeakerThan.pbl h;

end sumQuasiNormal

inductive sumQuasiNormal' (L₁ L₂ : Logic α) : Logic α
| mem₁ {φ} (s : Substitution _) : L₁ ⊢ φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mem₂ {φ} (s : Substitution _) : L₂ ⊢ φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mdp {φ ψ : Formula α} : sumQuasiNormal' L₁ L₂ (φ ➝ ψ) → sumQuasiNormal' L₁ L₂ φ → sumQuasiNormal' L₁ L₂ ψ

namespace sumQuasiNormal'

@[grind]
lemma mem₁! (h : L₁ ⊢ φ) : sumQuasiNormal' L₁ L₂ ⊢ (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₁ _ h;

@[grind]
lemma mem₁!_nosub (h : L₁ ⊢ φ) : sumQuasiNormal' L₁ L₂ ⊢ φ := by
  simpa using mem₁! (s := Substitution.id) h;

@[grind]
lemma mem₂! (h : L₂ ⊢ φ) : sumQuasiNormal' L₁ L₂ ⊢ (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₂ _ h;

@[grind]
lemma mem₂!_nosub (h : L₂ ⊢ φ) : sumQuasiNormal' L₁ L₂ ⊢ φ := by
  simpa using mem₂! (s := Substitution.id) h;

instance : Entailment.ModusPonens (sumQuasiNormal' L₁ L₂) where
  mdp := by rintro φ ψ ⟨hφψ⟩ ⟨hφ⟩; exact ⟨sumQuasiNormal'.mdp hφψ hφ⟩;

lemma rec!
  {motive : (φ : Formula α) → ((sumQuasiNormal' L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢ φ) → motive (φ⟦s⟧) (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢ φ) → motive (φ⟦s⟧) (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal' L₁ L₂) ⊢ (φ ➝ ψ)} → {hφ : (sumQuasiNormal' L₁ L₂) ⊢ φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal' L₁ L₂ ⊢ φ) → motive φ h := by
  intro φ hφ;
  induction (iff_provable.mp $ hφ) with
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;
    . apply iff_provable.mpr; assumption;
  | _ => grind;

instance : (sumQuasiNormal' L₁ L₂).Substitution where
  subst s hφ := by
    rw [iff_provable] at ⊢ hφ;
    induction hφ with
    | mem₁ s' h => simpa using mem₁ (s := s' ∘ s) h
    | mem₂ s' h => simpa using mem₂ (s := s' ∘ s) h
    | mdp _ _ ihφψ ihφ => exact mdp ihφψ ihφ

end sumQuasiNormal'


attribute [grind] Logic.sumQuasiNormal.mem₁! Logic.sumQuasiNormal.mem₂!

lemma eq_sumQuasiNormal_sumQuasiNormal' : Logic.sumQuasiNormal L₁ L₂ = Logic.sumQuasiNormal' L₁ L₂ := by
  ext φ;
  suffices (Logic.sumQuasiNormal L₁ L₂ ⊢ φ) ↔ (Logic.sumQuasiNormal' L₁ L₂ ⊢ φ) by grind;
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | @subst ψ s _ ihφ => exact Logic.subst _ ihφ;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => grind;
  . intro h;
    induction h using Logic.sumQuasiNormal'.rec! with
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => apply Logic.subst; grind;

@[grind]
lemma iff_provable_sumQuasiNormal'_provable_sumQuasiNormal : (sumQuasiNormal' L₁ L₂ ⊢ φ) ↔ (sumQuasiNormal L₁ L₂ ⊢ φ) := by
  rw [eq_sumQuasiNormal_sumQuasiNormal'];

lemma sumQuasiNormal.rec!_omitSubst
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢ φ) → motive (φ⟦s⟧) (Logic.subst s $ mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢ φ) → motive (φ⟦s⟧) (Logic.subst s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢ (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢ φ) → motive φ h := by
  intro φ hφ;
  induction (iff_provable_sumQuasiNormal'_provable_sumQuasiNormal.mpr hφ) using Logic.sumQuasiNormal'.rec! with
  | mem₁ s h => grind;
  | mem₂ s h => grind;
  | @mdp _ _ hφψ hφ ihφψ ihφ => exact mdp (ihφψ $ by grind) (ihφ $ by grind);

attribute [grind] Logic.subst


def substitution_of_letterless (L_letterless : FormulaSet.Letterless L) : L.Substitution where
  subst s hφ := by
    rw [Logic.iff_provable] at ⊢ hφ;
    simpa [Formula.subst.subst_letterless (s := s) $ L_letterless _ hφ];

lemma sumQuasiNormal.rec!_omitSubst₁ (hL₁ : L₁.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢ φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢ φ) → motive (φ⟦s⟧) (Logic.subst s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢ (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢ φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ s h;
    apply mem₁;
    grind;
  . assumption;
  . assumption;

lemma sumQuasiNormal.rec!_omitSubst₂ (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢ φ) → motive (φ⟦s⟧) (Logic.subst s $ mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢ φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢ (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢ φ) → motive φ h := by
  simp_all only [Logic.sumQuasiNormal.symm (L₁ := L₁) (L₂ := L₂)]
  apply sumQuasiNormal.rec!_omitSubst₁ <;> assumption;

lemma sumQuasiNormal.rec!_omitSubst_strong (hL₁ : L₁.Substitution) (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢ φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢ φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢ φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢ (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢ φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢ φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ h _; apply mem₁; grind;
  . intro φ h _; apply mem₂; grind;
  . assumption;

end Logic


end LO.Modal
