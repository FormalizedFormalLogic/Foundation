import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Modal.Logic.Basic
import Foundation.Meta.ClProver

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {L L₀ L₁ L₂ L₃ : Logic α}

namespace Logic


section

variable [DecidableEq α] [L.IsQuasiNormal]

lemma lconj_subst {X : List (Formula α)} {s : Substitution α} : L ⊢! (X.map (·⟦s⟧)).conj₂ ➝ X.conj₂⟦s⟧ := by
  induction X using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ X hφ ih =>
    suffices L ⊢! φ⟦s⟧ ⋏ ⋀(X.map (·⟦s⟧)) ➝ φ⟦s⟧ ⋏ (⋀X)⟦s⟧ by
      simpa [List.conj₂_cons_nonempty hφ, List.conj₂_cons_nonempty (show X.map (·⟦s⟧) ≠ [] by simpa), -iff_provable];
    cl_prover [ih];

lemma fconj_subst {X : Finset (Formula α)} {s : Substitution α} : L ⊢! (X.image (·⟦s⟧)).conj ➝ X.conj⟦s⟧ := by
  apply C!_trans ?_ $ lconj_subst (L := L) (X := X.toList) (s := s);
  apply right_Conj₂!_intro;
  intro φ hφ;
  apply left_Fconj!_intro;
  simp_all;

end


inductive sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : L₁ ⊢! φ → sumQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : L₂ ⊢! φ → sumQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ ➝ ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
  | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

namespace sumQuasiNormal

variable {φ ψ : Formula α}

lemma mem₁! (hφ : L₁ ⊢! φ) : sumQuasiNormal L₁ L₂ ⊢! φ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₁ hφ;

lemma mem₂! (hφ : L₂ ⊢! φ) : sumQuasiNormal L₁ L₂ ⊢! φ := by
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
    constructor;
    apply sumQuasiNormal.subst;
    exact PLift.down hφ;

lemma rec!
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! φ ➝ ψ} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  (subst : ∀ {φ s}, {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} → (motive φ hφ) → motive (φ⟦s⟧) (Logic.subst! _ hφ))
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
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
  imply₁ _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  imply₂ _ _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  elimContra _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;

instance [L₁.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal where
  K _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  subst s hφ := by
    constructor;
    apply sumQuasiNormal.subst;
    exact PLift.down hφ;

instance [L₂.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal := by
  rw [sumQuasiNormal.symm];
  infer_instance;

instance : L₁ ⪯ sumQuasiNormal L₁ L₂ := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  exact mem₁! hφ;

instance : L₂ ⪯ sumQuasiNormal L₁ L₂ := by
  rw [sumQuasiNormal.symm];
  infer_instance;

omit [DecidableEq α] in
lemma iff_subset {X Y} : L.sumQuasiNormal Y ⊆ L.sumQuasiNormal X ↔ ∀ ψ ∈ Y, L.sumQuasiNormal X ⊢! ψ := by
  suffices (∀ φ, L.sumQuasiNormal Y ⊢! φ → L.sumQuasiNormal X ⊢! φ) ↔ (∀ ψ ∈ Y, L.sumQuasiNormal X ⊢! ψ) by
    apply Iff.trans ?_ this;
    constructor;
    . intro h ψ; simpa using @h ψ;
    . intro h ψ; simpa using @h ψ;
  constructor;
  . intro h ψ hψ;
    apply h;
    apply Logic.sumQuasiNormal.mem₂!
    simpa using hψ;
  . intro h ψ hψ;
    induction hψ using Logic.sumQuasiNormal.rec! with
    | mem₁ hψ => apply Logic.sumQuasiNormal.mem₁! hψ;
    | mem₂ hψ => apply h; simpa using hψ;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | subst ihφ => apply Logic.subst!; assumption;

section

variable [L₁.IsQuasiNormal]

open LO.Entailment

lemma provable_of_finite_provable : (∃ X : Finset _, (X.toSet ⊆ L₂) ∧ L₁ ⊢! X.conj ➝ φ) → sumQuasiNormal L₁ L₂ ⊢! φ := by
  rintro ⟨X, hX₂, hφ⟩;
  apply (WeakerThan.pbl (𝓣 := sumQuasiNormal L₁ L₂) hφ) ⨀ ?_;
  apply FConj!_iff_forall_provable.mpr;
  intro χ hχ;
  apply mem₂!;
  apply iff_provable.mpr;
  apply hX₂ hχ;

lemma finite_provable_of_provable (h : ∀ ξ ∈ L₂, ∀ s : Substitution _, ξ⟦s⟧ ∈ L₂) :
  sumQuasiNormal L₁ L₂ ⊢! φ → ∃ X : Finset _, (↑X ⊆ L₂) ∧ L₁ ⊢! X.conj ➝ φ := by
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
    . simpa using h;
    . simp;
  | @mdp φ ψ _ _ ihφψ ihφ =>
    obtain ⟨X₁, _, hφψ⟩ := ihφψ;
    obtain ⟨X₂, _, hφ⟩ := ihφ;
    use X₁ ∪ X₂;
    constructor;
    . simp_all;
    . suffices L₁ ⊢! (X₁.conj ⋏ X₂.conj) ➝ ψ by exact C!_trans CFconjUnionKFconj! this;
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
    . apply C!_trans ?_ (subst! s hφ);
      exact Logic.fconj_subst;

lemma iff_provable_finite_provable (h : ∀ ξ ∈ L₂, ∀ s : Substitution _, ξ⟦s⟧ ∈ L₂)  :
  sumQuasiNormal L₁ L₂ ⊢! φ ↔ ∃ X : Finset _, (↑X ⊆ L₂) ∧ L₁ ⊢! X.conj ➝ φ := ⟨finite_provable_of_provable h, provable_of_finite_provable⟩

end

end sumQuasiNormal

inductive sumNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : L₁ ⊢! φ → sumNormal L₁ L₂ φ
  | mem₂ {φ}    : L₂ ⊢! φ → sumNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumNormal L₁ L₂ (φ ➝ ψ) → sumNormal L₁ L₂ φ → sumNormal L₁ L₂ ψ
  | subst {φ s} : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (□φ)

namespace sumNormal

variable {φ ψ : Formula α}

lemma mem₁! (hφ : L₁ ⊢! φ) : sumNormal L₁ L₂ ⊢! φ := by
  apply iff_provable.mpr;
  apply sumNormal.mem₁ hφ;

lemma mem₂! (hφ : L₂ ⊢! φ) : sumNormal L₁ L₂ ⊢! φ := by
  apply iff_provable.mpr;
  apply sumNormal.mem₂ hφ;

instance : Entailment.ModusPonens (sumNormal L₁ L₂) where
  mdp hφψ hφ := by
    constructor;
    apply sumNormal.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;

instance : Entailment.Necessitation (sumNormal L₁ L₂) where
  nec hφ := by
    constructor;
    apply sumNormal.nec;
    exact PLift.down hφ;

instance : (sumNormal L₁ L₂).Substitution where
  subst s hφ := by
    constructor;
    apply sumNormal.subst;
    exact PLift.down hφ;


lemma rec!
  {motive : (φ : Formula α) → ((sumNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumNormal L₁ L₂) ⊢! φ ➝ ψ} → {hφ : (sumNormal L₁ L₂) ⊢! φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  (nec   : ∀ {φ}, {hφ : (sumNormal L₁ L₂) ⊢! φ} → (motive φ hφ) → motive (□φ) (Entailment.nec! hφ))
  (subst : ∀ {φ s}, {hφ : (sumNormal L₁ L₂) ⊢! φ} → (motive φ hφ) → motive (φ⟦s⟧) (Logic.subst! _ hφ))
  : ∀ {φ}, (h : sumNormal L₁ L₂ ⊢! φ) → motive φ h := by
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
  | nec hφ ihφ =>
    apply nec;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;
  | subst hφ ihφ =>
    apply subst;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;

lemma symm : sumNormal L₁ L₂ = sumNormal L₂ L₁ := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact sumNormal.mem₂ h;
    | mem₂ h => exact sumNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumNormal.subst ihφ;
    | nec _ ihφ => exact sumNormal.nec ihφ;
  . intro h;
    induction h with
    | mem₁ h => exact sumNormal.mem₂ h;
    | mem₂ h => exact sumNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumNormal.subst ihφ;
    | nec _ ihφ => exact sumNormal.nec ihφ;

variable [DecidableEq α]

instance [Entailment.Cl L₁] : Entailment.Lukasiewicz (sumNormal L₁ L₂) where
  imply₁ _ _ := by constructor; apply sumNormal.mem₁; simp;
  imply₂ _ _ _ := by constructor; apply sumNormal.mem₁; simp;
  elimContra _ _ := by constructor; apply sumNormal.mem₁; simp;
  mdp hφψ hφ := by
    constructor;
    apply sumNormal.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;

instance [L₁.IsNormal] : (sumNormal L₁ L₂).IsNormal where
  K _ _ := by constructor; apply sumNormal.mem₁; simp;
  subst s hφ := by
    constructor;
    apply sumNormal.subst;
    exact PLift.down hφ;
  nec hφ := by
    constructor;
    apply sumNormal.nec;
    exact PLift.down hφ;

instance [L₂.IsNormal] : (sumNormal L₁ L₂).IsNormal := by
  rw [sumNormal.symm];
  infer_instance;

instance : L₁ ⪯ sumNormal L₁ L₂ := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  exact mem₁! hφ;

instance : L₂ ⪯ sumNormal L₁ L₂ := by
  rw [sumNormal.symm];
  infer_instance;

end sumNormal

end Logic

end LO.Modal
