import Foundation.Modal.Logic.Extension
import Foundation.ProvabilityLogic.Classification.LetterlessTrace

namespace LO.Modal

namespace Logic

attribute [grind] Modal.Logic.iff_provable

variable {L L₁ L₂ : Logic α} {φ ψ : Formula α} {s : Substitution α}


lemma sumQuasiNormal.with_empty [DecidableEq α] {L₁ : Logic α} [L₁.IsQuasiNormal] : L₁.sumQuasiNormal ∅ = L₁ := by
  ext φ;
  suffices L₁.sumQuasiNormal ∅ ⊢! φ ↔ L₁ ⊢! φ by simpa [Logic.iff_provable];
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | mem₁ => assumption;
    | mem₂ => simp_all;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => exact Logic.subst! _ ihφ;
  . intro h;
    exact Entailment.WeakerThan.pbl h;


inductive sumQuasiNormal' (L₁ L₂ : Logic α) : Logic α
| mem₁ {φ} (s : Substitution _) : L₁ ⊢! φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mem₂ {φ} (s : Substitution _) : L₂ ⊢! φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mdp {φ ψ : Formula α} : sumQuasiNormal' L₁ L₂ (φ ➝ ψ) → sumQuasiNormal' L₁ L₂ φ → sumQuasiNormal' L₁ L₂ ψ

namespace sumQuasiNormal'

@[grind]
lemma mem₁! (h : L₁ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₁ _ h;

@[grind]
lemma mem₁!_nosub (h : L₁ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! φ := by
  simpa using mem₁! (s := Substitution.id) h;

@[grind]
lemma mem₂! (h : L₂ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₂ _ h;

@[grind]
lemma mem₂!_nosub (h : L₂ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! φ := by
  simpa using mem₂! (s := Substitution.id) h;

instance : Entailment.ModusPonens (sumQuasiNormal' L₁ L₂) where
  mdp := by rintro φ ψ ⟨hφψ⟩ ⟨hφ⟩; exact ⟨sumQuasiNormal'.mdp hφψ hφ⟩;

lemma rec!
  {motive : (φ : Formula α) → ((sumQuasiNormal' L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal' L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal' L₁ L₂) ⊢! φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal' L₁ L₂ ⊢! φ) → motive φ h := by
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
  subst s := by
    rintro ⟨hφ⟩;
    constructor;
    induction hφ with
    | mem₁ s' h => simpa using mem₁ (s := s' ∘ s) h
    | mem₂ s' h => simpa using mem₂ (s := s' ∘ s) h
    | mdp _ _ ihφψ ihφ => exact mdp ihφψ ihφ

end sumQuasiNormal'


attribute [grind] Logic.sumQuasiNormal.mem₁! Logic.sumQuasiNormal.mem₂!

lemma eq_sumQuasiNormal_sumQuasiNormal' : Logic.sumQuasiNormal L₁ L₂ = Logic.sumQuasiNormal' L₁ L₂ := by
  ext φ;
  suffices (Logic.sumQuasiNormal L₁ L₂ ⊢! φ) ↔ (Logic.sumQuasiNormal' L₁ L₂ ⊢! φ) by grind;
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | @subst ψ s _ ihφ => exact subst! _ ihφ;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => grind;
  . intro h;
    induction h using Logic.sumQuasiNormal'.rec! with
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => apply subst!; grind;

@[grind]
lemma iff_provable_sumQuasiNormal'_provable_sumQuasiNormal : (sumQuasiNormal' L₁ L₂ ⊢! φ) ↔ (sumQuasiNormal L₁ L₂ ⊢! φ) := by
  rw [eq_sumQuasiNormal_sumQuasiNormal'];

lemma sumQuasiNormal.rec!_omitSubst
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  intro φ hφ;
  induction (iff_provable_sumQuasiNormal'_provable_sumQuasiNormal.mpr hφ) using Logic.sumQuasiNormal'.rec! with
  | mem₁ s h => grind;
  | mem₂ s h => grind;
  | @mdp _ _ hφψ hφ ihφψ ihφ => exact mdp (ihφψ $ by grind) (ihφ $ by grind);

attribute [grind] Logic.subst!

@[grind]
def substitution_of_letterless (L_letterless : FormulaSet.letterless L) : L.Substitution where
  subst s := by
    rintro ⟨hφ⟩;
    constructor;
    simpa [Formula.subst.subst_letterless (s := s) $ L_letterless _ hφ];

lemma sumQuasiNormal.rec!_omitSubst₁ (hL₁ : L₁.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ s h;
    apply mem₁;
    grind;
  . assumption;
  . assumption;

lemma sumQuasiNormal.rec!_omitSubst₂ (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  simp_all only [Logic.sumQuasiNormal.symm (L₁ := L₁) (L₂ := L₂)]
  apply sumQuasiNormal.rec!_omitSubst₁ <;> assumption;

lemma sumQuasiNormal.rec!_omitSubst_strong (hL₁ : L₁.Substitution) (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ h _; apply mem₁; grind;
  . intro φ h _; apply mem₂; grind;
  . assumption;

end Logic


end LO.Modal
