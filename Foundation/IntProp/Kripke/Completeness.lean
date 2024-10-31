import Foundation.IntProp.ConsistentTableau
import Foundation.IntProp.Kripke.Semantics

set_option autoImplicit false
universe u v

namespace LO.IntProp

open System System.FiniteContext
open Formula (atom)
open Formula.Kripke (Satisfies ValidOnModel)
open Kripke

namespace Kripke

-- variable [Inhabited α] [DecidableEq α] [Encodable α] [Λ.IncludeEFQ]
variable {α : Type u}
         {Λ : Hilbert α}

open SaturatedConsistentTableau

def CanonicalFrame (Λ : Hilbert α) [Nonempty (SCT Λ)] : Kripke.Frame.Dep α where
  World := SCT Λ
  Rel t₁ t₂ := t₁.tableau.1 ⊆ t₂.tableau.1

namespace CanonicalFrame

variable [Nonempty (SCT Λ)]

lemma reflexive : Reflexive (CanonicalFrame Λ) := by
  simp [CanonicalFrame];
  intro x;
  apply Set.Subset.refl;

lemma antisymmetric : Antisymmetric (CanonicalFrame Λ) := by
  simp [CanonicalFrame];
  intro x y Rxy Ryx;
  exact equality_of₁ $ Set.Subset.antisymm Rxy Ryx;

lemma transitive : Transitive (CanonicalFrame Λ) := by
  simp [CanonicalFrame];
  intro x y z;
  apply Set.Subset.trans;

open Classical in
lemma confluent [Encodable α] [Λ.IncludeEFQ] [HasAxiomWeakLEM Λ] : Confluent (CanonicalFrame Λ) := by
  simp [Confluent, CanonicalFrame];
  intro x y z Rxy Rxz;
  suffices Tableau.Consistent Λ (y.tableau.1 ∪ z.tableau.1, ∅) by
    obtain ⟨w, hw⟩ := lindenbaum (Λ := Λ) this;
    use w;
    simp_all;

  intro Γ Δ;
  intro hΓ hΔ h;
  simp_all;
  have := List.nil_iff.mpr hΔ; subst this; simp at h; clear hΔ;

  have hΓy : ¬(∀ w, w ∈ Γ → w ∈ y.tableau.1) := by
    by_contra hC;
    have := by simpa using y.consistent (Γ := Γ) (Δ := []) hC (by simp);
    contradiction;
  push_neg at hΓy;

  have hΓz : ¬(∀ w, w ∈ Γ → w ∈ z.tableau.1) := by
    by_contra hC;
    have := by simpa using z.consistent (Γ := Γ) (Δ := []) hC (by simp);
    contradiction;
  push_neg at hΓz;

  let Θy := Γ.filter (λ φ => φ ∈ y.tableau.1 ∧ φ ∉ x.tableau.1);
  let Θz := Γ.filter (λ φ => φ ∈ z.tableau.1 ∧ φ ∉ x.tableau.1);
  let Θx := Γ.filter (λ φ => (φ ∈ y.tableau.1 ∧ φ ∈ x.tableau.1) ∨ (φ ∈ z.tableau.1 ∧ φ ∈ x.tableau.1));

  suffices ∼⋀Θy ∈ x.tableau.1 by
    have : ∼⋀Θy ∈ y.tableau.1 := Rxy this;
    have : ⋀Θy ∈ y.tableau.1 := iff_mem₁_conj.mpr $ by
      intro φ hp;
      have := by simpa using List.of_mem_filter hp;
      exact this.1;
    have : Λ ⊬ ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := y.consistent (Γ := [⋀Θy, ∼⋀Θy]) (Δ := []) (by simp; constructor <;> assumption) (by simp);
    have : Λ ⊢! ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := by simp;
    contradiction;

  have : Λ ⊢! (⋀Θx ⋏ (⋀Θy ⋏ ⋀Θz)) ➝ ⊥ := imp_trans''! (by
    -- TODO: need more refactor
    have d₁ : Λ ⊢! ⋀Θx ⋏ ⋀(Θy ++ Θz) ➝ ⋀(Θx ++ (Θy ++ Θz)) := and₂'! $ iff_concat_conj!;
    have d₂ : Λ ⊢! ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θy ++ Θz) := and₂'! $ iff_concat_conj!;
    have d₃ : Λ ⊢! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θx ++ (Θy ++ Θz)) := imp_trans''! (by
      apply deduct'!;
      have : [⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz] ⊢[Λ]! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz := FiniteContext.by_axm!;
      apply and₃'!;
      . exact and₁'! this;
      . exact (FiniteContext.of'! d₂) ⨀ (and₂'! this);
    ) d₁;
    exact imp_trans''! d₃ $ conjconj_subset! $ by
      intro φ hp; simp;
      apply or_iff_not_imp_left.mpr;
      intro nmem_Θx;
      have := (not_imp_not.mpr $ List.mem_filter_of_mem hp) nmem_Θx; simp at this;
      have ⟨hy₁, hz₁⟩ := this;
      rcases hΓ _ hp with (hy | hz);
      . left;
        apply List.mem_filter_of_mem hp;
        simp;
        constructor;
        . assumption;
        . exact hy₁ hy;
      . right;
        apply List.mem_filter_of_mem hp;
        simp;
        constructor;
        . assumption;
        . exact hz₁ hz;
  ) h;
  have : Λ ⊢! ⋀Θx ➝ ⋀Θy ➝ ∼⋀Θz := and_imply_iff_imply_imply'!.mp $
    (imp_trans''! (and_imply_iff_imply_imply'!.mp $ imp_trans''! (and₁'! and_assoc!) this) (and₂'! $ neg_equiv!));
  have d : Λ ⊢! ⋀Θx ➝ ∼∼⋀Θz ➝ ∼⋀Θy := imp_trans''! this contra₀!;

  have mem_Θx_x : ⋀Θx ∈ x.tableau.1 := iff_mem₁_conj.mpr $ by
    intro φ hp;
    have := by simpa using List.of_mem_filter hp;
    rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> assumption;
  have mem_Θz_z : ⋀Θz ∈ z.tableau.1 := iff_mem₁_conj.mpr $ by
    intro φ hp;
    have := by simpa using List.of_mem_filter hp;
    exact this.1;

  have nmem_nΘz_z : ∼⋀Θz ∉ z.tableau.1 := not_mem₁_neg_of_mem₁ mem_Θz_z;
  have nmem_nΘz_x : ∼⋀Θz ∉ x.tableau.1 := Set.not_mem_subset Rxz nmem_nΘz_z;
  have mem_nnΘz_x : ∼∼⋀Θz ∈ x.tableau.1 := or_iff_not_imp_left.mp (iff_mem₁_or.mp $ mem₁_of_provable $ wlem!) nmem_nΘz_x;

  exact mdp₁_mem mem_nnΘz_x $ mdp₁ mem_Θx_x d;


lemma connected [DecidableEq α] [HasAxiomDummett Λ] : Connected (CanonicalFrame Λ) := by
  simp [Connected, CanonicalFrame];
  intro x y z Rxy Ryz;
  apply or_iff_not_imp_left.mpr;
  intro nRyz;
  obtain ⟨φ, hyp, nhzp⟩ := Set.not_subset.mp nRyz;
  intro ψ hqz;
  have : ψ ➝ φ ∉ x.tableau.1 := by
    by_contra hqpx;
    have hqpz : ψ ➝ φ ∈ z.tableau.1 := by aesop;
    have : φ ∈ z.tableau.1 := mdp₁_mem hqz hqpz;
    contradiction;
  have := iff_mem₁_or.mp $ mem₁_of_provable (t := x) (φ := (φ ➝ ψ) ⋎ (ψ ➝ φ)) dummett!;
  have hpqx : φ ➝ ψ ∈ x.tableau.1 := by aesop;
  have hpqy : φ ➝ ψ ∈ y.tableau.1 := Rxy hpqx;
  have : ψ ∈ y.tableau.1 := mdp₁_mem hyp hpqy;
  exact this;

end CanonicalFrame


def CanonicalModel (Λ : Hilbert α) [Nonempty (SCT Λ)] : Kripke.Model α where
  Frame := CanonicalFrame Λ
  Valuation t a := (atom a) ∈ t.tableau.1
  -- hereditary := by aesop;

namespace CanonicalModel

variable [Nonempty (SCT Λ)] {t t₁ t₂ : SCT Λ}

lemma hereditary : (CanonicalModel Λ).Valuation.atomic_hereditary := by
  intros _ _;
  aesop;

@[reducible]
instance : Semantics (Formula α) (CanonicalModel Λ).World := Formula.Kripke.Satisfies.semantics (CanonicalModel Λ)

@[simp] lemma frame_def : (CanonicalModel Λ).Frame t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {a : α} : (CanonicalModel Λ).Valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end CanonicalModel

section

variable [Nonempty (SCT Λ)]

variable {t : SCT Λ} {φ ψ : Formula α}

private lemma truthlemma.himp
  [Λ.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel Λ).World}
  (ihp : ∀ {t : (CanonicalModel Λ).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
  (ihq : ∀ {t : (CanonicalModel Λ).World}, t ⊧ ψ ↔ ψ ∈ t.tableau.1)
  : t ⊧ φ ➝ ψ ↔ φ ➝ ψ ∈ t.tableau.1 := by
  constructor;
  . contrapose;
    simp_all [Satisfies];
    intro h;
    replace h := not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (Λ := Λ) (t₀ := (insert φ t.tableau.1, {ψ})) $ by
      simp only [Tableau.Consistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ χ, χ ∈ Γ.remove φ → χ ∈ t.tableau.1 := by
        intro χ hr;
        have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
        have := by simpa using hΓ χ hr₁;
        simp_all;
      by_contra hC;
      have : Λ ⊢! ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj! hC) (by
        apply deduct'!;
        apply deduct!;
        have : [φ, φ ➝ ⋁Δ] ⊢[Λ]! φ := by_axm!;
        have : [φ, φ ➝ ⋁Δ] ⊢[Λ]! ⋁Δ := by_axm! ⨀ this;
        exact disj_allsame'! (by simpa using hΔ) this;
      )
      have : Λ ⊬ ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := by simpa using (t.consistent hΓ (show ∀ χ ∈ [φ ➝ ψ], χ ∈ t.tableau.2 by simp_all));
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    use t';
    constructor;
    . simp_all only [Set.singleton_subset_iff];
    . constructor;
      . assumption;
      . apply not_mem₁_iff_mem₂.mpr;
        simp_all only [Set.singleton_subset_iff];
  . simp [Satisfies.imp_def];
    intro h t' htt' hp;
    replace hp := ihp.mp hp;
    have hpq := htt' h;
    apply ihq.mpr;
    apply not_mem₂_iff_mem₁.mp;
    exact not_mem₂
      (by simp_all)
      (show Λ ⊢! ⋀[φ, φ ➝ ψ] ➝ ψ by
        simp;
        apply and_imply_iff_imply_imply'!.mpr;
        apply deduct'!;
        apply deduct!;
        exact by_axm! ⨀ (by_axm! (φ := φ));
      );

private lemma truthlemma.hneg
  [Λ.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel Λ).World}
  (ihp : ∀ {t : (CanonicalModel Λ).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
  : t ⊧ ∼φ ↔ ∼φ ∈ t.tableau.1 := by
  constructor;
  . contrapose;
    simp_all [Satisfies];
    intro h;
    replace h := not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (Λ := Λ) (t₀ := (insert φ t.tableau.1, ∅)) $ by
      simp only [Tableau.Consistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ ψ, ψ ∈ Γ.remove φ → ψ ∈ t.tableau.1 := by
        intro ψ hq;
        have ⟨hq₁, hq₂⟩ := List.mem_remove_iff.mp hq;
        have := by simpa using hΓ ψ hq₁;
        simp_all;
      replace hΔ : Δ = [] := List.nil_iff.mpr hΔ; subst hΔ;
      by_contra hC; simp at hC;
      have : Λ ⊢! ⋀(Γ.remove φ) ➝ ∼φ := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj! hC) (and₂'! neg_equiv!);
      have : Λ ⊬ ⋀(Γ.remove φ) ➝ ∼φ := by simpa using t.consistent (Δ := [∼φ]) hΓ (by simpa);
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    use t';
  . simp;
    intro ht t' htt';
    apply ihp.not.mpr;
    by_contra hC;
    have : Λ ⊬ φ ⋏ ∼φ ➝ ⊥ := by simpa using t'.consistent (Γ := [φ, ∼φ]) (Δ := []) (by aesop) (by simp);
    have : Λ ⊢! φ ⋏ ∼φ ➝ ⊥ := intro_bot_of_and!;
    contradiction;

lemma truthlemma
  [Λ.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel Λ).World} : t ⊧ φ ↔ φ ∈ t.tableau.1 := by
  induction φ using Formula.rec' generalizing t with
  | himp φ ψ ihp ihq => exact truthlemma.himp ihp ihq
  | hneg φ ihp => exact truthlemma.hneg ihp;
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma deducible_of_validOnCanonicelModel
  [Λ.IncludeEFQ] [Encodable α] [DecidableEq α]
  : (CanonicalModel Λ) ⊧ φ ↔ Λ ⊢! φ := by
  constructor;
  . contrapose;
    intro h;
    have : Tableau.Consistent Λ (∅, {φ}) := by
      simp only [Tableau.Consistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      replace hΓ : Γ = [] := List.nil_iff.mpr hΓ;
      subst hΓ;
      have : Λ ⊢! φ := disj_allsame'! hΔ (hC ⨀ verum!);
      contradiction;
    obtain ⟨t', ht'⟩ := lindenbaum this;
    simp [ValidOnModel.iff_models, ValidOnModel]
    existsi t';
    apply truthlemma.not.mpr;
    apply not_mem₁_iff_mem₂.mpr;
    simp_all;
  . intro h t;
    suffices φ ∈ t.tableau.1 by exact truthlemma.mpr this;
    exact mem₁_of_provable h;


section

variable [System.Consistent Λ]
variable [DecidableEq α] [Encodable α] [Λ.IncludeEFQ]
variable {𝔽 : Kripke.FrameClass}

omit [Consistent Λ] in
lemma complete (H : CanonicalFrame Λ ∈ 𝔽) {φ : Formula α} : 𝔽#α ⊧ φ → Λ ⊢! φ := by
  intro h;
  apply deducible_of_validOnCanonicelModel.mp;
  apply h;
  . exact H;
  . exact CanonicalModel.hereditary;

instance instComplete (H : CanonicalFrame Λ ∈ 𝔽) : Complete Λ (𝔽#α) := ⟨complete H⟩

instance Int_complete : Complete 𝐈𝐧𝐭 (Kripke.ReflexiveTransitiveFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
  ⟩

instance LC_complete : Complete 𝐋𝐂 (Kripke.ReflexiveTransitiveConnectedFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
    CanonicalFrame.connected
  ⟩;

instance KC_complete : Complete 𝐊𝐂 (Kripke.ReflexiveTransitiveConfluentFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
    CanonicalFrame.confluent
  ⟩;

end


end

end Kripke

end LO.IntProp
