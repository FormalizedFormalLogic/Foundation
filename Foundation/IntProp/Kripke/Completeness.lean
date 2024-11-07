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

variable {α : Type u}
         {H : Hilbert α}

open SaturatedConsistentTableau

def CanonicalFrame (H : Hilbert α) [Nonempty (SCT H)] : Kripke.Frame.Dep α where
  World := SCT H
  Rel t₁ t₂ := t₁.tableau.1 ⊆ t₂.tableau.1

namespace CanonicalFrame

variable [Nonempty (SCT H)]

lemma reflexive : Reflexive (CanonicalFrame H) := by
  simp [CanonicalFrame];
  intro x;
  apply Set.Subset.refl;

lemma antisymmetric : Antisymmetric (CanonicalFrame H) := by
  simp [CanonicalFrame];
  intro x y Rxy Ryx;
  exact equality_of₁ $ Set.Subset.antisymm Rxy Ryx;

lemma transitive : Transitive (CanonicalFrame H) := by
  simp [CanonicalFrame];
  intro x y z;
  apply Set.Subset.trans;

open Classical in
lemma confluent [Encodable α] [H.IncludeEFQ] [HasAxiomWeakLEM H] : Confluent (CanonicalFrame H) := by
  simp [Confluent, CanonicalFrame];
  intro x y z Rxy Rxz;
  suffices Tableau.Consistent H (y.tableau.1 ∪ z.tableau.1, ∅) by
    obtain ⟨w, hw⟩ := lindenbaum (H := H) this;
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
    have : H ⊬ ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := y.consistent (Γ := [⋀Θy, ∼⋀Θy]) (Δ := []) (by simp; constructor <;> assumption) (by simp);
    have : H ⊢! ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := by simp;
    contradiction;

  have : H ⊢! (⋀Θx ⋏ (⋀Θy ⋏ ⋀Θz)) ➝ ⊥ := imp_trans''! (by
    -- TODO: need more refactor
    have d₁ : H ⊢! ⋀Θx ⋏ ⋀(Θy ++ Θz) ➝ ⋀(Θx ++ (Θy ++ Θz)) := and₂'! $ iff_concat_conj!;
    have d₂ : H ⊢! ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θy ++ Θz) := and₂'! $ iff_concat_conj!;
    have d₃ : H ⊢! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θx ++ (Θy ++ Θz)) := imp_trans''! (by
      apply deduct'!;
      have : [⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz] ⊢[H]! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz := FiniteContext.by_axm!;
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
  have : H ⊢! ⋀Θx ➝ ⋀Θy ➝ ∼⋀Θz := and_imply_iff_imply_imply'!.mp $
    (imp_trans''! (and_imply_iff_imply_imply'!.mp $ imp_trans''! (and₁'! and_assoc!) this) (and₂'! $ neg_equiv!));
  have d : H ⊢! ⋀Θx ➝ ∼∼⋀Θz ➝ ∼⋀Θy := imp_trans''! this contra₀!;

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


lemma connected [DecidableEq α] [HasAxiomDummett H] : Connected (CanonicalFrame H) := by
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


def CanonicalModel (H : Hilbert α) [Nonempty (SCT H)] : Kripke.Model α where
  Frame := CanonicalFrame H
  Valuation t a := (atom a) ∈ t.tableau.1
  -- hereditary := by aesop;

namespace CanonicalModel

variable [Nonempty (SCT H)] {t t₁ t₂ : SCT H}

lemma hereditary : (CanonicalModel H).Valuation.atomic_hereditary := by
  intros _ _;
  aesop;

@[reducible]
instance : Semantics (Formula α) (CanonicalModel H).World := Formula.Kripke.Satisfies.semantics (CanonicalModel H)

@[simp] lemma frame_def : (CanonicalModel H).Frame t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {a : α} : (CanonicalModel H).Valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end CanonicalModel

section

variable [Nonempty (SCT H)]

variable {t : SCT H} {φ ψ : Formula α}

private lemma truthlemma.himp
  [H.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel H).World}
  (ihp : ∀ {t : (CanonicalModel H).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
  (ihq : ∀ {t : (CanonicalModel H).World}, t ⊧ ψ ↔ ψ ∈ t.tableau.1)
  : t ⊧ φ ➝ ψ ↔ φ ➝ ψ ∈ t.tableau.1 := by
  constructor;
  . contrapose;
    simp_all [Satisfies];
    intro h;
    replace h := not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (H := H) (t₀ := (insert φ t.tableau.1, {ψ})) $ by
      simp only [Tableau.Consistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ χ, χ ∈ Γ.remove φ → χ ∈ t.tableau.1 := by
        intro χ hr;
        have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
        have := by simpa using hΓ χ hr₁;
        simp_all;
      by_contra hC;
      have : H ⊢! ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj! hC) (by
        apply deduct'!;
        apply deduct!;
        have : [φ, φ ➝ ⋁Δ] ⊢[H]! φ := by_axm!;
        have : [φ, φ ➝ ⋁Δ] ⊢[H]! ⋁Δ := by_axm! ⨀ this;
        exact disj_allsame'! (by simpa using hΔ) this;
      )
      have : H ⊬ ⋀(Γ.remove φ) ➝ (φ ➝ ψ) := by simpa using (t.consistent hΓ (show ∀ χ ∈ [φ ➝ ψ], χ ∈ t.tableau.2 by simp_all));
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
      (show H ⊢! ⋀[φ, φ ➝ ψ] ➝ ψ by
        simp;
        apply and_imply_iff_imply_imply'!.mpr;
        apply deduct'!;
        apply deduct!;
        exact by_axm! ⨀ (by_axm! (φ := φ));
      );

private lemma truthlemma.hneg
  [H.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel H).World}
  (ihp : ∀ {t : (CanonicalModel H).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
  : t ⊧ ∼φ ↔ ∼φ ∈ t.tableau.1 := by
  constructor;
  . contrapose;
    simp_all [Satisfies];
    intro h;
    replace h := not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (H := H) (t₀ := (insert φ t.tableau.1, ∅)) $ by
      simp only [Tableau.Consistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ ψ, ψ ∈ Γ.remove φ → ψ ∈ t.tableau.1 := by
        intro ψ hq;
        have ⟨hq₁, hq₂⟩ := List.mem_remove_iff.mp hq;
        have := by simpa using hΓ ψ hq₁;
        simp_all;
      replace hΔ : Δ = [] := List.nil_iff.mpr hΔ; subst hΔ;
      by_contra hC; simp at hC;
      have : H ⊢! ⋀(Γ.remove φ) ➝ ∼φ := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj! hC) (and₂'! neg_equiv!);
      have : H ⊬ ⋀(Γ.remove φ) ➝ ∼φ := by simpa using t.consistent (Δ := [∼φ]) hΓ (by simpa);
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    use t';
  . simp;
    intro ht t' htt';
    apply ihp.not.mpr;
    by_contra hC;
    have : H ⊬ φ ⋏ ∼φ ➝ ⊥ := by simpa using t'.consistent (Γ := [φ, ∼φ]) (Δ := []) (by aesop) (by simp);
    have : H ⊢! φ ⋏ ∼φ ➝ ⊥ := intro_bot_of_and!;
    contradiction;

lemma truthlemma
  [H.IncludeEFQ] [Encodable α] [DecidableEq α]
  {t : (CanonicalModel H).World} : t ⊧ φ ↔ φ ∈ t.tableau.1 := by
  induction φ using Formula.rec' generalizing t with
  | himp φ ψ ihp ihq => exact truthlemma.himp ihp ihq
  | hneg φ ihp => exact truthlemma.hneg ihp;
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma deducible_of_validOnCanonicelModel
  [H.IncludeEFQ] [Encodable α] [DecidableEq α]
  : (CanonicalModel H) ⊧ φ ↔ H ⊢! φ := by
  constructor;
  . contrapose;
    intro h;
    have : Tableau.Consistent H (∅, {φ}) := by
      simp only [Tableau.Consistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      replace hΓ : Γ = [] := List.nil_iff.mpr hΓ;
      subst hΓ;
      have : H ⊢! φ := disj_allsame'! hΔ (hC ⨀ verum!);
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

variable [System.Consistent H]
variable [DecidableEq α] [Encodable α] [H.IncludeEFQ]
variable {𝔽 : Kripke.FrameClass}

omit [Consistent H] in
lemma complete (hC : CanonicalFrame H ∈ 𝔽) {φ : Formula α} : 𝔽#α ⊧ φ → H ⊢! φ := by
  intro h;
  apply deducible_of_validOnCanonicelModel.mp;
  apply h;
  . exact hC;
  . exact CanonicalModel.hereditary;

instance instComplete (hC : CanonicalFrame H ∈ 𝔽) : Complete H (𝔽#α) := ⟨complete hC⟩

instance Int_complete : Complete (Hilbert.Int α) (Kripke.ReflexiveTransitiveFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
  ⟩

instance LC_complete : Complete (Hilbert.LC α) (Kripke.ReflexiveTransitiveConnectedFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
    CanonicalFrame.connected
  ⟩;

instance KC_complete : Complete (Hilbert.KC α) (Kripke.ReflexiveTransitiveConfluentFrameClass.{u}#α) := instComplete $ by
  refine ⟨
    CanonicalFrame.reflexive,
    CanonicalFrame.transitive,
    CanonicalFrame.confluent
  ⟩;

end


end

end Kripke

end LO.IntProp
