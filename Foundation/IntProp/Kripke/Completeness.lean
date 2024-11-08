import Foundation.IntProp.ConsistentTableau
import Foundation.IntProp.Kripke.Semantics

set_option autoImplicit false
universe u

namespace LO.IntProp

variable {H : Hilbert ℕ}
variable {t t₁ t₂ : SCT H} {φ ψ : Formula ℕ}

open System System.FiniteContext
open Formula (atom)
open Formula.Kripke (Satisfies ValidOnModel)
open Kripke
open SaturatedConsistentTableau

namespace Hilbert

namespace Kripke

def canonicalFrameOf (H : Hilbert ℕ) [H.Consistent] [H.IncludeEFQ] : Kripke.Frame where
  World := SCT H
  Rel t₁ t₂ := t₁.tableau.1 ⊆ t₂.tableau.1
  rel_po := {
    refl := by simp;
    trans := fun x y z Sxy Syz => Set.Subset.trans Sxy Syz
    antisymm := fun x y Sxy Syx => equality_of₁ (Set.Subset.antisymm Sxy Syx)
  }

namespace canonicalFrame

variable {H : Hilbert ℕ} [H.IncludeEFQ] [H.Consistent]

open Classical in
lemma is_confluent [HasAxiomWeakLEM H] : Confluent (Kripke.canonicalFrameOf H) := by
  simp [Confluent, Kripke.canonicalFrameOf];
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

lemma is_connected [HasAxiomDummett H] : Connected (Kripke.canonicalFrameOf H) := by
  simp [Connected, Kripke.canonicalFrameOf];
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

end canonicalFrame


def canonicalModelOf (H : Hilbert ℕ) [H.Consistent] [H.IncludeEFQ] : Kripke.Model where
  toFrame := Kripke.canonicalFrameOf H
  Val := ⟨λ t a => (atom a) ∈ t.tableau.1, by aesop⟩

/-
namespace canonicalModelOf

variable [Nonempty (SCT H)]

@[reducible]
instance : Semantics (Formula α) (Kripke.canonicalFrameOf H).World := Formula.Kripke.Satisfies.semantics $ Kripke.canonicalModelOf H

@[simp] lemma frame_def : (Kripke.canonicalModelOf H).toFrame t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {a : α} : (Kripke.canonicalModelOf H).Valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end canonicalModelOf
-/

section lemmata

variable [H.IncludeEFQ] [H.Consistent]
variable {C : Kripke.FrameClass}

section truthlemma

variable {t : (Kripke.canonicalModelOf H).World}

private lemma truthlemma.himp
  (ihp : ∀ {t : (Kripke.canonicalModelOf H).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
  (ihq : ∀ {t : (Kripke.canonicalModelOf H).World}, t ⊧ ψ ↔ ψ ∈ t.tableau.1)
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
    . assumption;
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
  (ihp : ∀ {t : (Kripke.canonicalModelOf H).World}, t ⊧ φ ↔ φ ∈ t.tableau.1)
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
    constructor <;> assumption;
  . simp;
    intro ht t' htt';
    apply ihp.not.mpr;
    by_contra hC;
    have : H ⊬ φ ⋏ ∼φ ➝ ⊥ := by simpa using t'.consistent (Γ := [φ, ∼φ]) (Δ := []) (by aesop) (by simp);
    have : H ⊢! φ ⋏ ∼φ ➝ ⊥ := intro_bot_of_and!;
    contradiction;

lemma truthlemma : t ⊧ φ ↔ φ ∈ t.tableau.1 := by
  induction φ using Formula.rec' generalizing t with
  | hatom => tauto;
  | himp φ ψ ihp ihq => exact truthlemma.himp ihp ihq
  | hneg φ ihp => exact truthlemma.hneg ihp;
  | _ => simp [Satisfies.iff_models, Satisfies, *];

end truthlemma

lemma deducible_of_validOnCanonicelModel : (Kripke.canonicalModelOf H) ⊧ φ ↔ H ⊢! φ := by
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

lemma complete_of_canonical (hC : (Kripke.canonicalFrameOf H) ∈ C) : C ⊧ φ → H ⊢! φ := by
  intro h;
  apply deducible_of_validOnCanonicelModel.mp;
  apply h;
  exact hC;

instance instCompleteOfCanonical (hC : (Kripke.canonicalFrameOf H) ∈ C) : Complete H C := ⟨complete_of_canonical hC⟩

end lemmata

end Kripke


section completeness


set_option pp.universes true

instance Int.Kripke.complete : Complete (Hilbert.Int ℕ) (AllFrameClass.{0}) :=
  Hilbert.Kripke.instCompleteOfCanonical (H := Hilbert.Int ℕ) (C := AllFrameClass.{0}) (by simp)

instance KC.Kripke.complete : Complete (Hilbert.KC ℕ) (ConfluentFrameClass.{0}) :=
  Hilbert.Kripke.instCompleteOfCanonical (H := Hilbert.KC ℕ) (C := ConfluentFrameClass.{0}) $ by
    apply Kripke.canonicalFrame.is_confluent;

instance LC.Kripke.complete : Complete (Hilbert.LC ℕ) (ConnectedFrameClass.{0}) :=
  Hilbert.Kripke.instCompleteOfCanonical (H := Hilbert.LC ℕ) (C := ConnectedFrameClass.{0}) $ by
    apply Kripke.canonicalFrame.is_connected;

end completeness

end Hilbert

end LO.IntProp
