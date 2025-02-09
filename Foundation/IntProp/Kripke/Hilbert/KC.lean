import Foundation.IntProp.Hilbert.WellKnown
import Foundation.IntProp.Kripke.Hilbert.Soundness
import Foundation.IntProp.Kripke.Completeness

namespace LO.IntProp

open Kripke
open Formula.Kripke

abbrev Kripke.ConfluentFrameClass : FrameClass := { F | Confluent F }

instance : Kripke.ConfluentFrameClass.DefinedByFormula (Axioms.WeakLEM (.atom 0)) := ⟨by
  rintro F;
  constructor;
  . rintro h φ ⟨_, rfl⟩;
    apply ValidOnFrame.wlem;
    exact h;
  . rintro h x y z ⟨Rxy, Ryz⟩;
    let V : Kripke.Valuation F := ⟨λ {v a} => y ≺ v, by
      intro w v Rwv a Ryw;
      exact F.rel_trans Ryw Rwv;
    ⟩;
    replace h : F ⊧ (Axioms.WeakLEM (.atom 0)) := by simpa using h;
    have : ¬Satisfies ⟨F, V⟩ x (∼(.atom 0)) := by
      simp [Satisfies];
      use y;
      constructor;
      . exact Rxy;
      . apply F.rel_refl;
    have : Satisfies ⟨F, V⟩ x (∼∼(.atom 0)) := by
      apply or_iff_not_imp_left.mp $ Satisfies.or_def.mp $ @h V x;
      assumption;
    obtain ⟨w, Rzw, hw⟩ := by simpa [Satisfies] using @this z Ryz;
    use w;
⟩

instance : Kripke.ConfluentFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Confluent];
⟩



namespace Hilbert.KC.Kripke

instance : ConfluentFrameClass.DefinedBy (Hilbert.KC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.KC ConfluentFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.KC := Kripke.Hilbert.consistent_of_FrameClass ConfluentFrameClass

open
  System
  System.FiniteContext
  Classical
  SaturatedConsistentTableau
in
instance canonical : Canonical Hilbert.KC ConfluentFrameClass := by
  constructor;
  simp [Confluent];
  intro x y z Rxy Rxz;
  suffices Tableau.Consistent (Hilbert.KC) (y.1.1 ∪ z.1.1, ∅) by
    obtain ⟨w, hw⟩ := lindenbaum (𝓢 := Hilbert.KC) this;
    use w;
    simpa using hw;

  intro Γ Δ;
  intro hΓ hΔ h;
  simp_all;
  have := List.eq_nil_iff_forall_not_mem.mpr hΔ; subst this; simp at h; clear hΔ;

  have hΓy : ¬(∀ w, w ∈ Γ → w ∈ y.1.1) := by
    by_contra hC;
    have := by simpa using y.consistent (Γ := Γ) (Δ := []) hC (by simp);
    contradiction;
  push_neg at hΓy;

  have hΓz : ¬(∀ w, w ∈ Γ → w ∈ z.1.1) := by
    by_contra hC;
    have := by simpa using z.consistent (Γ := Γ) (Δ := []) hC (by simp);
    contradiction;
  push_neg at hΓz;

  let Θy := Γ.filter (λ φ => φ ∈ y.1.1 ∧ φ ∉ x.1.1);
  let Θz := Γ.filter (λ φ => φ ∈ z.1.1 ∧ φ ∉ x.1.1);
  let Θx := Γ.filter (λ φ => (φ ∈ y.1.1 ∧ φ ∈ x.1.1) ∨ (φ ∈ z.1.1 ∧ φ ∈ x.1.1));

  suffices ∼⋀Θy ∈ x.1.1 by
    have : ∼⋀Θy ∈ y.1.1 := Rxy this;
    have : ⋀Θy ∈ y.1.1 := iff_mem₁_conj.mpr $ by
      intro φ hp;
      have := by simpa using List.of_mem_filter hp;
      exact this.1;
    have : Hilbert.KC ⊬ ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := y.consistent (Γ := [⋀Θy, ∼⋀Θy]) (Δ := []) (by simp; constructor <;> assumption) (by simp);
    have : Hilbert.KC ⊢! ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := intro_bot_of_and!;
    contradiction;

  have : Hilbert.KC ⊢! (⋀Θx ⋏ (⋀Θy ⋏ ⋀Θz)) ➝ ⊥ := imp_trans''! (by
    -- TODO: need more refactor
    have d₁ : Hilbert.KC ⊢! ⋀Θx ⋏ ⋀(Θy ++ Θz) ➝ ⋀(Θx ++ (Θy ++ Θz)) := and₂'! $ iff_concat_conj!;
    have d₂ : Hilbert.KC ⊢! ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θy ++ Θz) := and₂'! $ iff_concat_conj!;
    have d₃ : Hilbert.KC ⊢! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θx ++ (Θy ++ Θz)) := imp_trans''! (by
      apply deduct'!;
      have : [⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz] ⊢[Hilbert.KC]! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz := FiniteContext.by_axm!;
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
  have : Hilbert.KC ⊢! ⋀Θx ➝ ⋀Θy ➝ ∼⋀Θz := and_imply_iff_imply_imply'!.mp $
    (imp_trans''! (and_imply_iff_imply_imply'!.mp $ imp_trans''! (and₁'! and_assoc!) this) (and₂'! $ neg_equiv!));
  have d : Hilbert.KC ⊢! ⋀Θx ➝ ∼∼⋀Θz ➝ ∼⋀Θy := imp_trans''! this contra₀!;

  have mem_Θx_x : ⋀Θx ∈ x.1.1 := iff_mem₁_conj.mpr $ by
    intro φ hp;
    have := by simpa using List.of_mem_filter hp;
    rcases this with ⟨_, _⟩ | ⟨_, _⟩ <;> assumption;
  have mem_Θz_z : ⋀Θz ∈ z.1.1 := iff_mem₁_conj.mpr $ by
    intro φ hp;
    have := by simpa using List.of_mem_filter hp;
    exact this.1;

  have nmem_nΘz_z : ∼⋀Θz ∉ z.1.1 := not_mem₁_neg_of_mem₁ mem_Θz_z;
  have nmem_nΘz_x : ∼⋀Θz ∉ x.1.1 := Set.not_mem_subset Rxz nmem_nΘz_z;
  have mem_nnΘz_x : ∼∼⋀Θz ∈ x.1.1 := or_iff_not_imp_left.mp (iff_mem₁_or.mp $ mem₁_of_provable $ wlem!) nmem_nΘz_x;

  exact mdp₁_mem mem_nnΘz_x $ mdp₁ mem_Θx_x d;

instance complete : Complete Hilbert.KC ConfluentFrameClass := inferInstance

end Hilbert.KC.Kripke


end LO.IntProp
