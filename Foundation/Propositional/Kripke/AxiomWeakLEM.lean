import Foundation.Propositional.Kripke.Completeness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_WeakLEM_of_confluent : Confluent F → F ⊧ (Axioms.WeakLEM (.atom 0)) := by
  unfold Confluent Axioms.WeakLEM;
  contrapose;
  push_neg;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  unfold Satisfies at h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := Satisfies.neg_def.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, hy⟩ := h₁;

  replace h₂ := Satisfies.neg_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, hz⟩ := h₂;

  use x, y, z;
  constructor;
  . constructor <;> assumption;
  . intro u Ryu;
    by_contra Rzu;
    exact (Satisfies.neg_def.mp hz) Rzu $ Satisfies.formula_hereditary Ryu hy;

lemma confluent_of_validate_WeakLEM : F ⊧ (Axioms.WeakLEM (.atom 0)) → Confluent F := by
  rintro h x y z ⟨Rxy, Ryz⟩;
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

protected abbrev FrameClass.confluent : FrameClass := { F | Confluent F }

instance FrameClass.confluent.definability : FrameClass.confluent.DefinedBy {Axioms.WeakLEM (.atom 0)} := ⟨by
  intro F;
  constructor;
  . simpa using validate_WeakLEM_of_confluent;
  . simpa using confluent_of_validate_WeakLEM;
⟩

@[simp]
instance FrameClass.confluent.nonempty : FrameClass.confluent.Nonempty := by
  use pointFrame;
  simp [Confluent];

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

namespace Canonical

protected lemma confluent [Entailment.HasAxiomWeakLEM 𝓢] : Confluent (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  suffices Tableau.Consistent 𝓢 (y.1.1 ∪ z.1.1, ∅) by
    obtain ⟨w, hw⟩ := lindenbaum (𝓢 := 𝓢) this;
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
    have : 𝓢 ⊬ ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := y.consistent (Γ := [⋀Θy, ∼⋀Θy]) (Δ := []) (by simp; constructor <;> assumption) (by simp);
    have : 𝓢 ⊢! ⋀Θy ⋏ ∼⋀Θy ➝ ⊥ := intro_bot_of_and!;
    contradiction;

  have : 𝓢 ⊢! (⋀Θx ⋏ (⋀Θy ⋏ ⋀Θz)) ➝ ⊥ := imp_trans''! (by
    -- TODO: need more refactor
    have d₁ : 𝓢 ⊢! ⋀Θx ⋏ ⋀(Θy ++ Θz) ➝ ⋀(Θx ++ (Θy ++ Θz)) := and₂'! $ iff_concat_conj!;
    have d₂ : 𝓢 ⊢! ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θy ++ Θz) := and₂'! $ iff_concat_conj!;
    have d₃ : 𝓢 ⊢! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz ➝ ⋀(Θx ++ (Θy ++ Θz)) := imp_trans''! (by
      apply deduct'!;
      have : [⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz] ⊢[𝓢]! ⋀Θx ⋏ ⋀Θy ⋏ ⋀Θz := FiniteContext.by_axm!;
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
  have : 𝓢 ⊢! ⋀Θx ➝ ⋀Θy ➝ ∼⋀Θz := and_imply_iff_imply_imply'!.mp $
    (imp_trans''! (and_imply_iff_imply_imply'!.mp $ imp_trans''! (and₁'! and_assoc!) this) (and₂'! $ neg_equiv!));
  have d : 𝓢 ⊢! ⋀Θx ➝ ∼∼⋀Θz ➝ ∼⋀Θy := imp_trans''! this contra₀!;

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

  exact mdp₁_mem mem_nnΘz_x $ mdp_mem₁_provable d mem_Θx_x;

end Canonical

end canonicality

end Kripke

end LO.Propositional
