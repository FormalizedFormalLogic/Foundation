module

public import Foundation.ProvabilityLogic.S.Basic
public import Foundation.ProvabilityLogic.D.Gentzen.Kripke

/-!
# The logic `D`

## References

- [KKIM25]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

abbrev Logic.D {α : Type*} : Logic α := 𝐆𝐋 +ᴸ insert (∼□⊥) { □(□A ⋎ □B) 🡒 □A ⋎ □B | (A) (B) }

notation "𝐃" => Logic.D

/-- The instances `□(□B₁ ⋎ ⋯ ⋎ □Bₙ) 🡒 □B₁ ⋎ ⋯ ⋎ □Bₙ` of axiom `D` for subformulas `□Bᵢ` of `A`. -/
noncomputable def Formula.dSubfmls {α : Type*} [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  A.subfmls.prebox.powerset.image fun Γ : FormulaFinset α ↦ □Γ.box.disj 🡒 Γ.box.disj

namespace Logic.D

variable {α : Type*} {A B : Formula α}

lemma of_GL (h : 𝐆𝐋 ⊢ A) : 𝐃 ⊢ A := sumQuasiNormal.of_left h

lemma axiomP : 𝐃 ⊢ ∼□(⊥ : Formula α) := sumQuasiNormal.mem₂ (Set.mem_insert _ _)

lemma axiomD : 𝐃 ⊢ □(□A ⋎ □B) 🡒 □A ⋎ □B := sumQuasiNormal.mem₂ (Set.mem_insert_of_mem _ ⟨A, B, rfl⟩)

instance : (𝐃 : Logic α) ⪯ 𝐒 := by
  apply Logic.weakerThan_iff.mpr;
  intro A h;
  induction h with
  | mem₁ h => exact S.of_GL h;
  | mem₂ h => rcases h with rfl | ⟨A, B, rfl⟩ <;> exact S.axiomT;
  | mdp _ _ ih₁ ih₂ => exact sumQuasiNormal.mdp ih₁ ih₂;
  | subst _ ih => exact sumQuasiNormal.subst ih;

instance : Consistent (𝐃 : Logic α) := .of_le (𝓢 := 𝐒) inferInstance inferInstance

/-- - [KKIM25, Theorem 5.8] -/
lemma sound_freeTail (h : 𝐃 ⊢ A) {κ : Type*} [Nonempty κ] (M : Model κ α) [M.IsGL]
    (V : ℕ∞ → α → Prop) : Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] A := by
  induction h generalizing κ V with
  | mem₁ h => exact GL.sound _ h _;
  | mem₂ h =>
    rcases h with rfl | ⟨B, C, rfl⟩;
    · exact fun h ↦ h (.inr 0) (toFreeTail.rel_inr_inr.mpr (by simp));
    · intro h;
      by_contra hBC;
      obtain ⟨hB, hC⟩ := not_or.mp (forces_or.not.mp hBC);
      obtain ⟨x, Rx, hx⟩ := not_forces_box.mp hB;
      obtain ⟨y, Ry, hy⟩ := not_forces_box.mp hC;
      obtain ⟨k₁, hk₁⟩ := toFreeTail.eventually_rel Rx;
      obtain ⟨k₂, hk₂⟩ := toFreeTail.eventually_rel Ry;
      rcases forces_or.mp (h (.inr (max k₁ k₂ : ℕ)) (toFreeTail.rel_inr_inr.mpr (by simp)))
        with h | h;
      · exact hx (h x (hk₁ _ (le_max_left _ _)));
      · exact hy (h y (hk₂ _ (le_max_right _ _)));
  | mdp _ _ ih₁ ih₂ => exact ih₁ M V (ih₂ M V);
  | @subst A s _ ih =>
    apply forces_subst.mp;
    apply (forces_congr (M := ((M.subst s).toFreeTail fun i a ↦
      Sum.inr i ⊩[(M.toFreeTail V).toModel] s a).toModel) _ _).mp (ih (M.subst s) _);
    · funext x y;
      rcases x <;> rcases y <;> rfl;
    · rintro (x | i) a;
      · exact toFreeTail.forces_inl.symm;
      · rfl;

lemma not_axiomT {a : α} : 𝐃 ⊬ □#a 🡒 #a := fun h ↦
  sound_freeTail h (pointModel fun _ ↦ True) (fun i _ ↦ i ≠ ⊤)
    (by rintro (_ | i) R; exacts [trivial, ne_top_of_lt R]) rfl

instance : (𝐆𝐋 : Logic α) ⪱ 𝐃 :=
  .of_unprovable_provable (φ := ∼□⊥)
    (fun h ↦ GL.sound (pointModel fun _ ↦ True) h 0 fun _ h ↦ h.elim) axiomP

instance [Inhabited α] : (𝐃 : Logic α) ⪱ 𝐒 :=
  .of_unprovable_provable (not_axiomT (a := default)) S.axiomT

variable [DecidableEq α]

/-- The `n`-ary form of axiom `D`. -/
lemma axiomD_disj {Γ : FormulaFinset α} : 𝐃 ⊢ □Γ.box.disj 🡒 Γ.box.disj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : (FormulaFinset.box (∅ : FormulaFinset α)).disj = ⊥ := by simp [Finset.disj];
    rw [this];
    exact axiomP;
  | insert A Γ _ ih =>
    set Φ := (FormulaFinset.box Γ).disj;
    set Ψ := (FormulaFinset.box (insert A Γ)).disj;
    have h₁ : 𝐆𝐋 ⊢ Φ 🡒 □Φ := left_Fdisj_intro _ fun C hC ↦ by
      obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hC;
      exact C_trans GL.axiom4 (normalOf.box_mono (right_Fdisj_intro _ hC));
    have h₂ : 𝐆𝐋 ⊢ Ψ 🡒 □A ⋎ Φ := by simp [Ψ, Φ, Finset.image_insert];
    have h₃ : 𝐆𝐋 ⊢ □A ⋎ Φ 🡒 Ψ := by simp [Ψ, Φ, Finset.image_insert];
    have h₄ : 𝐆𝐋 ⊢ □Ψ 🡒 □(□A ⋎ □Φ) := normalOf.box_mono (by cl_prover [h₁, h₂]);
    have h₅ : 𝐆𝐋 ⊢ (□(□A ⋎ □Φ) 🡒 □A ⋎ □Φ) 🡒 (□Φ 🡒 Φ) 🡒 □Ψ 🡒 Ψ := by cl_prover [h₃, h₄];
    exact of_GL h₅ ⨀ axiomD ⨀ ih;

omit [DecidableEq α] in
lemma provable_TBB {n : ℕ} : 𝐃 ⊢ Formula.TBB n (α := α) := by
  classical
  cases n with
  | zero => exact axiomP;
  | succ n => simpa [Formula.TBB] using axiomD_disj (Γ := {□^[n]⊥});

open Classical in
/-- - [KKIM25, Proposition 3.6] -/
lemma root_forces_of_forces_pseudoTail {κ : Type*} [Nonempty κ] {M : RootedModel κ α} [M.IsFiniteGL]
    (h : ∀ x, M.root ≺ x → Sum.inr ⊤ ⊩[((M.toModel.cone x).toPseudoTail (M M.root)).toModel] A)
    (hΓ : M.root ⊩[M.toModel] A.dSubfmls.conj) : M.root ⊩[M.toModel] A := by
  let Δ := A.subfmls.prebox.filter fun B ↦ ¬M.root ⊩ □B;
  obtain ⟨x, Rx, hx⟩ : ∃ x, M.root ≺ x ∧ ∀ B ∈ Δ, ¬x ⊩ □B := by
    have h₁ := forces_conj.mp hΓ _ (Finset.mem_image.mpr
      ⟨Δ, Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩);
    have h₂ : ¬M.root ⊩ (FormulaFinset.box Δ).disj := by
      simp only [forces_disj, Finset.mem_image];
      rintro ⟨_, ⟨B, hB, rfl⟩, h⟩;
      exact (Finset.mem_filter.mp hB).2 h;
    obtain ⟨x, Rx, hx⟩ := not_forces_box.mp fun h ↦ h₂ (h₁ h);
    exact ⟨x, Rx, fun B hB h ↦ hx (forces_disj.mpr ⟨□B, Finset.mem_image_of_mem _ hB, h⟩)⟩;
  have hbox : ∀ B, □B ∈ A.subfmls → (x ⊩ □B ↔ M.root ⊩ □B) := by
    intro B hB;
    constructor;
    · intro h;
      by_contra hr;
      exact hx B (Finset.mem_filter.mpr ⟨FormulaFinset.mem_prebox.mpr hB, hr⟩) h;
    · exact fun h y Rxy ↦ h y (IsTrans.trans _ _ _ Rx Rxy);
  have hrefl : ∀ B, □B ∈ A.subfmls →
      (M.toModel.cone x).root ⊩ □B 🡒 B := by
    intro B hB h;
    exact forces_cone.mpr ((hbox B hB).mp (forces_cone.mp h) x Rx);
  have key : ∀ B ∈ A.subfmls,
      Sum.inr ⊤ ⊩[((M.toModel.cone x).toPseudoTail (M M.root)).toModel] B ↔
        M.root ⊩[M.toModel] B := by
    intro B hB;
    induction B with
    | atom | falsum => rfl;
    | imp B C ihB ihC =>
      exact imp_congr (ihB (Formula.subfmls_trans hB (by grind)))
        (ihC (Formula.subfmls_trans hB (by grind)));
    | box B _ =>
      constructor;
      · intro h;
        apply (hbox B hB).mp;
        exact forces_cone.mp <| toFreeTail.forces_inl.mp <|
          toFreeTail.forces_box_of_root h (.inl ⟨x, .inl rfl⟩);
      · rintro h (⟨y, rfl | Rxy⟩ | j) R;
        · exact toFreeTail.forces_inl.mpr <| forces_cone.mpr <| h y Rx;
        · exact toFreeTail.forces_inl.mpr <| forces_cone.mpr <| h y (IsTrans.trans _ _ _ Rx Rxy);
        · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (toFreeTail.rel_inr_inr.mp R));
          apply (toFreeTail.forces_inr_iff (fun n ↦ by simp) (fun _ hC ↦ Formula.subfmls_trans hC)
            hrefl (Formula.subfmls_trans hB (by grind)) m).mpr;
          exact forces_cone.mpr (h x Rx);
  exact (key A Formula.mem_subfmls_self).mp (h x Rx);

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

/-- - [KKIM25, Proposition 3.6, Theorem 5.8] -/
theorem provability_TFAE : [
    𝐃 ⊢ A,
    ⊢ᴳ[𝐃] ∅ ⟹[2] {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] (V : ℕ∞ → α → Prop),
      Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop),
      Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL],
      M.root ⊩[M.toModel] A.dSubfmls.conj 🡒 A,
    𝐆𝐋 ⊢ A.dSubfmls.conj 🡒 A
  ].TFAE := by
  tfae_have 1 → 3 := fun h _ _ M _ V ↦ sound_freeTail h M V;
  tfae_have 2 ↔ 3 := by
    have h : ∀ {κ : Type u} [Nonempty κ] {M : Model κ α} {x : M.World},
        x ⊩ (∅ ⟹ {A}) ↔ x ⊩ A := by simp [ForcesSequent];
    have e : ⊢ᴳ[𝐃] ∅ ⟹[2] {A} ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsGL] V,
        Sum.inr ⊤ ⊩[(M.toFreeTail V).toModel] (∅ ⟹ {A}) := D.Gentzen.TFAE.out 1 2;
    rw [e];
    constructor;
    · intro h' _ _ M _ V;
      exact h.mp (h' M V);
    · intro h' _ _ M _ V;
      exact h.mpr (h' M V);
  tfae_have 3 → 4 := fun h _ _ M _ _ ↦ h M.toModel _;
  tfae_have 4 → 5 := fun h _ _ M _ ↦ root_forces_of_forces_pseudoTail fun x _ ↦ h _ _;
  tfae_have 5 ↔ 6 := GL.iff_root_forces.symm;
  tfae_have 6 → 1 := GL.sumQuasiNormal_of_conj fun B hB ↦ by
    obtain ⟨Γ, -, rfl⟩ := Finset.mem_image.mp hB;
    exact axiomD_disj;
  tfae_finish;

lemma iff_provable_gentzen : 𝐃 ⊢ A ↔ ⊢ᴳ[𝐃] ∅ ⟹[2] {A} := provability_TFAE.out 1 2

omit [DecidableEq α] in
lemma iff_forces_pseudoTail : 𝐃 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop),
      Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] A := by
  classical
  exact provability_TFAE.out 1 4

lemma iff_provable_GL : 𝐃 ⊢ A ↔ 𝐆𝐋 ⊢ A.dSubfmls.conj 🡒 A := provability_TFAE.out 1 6

omit [DecidableEq α] in
lemma iff_box_provable_GL : 𝐃 ⊢ □A ↔ 𝐆𝐋 ⊢ A := by
  constructor;
  · intro h;
    exact GL.iff_valid_finite.mpr fun M _ x ↦
      toFreeTail.forces_inl.mp (sound_freeTail h M (fun _ _ ↦ True) (.inl x) trivial);
  · exact fun h ↦ of_GL (normalOf.nec h);
end Logic.D

end FFL.ProvabilityLogic

end
