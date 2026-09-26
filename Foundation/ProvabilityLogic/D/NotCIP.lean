module

public import Foundation.ProvabilityLogic.D.Basic
public import Foundation.ProvabilityLogic.GL.Fixedpoint

/-!
# `D` does not have the Craig interpolation property

`𝐃 ⊢ ∼(□(□b ⋎ a) 🡒 □b) 🡒 □(a 🡒 □c) 🡒 □c`, but no formula in the sole shared atom `a`
interpolates it.

## References

- [Bek89, Section 8]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

universe u

variable {α : Type u} {a b c : α} {C : Formula α}

namespace Logic.D

variable [DecidableEq α]

lemma forces_pseudoTail_interpolant_iff (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a})
    {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop) :
    Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] C ↔ M M.root a := by
  let V x p := if p = a then M x a else x ≠ M.root;
  let N : RootedModel κ α := ⟨M.toModel.overwrite V, M.root, M.root_rel⟩;
  have : N.IsFiniteGL := Model.overwrite.isFiniteGL (M := M.toModel);
  have e : Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] C ↔
      Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] C := by
    apply forces_congr_of_atoms (by rfl);
    rintro (x | i) p hp <;> obtain rfl := Finset.mem_singleton.mp (hC hp) <;>
      simp [N, V, Model.overwrite, Model.toFreeTail, Model.Val];
    split_ifs <;> simp;
  have h₃ : ∀ x, ∀ p ≠ a, x ⊩[N.toModel] □#p := fun x p hp y R ↦ by
    simpa [N, V, Model.overwrite, Model.Val, hp] using fun h ↦ RootedModel.not_rel_root (h ▸ R);
  have h₄ : ∀ i, ∀ p ≠ a, Sum.inr i ⊮[(N.toPseudoTail o).toModel] □#p := fun i p hp h ↦
    (show ¬V M.root p by simp [V, hp]) <| h (.inl M.root) trivial;
  have h₅ : ∀ n : ℕ, Sum.inr (n : ℕ∞) ⊩[(N.toPseudoTail o).toModel] #a ↔ M M.root a := by
    simp [N, V, Model.overwrite, Model.toFreeTail, Model.Val];
  have hA : Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] ∼(□(□#b ⋎ #a) 🡒 □#b) ↔ M M.root a := by
    simp [forces_neg, forces_imp, forces_or, toFreeTail.forces_root_box_iff (A := □#b ⋎ #a),
      h₄ _ b hab.symm, h₃ _ b hab.symm, h₅];
  have hB : Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] □(#a 🡒 □#c) 🡒 □#c ↔ M M.root a := by
    simp [forces_imp, toFreeTail.forces_root_box_iff (A := #a 🡒 □#c), h₄ _ c hac.symm,
      h₃ _ c hac.symm, h₅];
  exact e.trans ⟨fun h ↦ hB.mp <| iff_forces_pseudoTail.mp h₂ N o h,
    fun h ↦ iff_forces_pseudoTail.mp h₁ N o <| hA.mpr h⟩;

lemma S_modalize_iff_of_interpolant (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a}) :
    𝐒 ⊢ C.modalize 🡘 #a := by
  apply (S.provability_TFAE.out 1 5).mpr;
  intro κ _ M _ hΓ;
  set X := (C.modalize 🡘 #a).subfmls;
  have hroot : ∀ B, □B ∈ X → M.root ⊩ □B 🡒 B :=
    fun B hB ↦ forces_conj.mp hΓ _ (Finset.mem_image.mpr ⟨B, FormulaFinset.mem_prebox.mpr hB, rfl⟩);
  have key : ∀ D : Formula α, D.modalize ∈ X →
      (Sum.inr ⊤ ⊩[(M.toPseudoTail fun _ ↦ False).toModel] D ↔ M.root ⊩[M.toModel] D.modalize) := by
    intro D hD;
    induction D with
    | atom | falsum => exact iff_of_false id id;
    | imp A B ihA ihB =>
      exact imp_congr (ihA (subfmls_trans hD mem_subfmls_imp_left))
        (ihB (subfmls_trans hD mem_subfmls_imp_right));
    | box A =>
      exact toFreeTail.forces_inr_box_iff (toFreeTail.forces_inr_iff (fun n ↦ by simp)
        (fun _ h ↦ subfmls_trans h) hroot (subfmls_trans hD mem_subfmls_box)) (hroot A hD) ⊤;
  exact forces_iff.mpr <| (key C (by simp [X, subfmls])).symm.trans <|
    forces_pseudoTail_interpolant_iff hab hac h₁ h₂ hC M _;

/-- **`𝐃` does not have the Craig interpolation property.**

- [Bek89, Theorem 2] -/
theorem not_CIP (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∀ A B : Formula α, 𝐃 ⊢ A 🡒 B →
      ∃ C, 𝐃 ⊢ A 🡒 C ∧ 𝐃 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  by_contra! h;
  have : 𝐆𝐋 ⊢ □(□#b ⋎ #a) ⋏ □(#a 🡒 □#c) 🡒 □(□#b ⋎ □#c) :=
    C_trans normalOf.box_and (normalOf.box_mono (by cl_prover));
  obtain ⟨C, h₁, h₂, hC⟩ := h (∼(□(□#b ⋎ #a) 🡒 □#b)) (□(#a 🡒 □#c) 🡒 □#c)
    (by cl_prover [of_GL this, axiomD (A := #b) (B := #c)]);
  replace hC : C.atoms ⊆ {a} := hC.trans (by intro; simp; grind);
  have hb : b ∉ C.modalize.atoms := fun h ↦ by
    simpa [hab.symm] using hC <| atoms_modalize_subset h;
  obtain ⟨E, -, hE⟩ := GL.exists_fixpoint (A := ∼C.modalize) hab ⟨modalizedIn_modalize, trivial⟩
    (by simpa using hb);
  have : 𝐒 ⊢ C.modalize⟦a ↦ E⟧ 🡘 E := by
    simpa only [subst_iff, subst_atom, Substitution.single_apply, ite_true] using
      show 𝐒 ⊢ (C.modalize 🡘 #a)⟦a ↦ E⟧ from
        sumQuasiNormal.subst (S_modalize_iff_of_interpolant hab hac h₁ h₂ hC);
  exact unprovable_bot (L := 𝐒) <|
    by cl_prover [this, (S.of_GL hE : 𝐒 ⊢ ∼C.modalize⟦a ↦ E⟧ 🡘 E)];

end Logic.D

end FFL.ProvabilityLogic

end
