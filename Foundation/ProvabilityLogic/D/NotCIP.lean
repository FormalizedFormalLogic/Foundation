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

namespace Logic.D

universe u

variable {α : Type u} {a b c : α} {C : Formula α}

lemma provable_counterexample : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 □(#a 🡒 □#c) 🡒 □#c := by
  have h : 𝐆𝐋 ⊢ □(□#b ⋎ #a) ⋏ □(#a 🡒 □#c) 🡒 □(□#b ⋎ □#c) :=
    C_trans normalOf.box_and (normalOf.box_mono (by cl_prover));
  cl_prover [of_GL h, axiomD (A := #b) (B := #c)];

variable [DecidableEq α]

lemma forces_pseudoTail_interpolant_iff (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a})
    {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop) :
    Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] C ↔ M.Val M.root a := by
  let V x p := if p = a then M.Val x a else x ≠ M.root;
  let N : RootedModel κ α := ⟨M.toModel.overwrite V, M.root, M.root_rel⟩;
  have : N.IsFiniteGL := inferInstanceAs (M.toModel.overwrite V).IsFiniteGL;
  have e : Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] C ↔ Sum.inr ⊤ ⊩[(M.toPseudoTail o).toModel] C := by
    apply forces_congr_of_atoms (by rfl);
    rintro (x | i) p hp <;> obtain rfl := Finset.mem_singleton.mp (hC hp);
    · simp [N, V, Model.overwrite, Model.toFreeTail, Model.Val];
    · by_cases hi : i = ⊤ <;> simp [hi, N, V, Model.overwrite, Model.toFreeTail, Model.Val];
  have hbox : ∀ D, Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] □D ↔
      (∀ x, Sum.inl x ⊩[(N.toPseudoTail o).toModel] D) ∧
        ∀ n : ℕ, Sum.inr (n : ℕ∞) ⊩[(N.toPseudoTail o).toModel] D := by
    intro D;
    constructor;
    · exact fun h ↦ ⟨fun x ↦ h _ trivial, fun n ↦ h _ (toFreeTail.rel_inr_inr.mpr (by simp))⟩;
    · rintro ⟨h₁, h₂⟩ (x | i) R;
      · exact h₁ x;
      · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (toFreeTail.rel_inr_inr.mp R));
        exact h₂ n;
  have h₃ : ∀ x, ∀ p ≠ a, Sum.inl x ⊩[(N.toPseudoTail o).toModel] □#p := by
    rintro x p hp (y | j) R;
    · change V y p;
      simp only [V, hp, ite_false];
      rintro rfl;
      exact RootedModel.not_rel_root R;
    · exact R.elim;
  have h₄ : ∀ i, ∀ p ≠ a, Sum.inr i ⊮[(N.toPseudoTail o).toModel] □#p := by
    intro i p hp h;
    have : V M.root p := h (.inl M.root) trivial;
    simp [V, hp] at this;
  have h₅ : ∀ n : ℕ, Sum.inr (n : ℕ∞) ⊩[(N.toPseudoTail o).toModel] #a ↔ M.Val M.root a := by
    intro n;
    change (if (n : ℕ∞) = ⊤ then o else V M.root) a ↔ M.Val M.root a;
    simp [V];
  have hA : Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] ∼(□(□#b ⋎ #a) 🡒 □#b) ↔ M.Val M.root a := by
    simp [forces_neg, forces_imp, forces_or, hbox (□#b ⋎ #a), h₄ ⊤ b hab.symm, h₄ _ b hab.symm,
      h₃ _ b hab.symm, h₅];
  have hB : Sum.inr ⊤ ⊩[(N.toPseudoTail o).toModel] □(#a 🡒 □#c) 🡒 □#c ↔ M.Val M.root a := by
    simp [forces_imp, hbox (#a 🡒 □#c), h₄ ⊤ c hac.symm, h₄ _ c hac.symm, h₃ _ c hac.symm, h₅];
  have h₁ := iff_forces_pseudoTail.mp h₁ N o;
  have h₂ := iff_forces_pseudoTail.mp h₂ N o;
  exact ⟨fun h ↦ hB.mp (h₂ (e.mpr h)), fun h ↦ e.mp (h₁ (hA.mpr h))⟩;

lemma S_modalize_iff_of_interpolant (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : 𝐃 ⊢ ∼(□(□#b ⋎ #a) 🡒 □#b) 🡒 C) (h₂ : 𝐃 ⊢ C 🡒 □(#a 🡒 □#c) 🡒 □#c) (hC : C.atoms ⊆ {a}) :
    𝐒 ⊢ C.modalize 🡘 #a := by
  apply (S.provability_TFAE.out 1 5).mpr;
  intro κ _ M _ hΓ;
  set X := (C.modalize 🡘 #a).subfmls;
  have hroot : ∀ B, □B ∈ X → M.root ⊩[M.toModel] □B 🡒 B :=
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

lemma _root_.FFL.ProvabilityLogic.Logic.S.not_iff_atom (hab : a ≠ b) (hC : C.ModalizedIn a)
    (hb : b ∉ C.atoms) : 𝐒 ⊬ C 🡘 #a := by
  intro h;
  obtain ⟨E, -, hE⟩ := Logic.GL.exists_fixpoint (A := ∼C) hab ⟨hC, trivial⟩ (by simpa using hb);
  have h₁ : 𝐒 ⊢ (C 🡘 #a)⟦.single a E⟧ := sumQuasiNormal.subst h;
  have h₂ : 𝐒 ⊢ ∼C⟦a ↦ E⟧ 🡘 E := S.of_GL hE;
  simp only [subst_iff, subst_atom, Substitution.single_apply, ite_true] at h₁;
  exact S.consistent (by cl_prover [h₁, h₂]);

/-- **`𝐃` does not have the Craig interpolation property.**

- [Bek89, Theorem 2] -/
theorem not_CIP (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∀ A B : Formula α, 𝐃 ⊢ A 🡒 B →
      ∃ C, 𝐃 ⊢ A 🡒 C ∧ 𝐃 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  intro h;
  obtain ⟨C, h₁, h₂, hC⟩ := h _ _ (provable_counterexample (a := a) (b := b) (c := c));
  have hC : C.atoms ⊆ {a} := hC.trans (by intro; simp; grind);
  exact S.not_iff_atom hab modalizedIn_modalize
    (fun h ↦ hab (Finset.mem_singleton.mp (hC (atoms_modalize_subset h))).symm)
    (S_modalize_iff_of_interpolant hab hac h₁ h₂ hC);

end Logic.D

end FFL.ProvabilityLogic

end
