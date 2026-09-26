module

public import Foundation.ProvabilityLogic.GL.Gentzen.Basic
public import Foundation.ProvabilityLogic.Kripke.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Finite.Prod

/-!
# Kripke completeness of the sequent calculus of `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

/-! ### Soundness -/

namespace Kripke

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {M : Model κ α}
         {Γ Δ : FormulaFinset α} {A B : Formula α}

@[grind →]
lemma Model.validateSequent_boxGL [M.IsGL] (h : M ⊧ (insert (□A) (Γ ∪ Γ.box) ⟹ {A})) :
    M ⊧ (Γ.box ⟹ {□A}) := by
  apply validateSequent_singleton_iff.mpr;
  intro x hx;
  have hΓ : ∀ C ∈ Γ, x ⊩ □C := fun C hC ↦ hx _ (Finset.mem_image_of_mem _ hC);
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮ A} ⟨y, Rxy, hy⟩;
  apply ht;
  apply validateSequent_singleton_iff.mp h t;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image];
  rintro C (rfl | hC | ⟨C, hC, rfl⟩);
  · intro z Rtz;
    by_contra hz;
    exact tmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz;
  · exact hΓ C hC t Rxt;
  · intro z Rtz;
    exact hΓ C hC z (IsTrans.trans _ _ _ Rxt Rtz);

end Kripke

namespace GL.Gentzen

variable {α : Type*} [DecidableEq α] {S : Sequent α}

theorem sound {κ : Type*} [Nonempty κ] (M : Kripke.Model κ α) [M.IsGL] (h : ⊢ᴳ[𝐆𝐋] S) :
    M ⊧ S := by
  induction h <;> grind;

@[simp, grind .]
lemma not_empty : ⊬ᴳ[𝐆𝐋] (∅ ⟹ ∅ : Sequent α) := by
  intro h;
  simpa [Model.ValidateSequent, Model.World.ForcesSequent]
    using sound (Kripke.Model.pointModel (α := α) fun _ ↦ False) h 0;

end GL.Gentzen

/-! ### Completeness -/

namespace GL

variable {α : Type*} [DecidableEq α]

/-- The worlds of the canonical countermodel of `BS`. -/
structure SaturatedSequent (BS : Sequent α) extends Sequent α where
  saturated : toSequent.Saturated
  subset_subfmls : ant ∪ suc ⊆ BS.subfmls
  unprovable : ⊬ᴳ[𝐆𝐋] toSequent

namespace SaturatedSequent

variable {BS : Sequent α} {S : SaturatedSequent BS} {A B : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ S.ant ∧ A ∈ S.suc) := fun h ↦ S.unprovable (Gentzen.union' _ h.1 h.2)

@[grind .]
lemma bot_not_mem_ant : ⊥ ∉ S.ant := fun h ↦ S.unprovable (Gentzen.botL_mem h)

lemma ext {S T : SaturatedSequent BS} (ha : S.ant = T.ant) (hs : S.suc = T.suc) : S = T := by
  obtain ⟨⟨_, _⟩, _⟩ := S;
  obtain ⟨⟨_, _⟩, _⟩ := T;
  grind;

instance : Finite (SaturatedSequent BS) :=
  Finite.of_injective
    (β := BS.subfmls.powerset × BS.subfmls.powerset)
    (fun S ↦ (⟨S.ant, Finset.mem_powerset.mpr (by grind [S.subset_subfmls])⟩,
              ⟨S.suc, Finset.mem_powerset.mpr (by grind [S.subset_subfmls])⟩))
    (fun S T h ↦ by simp only [Prod.mk.injEq, Subtype.mk.injEq] at h; exact ext h.1 h.2)

/-- The Lindenbaum lemma. -/
lemma lindenbaum {S₀ : Sequent α} (h₀ : ⊬ᴳ[𝐆𝐋] S₀) (hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls) :
    ∃ S : SaturatedSequent BS, S₀ ⊆ S.toSequent := by
  obtain ⟨S, h₁, h₂, h₃, h₄, -⟩ := Sequent.exists_saturated
    ⟨fun h₁ h₂ ↦ Gentzen.union' _ h₁ h₂, Gentzen.impL, Gentzen.impR⟩ h₀ hS₀;
  exact ⟨⟨S, h₃, h₄, h₂⟩, h₁⟩

instance [Fact (⊬ᴳ[𝐆𝐋] BS)] : Nonempty (SaturatedSequent BS) :=
  (lindenbaum (BS := BS) (S₀ := BS) Fact.out (by grind)).nonempty

end SaturatedSequent

open SaturatedSequent

def countermodel (BS : Sequent α) [Fact (⊬ᴳ[𝐆𝐋] BS)] : Kripke.Model (SaturatedSequent BS) α where
  Val' x a := #a ∈ x.ant
  Rel' x y := x.ant.prebox ⊂ y.ant.prebox ∧ x.ant.prebox ⊆ y.ant

namespace countermodel

variable {BS : Sequent α} [Fact (⊬ᴳ[𝐆𝐋] BS)] {x : (countermodel BS).World} {A : Formula α}

instance : (countermodel BS).IsFiniteGL where
  trans x y z Rxy Ryz := by
    obtain ⟨h₁, h₂⟩ := Rxy;
    obtain ⟨h₃, h₄⟩ := Ryz;
    exact ⟨h₁.trans h₃, h₁.subset.trans h₄⟩;
  irrefl x h := h.1.ne rfl

lemma truthlemma : (A ∈ x.ant → x ⊩ A) ∧ (A ∈ x.suc → x ⊮ A) := by
  induction A generalizing x with
  | atom a => exact ⟨id, fun h hf ↦ not_mem_both ⟨hf, h⟩⟩;
  | falsum => exact ⟨fun h ↦ absurd h bot_not_mem_ant, fun _ ↦ id⟩;
  | imp A B ihA ihB =>
    constructor;
    · intro h hA;
      rcases x.saturated.impL h with hA' | hB;
      · exact absurd hA (ihA.2 hA');
      · exact ihB.1 hB;
    · intro h hf;
      obtain ⟨hA, hB⟩ := x.saturated.impR h;
      exact ihB.2 hB (hf (ihA.1 hA));
  | box A ih =>
    constructor;
    · intro h y Rxy;
      exact ih.1 <| Rxy.2 (by simpa);
    · intro h;
      apply not_forces_box.mpr;
      have h₀ : ⊬ᴳ[𝐆𝐋] insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A} := fun hp ↦
        x.unprovable <|
          Gentzen.wk (Gentzen.boxGL hp) FormulaFinset.box_prebox_subset (by simpa using h);
      have hS₀ : (insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A}).ant ∪
          (insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A}).suc ⊆ BS.subfmls := by
        have hx := x.subset_subfmls;
        have hbox : □A ∈ BS.subfmls := hx (Finset.mem_union_right _ h);
        intro B;
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          FormulaFinset.mem_prebox, Finset.mem_image];
        rintro ((rfl | hB | ⟨B, hB, rfl⟩) | rfl);
        · exact hbox;
        · exact Sequent.mem_subfmls_subfmls (hx (Finset.mem_union_left _ hB))
            Formula.mem_subfmls_box;
        · exact hx (Finset.mem_union_left _ hB);
        · exact Sequent.mem_subfmls_subfmls hbox Formula.mem_subfmls_box;
      obtain ⟨y, hy⟩ := lindenbaum h₀ hS₀;
      use y;
      and_intros;
      · intro B hB;
        exact FormulaFinset.mem_prebox.mpr <| hy.ant <|
          Finset.mem_insert_of_mem <| Finset.mem_union_right _ <| Finset.mem_image_of_mem _ hB;
      · intro hsub;
        have : A ∈ y.ant.prebox :=
          FormulaFinset.mem_prebox.mpr <| hy.ant <| Finset.mem_insert_self _ _;
        exact not_mem_both (S := x) ⟨FormulaFinset.mem_prebox.mp (hsub this), h⟩;
      · intro B hB;
        exact hy.ant <| Finset.mem_insert_of_mem <| Finset.mem_union_left _ hB;
      · exact ih.2 (hy.suc (by simp));

end countermodel

namespace Gentzen

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGL] → M ⊧ S) :
    ⊢ᴳ[𝐆𝐋] S := by
  by_contra hS;
  have : Fact (⊬ᴳ[𝐆𝐋] S) := ⟨hS⟩;
  obtain ⟨x, hS₀⟩ := lindenbaum (BS := S) hS (by grind);
  obtain ⟨D, hD, hxD⟩ := h (countermodel S) x (fun C hC ↦ countermodel.truthlemma.1 (hS₀.ant hC));
  exact countermodel.truthlemma.2 (hS₀.suc hD) hxD;

theorem iff_valid : ⊢ᴳ[𝐆𝐋] S ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGL] → M ⊧ S :=
  ⟨fun h _ _ M _ ↦ sound M h, complete⟩

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible. -/
theorem cut (h₁ : ⊢ᴳ[𝐆𝐋] Γ₁ ⟹ insert A Δ₁) (h₂ : ⊢ᴳ[𝐆𝐋] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[𝐆𝐋] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ :=
  complete fun M _ x ↦ forcesSequent_cut (sound M h₁ x) (sound M h₂ x)

end Gentzen

end GL

end FFL.ProvabilityLogic

end
