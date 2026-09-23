module

public import Foundation.ProvabilityLogic.GL.Gentzen.Basic
public import Foundation.ProvabilityLogic.Kripke.Sequent
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

lemma Model.validateSequent_boxGL [M.IsGL] (h : M ⊧ (insert (□A) (Γ ∪ Γ.box) ⟹ {A})) :
    M ⊧ (Γ.box ⟹ {□A}) := by
  apply validateSequent_singleton_iff.mpr;
  intro x hx;
  have hΓ : ∀ C ∈ Γ, x ⊩[M] □C := fun C hC ↦ hx _ (Finset.mem_image_of_mem _ hC);
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮[M] A} ⟨y, Rxy, hy⟩;
  apply ht;
  apply validateSequent_singleton_iff.mp h t;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image];
  rintro C (rfl | hC | ⟨C, hC, rfl⟩);
  . intro z Rtz;
    by_contra hz;
    exact tmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz;
  . exact hΓ C hC t Rxt;
  . intro z Rtz;
    exact hΓ C hC z (IsTrans.trans _ _ _ Rxt Rtz);

end Kripke

namespace GL.Gentzen

variable {α : Type*} [DecidableEq α] {S : Sequent α}

theorem sound {κ : Type*} [Nonempty κ] (M : Kripke.Model κ α) [M.IsGL] (h : ⊢ᴳ[GL] S) :
    M ⊧ S := by
  induction h with
  | axm => exact validateSequent_axm;
  | botL => exact validateSequent_botL;
  | wkL _ hΓ ih => exact validateSequent_wk ih hΓ subset_rfl;
  | wkR _ hΔ ih => exact validateSequent_wk ih subset_rfl hΔ;
  | impL _ _ ih₁ ih₂ => exact validateSequent_impL ih₁ ih₂;
  | impR _ ih => exact validateSequent_impR ih;
  | boxGL _ ih => exact Kripke.Model.validateSequent_boxGL ih;

@[simp, grind .]
lemma not_empty : ⊬ᴳ[GL] (∅ ⟹ ∅ : Sequent α) := by
  intro h;
  simpa [Model.ValidateSequent, Model.World.ForcesSequent] using sound (Kripke.Model.pointModel (α := α) fun _ ↦ False) h 0;

end GL.Gentzen

/-! ### Completeness -/

namespace GL

variable {α : Type*} [DecidableEq α]

/-- The worlds of the canonical countermodel of `BS`. -/
structure SaturatedSequent (BS : Sequent α) extends Sequent α where
  saturated : toSequent.Saturated
  subset_subfmls : ant ∪ suc ⊆ BS.subfmls
  unprovable : ⊬ᴳ[GL] toSequent

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

open Classical in
/-- One saturation step for each implication of the list, processed from the last to the
first. -/
noncomputable def saturate (S₀ : Sequent α) (h₀ : ⊬ᴳ[GL] S₀) :
    List (Formula α) → { S : Sequent α // ⊬ᴳ[GL] S }
  | [] => ⟨S₀, h₀⟩
  | (A 🡒 B) :: l =>
    let ⟨S, hS⟩ := saturate S₀ h₀ l;
    if hAB : A 🡒 B ∈ S.ant then
      if h : ⊬ᴳ[GL] S.ant ⟹ insert A S.suc then ⟨S.ant ⟹ insert A S.suc, h⟩
      else ⟨insert B S.ant ⟹ S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hAB] using Gentzen.impL (not_not.mp h) h'⟩
    else if hAB : A 🡒 B ∈ S.suc then
      ⟨insert A S.ant ⟹ insert B S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hAB] using Gentzen.impR h'⟩
    else ⟨S, hS⟩
  | _ :: l => saturate S₀ h₀ l

variable {S₀ : Sequent α} {h₀ : ⊬ᴳ[GL] S₀} {l : List (Formula α)}

lemma subset_saturate : S₀ ⊆ (saturate S₀ h₀ l).1 := by
  induction l with
  | nil => exact ⟨subset_refl _, subset_refl _⟩;
  | cons A l ih =>
    cases A with
    | imp A B =>
      dsimp only [saturate];
      split_ifs <;>
      exact ⟨ih.ant.trans (by first | exact subset_refl _ | exact Finset.subset_insert _ _),
        ih.suc.trans (by first | exact subset_refl _ | exact Finset.subset_insert _ _)⟩;
    | _ => exact ih;

lemma saturate_subset_subfmls {BS : Sequent α} (hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls)
    (hl : ∀ C ∈ l, C ∈ BS.subfmls) :
    (saturate S₀ h₀ l).1.ant ∪ (saturate S₀ h₀ l).1.suc ⊆ BS.subfmls := by
  induction l with
  | nil => exact hS₀;
  | cons A l ih =>
    replace ih := ih (fun C hC ↦ hl C (by simp [hC]));
    cases A with
    | imp A B =>
      have hAB : A 🡒 B ∈ BS.subfmls := hl _ (by simp);
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls hAB Formula.mem_subfmls_imp_left;
      have : B ∈ BS.subfmls := Sequent.mem_subfmls_subfmls hAB Formula.mem_subfmls_imp_right;
      dsimp only [saturate];
      split_ifs <;> grind;
    | _ => exact ih;

lemma saturate_cons_imp {C D : Formula α} :
    (saturate S₀ h₀ l).1 ⊆ (saturate S₀ h₀ ((C 🡒 D) :: l)).1 ∧
    (saturate S₀ h₀ ((C 🡒 D) :: l)).1.ant ⊆ insert C (insert D (saturate S₀ h₀ l).1.ant) ∧
    (saturate S₀ h₀ ((C 🡒 D) :: l)).1.suc ⊆ insert C (insert D (saturate S₀ h₀ l).1.suc) ∧
    (C 🡒 D ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.ant →
      C ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.suc ∨ D ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.ant) ∧
    (C 🡒 D ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.suc →
      C ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.ant ∧ D ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.suc) := by
  have hC : C ≠ C 🡒 D := fun h ↦ by simpa using congrArg Formula.complexity h;
  have hD : D ≠ C 🡒 D := fun h ↦ by simpa using congrArg Formula.complexity h;
  have := hC.symm;
  have := hD.symm;
  have hboth : ∀ E, ¬(E ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.ant ∧
      E ∈ (saturate S₀ h₀ ((C 🡒 D) :: l)).1.suc) :=
    fun E h ↦ (saturate S₀ h₀ ((C 🡒 D) :: l)).2 (Gentzen.union' E h.1 h.2);
  revert hboth;
  dsimp only [saturate];
  split_ifs with h₁ h₂ h₃ <;>
  . intro hboth;
    and_intros <;> simp_all [Finset.subset_iff];

lemma saturate_saturated (hl : l.Pairwise (·.complexity ≤ ·.complexity)) :
    (∀ {A B}, A 🡒 B ∈ l → A 🡒 B ∈ (saturate S₀ h₀ l).1.ant →
      A ∈ (saturate S₀ h₀ l).1.suc ∨ B ∈ (saturate S₀ h₀ l).1.ant) ∧
    (∀ {A B}, A 🡒 B ∈ l → A 🡒 B ∈ (saturate S₀ h₀ l).1.suc →
      A ∈ (saturate S₀ h₀ l).1.ant ∧ B ∈ (saturate S₀ h₀ l).1.suc) := by
  induction l with
  | nil => simp;
  | cons C l ih =>
    obtain ⟨hC, hl⟩ := List.pairwise_cons.mp hl;
    obtain ⟨ihL, ihR⟩ := ih hl;
    cases C with
    | imp C D =>
      obtain ⟨hsub, hant, hsuc, hL, hR⟩ := saturate_cons_imp (S₀ := S₀) (h₀ := h₀) (l := l) (C := C) (D := D);
      have hnew : ∀ {A B}, A 🡒 B ∈ l → A 🡒 B ≠ C ∧ A 🡒 B ≠ D := by
        intro A B hAB;
        have := hC _ hAB;
        constructor <;>
        . rintro rfl;
          simp at this;
          omega;
      and_intros;
      . intro A B hmem hx;
        rcases List.mem_cons.mp hmem with h | h;
        . obtain ⟨rfl, rfl⟩ := Formula.imp_inj.mp h;
          exact hL hx;
        . have := hant hx;
          simp only [Finset.mem_insert, (hnew h).1, (hnew h).2, false_or] at this;
          rcases ihL h this with h' | h';
          . exact .inl (hsub.suc h');
          . exact .inr (hsub.ant h');
      . intro A B hmem hx;
        rcases List.mem_cons.mp hmem with h | h;
        . obtain ⟨rfl, rfl⟩ := Formula.imp_inj.mp h;
          exact hR hx;
        . have := hsuc hx;
          simp only [Finset.mem_insert, (hnew h).1, (hnew h).2, false_or] at this;
          obtain ⟨h₁, h₂⟩ := ihR h this;
          exact ⟨hsub.ant h₁, hsub.suc h₂⟩;
    | _ =>
      constructor <;>
      . intro A B hmem hx;
        rcases List.mem_cons.mp hmem with h | h;
        . simp at h;
        . first | exact ihL h hx | exact ihR h hx;

noncomputable abbrev sortedSubfmls (BS : Sequent α) : List (Formula α) :=
  BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity)

lemma mem_sortedSubfmls {BS : Sequent α} {C : Formula α} : C ∈ sortedSubfmls BS ↔ C ∈ BS.subfmls := by
  simp [List.mem_insertionSort];

lemma sortedSubfmls_pairwise {BS : Sequent α} :
    (sortedSubfmls BS).Pairwise (·.complexity ≤ ·.complexity) :=
  haveI : Std.Total (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ ↦ le_total _ _⟩;
  haveI : IsTrans _ (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ _ ↦ le_trans⟩;
  List.pairwise_insertionSort _ _

noncomputable def lindenbaum {BS : Sequent α} (S₀ : Sequent α) (h₀ : ⊬ᴳ[GL] S₀)
    (hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls) : SaturatedSequent BS where
  toSequent := (saturate S₀ h₀ (sortedSubfmls BS)).1
  unprovable := (saturate S₀ h₀ (sortedSubfmls BS)).2
  subset_subfmls := saturate_subset_subfmls hS₀ fun _ ↦ mem_sortedSubfmls.mp
  saturated := {
    impL := fun h ↦ (saturate_saturated sortedSubfmls_pairwise).1
      (mem_sortedSubfmls.mpr <| saturate_subset_subfmls hS₀ (fun _ ↦ mem_sortedSubfmls.mp) <|
        Finset.mem_union_left _ h) h
    impR := fun h ↦ (saturate_saturated sortedSubfmls_pairwise).2
      (mem_sortedSubfmls.mpr <| saturate_subset_subfmls hS₀ (fun _ ↦ mem_sortedSubfmls.mp) <|
        Finset.mem_union_right _ h) h
  }

lemma subset_lindenbaum {BS : Sequent α} {S₀ : Sequent α} {h₀ : ⊬ᴳ[GL] S₀}
    {hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls} : S₀ ⊆ (lindenbaum (BS := BS) S₀ h₀ hS₀).toSequent :=
  subset_saturate

instance [Fact (⊬ᴳ[GL] BS)] : Nonempty (SaturatedSequent BS) :=
  ⟨lindenbaum BS Fact.out (by grind)⟩

end SaturatedSequent

open SaturatedSequent

def countermodel (BS : Sequent α) [Fact (⊬ᴳ[GL] BS)] : Kripke.Model (SaturatedSequent BS) α where
  Val' x a := #a ∈ x.ant
  Rel' x y := x.ant.prebox ⊂ y.ant.prebox ∧ x.ant.prebox ⊆ y.ant

namespace countermodel

variable {BS : Sequent α} [Fact (⊬ᴳ[GL] BS)] {x : (countermodel BS).World} {A : Formula α}

instance : (countermodel BS).IsFiniteGL where
  trans x y z Rxy Ryz := by
    obtain ⟨h₁, h₂⟩ := Rxy;
    obtain ⟨h₃, h₄⟩ := Ryz;
    exact ⟨h₁.trans h₃, h₁.subset.trans h₄⟩;
  irrefl x h := h.1.ne rfl

lemma truthlemma : (A ∈ x.ant → x ⊩[countermodel BS] A) ∧ (A ∈ x.suc → x ⊮[countermodel BS] A) := by
  induction A generalizing x with
  | atom a => exact ⟨id, fun h hf ↦ not_mem_both ⟨hf, h⟩⟩;
  | falsum => exact ⟨fun h ↦ absurd h bot_not_mem_ant, fun _ ↦ id⟩;
  | imp A B ihA ihB =>
    constructor;
    . intro h hA;
      rcases x.saturated.impL h with hA' | hB;
      . exact absurd hA (ihA.2 hA');
      . exact ihB.1 hB;
    . intro h hf;
      obtain ⟨hA, hB⟩ := x.saturated.impR h;
      exact ihB.2 hB (hf (ihA.1 hA));
  | box A ih =>
    constructor;
    . intro h y Rxy;
      exact ih.1 <| Rxy.2 (by simpa);
    . intro h;
      apply not_forces_box.mpr;
      have h₀ : ⊬ᴳ[GL] insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A} := fun hp ↦
        x.unprovable <| Gentzen.wk (Gentzen.boxGL hp) FormulaFinset.box_prebox_subset (by simpa using h);
      have hS₀ : (insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A}).ant ∪
          (insert (□A) (x.ant.prebox ∪ x.ant.prebox.box) ⟹ {A}).suc ⊆ BS.subfmls := by
        have hx := x.subset_subfmls;
        have hbox : □A ∈ BS.subfmls := hx (Finset.mem_union_right _ h);
        intro B;
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          FormulaFinset.mem_prebox, Finset.mem_image];
        rintro ((rfl | hB | ⟨B, hB, rfl⟩) | rfl);
        . exact hbox;
        . exact Sequent.mem_subfmls_subfmls (hx (Finset.mem_union_left _ hB))
            Formula.mem_subfmls_box;
        . exact hx (Finset.mem_union_left _ hB);
        . exact Sequent.mem_subfmls_subfmls hbox Formula.mem_subfmls_box;
      let y : SaturatedSequent BS := lindenbaum _ h₀ hS₀;
      have hy := subset_lindenbaum (BS := BS) (h₀ := h₀) (hS₀ := hS₀);
      use y;
      and_intros;
      . intro B hB;
        exact FormulaFinset.mem_prebox.mpr <| hy.ant <|
          Finset.mem_insert_of_mem <| Finset.mem_union_right _ <| Finset.mem_image_of_mem _ hB;
      . intro hsub;
        have : A ∈ y.ant.prebox := FormulaFinset.mem_prebox.mpr <| hy.ant <| Finset.mem_insert_self _ _;
        exact not_mem_both (S := x) ⟨FormulaFinset.mem_prebox.mp (hsub this), h⟩;
      . intro B hB;
        exact hy.ant <| Finset.mem_insert_of_mem <| Finset.mem_union_left _ hB;
      . exact ih.2 (hy.suc (by simp));

end countermodel

namespace Gentzen

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGL] → M ⊧ S) :
    ⊢ᴳ[GL] S := by
  by_contra hS;
  have : Fact (⊬ᴳ[GL] S) := ⟨hS⟩;
  have hS₀ := subset_lindenbaum (BS := S) (S₀ := S) (h₀ := hS) (hS₀ := by grind);
  obtain ⟨D, hD, hxD⟩ := h (countermodel S) (lindenbaum S hS (by grind))
    (fun C hC ↦ countermodel.truthlemma.1 (hS₀.ant hC));
  exact countermodel.truthlemma.2 (hS₀.suc hD) hxD;

theorem iff_valid : ⊢ᴳ[GL] S ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGL] → M ⊧ S :=
  ⟨fun h _ _ M _ ↦ sound M h, complete⟩

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible. -/
theorem cut (h₁ : ⊢ᴳ[GL] Γ₁ ⟹ insert A Δ₁) (h₂ : ⊢ᴳ[GL] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[GL] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ := by
  apply complete;
  intro _ _ M _ x hx;
  obtain ⟨D, hD, hxD⟩ := sound M h₁ x (fun C hC ↦ hx C (by simp [hC]));
  rcases Finset.mem_insert.mp hD with rfl | hD;
  . obtain ⟨E, hE, hxE⟩ := sound M h₂ x (by
      intro C hC;
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact hxD;
      . exact hx C (by simp [hC]));
    exact ⟨E, by simp [hE], hxE⟩;
  . exact ⟨D, by simp [hD], hxD⟩;

end Gentzen

end GL

end FFL.ProvabilityLogic

end
