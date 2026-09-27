module

public import Foundation.ProvabilityLogic.Grz.Gentzen.Basic
public import Foundation.ProvabilityLogic.Kripke.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Finite.Prod

/-!
# Kripke completeness of the sequent calculus of `Grz`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

/-! ### Soundness -/

namespace Kripke

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {M : Model κ α}
         {Γ : FormulaFinset α} {A : Formula α}

@[grind →]
lemma Model.validateSequent_boxGrz [M.IsGrz] (h : M ⊧ (insert (□(A 🡒 □A)) Γ.box ⟹ {A})) :
    M ⊧ (Γ.box ⟹ {□A}) := by
  apply validateSequent_singleton_iff.mpr;
  intro x hx y Rxy;
  by_contra hy;
  obtain ⟨v, ⟨Rxv, hv⟩, hmax⟩ := WeaklyConverseWellFounded.has_max (r := M.Rel)
    {z | x ≺ z ∧ z ⊮ □A} ⟨y, Rxy, fun h ↦ hy (h y (Std.Refl.refl y))⟩;
  obtain ⟨w, Rvw, hw⟩ := not_forces_box.mp hv;
  obtain rfl : v = w :=
    hmax w ⟨IsTrans.trans _ _ _ Rxv Rvw, fun h ↦ hw (h w (Std.Refl.refl w))⟩ Rvw;
  apply hw;
  apply validateSequent_singleton_iff.mp h v;
  simp only [Finset.mem_insert, Finset.mem_image];
  rintro C (rfl | ⟨C, hC, rfl⟩);
  · intro u Rvu hu;
    by_contra hnu;
    obtain rfl := hmax u ⟨IsTrans.trans _ _ _ Rxv Rvu, hnu⟩ Rvu;
    exact hw hu;
  · intro z Rvz;
    exact hx _ (Finset.mem_image_of_mem _ hC) z (IsTrans.trans _ _ _ Rxv Rvz);

end Kripke

namespace Grz.Gentzen

variable {α : Type*} [DecidableEq α] {S : Sequent α}

theorem sound {κ : Type*} [Nonempty κ] (M : Kripke.Model κ α) [M.IsGrz] (h : ⊢ᴳ[𝐆𝐫𝐳] S) :
    M ⊧ S := by
  induction h with
  | boxT _ ih =>
    intro x hx;
    apply ih x;
    simp only [Finset.mem_insert];
    rintro C (rfl | hC);
    · exact hx _ (Finset.mem_insert_self _ _) x (Std.Refl.refl x);
    · exact hx C (Finset.mem_insert_of_mem hC);
  | _ => grind;

@[simp, grind .]
lemma not_empty : ⊬ᴳ[𝐆𝐫𝐳] (∅ ⟹ ∅ : Sequent α) := by
  intro h;
  let M : Kripke.Model (Fin 1) α := ⟨fun _ _ ↦ True, fun _ _ ↦ False⟩;
  have : M.IsFiniteGrz :=
    { refl := by tauto, trans := by tauto, antisymm := fun a b _ _ ↦ Subsingleton.elim a b };
  simpa [Model.ValidateSequent, Model.World.ForcesSequent] using sound M h 0;

end Grz.Gentzen

/-! ### Completeness -/

namespace Grz

variable {α : Type*} [DecidableEq α] {BS : Sequent α} {A B C : Formula α}

/-- The subformulas of `BS` together with `A 🡒 □A` and `□(A 🡒 □A)` for each subformula `□A`. -/
noncomputable def closure (BS : Sequent α) : FormulaFinset α :=
  BS.subfmls ∪ BS.subfmls.prebox.image (fun A ↦ A 🡒 □A) ∪
    BS.subfmls.prebox.image (fun A ↦ □(A 🡒 □A))

lemma mem_closure : C ∈ closure BS ↔
    C ∈ BS.subfmls ∨ (∃ A, □A ∈ BS.subfmls ∧ A 🡒 □A = C) ∨
      (∃ A, □A ∈ BS.subfmls ∧ □(A 🡒 □A) = C) := by
  simp [closure];

@[grind .]
lemma subfmls_subset_closure : BS.subfmls ⊆ closure BS :=
  Finset.subset_union_left.trans Finset.subset_union_left

@[grind →]
lemma mem_closure_of_box (h : □A ∈ BS.subfmls) : □(A 🡒 □A) ∈ closure BS := by
  simp [closure, h];

@[grind →]
lemma mem_subfmls_of_imp_mem_closure (h : A 🡒 B ∈ closure BS) :
    A ∈ BS.subfmls ∧ B ∈ BS.subfmls := by
  rcases mem_closure.mp h with h | ⟨C, hC, h⟩ | ⟨C, hC, h⟩;
  · exact ⟨BS.mem_subfmls_subfmls h Formula.mem_subfmls_imp_left,
      BS.mem_subfmls_subfmls h Formula.mem_subfmls_imp_right⟩;
  · obtain ⟨rfl, rfl⟩ := Formula.imp_inj.mp h;
    exact ⟨BS.mem_subfmls_subfmls hC Formula.mem_subfmls_box, hC⟩;
  · cases h;

@[grind →]
lemma mem_closure_of_box_mem_closure (h : □A ∈ closure BS) : A ∈ closure BS := by
  rcases mem_closure.mp h with h | ⟨C, hC, h⟩ | ⟨C, hC, h⟩;
  · exact subfmls_subset_closure (BS.mem_subfmls_subfmls h Formula.mem_subfmls_box);
  · cases h;
  · cases h;
    simp [closure, hC];

/-- The worlds of the canonical countermodel of `BS`. -/
structure SaturatedSequent (BS : Sequent α) extends Sequent α where
  saturated : toSequent.Saturated
  boxT_closed : ∀ {A}, □A ∈ ant → A ∈ ant
  ant_subset : ant ⊆ closure BS
  suc_subset : suc ⊆ BS.subfmls
  unprovable : ⊬ᴳ[𝐆𝐫𝐳] toSequent

namespace SaturatedSequent

variable {S : SaturatedSequent BS}

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
    (β := (closure BS).powerset × BS.subfmls.powerset)
    (fun S ↦ (⟨S.ant, Finset.mem_powerset.mpr S.ant_subset⟩,
              ⟨S.suc, Finset.mem_powerset.mpr S.suc_subset⟩))
    (fun S T h ↦ by simp only [Prod.mk.injEq, Subtype.mk.injEq] at h; exact ext h.1 h.2)

lemma lindenbaum {S₀ : Sequent α} (h₀ : ⊬ᴳ[𝐆𝐫𝐳] S₀) (hant : S₀.ant ⊆ closure BS)
    (hsuc : S₀.suc ⊆ BS.subfmls) : ∃ S : SaturatedSequent BS, S₀ ⊆ S.toSequent := by
  obtain ⟨S, h₁, h₂, h₃, h₄, h₅, h₆⟩ := Sequent.exists_saturated_within
    ⟨fun h₁ h₂ ↦ Gentzen.union' _ h₁ h₂, Gentzen.impL, Gentzen.impR⟩
    (fun h ↦ (mem_subfmls_of_imp_mem_closure h).imp_right (subfmls_subset_closure ·))
    (fun h ↦ (mem_subfmls_of_imp_mem_closure (subfmls_subset_closure h)).imp_left
      (subfmls_subset_closure ·))
    mem_closure_of_box_mem_closure h₀ hant hsuc;
  exact ⟨⟨S, h₃, h₆ Gentzen.boxT, h₄, h₅, h₂⟩, h₁⟩

instance [Fact (⊬ᴳ[𝐆𝐫𝐳] BS)] : Nonempty (SaturatedSequent BS) :=
  (lindenbaum (S₀ := BS) Fact.out (fun _ h ↦ subfmls_subset_closure (by grind)) (by grind)).nonempty

end SaturatedSequent

open SaturatedSequent

def countermodel (BS : Sequent α) [Fact (⊬ᴳ[𝐆𝐫𝐳] BS)] : Kripke.Model (SaturatedSequent BS) α where
  Val' x a := #a ∈ x.ant
  Rel' x y := x.ant.prebox ⊆ y.ant.prebox ∧ (y.ant.prebox ⊆ x.ant.prebox → x = y)

namespace countermodel

variable [Fact (⊬ᴳ[𝐆𝐫𝐳] BS)] {x : (countermodel BS).World}

instance : (countermodel BS).IsFiniteGrz where
  refl _ := ⟨subset_rfl, fun _ ↦ rfl⟩
  trans x y z Rxy Ryz := by
    use Rxy.1.trans Ryz.1;
    intro h;
    obtain rfl := Rxy.2 (Ryz.1.trans h);
    exact Ryz.2 h;
  antisymm _ _ Rxy Ryx := Rxy.2 Ryx.1

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
      exact ih.1 <| y.boxT_closed <| FormulaFinset.mem_prebox.mp <| Rxy.1 (by simpa);
    · intro h;
      apply not_forces_box.mpr;
      by_cases hA : A ∈ x.suc;
      · exact ⟨x, ⟨subset_rfl, fun _ ↦ rfl⟩, ih.2 hA⟩;
      have h₀ : ⊬ᴳ[𝐆𝐫𝐳] insert (□(A 🡒 □A)) x.ant.prebox.box ⟹ {A} := fun hp ↦
        x.unprovable <|
          Gentzen.wk (Gentzen.boxGrz hp) FormulaFinset.box_prebox_subset (by simpa using h);
      have hant : insert (□(A 🡒 □A)) x.ant.prebox.box ⊆ closure BS :=
        Finset.insert_subset (mem_closure_of_box (x.suc_subset h))
          (FormulaFinset.box_prebox_subset.trans x.ant_subset);
      have hsuc : {A} ⊆ BS.subfmls := by
        simpa using Sequent.mem_subfmls_subfmls (x.suc_subset h) Formula.mem_subfmls_box;
      obtain ⟨y, hy⟩ := lindenbaum h₀ hant hsuc;
      use y;
      and_intros;
      · intro B hB;
        exact FormulaFinset.mem_prebox.mpr <| hy.ant <|
          Finset.mem_insert_of_mem <| Finset.mem_image_of_mem _ hB;
      · intro hyx;
        have : A 🡒 □A ∈ x.ant := x.boxT_closed <| FormulaFinset.mem_prebox.mp <| hyx <|
          FormulaFinset.mem_prebox.mpr <| hy.ant (Finset.mem_insert_self _ _);
        rcases x.saturated.impL this with h' | h';
        · contradiction;
        · exact absurd ⟨h', h⟩ not_mem_both;
      · exact ih.2 (hy.suc (by simp));

end countermodel

namespace Gentzen

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGrz] → M ⊧ S) :
    ⊢ᴳ[𝐆𝐫𝐳] S := by
  by_contra hS;
  have : Fact (⊬ᴳ[𝐆𝐫𝐳] S) := ⟨hS⟩;
  obtain ⟨x, hS₀⟩ :=
    lindenbaum (BS := S) hS (fun _ h ↦ subfmls_subset_closure (by grind)) (by grind);
  obtain ⟨D, hD, hxD⟩ := h (countermodel S) x (fun C hC ↦ countermodel.truthlemma.1 (hS₀.ant hC));
  exact countermodel.truthlemma.2 (hS₀.suc hD) hxD;

lemma iff_valid : ⊢ᴳ[𝐆𝐫𝐳] S ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGrz] → M ⊧ S :=
  ⟨fun h _ _ M _ ↦ sound M h, complete⟩

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

theorem cut (h₁ : ⊢ᴳ[𝐆𝐫𝐳] Γ₁ ⟹ insert A Δ₁) (h₂ : ⊢ᴳ[𝐆𝐫𝐳] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[𝐆𝐫𝐳] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ :=
  complete fun M _ x ↦ forcesSequent_cut (sound M h₁ x) (sound M h₂ x)

end Gentzen

end Grz

end FFL.ProvabilityLogic

end
