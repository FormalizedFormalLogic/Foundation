module

public import Foundation.ProvabilityLogic.Grz.Gentzen.Basic
public import Foundation.ProvabilityLogic.Kripke.Sequent
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
         {Γ Δ : FormulaFinset α} {A : Formula α}

lemma Model.validateSequent_boxT [Std.Refl M.Rel] (h : M ⊧ (insert A Γ ⟹ Δ)) :
    M ⊧ (insert (□A) Γ ⟹ Δ) := by
  intro x hx;
  apply h x;
  simp only [Finset.mem_insert];
  rintro C (rfl | hC);
  · exact hx _ (Finset.mem_insert_self _ _) x (Std.Refl.refl x);
  · exact hx C (Finset.mem_insert_of_mem hC);

@[grind →]
lemma Model.validateSequent_boxGrz [M.IsGrz] (h : M ⊧ (insert (□(A 🡒 □A)) Γ.box ⟹ {A})) :
    M ⊧ (Γ.box ⟹ {□A}) := by
  apply validateSequent_singleton_iff.mpr;
  intro x hx y Rxy;
  by_contra hy;
  obtain ⟨v, ⟨Rxv, hv⟩, hmax⟩ := WeaklyConverseWellFounded.has_max (r := M.Rel)
    {z | x ≺ z ∧ z ⊮[M] □A} ⟨y, Rxy, fun h ↦ hy (h y (Std.Refl.refl y))⟩;
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
  | boxT _ ih => exact validateSequent_boxT ih;
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
lemma subfmls_subset_closure : BS.subfmls ⊆ closure BS := fun _ h ↦ mem_closure.mpr (.inl h)

@[grind →]
lemma mem_closure_of_box (h : □A ∈ BS.subfmls) : □(A 🡒 □A) ∈ closure BS :=
  mem_closure.mpr (.inr (.inr ⟨A, h, rfl⟩))

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
    exact mem_closure.mpr (.inr (.inl ⟨C, hC, rfl⟩));

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

def SaturatedAt (S : Sequent α) : Formula α → Prop
  | A 🡒 B => (A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant) ∧ (A 🡒 B ∈ S.suc → A ∈ S.ant ∧ B ∈ S.suc)
  | □A => □A ∈ S.ant → A ∈ S.ant
  | _ => True

omit [DecidableEq α] in
lemma SaturatedAt.mono {S T : Sequent α} {E : Formula α} (h : SaturatedAt S E) (hST : S ⊆ T)
    (hant : ∀ F ∈ T.ant, F ∈ S.ant ∨ F.complexity < E.complexity)
    (hsuc : ∀ F ∈ T.suc, F ∈ S.suc ∨ F.complexity < E.complexity) : SaturatedAt T E := by
  obtain ⟨h₁, h₂⟩ := hST;
  cases E with
  | imp A B =>
    have := hant (A 🡒 B);
    have := hsuc (A 🡒 B);
    simp only [SaturatedAt] at h ⊢;
    grind;
  | box A =>
    have := hant (□A);
    simp only [SaturatedAt] at h ⊢;
    grind;
  | _ => trivial;

open Classical in
/-- One saturation step for each implication and box of the list, processed from the last to the
first. -/
noncomputable def saturate (S₀ : Sequent α) (h₀ : ⊬ᴳ[𝐆𝐫𝐳] S₀) :
    List (Formula α) → { S : Sequent α // ⊬ᴳ[𝐆𝐫𝐳] S }
  | [] => ⟨S₀, h₀⟩
  | (A 🡒 B) :: l =>
    let ⟨S, hS⟩ := saturate S₀ h₀ l;
    if hAB : A 🡒 B ∈ S.ant then
      if h : ⊬ᴳ[𝐆𝐫𝐳] S.ant ⟹ insert A S.suc then ⟨S.ant ⟹ insert A S.suc, h⟩
      else ⟨insert B S.ant ⟹ S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hAB] using Gentzen.impL (not_not.mp h) h'⟩
    else if hAB : A 🡒 B ∈ S.suc then
      ⟨insert A S.ant ⟹ insert B S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hAB] using Gentzen.impR h'⟩
    else ⟨S, hS⟩
  | (□A) :: l =>
    let ⟨S, hS⟩ := saturate S₀ h₀ l;
    if hA : □A ∈ S.ant then
      ⟨insert A S.ant ⟹ S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hA] using Gentzen.boxT h'⟩
    else ⟨S, hS⟩
  | _ :: l => saturate S₀ h₀ l

variable {S₀ : Sequent α} {h₀ : ⊬ᴳ[𝐆𝐫𝐳] S₀} {l : List (Formula α)}

lemma saturate_cons {E : Formula α} :
    (saturate S₀ h₀ l).1 ⊆ (saturate S₀ h₀ (E :: l)).1 ∧
    (∀ F ∈ (saturate S₀ h₀ (E :: l)).1.ant,
      F ∈ (saturate S₀ h₀ l).1.ant ∨ F.complexity < E.complexity) ∧
    (∀ F ∈ (saturate S₀ h₀ (E :: l)).1.suc,
      F ∈ (saturate S₀ h₀ l).1.suc ∨ F.complexity < E.complexity) ∧
    SaturatedAt (saturate S₀ h₀ (E :: l)).1 E := by
  have hboth : ∀ F, ¬(F ∈ (saturate S₀ h₀ (E :: l)).1.ant ∧ F ∈ (saturate S₀ h₀ (E :: l)).1.suc) :=
    fun F h ↦ (saturate S₀ h₀ (E :: l)).2 (Gentzen.union' F h.1 h.2);
  revert hboth;
  cases E with
  | imp A B =>
    dsimp only [saturate];
    split_ifs <;>
    · intro hboth;
      and_intros <;> simp_all [Finset.subset_iff] <;> grind;
  | box A =>
    dsimp only [saturate];
    split_ifs <;>
    · intro hboth;
      and_intros <;> simp_all [SaturatedAt, Finset.subset_iff];
  | atom | falsum =>
    intro;
    dsimp only [saturate];
    exact ⟨⟨subset_rfl, subset_rfl⟩, fun _ h ↦ .inl h, fun _ h ↦ .inl h, trivial⟩;

lemma subset_saturate : S₀ ⊆ (saturate S₀ h₀ l).1 := by
  induction l with
  | nil => exact ⟨subset_rfl, subset_rfl⟩;
  | cons E l ih =>
    obtain ⟨⟨h₁, h₂⟩, -⟩ := saturate_cons (S₀ := S₀) (h₀ := h₀) (l := l) (E := E);
    exact ⟨ih.1.trans h₁, ih.2.trans h₂⟩;

lemma saturate_bound (hant : S₀.ant ⊆ closure BS) (hsuc : S₀.suc ⊆ BS.subfmls) :
    (saturate S₀ h₀ l).1.ant ⊆ closure BS ∧ (saturate S₀ h₀ l).1.suc ⊆ BS.subfmls := by
  induction l with
  | nil => exact ⟨hant, hsuc⟩;
  | cons E l ih =>
    obtain ⟨ih₁, ih₂⟩ := ih;
    cases E with
    | imp A B =>
      dsimp only [saturate];
      split_ifs with h₁ h₂ h₃;
      · exact ⟨Finset.insert_subset
          (subfmls_subset_closure (mem_subfmls_of_imp_mem_closure (ih₁ h₁)).2) ih₁, ih₂⟩;
      · exact ⟨ih₁, Finset.insert_subset (mem_subfmls_of_imp_mem_closure (ih₁ h₁)).1 ih₂⟩;
      · have := mem_subfmls_of_imp_mem_closure (subfmls_subset_closure (ih₂ h₃));
        exact ⟨Finset.insert_subset (subfmls_subset_closure this.1) ih₁,
          Finset.insert_subset this.2 ih₂⟩;
      · exact ⟨ih₁, ih₂⟩;
    | box A =>
      dsimp only [saturate];
      split_ifs with h;
      · exact ⟨Finset.insert_subset (mem_closure_of_box_mem_closure (ih₁ h)) ih₁, ih₂⟩;
      · exact ⟨ih₁, ih₂⟩;
    | _ => exact ⟨ih₁, ih₂⟩;

lemma saturate_saturated (hl : l.Pairwise (·.complexity ≤ ·.complexity)) :
    ∀ E ∈ l, SaturatedAt (saturate S₀ h₀ l).1 E := by
  induction l with
  | nil => simp;
  | cons D l ih =>
    obtain ⟨hD, hl⟩ := List.pairwise_cons.mp hl;
    obtain ⟨hsub, hant, hsuc, hsat⟩ := saturate_cons (S₀ := S₀) (h₀ := h₀) (l := l) (E := D);
    rintro E (_ | ⟨_, hE⟩);
    · exact hsat;
    · exact (ih hl E hE).mono hsub
        (fun F hF ↦ (hant F hF).imp_right fun h ↦ lt_of_lt_of_le h (hD E hE))
        (fun F hF ↦ (hsuc F hF).imp_right fun h ↦ lt_of_lt_of_le h (hD E hE));

noncomputable abbrev sortedClosure (BS : Sequent α) : List (Formula α) :=
  (closure BS).toList.insertionSort (·.complexity ≤ ·.complexity)

lemma mem_sortedClosure : C ∈ sortedClosure BS ↔ C ∈ closure BS := by
  simp [List.mem_insertionSort];

lemma sortedClosure_pairwise : (sortedClosure BS).Pairwise (·.complexity ≤ ·.complexity) :=
  haveI : Std.Total (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ ↦ le_total _ _⟩;
  haveI : IsTrans _ (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ _ ↦ le_trans⟩;
  List.pairwise_insertionSort _ _

noncomputable def lindenbaum (S₀ : Sequent α) (h₀ : ⊬ᴳ[𝐆𝐫𝐳] S₀) (hant : S₀.ant ⊆ closure BS)
    (hsuc : S₀.suc ⊆ BS.subfmls) : SaturatedSequent BS where
  toSequent := (saturate S₀ h₀ (sortedClosure BS)).1
  unprovable := (saturate S₀ h₀ (sortedClosure BS)).2
  ant_subset := (saturate_bound hant hsuc).1
  suc_subset := (saturate_bound hant hsuc).2
  saturated := {
    impL := fun h ↦ (saturate_saturated sortedClosure_pairwise _
      (mem_sortedClosure.mpr <| (saturate_bound hant hsuc).1 h)).1 h
    impR := fun h ↦ (saturate_saturated sortedClosure_pairwise _
      (mem_sortedClosure.mpr <| subfmls_subset_closure <| (saturate_bound hant hsuc).2 h)).2 h
  }
  boxT_closed := fun h ↦ saturate_saturated sortedClosure_pairwise _
    (mem_sortedClosure.mpr <| (saturate_bound hant hsuc).1 h) h

lemma subset_lindenbaum {S₀ : Sequent α} {h₀ : ⊬ᴳ[𝐆𝐫𝐳] S₀} {hant : S₀.ant ⊆ closure BS}
    {hsuc : S₀.suc ⊆ BS.subfmls} : S₀ ⊆ (lindenbaum S₀ h₀ hant hsuc).toSequent :=
  subset_saturate

instance [Fact (⊬ᴳ[𝐆𝐫𝐳] BS)] : Nonempty (SaturatedSequent BS) :=
  ⟨lindenbaum BS Fact.out (fun _ h ↦ subfmls_subset_closure (by grind)) (by grind)⟩

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

lemma truthlemma : (A ∈ x.ant → x ⊩[countermodel BS] A) ∧ (A ∈ x.suc → x ⊮[countermodel BS] A) := by
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
      let y : SaturatedSequent BS := lindenbaum _ h₀ hant hsuc;
      have hy := subset_lindenbaum (h₀ := h₀) (hant := hant) (hsuc := hsuc);
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
  have hant : S.ant ⊆ closure S := fun _ h ↦ subfmls_subset_closure (by grind);
  have hsuc : S.suc ⊆ S.subfmls := by grind;
  have hS₀ := subset_lindenbaum (h₀ := hS) (hant := hant) (hsuc := hsuc);
  obtain ⟨D, hD, hxD⟩ := h (countermodel S) (lindenbaum S hS hant hsuc)
    (fun C hC ↦ countermodel.truthlemma.1 (hS₀.ant hC));
  exact countermodel.truthlemma.2 (hS₀.suc hD) hxD;

theorem iff_valid : ⊢ᴳ[𝐆𝐫𝐳] S ↔
    ∀ {κ : Type u} [Nonempty κ] (M : Kripke.Model κ α), [M.IsFiniteGrz] → M ⊧ S :=
  ⟨fun h _ _ M _ ↦ sound M h, complete⟩

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

/-- Cut is admissible. -/
theorem cut (h₁ : ⊢ᴳ[𝐆𝐫𝐳] Γ₁ ⟹ insert A Δ₁) (h₂ : ⊢ᴳ[𝐆𝐫𝐳] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[𝐆𝐫𝐳] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ := by
  apply complete;
  intro _ _ M _ x hx;
  obtain ⟨D, hD, hxD⟩ := sound M h₁ x (fun C hC ↦ hx C (by simp [hC]));
  rcases Finset.mem_insert.mp hD with rfl | hD;
  · obtain ⟨E, hE, hxE⟩ := sound M h₂ x (by
      intro C hC;
      rcases Finset.mem_insert.mp hC with rfl | hC;
      · exact hxD;
      · exact hx C (by simp [hC]));
    exact ⟨E, by simp [hE], hxE⟩;
  · exact ⟨D, by simp [hD], hxD⟩;

end Gentzen

end Grz

end FFL.ProvabilityLogic

end
