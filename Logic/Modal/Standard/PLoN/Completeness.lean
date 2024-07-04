import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.PLoN.Soundness

namespace LO.Modal.Standard

namespace PLoN

variable {α : Type u} [DecidableEq α]
variable {Λ : DeductionParameter α}

open Formula
open Theory
open MaximalConsistentTheory

section forN

abbrev CanonicalFrame (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Frame α where
  World := (Λ)-MCT
  Rel := λ p Ω₁ Ω₂ => ~(□p) ∈ Ω₁.theory ∧ ~p ∈ Ω₂.theory

abbrev CanonicalModel (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : PLoN.Model α where
  Frame := CanonicalFrame Λ
  Valuation Ω a := (atom a) ∈ Ω.theory

instance CanonicalModel.instSatisfies [Inhabited (Λ)-MCT] : Semantics (Formula α) ((CanonicalModel Λ).World) := Formula.PLoN.Satisfies.semantics (CanonicalModel Λ)

variable {Λ : DeductionParameter α} [Inhabited (Λ)-MCT] [Λ.HasNecessitation]
         {p : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Λ).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      by_contra hC;
      suffices ¬Ω ⊧ □p by contradiction; done;
      simp [PLoN.Satisfies];
      constructor;
      . assumption;
      . obtain ⟨Ω', hΩ'⟩ := lindenbaum (Λ := Λ) (T := {~p}) (not_singleton_consistent Ω.consistent (iff_mem_neg.mpr hC));
        use Ω';
        constructor;
        . apply iff_mem_neg.mp;
          simp_all;
        . apply ih.not.mpr;
          apply iff_mem_neg.mp;
          simp_all;
    . intro h;
      by_contra hC;
      simp [PLoN.Satisfies] at hC;
      simp_all only [PLoN.Satisfies.iff_models];
  | _ => simp_all [PLoN.Satisfies];

lemma complete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : 𝔽 ⊧ p → Λ ⊢! p:= by
  simp [PLoN.ValidOnFrameClass, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  contrapose; push_neg;
  intro h;
  use (CanonicalFrame Λ);
  constructor;
  . exact hFC;
  . use (CanonicalModel Λ).Valuation;
    obtain ⟨Ω, hΩ⟩ := lindenbaum (Λ := Λ) (T := {~p}) (by
      apply unprovable_iff_singleton_neg_consistent.mp;
      exact h;
    );
    use Ω;
    apply truthlemma.not.mpr;
    apply iff_mem_neg.mp;
    simp_all;

lemma instComplete_of_mem_canonicalFrame {𝔽 : FrameClass α} (hFC : CanonicalFrame Λ ∈ 𝔽) : Complete Λ 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance : Complete 𝐍 (AllFrameClass.{u, u} α) := instComplete_of_mem_canonicalFrame (by simp)

end forN


section Others

abbrev RestrictedFrame (F : PLoN.FiniteFrame α) (p : Formula α) : PLoN.FiniteFrame α where
  World := F.World
  World_inhabited := F.World_inhabited
  World_finite := F.World_finite
  Rel := λ q x y =>
    if □q ∈ Sub p then x ≺[q] y
    else x = y

namespace RestrictedFrame

variable {F : PLoN.FiniteFrame α} {p : Formula α} {x y : F.World} -- {x y : (RestrictedFrame F p).World}

lemma def_rel_mem_sub {q : Formula α} (h : □q ∈ p.Subformulas) {x y : F.World} : F.Rel q x y ↔ (RestrictedFrame F p).Rel q x y := by aesop;

lemma def_rel_mem_sub' {q : Formula α} (h : □q ∈ p.Subformulas) {x y : (RestrictedFrame F p).World} : F.Rel q x y ↔ (RestrictedFrame F p).Rel q x y := by
  simp_all;

lemma def_rel_not_mem_sub {q : Formula α} (h : □q ∉ p.Subformulas) {x y : F.World} : x = y ↔ (RestrictedFrame F p).Rel q x y := by aesop;

open Formula.Subformulas RestrictedFrame

lemma restricted_serial_of_serial (F_serial : F.toFrame.Serial) : (RestrictedFrame F p).toFrame.Serial := by
  intro q hq x;
  by_cases h : □q ∈ p.Subformulas;
  . obtain ⟨y, rxy⟩ := @F_serial q hq x;
    use y; exact def_rel_mem_sub h |>.mp rxy;
  . use x; apply def_rel_not_mem_sub h |>.mp; rfl;

lemma subformula_restricted_serial_of_serial (p : Formula α) (F_serial : F.toFrame.Serial) : (RestrictedFrame F p).SerialOnTheory p.Subformulas  := by
  sorry;
  -- apply Frame.serialOnTheory_of_serial;
  -- simp only [Frame.SerialOnTheory];
  -- exact restricted_serial_of_serial F_serial;

lemma transitive_of_base_transitive (F_transitive : F.toFrame.Transitive) : (RestrictedFrame F p).toFrame.Transitive := by
  intro q hq x y z rxy ryz;
  by_cases h : □(□q) ∈ p.Subformulas
  . have := @F_transitive q hq x y z;
    replace rxy := def_rel_mem_sub' h |>.mpr rxy;
    replace ryz := def_rel_mem_sub' (mem_box h) |>.mpr ryz;
    have rxz := this rxy ryz;
    sorry;
  . have := def_rel_not_mem_sub h |>.mpr rxy; subst_vars;
    exact ryz;

lemma subformula_restricted_transitive_of_transitive (p : Formula α) (F_transitive : F.toFrame.Transitive) : (RestrictedFrame F p).TransitiveOnTheory p.Subformulas := by
  sorry;
  -- apply Frame.transitiveOnTheory_of_transitive;
  -- exact transitive_of_base_transitive F_transitive;

abbrev RestrictedModel (M : PLoN.FiniteModel α) (p : Formula α) : PLoN.Model α where
  Frame := RestrictedFrame M.FiniteFrame p
  Valuation a x := M.Valuation a x

end RestrictedFrame

end Others

end PLoN


section

open System
open Formula

variable {Λ : DeductionParameter α} [System.Classical Λ]

namespace Formula

variable [DecidableEq α]


def complement : Formula α → Formula α
  | ~p => p
  | p  => ~p
postfix:80 "ᶜ" => complement

@[simp]
lemma complement_complement (p : Formula α) : pᶜᶜ = p := by sorry;

lemma complement_congr (p q : Formula α) : p = q ↔ pᶜ = qᶜ := by
  constructor;
  . intro h;
    subst h;
    rfl;
  . intro h;
    sorry;

abbrev ComplementSubformula (p : Formula α) : Finset (Formula α) := (Sub p) ∪ (Finset.image (Formula.complement) $ Sub p)
prefix:70 "Subᶜ " => ComplementSubformula

namespace ComplementSubformula

variable {p q : Formula α}

@[simp]
lemma mem_self : p ∈ Subᶜ p := by simp;

@[simp]
lemma mem_self_complement : pᶜ ∈ Subᶜ p := by
  simp [ComplementSubformula];
  right;
  use p;
  constructor;
  . simp only [Subformulas.mem_self];
  . rfl;

lemma mem_complement : q ∈ Subᶜ p ↔ qᶜ ∈ Subᶜ p := by
  constructor;
  . simp_all [ComplementSubformula];
    rintro (hl | hr);
    . right; sorry;
    . obtain ⟨r, hr₁, hr₂⟩ := hr;
      left; rw [←hr₂];
      sorry;
  . simp_all [ComplementSubformula];
    rintro (hl | hr);
    . right; use qᶜ; simp_all;
    . obtain ⟨r, hr₁, hr₂⟩ := hr;
      left; sorry;

lemma mem_box (h : □q ∈ Subᶜ p) : q ∈ Subᶜ p := by
  simp_all;
  rcases h with (hl | hr);
  . left; exact Subformulas.mem_box hl;
  . obtain ⟨r, hr₁, hr₂⟩ := hr;
    sorry;

end ComplementSubformula

end Formula

variable [DecidableEq α]


namespace Theory

variable {Λ : DeductionParameter α} {p : Formula α} {T : Theory α} (T_consis : (Λ)-Consistent T) (T_subset : T ⊆ Subᶜ p)

lemma exists_maximal_cs_consistent_theory
  : ∃ Z, ((Λ)-Consistent Z ∧ Z ⊆ Subᶜ p) ∧ T ⊆ Z ∧ (∀ U, ((Λ)-Consistent U ∧ U ⊆ Subᶜ p) → Z ⊆ U → U = Z)
  := zorn_subset_nonempty { T : Theory α | (Λ)-Consistent T ∧ T ⊆ Subᶜ p } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Consistent, Set.mem_setOf_eq, Set.mem_sUnion];
    refine ⟨⟨?h₁, ?h₂⟩, ?h₃⟩;
    . intro Γ;
      by_contra hC; simp at hC;
      have ⟨hΓs, hΓd⟩ := hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : (Λ)-Consistent U := hc hUc |>.1;
      have : ¬(Λ)-Consistent U := by
        simp only [Consistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . apply hUs;
        . assumption;
      contradiction;
    . apply Set.sUnion_subset;
      intro T hT;
      apply hc hT |>.2;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T ⟨T_consis, T_subset⟩

lemma complement_consistent [System.Consistent Λ] {p : Formula α} (h : Λ ⊬! p) : (Λ)-Consistent {pᶜ} := by
  simp [Theory.Consistent];
  intro Γ hΓ; by_contra hC;
  have := imply_left_remove_conj'! (p := pᶜ) hC;
  -- have a : (List.remove (pᶜ) Γ) = [] := by sorry;
  sorry;
  /-
  induction p using Formula.rec' with
  | himp q r =>
    simp [complement] at d;
    split at d;
    . rename_i heq;
      simp at heq;
    . have := dne'! $ negneg_equiv'!.mpr d;
      contradiction;
  | _ => sorry;
  -/
  /-
  | _ =>
    simp [complement] at d;
    have := dne'! $ negneg_equiv'!.mpr d;
    contradiction;
  -/

end Theory

structure ComplementClosedMaximalConsistentTheory (Λ : DeductionParameter α) (p : Formula α) where
  theory : Theory α
  subset : theory ⊆ Subᶜ p
  consistent : (Λ)-Consistent theory
  maximal : ∀ {U}, U ⊆ ↑(Subᶜ p) → theory ⊂ U → ¬(Λ)-Consistent U

notation "(" Λ "," p ")-MCT" => ComplementClosedMaximalConsistentTheory Λ p

namespace ComplementClosedMaximalConsistentTheory

open Theory


lemma exists_maximal_Lconsistented_theory {T : Theory α} {p : Formula α} (T_subset : T ⊆ Subᶜ p) (T_consis : (𝓓)-Consistent T)
  : ∃ Ω : (𝓓, p)-MCT, (T ⊆ Ω.theory) := by
  have ⟨Ω, ⟨Ω_consis, Ω_subset⟩, T_Ω, Ω_maximal⟩ := Theory.exists_maximal_cs_consistent_theory T_consis T_subset;
  existsi {
    theory := Ω,
    consistent := Ω_consis,
    subset := Ω_subset,
    maximal := by
      rintro U hU₁ hU₂; by_contra hC;
      rw [Ω_maximal U ⟨hC, hU₁⟩ hU₂.subset] at hU₂;
      simp [Set.ssubset_def] at hU₂;
  };
  exact T_Ω;
alias lindenbaum := exists_maximal_Lconsistented_theory

-- noncomputable instance [System.Consistent Λ] : Inhabited (Λ, p)-MCT := ⟨lindenbaum (T := Subᶜ p) (by rfl) (by sorry) |>.choose⟩

variable {Ω Ω₁ Ω₂ : (Λ, p)-MCT}
variable {q r : Formula α}

@[simp]
lemma mem_sub_of_mem (h : q ∈ Ω.theory) : q ∈ Subᶜ p := by apply Ω.subset; assumption;

lemma either_mem (Ω : (Λ, p)-MCT) {q} (hq : q ∈ Subᶜ p) : q ∈ Ω.theory ∨ ~q ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent q with
  | inl h =>
    have := Ω.maximal (show insert q Ω.theory ⊆ ↑(Subᶜ p) by
      apply Set.insert_subset_iff.mpr;
      constructor;
      . sorry;
      . exact Ω.subset;
    ) (Set.ssubset_insert hC.1);
    contradiction;
  | inr h =>
    have := Ω.maximal (show insert (~q) Ω.theory ⊆ ↑(Subᶜ p) by sorry) (Set.ssubset_insert hC.2);
    contradiction;

variable (q_sub : q ∈ Subᶜ p)

lemma membership_iff : (q ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~q ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω q_sub); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[Λ]! ~q := Context.by_axm! hC;
    have := neg_mdp! hnp hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_Consistent Ω.consistent

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[Λ]! ⊥ := by apply membership_iff (by sorry) |>.not.mp; simp;

lemma iff_mem_neg : (~q ∈ Ω.theory) ↔ (q ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff q_sub |>.mp hp;
    replace hnp := membership_iff (by sorry) |>.mp hnp;
    have : Ω.theory *⊢[Λ]! ⊥ := neg_mdp! hnp hp;
    have : Ω.theory *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    by_contra hnp;
    sorry;

/-
lemma mem_neg_of_not_mem : q ∉ Ω.theory → ~q ∈ Ω.theory := by
  intro h;
  have := Ω.maximal
-/

end ComplementClosedMaximalConsistentTheory

namespace PLoN

abbrev CanonicalFrame2 (Λ : DeductionParameter α) (p : Formula α) [Inhabited (Λ, p)-MCT] : PLoN.FiniteFrame α where
  World := (Λ, p)-MCT
  Rel := λ q Ω₁ Ω₂ => □q ∉ Ω₁.theory ∨ q ∈ Ω₂.theory
  World_finite := by
    simp;
    sorry;

abbrev CanonicalModel2 (Λ : DeductionParameter α) (p : Formula α) [Inhabited (Λ, p)-MCT] : PLoN.FiniteModel α where
  Frame := CanonicalFrame2 Λ p
  Valuation Ω a := (atom a) ∈ Ω.theory

namespace CanonicalModel2

variable {p : Formula α} [Inhabited (Λ, p)-MCT]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel2 Λ p).World := Formula.PLoN.Satisfies.semantics (M := (CanonicalModel2 Λ p).toModel)

end CanonicalModel2

variable {p q : Formula α} [Λ.HasNecessitation] [Inhabited (Λ, p)-MCT]

open ComplementClosedMaximalConsistentTheory

lemma truthlemma2 : ∀ {X : (CanonicalModel2 Λ p).World}, X ⊧ q ↔ (q ∈ X.theory) := by
  intro X;
  induction q using Formula.rec' with
  | hbox s ih =>
    constructor;
    . contrapose;
      intro hr;
      have : ~(□s) ∈ X.theory := by
        by_contra hC;
        have h := X.maximal (U := (insert (□s) X.theory)) (by sorry) (by
          apply Set.ssubset_iff_of_subset (by simp) |>.mpr;
          use (□s); simpa;
        );
        sorry;
      have d₁ := membership_iff (mem_sub_of_mem this) |>.mp this;
      obtain ⟨Y, hY⟩ := lindenbaum (𝓓 := Λ) (p := p) (T := {~s}) (T_subset := by sorry) $ by
        intro Γ hΓ hC;
        have : Λ ⊢! ~s ⟶ ⊥ := replace_imply_left_conj'! hΓ hC;
        have : Λ ⊢! □s := nec! $ dne'! $ neg_equiv'!.mpr this;
        have : X.theory *⊢[Λ]! ⊥ := neg_mdp! d₁ (Context.of! this);
        have : X.theory *⊬[Λ]! ⊥ := unprovable_falsum;
        contradiction;

      simp only [PLoN.Satisfies.iff_models, PLoN.Satisfies]; push_neg;
      use Y;
      constructor;
      . constructor;
        . sorry;
        . sorry;
      . sorry;
    . intro h;
      by_contra hC;
      simp [PLoN.Satisfies] at hC;
      simp_all only [PLoN.Satisfies.iff_models];
  | _ =>
    simp_all [PLoN.Satisfies];
    try sorry;

-- set_option pp.universes true in
lemma complete_of_N : (AllFrameClass.{u, u} α)ꟳ ⊧ p → 𝐍 ⊢! p := by
  contrapose; simp [PLoN.ValidOnFrameClass, PLoN.ValidOnFrame, PLoN.ValidOnModel];
  intro h;
  have : Inhabited (𝐍, p)-MCT := by sorry;
  use (CanonicalFrame2 𝐍 p);
  constructor;
  . use (CanonicalFrame2 𝐍 p); simp;
  . obtain ⟨Ω, hΩ⟩ := lindenbaum (p := p) (by simp; right; use p; simp) (Theory.complement_consistent h);
    use (CanonicalModel2 𝐍 p).Valuation, Ω;
    apply truthlemma2.not.mpr;
    sorry;

lemma serial_CanonicalFrame₂ [Λ.HasRosserRule] : (CanonicalFrame2 Λ p).toFrame.SerialOnTheory (Sub p) := by
  intro q hq X; simp at hq;
  by_cases h : (□q ∈ X.theory);
  . obtain ⟨Y, hY⟩ := lindenbaum (𝓓 := Λ) (p := p) (T := {q}) (T_subset := by sorry) $ by sorry;
    use Y; right; simp_all;
  . use X; left; assumption;

lemma transitive_CanonicalFrame₂ [Λ.HasAxiomFour] : (CanonicalFrame2 Λ p).toFrame.TransitiveOnTheory (Sub p) := by
  intro q hq X Y Z hXY hYZ;
  simp at hq;
  by_cases h : (□q) ∈ X.theory;
  . replace h := membership_iff (by sorry) |>.mp h;
    have : □□q ∈ X.theory := by
      apply membership_iff (by simp; left; exact hq) |>.mpr;
      sorry;
      -- exact axiomFour! h;
    have : □q ∈ Y.theory := by rcases hXY with ⟨_⟩ | ⟨_⟩ <;> rcases hYZ with ⟨_⟩ | ⟨_⟩ <;> simp_all only
    have : q ∈ Z.theory := by rcases hXY with ⟨_⟩ | ⟨_⟩ <;> rcases hYZ with ⟨_⟩ | ⟨_⟩ <;> simp_all only;
    right; assumption;
  . left; assumption;


end PLoN

end

end LO.Modal.Standard
