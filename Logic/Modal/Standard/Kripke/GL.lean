import Mathlib.Data.Fintype.List
import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Soundness
import Logic.Modal.Standard.Kripke.Filteration
import Logic.Modal.Standard.Kripke.Preservation

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]

section Definability_and_Soundness

variable {F : Kripke.Frame}

abbrev TransitiveCWFFrameClass : FrameClass := { F | Transitive F ∧ ConverseWellFounded F }

private lemma trans_of_L : F# ⊧* (𝗟 : AxiomSet α) → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, r₁₂, w₃, r₂₃, nr₁₃⟩ := hT;
  apply iff_not_validOnFrame.mpr;
  use (Axioms.L (atom default));
  constructor;
  . simp;
  . use (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁;
    simp only [Kripke.Satisfies]; push_neg;
    constructor;
    . intro x hx h;
      by_cases hx₂ : x = w₂;
      . subst hx₂; simpa [Kripke.Satisfies] using h r₂₃;
      . by_cases hx₃ : x = w₃ <;> simp_all [Kripke.Satisfies, hx₃];
    . existsi w₂; simpa [Kripke.Satisfies];

private lemma cwf_of_L  : F# ⊧* (𝗟 : AxiomSet α) → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  apply iff_not_validOnFrame.mpr;
  use (Axioms.L (atom default));
  constructor;
  . simp;
  . use (λ w _ => w ∉ X), hX₁.some;
    simp only [Kripke.Satisfies]; push_neg;
    constructor;
    . intro x _;
      by_cases hxs : x ∈ X
      . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
        intro h;
        exact h (by simp_all only [Kripke.Satisfies]);
      . aesop;
    . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ hX₁.some (by apply Set.Nonempty.some_mem);
      existsi w';
      constructor;
      . simpa using hw'₂;
      . simpa [Kripke.Satisfies];

private lemma L_of_trans_and_cwf : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F# ⊧* (𝗟 : AxiomSet α) := by
  rintro ⟨hTrans, hWF⟩;
  simp [Axioms.L];
  intro p V w;
  simp only [Kripke.Satisfies.iff_models, Kripke.Satisfies];
  contrapose; push_neg;
  intro h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Kripke.Satisfies ⟨F, V⟩ x p) }) (by use z; simp_all)
  use m;
  constructor;
  . exact rwm;
  . constructor;
    . simp [flip] at hm₂;
      intro n rmn;
      apply not_imp_not.mp $ hm₂ n (hTrans rwm rmn);
      exact rmn;
    . exact hm;

lemma axiomL_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗟 (TransitiveCWFFrameClass) := by
  intro F;
  constructor;
  . intro h;
    constructor;
    . exact trans_of_L h;
    . exact cwf_of_L h;
  . exact L_of_trans_and_cwf;


abbrev TransitiveIrreflexiveFrameClass : FrameClass := { F | Transitive F ∧ Irreflexive F }

/-
lemma TransitiveIrreflexiveFiniteFrameClass.nonempty : TransitiveIrreflexiveFrameClass.Nonempty.{0} := by
  use PointFrame;
  simp [Transitive, Irreflexive];
-/

lemma axiomL_finite_defines : AxiomSet.FinitelyDefinesKripkeFrameClass (α := α) 𝗟 ↑TransitiveIrreflexiveFrameClass := by
  intro F;
  constructor;
  . intro h;
    obtain ⟨hTrans, hCWF⟩ := axiomL_defines.mp h;
    refine ⟨hTrans, ?irreflexive⟩;
    . intro w;
      simpa using ConverseWellFounded.iff_has_max.mp hCWF {w} (by simp);
  . intro d;
    have ⟨hTrans, hIrrefl⟩ := d;
    apply axiomL_defines.mpr;
    constructor;
    . exact hTrans;
    . exact Finite.converseWellFounded_of_trans_irrefl' F.World_finite hTrans hIrrefl;

instance GL_sound : Sound (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClassꟳ# := sound_of_finitely_defines axiomL_finite_defines

instance : System.Consistent (𝐆𝐋 : DeductionParameter α) := consistent_of_finitely_defines.{u} axiomL_finite_defines $ by
  use PointFrame;
  simp [Transitive, Irreflexive];

end Definability_and_Soundness


section Completeness

open Formula (atom)
open Formula.Kripke
open MaximalConsistentTheory

variable [DecidableEq α]

noncomputable abbrev GLCanonicalFrame := CanonicalFrame (α := α) 𝐆𝐋

noncomputable abbrev GLCanonicalModel := CanonicalModel (α := α) 𝐆𝐋

lemma filter_truthlemma
  [Inhabited (Λ)-MCT] [Λ.IsNormal]
  {T : Theory α} [T.SubformulaClosed]
  {X Y : (CanonicalModel Λ).World} (hXY : filterEquiv _ T X Y := by aesop)
  {p : Formula α} (hp : p ∈ T := by aesop) : p ∈ X.theory ↔ p ∈ Y.theory := by
  constructor;
  . intro h; exact truthlemma.mp $ hXY p hp |>.mp $ truthlemma.mpr h;
  . intro h; exact truthlemma.mp $ hXY p hp |>.mpr $ truthlemma.mpr h;

noncomputable abbrev GLFilteredFrame (p : Formula α) : Kripke.FiniteFrame where
  World := FilterEqvQuotient GLCanonicalModel ((𝒮 p).toSet)
  World_finite := by apply FilterEqvQuotient.finite; simp;
  Rel := Quotient.lift₂
    (λ X Y =>
      (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.theory → q ⋏ □q ∈ Y.theory) ∧
      (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.theory ∧ □r ∈ Y.theory)
    )
    (by
      intro X₁ Y₁ X₂ Y₂ hX hY; simp;
      constructor;
      . rintro ⟨h₁, ⟨r, br_mem_sub, br_nmem_X₁, br_mem_Y₁⟩⟩;
        constructor;
        . intro q bq_mem_sub bq_mem_X₂;
          have bq_mem_X₁ : □q ∈ X₁.theory := filter_truthlemma (by simpa) |>.mpr bq_mem_X₂;
          have ⟨q_mem_Y₁, bq_mem_Y₁⟩ := h₁ q bq_mem_sub bq_mem_X₁;
          constructor;
          . exact filter_truthlemma (by simpa) |>.mp q_mem_Y₁;
          . exact filter_truthlemma (by simpa) |>.mp bq_mem_Y₁;
        . use r;
          refine ⟨br_mem_sub, ?br_nmem_X₂, ?br_mem_Y₂⟩;
          . exact filter_truthlemma (by simpa) |>.not.mp br_nmem_X₁;
          . exact filter_truthlemma (by simpa) |>.mp br_mem_Y₁;
      . rintro ⟨h₁, ⟨r, br_mem_sub, br_nmem_X₂, br_mem_Y₂⟩⟩;
        constructor;
        . intro q bq_mem_sub bq_mem_X₂;
          have bq_mem_X₂ : □q ∈ X₂.theory := filter_truthlemma (by simpa) |>.mp bq_mem_X₂;
          have ⟨q_mem_Y₂, bq_mem_Y₂⟩ := h₁ q bq_mem_sub bq_mem_X₂;
          constructor;
          . exact filter_truthlemma (by simpa) |>.mpr q_mem_Y₂;
          . exact filter_truthlemma (by simpa) |>.mpr bq_mem_Y₂;
        . use r;
          refine ⟨br_mem_sub, ?m, ?me⟩;
          . exact filter_truthlemma (by simpa) |>.not.mpr br_nmem_X₂;
          . exact filter_truthlemma (by simpa) |>.mpr br_mem_Y₂;
    )

lemma GLFilteredFrame.def_rel {p : Formula α} {X Y : GLCanonicalFrame.World} :
  ((GLFilteredFrame p).Rel ⟦X⟧ ⟦Y⟧) ↔
  (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.theory → q ⋏ □q ∈ Y.theory) ∧
  (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.theory ∧ □r ∈ Y.theory) := by
  simp;

noncomputable abbrev GLFilteredModel (p : Formula α) : Kripke.Model α where
  Frame := GLFilteredFrame p
  Valuation := StandardFilterationValuation GLCanonicalModel ((𝒮 p).toSet)

variable {T : Theory α} [T.SubformulaClosed]
variable {p : Formula α}

lemma irreflexive_GLFilteredFrame : Irreflexive (GLFilteredFrame p).Rel := by
  intro QX;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  simp_all;

lemma transitive_GLFilteredFrame : Transitive (GLFilteredFrame p).Rel := by
  intro QX QY QZ hXY hYZ;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
  obtain ⟨Z, hZ⟩ := Quotient.exists_rep QZ; subst hZ;
  have ⟨hXY₁, hXY₂⟩ := hXY;
  have ⟨hYZ₁, _⟩ := hYZ;
  constructor;
  . intro q hq bq_mem_X;
    have ⟨_, bq_mem_Y⟩ := MaximalConsistentTheory.iff_mem_and.mp $ hXY₁ q hq bq_mem_X;
    exact hYZ₁ q hq bq_mem_Y;
  . obtain ⟨r, hr, br_nmem_X, br_mem_Y⟩ := hXY₂;
    use r;
    constructor;
    . assumption;
    . constructor;
      . assumption;
      . have ⟨_, bq_mem_Y⟩ := MaximalConsistentTheory.iff_mem_and.mp $ hYZ₁ r hr br_mem_Y;
        assumption;

open System System.FiniteContext in
private lemma GL_truthlemma.lemma1
  {q : Formula α}
  {X : (CanonicalModel 𝐆𝐋).World} (h : □q ∉ X.theory) : (𝐆𝐋)-Consistent ({□q, ~q} ∪ (□''⁻¹X.theory ∪ □''□''⁻¹X.theory)) := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
  have := toₛ! hΓ₂;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⋏ ~q ⟶ ⊥ := imply_left_remove_conj! (p := ~q) this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ ~q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ q := imp_trans''! this $ imp_trans''! (and₂'! neg_equiv!) dne!
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⋏ □q ⟶ q := imply_left_remove_conj! (p := □q) this;
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⟶ (□q ⟶ q) := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □(□q ⟶ q) := imply_box_distribute'! this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □q := imp_trans''! this axiomL!;
  have : 𝐆𝐋 ⊢! ⋀□'(Γ.remove (~q)).remove (□q) ⟶ □q := imp_trans''! collect_box_conj! this;
  have : (□'(Γ.remove (~q)).remove (□q)) ⊢[𝐆𝐋]! □q := provable_iff.mpr this;
  have : X.theory *⊢[𝐆𝐋]! □q := by
    apply Context.provable_iff.mpr;
    use (□'List.remove (□q) (List.remove (~q) Γ));
    constructor;
    . intro r hr; simp at hr;
      obtain ⟨s, hs, es⟩ := hr; subst es;
      have ⟨s_mem', hs₁⟩ := List.mem_remove_iff.mp hs;
      have ⟨s_mem, hs₂⟩ := List.mem_remove_iff.mp s_mem';
      clear hs s_mem';
      have := hΓ₁ s s_mem;
      simp at this;
      rcases this with ((ns₁ | hs₂) | bs_mem | b);
      . contradiction;
      . contradiction;
      . assumption;
      . obtain ⟨t, ht, et⟩ := b; subst et;
        apply membership_iff.mpr;
        apply axiomFour'!;
        apply membership_iff.mp;
        assumption;
    . assumption;
  have : □q ∈ X.theory := membership_iff.mpr this;
  contradiction;

open Formula MaximalConsistentTheory in
lemma GL_truthlemma
  {p : Formula α} {X : (CanonicalModel 𝐆𝐋).World} {q : Formula α} (hq : q ∈ 𝒮 p) :
  Satisfies (GLFilteredModel p) ⟦X⟧ q ↔ q ∈ X.theory := by
  induction q using Formula.rec' generalizing X with
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {□q, ~q} ∪ (□''⁻¹X.theory ∪ □''□''⁻¹X.theory)) $ GL_truthlemma.lemma1 h;
      simp [Satisfies];
      use ⟦Y⟧;
      constructor;
      . apply GLFilteredFrame.def_rel.mpr;
        simp at hY;
        have ⟨hY₁, ⟨hY₂, hY₃⟩⟩ := hY;
        simp_all;
        constructor;
        . intro q _ bq_mem_X;
          constructor;
          . apply hY₂; simpa;
          . apply hY₃; simpa;
        . use q;
          simp_all;
          tauto;
      . apply ih (by aesop) |>.not.mpr;
        apply iff_mem_neg.mp;
        apply hY;
        simp;
    . intro bq_mem_X QY RXY;
      obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
      have ⟨h₁, _⟩ := GLFilteredFrame.def_rel.mp RXY; simp at h₁;
      have ⟨q_mem_Y, _⟩ := h₁ q hq bq_mem_X;
      exact ih (by aesop) |>.mpr q_mem_Y;
  | _ =>
    simp_all [Satisfies, StandardFilterationValuation];
    try aesop;
    done;

lemma exists_finite_frame : ¬𝔽ꟳ# ⊧ p ↔ ∃ F ∈ 𝔽.toFiniteFrameClass, ¬F# ⊧ p := by
  constructor;
  . simp;
  . rintro ⟨F, hF₁, hF₂⟩;
    simp; use F;
    constructor;
    . simp_all;
    . assumption;

private lemma GL_completeAux {p : Formula α} : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLFilteredFrame p);
  constructor;
  . exact ⟨transitive_GLFilteredFrame, irreflexive_GLFilteredFrame⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {~p}) (Theory.unprovable_iff_singleton_neg_consistent.mp h);
    use (GLFilteredModel p).Valuation, ⟦X⟧;
    apply GL_truthlemma (by simp) |>.not.mpr;
    apply MaximalConsistentTheory.iff_mem_neg.mp;
    simpa using hX;

instance GL_complete : Complete (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClass.{u}ꟳ# := ⟨GL_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐋 TransitiveIrreflexiveFrameClass where

end Completeness

end Kripke

end LO.Modal.Standard

-- TODO: Move to vorspiel or etc.
namespace List

variable {l l₁ l₂ : List α}
variable {R : α → α → Prop}

-- TODO: 使っていない．Mathlibにこれに対応する補題があるかは微妙．
lemma head?_eq_head_of_ne_nil (h : l₁ ≠ []) : l₁.head? = some (l₁.head h):= by
  induction l₁ with
  | nil => contradiction;
  | cons => simp_all;

lemma Chain'.nodup_of_trans_irreflex (R_trans : Transitive R) (R_irrefl : Irreflexive R) (h_chain : l.Chain' R) : l.Nodup := by
  by_contra hC;
  replace ⟨d, hC⟩ := List.exists_duplicate_iff_not_nodup.mpr hC;
  have := List.duplicate_iff_sublist.mp hC;
  have := @List.Chain'.sublist α R [d, d] l ⟨by aesop⟩ h_chain this;
  simp at this;
  exact R_irrefl d this;

instance finiteNodupList [DecidableEq α] [Finite α] : Finite { l : List α // l.Nodup } := @fintypeNodupList α _ (Fintype.ofFinite α) |>.finite

lemma chains_finite [DecidableEq α] [Finite α] (R_trans : Transitive R) (R_irrefl : Irreflexive R) : Finite { l : List α // l.Chain' R } := by
  apply @Finite.of_injective { l : List α // l.Chain' R } { l : List α // l.Nodup } _ ?f;
  case f => intro ⟨l, hl⟩; refine ⟨l, List.Chain'.nodup_of_trans_irreflex R_trans R_irrefl hl⟩;
  simp [Function.Injective];

end List



namespace LO.Modal.Standard

namespace Kripke

-- open System
open Kripke
open Formula.Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]

open Relation (TransGen ReflTransGen)


section TreeUnravelling

def Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  World_nonempty := ⟨[r], (by simp)⟩
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1

namespace Frame.TreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_length {x y : (F.TreeUnravelling r).World} (h : x ≺ y) : x.1.length < y.1.length := by
  obtain ⟨z, hz⟩ := h;
  rw [←hz];
  simp;

lemma irreflexive : Irreflexive (F.TreeUnravelling r).Rel := by
  intro x; simp [TreeUnravelling];

lemma assymetric : Assymetric (F.TreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

def PMorphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx.1 [z] |>.mp (by rw [hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . rw [←@List.getLast_append_singleton _ z cx.1]; simp_all;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . use y;
    . constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      . apply List.Chain'.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

end Frame.TreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TreeUnravelling

variable {M : Kripke.Model α} {r : M.World} {p : Formula α}

def PMorphism (M : Kripke.Model α) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TreeUnravelling.PMorphism M.Frame r) $ by aesop;

end Model.TreeUnravelling

end TreeUnravelling


section TransitiveTreeUnravelling

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := (F.TreeUnravelling r)^+

namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_length {x y : (F.TransitiveTreeUnravelling r).World} (Rxy : x ≺ y) : x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact TreeUnravelling.rel_length Rxy;
  | tail _ h ih => have := TreeUnravelling.rel_length h; omega;

lemma rel_transitive : Transitive (F.TransitiveTreeUnravelling r) := TransitiveClosure.rel_transitive

lemma rel_asymmetric : Assymetric (F.TransitiveTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

lemma rel_def {x y : (F.TransitiveTreeUnravelling r).World} : x ≺ y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) := by
  constructor;
  . intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy;
      rw [←hz];
      constructor;
      . simp;
      . use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h;
      obtain ⟨_, ⟨zs, hzs⟩⟩ := ih;
      rw [←hw, ←hzs];
      constructor;
      . simp;
      . use zs ++ [w];
        simp [List.append_assoc];
  . replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x;
    replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y;
    subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩; simp at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z =>
      apply TransGen.single;
      use z;
      simp_all;
    | hcons z zs h ih =>
      simp_all;
      refine TransGen.head ?h₁ $ ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅;
      . use z; simp;
      . apply List.Chain'.prefix hy₂;
        use zs; simp_all;
      . exact hy₂;
      . rw [←hzs]; simp;
        by_contra hC;
        simp_all;
      . simp_all;

lemma rooted : (F.TransitiveTreeUnravelling r).isRooted ⟨[r], by tauto⟩ := by
  intro x ha;
  apply rel_def.mpr;
  obtain ⟨zs, hzs⟩ := x.2.1;
  constructor;
  . rw [←hzs];
    by_contra hC;
    simp at hC;
    simp_all;
  . use zs;

def PMorphism (F : Frame) (F_trans : Transitive F.Rel) (r : F) : (F.TransitiveTreeUnravelling r) →ₚ F := (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans

end Frame.TransitiveTreeUnravelling


def Model.TransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TransitiveTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TransitiveTreeUnravelling

def PMorphism (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World) : M.TransitiveTreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TransitiveTreeUnravelling.PMorphism M.Frame M_trans r) $ by aesop;

lemma modal_equivalence_to_root (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  := modal_equivalence_of_modal_morphism (PMorphism M M_trans r) (⟨[r], by simp⟩)

end Model.TransitiveTreeUnravelling


end TransitiveTreeUnravelling


structure FiniteTransitiveTree extends Kripke.FiniteFrame, Kripke.RootedFrame where
  rel_assymetric : Assymetric Rel
  rel_transitive : Transitive Rel

set_option linter.unusedVariables false in
protected abbrev FiniteTransitiveTree.Dep (α : Type*) := FiniteTransitiveTree
protected abbrev FiniteTransitiveTree.alt (T : FiniteTransitiveTree) {α} : FiniteTransitiveTree.Dep α := T
postfix:max "#" => FiniteTransitiveTree.alt

namespace FiniteTransitiveTree

instance : Semantics (Formula α) (FiniteTransitiveTree.Dep α) := ⟨fun T ↦ Formula.Kripke.ValidOnFrame T.toFrame⟩

lemma rel_irreflexive (T : FiniteTransitiveTree) : Irreflexive T.Rel := irreflexive_of_assymetric $ T.rel_assymetric

end FiniteTransitiveTree

open Classical in
abbrev FiniteFrame.FiniteTransitiveTreeUnravelling
  (F : FiniteFrame) [DecidableEq F.World] (F_trans : Transitive F.toFrame) (F_irrefl : Irreflexive F.toFrame) (r : F.World) : FiniteTransitiveTree :=
  letI T := (F↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩
  {
    World := T
    Rel := T.Rel
    rel_transitive := Frame.TransitiveTreeUnravelling.rel_transitive
    rel_assymetric := Frame.TransitiveTreeUnravelling.rel_asymmetric
    root_rooted := Frame.TransitiveTreeUnravelling.rooted
    World_finite := by
      have := F.World_finite;
      simp [Frame.TreeUnravelling];
      suffices h : Finite { x // List.Chain' (F.PointGenerated r).Rel x } by
        exact Finite.of_injective (β := { x // List.Chain' (F.PointGenerated r).Rel x })
          (fun x => ⟨x.1, x.2.2⟩) (by simp [Function.Injective]);
      exact List.chains_finite (Frame.PointGenerated.rel_transitive F_trans) (Frame.PointGenerated.rel_irreflexive F_irrefl)
  }

abbrev Model.FiniteTransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α := (M↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩


namespace Model.GLTreeUnravelling

end Model.GLTreeUnravelling


section

structure FiniteTransitiveTreeModel (α) where
  Tree : FiniteTransitiveTree
  Valuation : Valuation Tree.toFrame α

namespace FiniteTransitiveTreeModel

abbrev World (M : FiniteTransitiveTreeModel α) := M.Tree.World

abbrev root (M : FiniteTransitiveTreeModel α) : M.World := M.Tree.root

abbrev toFrame (M : FiniteTransitiveTreeModel α) : Kripke.Frame := M.Tree.toFrame

abbrev toModel (M : FiniteTransitiveTreeModel α) : Kripke.Model α := ⟨M.toFrame, M.Valuation⟩
instance : Coe (FiniteTransitiveTreeModel α) (Kripke.Model α) := ⟨toModel⟩

instance : CoeSort (FiniteTransitiveTreeModel α) (Type u) := ⟨World⟩

@[reducible]
instance {M : FiniteTransitiveTreeModel α} : Semantics (Formula α) (M.World) := Formula.Kripke.Satisfies.semantics (M := M.toModel)

end FiniteTransitiveTreeModel


section


/-
  TODO: `FiniteTransitiveTreeClass`のようなものを定義して適当に書き換える
-/

variable {p : Formula α}

open Classical

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, T# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;
  . tauto;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ F : FiniteTransitiveTree.{u}, F# ⊧ p) : ∀ M : FiniteTransitiveTreeModel.{u, u} α, Satisfies M.toModel M.root p := by
  intro M;
  exact h M.Tree M.Valuation M.root

lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree : (∀ M : FiniteTransitiveTreeModel.{u, u} α, Satisfies M.toModel M.root p) → TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p := by
  rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r;
  let M : Kripke.Model α := ⟨F, V⟩;
  apply Model.PointGenerated.modal_equivalent_to_root M F_trans r |>.mp;
  apply Model.TransitiveTreeUnravelling.modal_equivalence_to_root (M↾r) (Frame.PointGenerated.rel_transitive F_trans) ⟨r, by tauto⟩ |>.mp;
  exact H ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r), (M.FiniteTransitiveTreeUnravelling r).Valuation⟩;

/--
  _Segerberg [1971]_?
-/
theorem iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊢! p ↔ (∀ M : FiniteTransitiveTreeModel.{u, u} α, Satisfies M.toModel M.root p) := by
  constructor;
  . intro h M;
    have : TransitiveIrreflexiveFrameClassꟳ# ⊧ p := GL_sound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply GL_complete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊬! p ↔ ∃ M : FiniteTransitiveTreeModel.{u, u} α, ¬Satisfies M.toModel M.root p := by
  constructor;
  . contrapose; simp;
    apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mpr;
  . contrapose; simp;
    apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mp;


end



def FiniteTransitiveTree.SimpleExtension (F : FiniteTransitiveTree) : Kripke.FiniteTransitiveTree where
  World := (Fin 1) ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inl _, .inr _ => True
    | _ , _ => False
  root := .inl 0
  root_rooted := by
    intro w hw;
    simp at w;
    match w with
    | .inl ⟨r, hr⟩ => induction r <;> simp at hw hr;
    | .inr _ => simp [Frame.Rel'];
  rel_assymetric := by
    simp_all;
    intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    simp_all;
    intro x y z hxy hyz;
    match x, y, z with
    | .inl _, .inr _, .inr _ => simp;
    | .inr x, .inr y, .inr z => exact F.rel_transitive hxy hyz;
postfix:max "↧" => FiniteTransitiveTree.SimpleExtension

namespace FiniteTransitiveTree.SimpleExtension

variable {F : FiniteTransitiveTree} {x y : F.World}

instance : Coe (F.World) (F↧.World) := ⟨Sum.inr⟩

@[simp] lemma root_not_original : (Sum.inr x) ≠ F↧.root := by simp [SimpleExtension]

lemma root_eq {x : Fin 1} : (Sum.inl x) = F↧.root := by simp [SimpleExtension]; ext1; simp;

lemma forth (h : x ≺ y) : F↧.Rel x y := by simpa [SimpleExtension];

def p_morphism : F.toFrame →ₚ (F↧.toFrame) where
  toFun x := x
  forth := forth
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', SimpleExtension] at h;
    | .inr y => use y; simp; exact h;

lemma through_original_root {x : F↧.World} (h : F↧.root ≺ x) : x = F.root ∨ (Sum.inr F.root ≺ x) := by
  match x with
  | .inl x =>
    simp [FiniteTransitiveTree.SimpleExtension.root_eq] at h;
    have := F↧.rel_irreflexive _ h;
    contradiction;
  | .inr x =>
    by_cases h : x = F.root;
    . subst h; left; tauto;
    . right; exact FiniteTransitiveTree.SimpleExtension.forth $ F.root_rooted x h;

end FiniteTransitiveTree.SimpleExtension

abbrev FiniteTransitiveTreeModel.SimpleExtension (M : FiniteTransitiveTreeModel α) : Kripke.FiniteTransitiveTreeModel α where
  Tree := M.Tree↧
  Valuation x a :=
    match x with
    | .inl _ => M.Valuation M.Tree.root a
    | .inr x => M.Valuation x a
postfix:max "↧" => FiniteTransitiveTreeModel.SimpleExtension


namespace FiniteTransitiveTreeModel.SimpleExtension

variable {M : FiniteTransitiveTreeModel α}

instance : Coe (M.World) (M↧.World) := ⟨Sum.inr⟩

def p_morphism : M →ₚ (M↧.toModel) := Model.PseudoEpimorphism.mkAtomic (FiniteTransitiveTree.SimpleExtension.p_morphism) $ by
  simp [FiniteTransitiveTree.SimpleExtension.p_morphism];

lemma modal_equivalence_original_world {x : M.toModel.World} : ModalEquivalent (M₁ := M) (M₂ := (M↧).toModel) x x := by
  apply Kripke.modal_equivalence_of_modal_morphism p_morphism;

end FiniteTransitiveTreeModel.SimpleExtension

-- def FiniteTransitiveTree.NthSimpleExplansion (T : FiniteTransitiveTree) (n : ℕ) : Kripke.FiniteTransitiveTree := (·⇓)^[n] T

end

end Kripke


section

open System
open Formula.Kripke (Satisfies)
open Kripke Kripke.FiniteTransitiveTreeModel

variable [DecidableEq α] [Inhabited α]
variable {p q : Formula α}

/-
  逆は以下を順に辿って構文論的に証明できる．
  - `System.imply_boxdot_boxdot_of_imply_boxdot_plain`
  - `System.imply_boxdot_axiomT_of_imply_boxdot_boxdot`
  - `System.imply_box_box_of_imply_boxdot_axiomT`
-/
lemma GL_imply_boxdot_plain_of_imply_box_box : 𝐆𝐋 ⊢! □p ⟶ □q → 𝐆𝐋 ⊢! ⊡p ⟶ q := by
  contrapose;
  intro h;
  have := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;

  replace hs : M.root ⊧ ⊡p ⋏ ~q := by
    simp only [Satisfies] at hs;
    push_neg at hs;
    exact hs;
  replace hs := @FiniteTransitiveTreeModel.SimpleExtension.modal_equivalence_original_world α M M.root (⊡p ⋏ ~q) |>.mp hs;
  replace ⟨⟨hs₁, hs₂⟩, hs₃⟩ := hs;

  have hbp : (Satisfies M↧.toModel (M↧.root) (□p)) := by
    intro x hx;
    rcases @FiniteTransitiveTree.SimpleExtension.through_original_root M.Tree x hx with (rfl | b)
    . assumption;
    . exact hs₂ b;
  have hbq : ¬(Satisfies M↧.toModel (M↧.root) (□q)) := by
    simp [Satisfies];
    use M.root;
    constructor;
    . apply M↧.Tree.toRootedFrame.root_rooted M.root;
      simp [SimpleExtension, FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    . assumption;
  have : ¬(Satisfies M↧.toModel M↧.root (□p ⟶ □q)) := _root_.not_imp.mpr ⟨hbp, hbq⟩;

  apply iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M↧;

theorem GL_unnecessitation! : 𝐆𝐋 ⊢! □p → 𝐆𝐋 ⊢! p := by
  intro h;
  have : 𝐆𝐋 ⊢! □⊤ ⟶ □p := dhyp! (q := □⊤) h;
  have : 𝐆𝐋 ⊢! ⊡⊤ ⟶ p := GL_imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : System.Unnecessitation (𝐆𝐋 : DeductionParameter α) where
  unnec := λ h => GL_unnecessitation! ⟨h⟩ |>.some

end


end LO.Modal.Standard
