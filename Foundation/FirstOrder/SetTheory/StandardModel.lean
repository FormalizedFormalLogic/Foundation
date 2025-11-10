import Foundation.Vorspiel.Small
import Foundation.FirstOrder.SetTheory.Basic
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Standard model of set theory

reference:
  https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ZFSet.20and.20computability
  https://github.com/vihdzp/combinatorial-games/blob/9130275873edbae2fba445e0c9fa4a9e17546b36/CombinatorialGames/Game/Functor.lean

 -/

namespace LO.FirstOrder.SetTheory

/-- QPF functor to generate universe -/
@[ext]
structure UniverseFunctor (α : Type (u + 1)) : Type _ where
  set : Set α
  small : Small.{u} set

attribute [coe] UniverseFunctor.set

namespace UniverseFunctor

variable {α : Type (u + 1)}

instance : SetLike (UniverseFunctor α) α where
  coe := set
  coe_injective' _ _ := UniverseFunctor.ext

instance (s : UniverseFunctor α) : Small.{u} s.set := s.small

instance : Functor UniverseFunctor.{u} where
  map m f := ⟨m '' f.set, inferInstance⟩

lemma mem_def {a : α} {f : UniverseFunctor α} : a ∈ f ↔ a ∈ f.set := by rfl

@[simp] lemma mem_mk {a : α} {s : Set α} {h : Small.{u} s} : a ∈ UniverseFunctor.mk s h ↔ a ∈ s := by rfl

@[simp] lemma map_functor (m : α → β) (f : UniverseFunctor α) : (m <$> f).set = m '' f := by rfl

noncomputable instance : QPF.{u + 1, u + 1, u + 1} UniverseFunctor.{u} where
  P := ⟨Type u, fun α ↦ PLift α⟩
  abs p := ⟨Set.range p.2, inferInstance⟩
  repr f := ⟨Shrink f.set, fun x ↦ ((equivShrink _).symm x.down).val⟩
  abs_repr f := by
    ext a; simp only [Set.mem_range, PLift.exists]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro ha
      refine ⟨equivShrink _ ⟨a, ha⟩, by simp⟩
  abs_map m p := by
    ext b
    rcases p
    simp [PFunctor.map]

@[simp] lemma liftp_iff {P : α → Prop} {f : UniverseFunctor α} :
    Functor.Liftp P f ↔ ∀ a ∈ f, P a := by
  constructor
  · rintro ⟨f, rfl⟩
    intro a
    simp [mem_def]; tauto
  · intro h
    refine ⟨
      ⟨Subtype.val ⁻¹' f, small_preimage_of_injective Subtype.val Subtype.val_injective f.set⟩, ?_⟩
    ext p
    simp; tauto

end UniverseFunctor

/-- The standard model of set theory -/
def Universe : Type (u + 1) := QPF.Fix UniverseFunctor

namespace Universe

/-- constructor of name -/
noncomputable def mk (s : Set Universe.{u}) [Small s] : Universe.{u} :=
  QPF.Fix.mk ⟨s, inferInstance⟩

/-- destructor of name -/
noncomputable def dest (x : Universe) : UniverseFunctor Universe := QPF.Fix.dest x

instance : SetLike Universe.{u} Universe.{u} where
  coe x := x.dest.set
  coe_injective' x y e := by
    have h (x : Universe.{u}) : mk x.dest.set = x := QPF.Fix.mk_dest _
    have : mk x.dest.set = mk y.dest.set := by simp_all
    simpa [h] using this

lemma mem_def {x y : Universe.{u}} : x ∈ y ↔ x ∈ y.dest.set := by rfl

lemma mem_def' {x y : Universe.{u}} : x ∈ y ↔ x ∈ (y : Set Universe) := by rfl

instance coe_small (x : Universe.{u}) : Small.{u} (x : Set Universe) := x.dest.small

@[simp] lemma mk_coe (x : Universe.{u}) : mk (↑x : Set Universe.{u}) = x := QPF.Fix.mk_dest _

@[simp] lemma coe_mk (s : Set Universe.{u}) [Small.{u} s] : ↑(mk s) = s :=
  UniverseFunctor.ext_iff.mp <| QPF.Fix.dest_mk (F := UniverseFunctor) ⟨s, inferInstance⟩

@[simp] lemma mem_mk {x} {s : Set Universe.{u}} [Small s] :
    x ∈ mk s ↔ x ∈ s := by simp [mem_def']

@[ext] lemma mem_ext {x y : Universe.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := calc
  x = mk (↑x : Set Universe.{u}) := by simp
  _ = mk (↑y : Set Universe.{u}) := by
    have : (↑x : Set Universe.{u}) = ↑y := by ext; simp [h]
    congr
  _ = y := by simp

noncomputable def rec (g : (s : Set α) → [Small.{u} s] → α) : Universe → α :=
  QPF.Fix.rec (F := UniverseFunctor) fun p ↦ g p.set

lemma rec_mk (g : (s : Set α) → [Small.{u} s] → α) (s : Set Universe.{u}) [Small.{u} s] :
    rec g (mk s) = g (rec g '' s) := by
  simpa using QPF.Fix.rec_eq (F := UniverseFunctor) (fun p ↦ g p.set) ⟨s, inferInstance⟩

theorem ind
    {P : Universe.{u} → Prop}
    (ind : ∀ x, (∀ y ∈ x, P y) → P x)
    (x : Universe) : P x :=
  QPF.Fix.ind P (fun s hs ↦ ind (mk s.set) (by simpa using hs)) x

/--/

namespace Standard

@[simp] lemma isEmpty_iff_eq_empty {x : ZFSet.{u}} :
    IsEmpty x ↔ x = ∅ := by
  simpa [IsEmpty] using Iff.symm (ZFSet.eq_empty x)

instance models_zf : ZFSet.{u} ⊧ₘ* 𝗭𝗙 where
  models_set φ hφ := by
    rcases hφ
    case axiom_of_equality h =>
      have : ZFSet.{u} ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ) := inferInstance
      simpa [models_iff] using modelsTheory_iff.mp this h
    case axiom_of_empty_set =>
      suffices ∃ x, ∀ y, y ∉ x by simpa [models_iff, Axiom.empty]
      exact ⟨∅, by simp⟩
    case axiom_of_extentionality =>
      simp [models_iff, Axiom.extentionality, ZFSet.ext_iff]
    case axiom_of_pairing =>
      suffices
          ∀ x y : ZFSet.{u}, ∃ z, ∀ v, v ∈ z ↔ v = x ∨ v = y by
        simpa [models_iff, Axiom.pairing]
      intro x y
      exact ⟨{x, y}, by simp⟩
    case axiom_of_union =>
      suffices
          ∀ x : ZFSet.{u}, ∃ y, ∀ z, z ∈ y ↔ ∃ v ∈ x, z ∈ v by
        simpa [models_iff, Axiom.union]
      intro x
      exact ⟨x.sUnion, by simp⟩
    case axiom_of_power_set =>
      suffices
          ∀ x : ZFSet.{u}, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x by
        simpa [models_iff, Axiom.power]
      intro x
      exact ⟨x.powerset, by simp⟩
    case axiom_of_infinity =>
      suffices
          ∃ ω, (∅ ∈ ω) ∧
            ∀ x ∈ ω, ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ ω by
        simpa [models_iff, Axiom.infinity, val_isSucc_iff]
      refine ⟨ZFSet.omega, ?_, ?_⟩
      · simp
      · intro x hx y  hy
        have : y = insert x x := by
          ext; simp_all
        simpa [this] using ZFSet.omega_succ hx
    case axiom_of_foundation =>
      suffices
          ∀ x : ZFSet.{u}, IsNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, Axiom.foundation]
      intro x hx
      rcases hx with ⟨y, hx⟩
      refine ⟨ZFSet.mem_wf.min x.toSet ⟨y, by simpa using hx⟩,
        WellFounded.min_mem _ _ _,
        fun _ hx ↦ ZFSet.mem_wf.not_lt_min _ _ (by simpa using hx)⟩
    case axiom_of_separation φ =>
      let P (f : ℕ → ZFSet.{u}) (x : ZFSet.{u}) : Prop :=
        Semiformula.Eval (standardStructure ZFSet.{u}) ![x] f φ
      suffices
          ∀ (f : ℕ → ZFSet.{u}) (x : ZFSet.{u}),
          ∃ y, ∀ z : ZFSet.{u}, z ∈ y ↔ z ∈ x ∧ P f z by
        simpa [models_iff, Axiom.separationSchema, Matrix.constant_eq_singleton, P]
      intro f x
      refine ⟨ZFSet.sep (P f) x, ?_⟩
      intro z; simp
    case axiom_of_replacement φ =>
      let R (f : ℕ → ZFSet.{u}) (x y : ZFSet.{u}) : Prop :=
        Semiformula.Eval (standardStructure ZFSet.{u}) ![x, y] f φ
      suffices
          ∀ f : ℕ → ZFSet.{u},
          (∀ x, ∃! y, R f x y) →
          ∀ X : ZFSet.{u}, ∃ Y : ZFSet.{u}, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R f x y by
        simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      intro f h X
      have : ∀ x, ∃ y, R f x y := fun x ↦ (h x).exists
      choose F hF using this
      have (x y : ZFSet) : R f x y ↔ F x = y :=
        ⟨fun hxy ↦ (h x).unique (hF x) hxy, by rintro rfl; exact hF x⟩
      refine ⟨ZFSet.image F X, fun _ ↦ by simp [this]⟩

instance models_ac : ZFSet.{u} ⊧ₘ* 𝗔𝗖 where
  models_set φ hφ := by
    rcases hφ
    suffices
        ∀ 𝓧 : ZFSet.{u},
          (∀ X ∈ 𝓧, IsNonempty X) →
          (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
          ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X by
      simpa [models_iff, Axiom.choice]
    intro 𝓧 nonempty pairwise_disjoint
    refine ⟨𝓧.choice', ?_⟩
    intro X hX
    exact 𝓧.choice'_uniqueExists
      (by intro h; rcases nonempty ∅ h; simp_all) pairwise_disjoint hX

instance models_zfc : ZFSet.{u} ⊧ₘ* 𝗭𝗙𝗖 := inferInstance

instance models_z : ZFSet.{u} ⊧ₘ* 𝗭 := ModelsTheory.of_ss inferInstance z_subset_zf

instance models_zc : ZFSet.{u} ⊧ₘ* 𝗭𝗖 := inferInstance

end Standard

instance z_consistent : Entailment.Consistent 𝗭 := consistent_of_model 𝗭 ZFSet.{0}

instance zc_consistent : Entailment.Consistent 𝗭𝗖 := consistent_of_model 𝗭𝗖 ZFSet.{0}

instance zf_consistent : Entailment.Consistent 𝗭𝗙 := consistent_of_model 𝗭𝗙 ZFSet.{0}

instance zfc_consistent : Entailment.Consistent 𝗭𝗙𝗖 := consistent_of_model 𝗭𝗙𝗖 ZFSet.{0}

end LO.FirstOrder.SetTheory
