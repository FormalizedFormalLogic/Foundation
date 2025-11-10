import Foundation.FirstOrder.Kripke.Basic
import Foundation.FirstOrder.SetTheory.Z
import Mathlib.Data.QPF.Univariate.Basic

/-! # $\mathbb{P}$-name -/

section Small

variable {α β : Type*}

def small_preimage_of_injective (f : α → β) (h : Function.Injective f) (s : Set β) [Small.{u} s] :
    Small.{u} (f ⁻¹' s) := small_of_injective (β := s) (f := fun x ↦ ⟨f x, x.prop⟩) fun x y ↦ by
  simp [Function.Injective.eq_iff h, SetCoe.ext_iff]

end Small

namespace LO.FirstOrder.SetTheory

variable (ℙ : Type u) [Preorder ℙ]

/-- ref:
  https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ZFSet.20and.20computability
  https://github.com/vihdzp/combinatorial-games/blob/9130275873edbae2fba445e0c9fa4a9e17546b36/CombinatorialGames/Game/Functor.lean -/
@[ext]
structure NameFunctor (α : Type (u + 1)) : Type _ where
  toFun : ℙ → Set α
  small : ∀ p, Small.{u} (toFun p)
  monotone : IsSetMonotone (· ≥ ·) toFun

attribute [coe] NameFunctor.toFun

variable {ℙ}

namespace NameFunctor

instance : CoeFun (NameFunctor ℙ α) (fun _ ↦ ℙ → Set α) := ⟨fun F ↦ F.toFun⟩

instance (F : NameFunctor ℙ α) (p : ℙ) : Small.{u} (F p) := F.small p

instance : Functor (NameFunctor ℙ) where
  map m F := ⟨fun p ↦ m '' F p, fun _ ↦ inferInstance, fun h b ↦ by
    simp only [Set.mem_image, forall_exists_index, and_imp]
    rintro a ha rfl
    exact ⟨a, F.monotone h ha, rfl⟩⟩

variable {F : NameFunctor ℙ α}

@[simp] lemma map_app (m : α → β) (p : ℙ) : (m <$> F) p = m '' F p := by rfl

lemma mem_of_le {p q : ℙ} (x : F p) (hqp : q ≤ p) : ↑x ∈ F q := F.monotone hqp x.prop

variable (ℙ)

abbrev MonotoneFunction (C : Type u) := {f : ℙ → Set C // IsSetMonotone (· ≥ ·) f}

noncomputable instance qpf : QPF.{u + 1, u + 1, u + 1} (NameFunctor ℙ) where
  P := ⟨(C : Type u) × MonotoneFunction ℙ C, fun s ↦ PLift s.1⟩
  abs {α} s := ⟨fun p ↦ s.2 ∘ PLift.up '' s.1.2.val p, fun _ ↦ inferInstance, fun h a ↦ by
    simp only [Set.mem_image, forall_exists_index, and_imp]
    rintro c hc rfl
    exact ⟨c, s.1.2.property h hc, by rfl⟩⟩
  repr F :=
    let C := (p : ℙ) × Shrink (F p)
    ⟨⟨C, fun p ↦ {c | p ≤ c.1}, fun h c ha ↦ le_trans h ha⟩, fun c ↦ ((equivShrink _).symm c.down.2).val⟩
  abs_repr {α} F := by
    ext p a
    suffices (∃ q, p ≤ q ∧ ∃ x, (equivShrink (F q)).symm x = a) ↔ a ∈ F p by simpa
    constructor
    · rintro ⟨q, h, x, rfl⟩
      exact mem_of_le _ h
    · rintro ha
      refine ⟨p, by rfl, equivShrink (F p) ⟨a, ha⟩, by simp⟩
  abs_map := by
    rintro α β m ⟨⟨C, s⟩, f⟩
    ext p b; simp [PFunctor.map]

@[simp] lemma liftp_iff {P : α → Prop} {f : NameFunctor ℙ α} :
    Functor.Liftp P f ↔ ∀ p, ∀ a ∈ f p, P a := by
  constructor
  · rintro ⟨u, rfl⟩
    intro p; simp; tauto
  · intro h
    refine ⟨
      ⟨fun p ↦ Subtype.val ⁻¹' f p,
       fun p ↦ small_preimage_of_injective Subtype.val Subtype.val_injective (f p),
       fun h ⟨a, _⟩ ha ↦ f.monotone h ha⟩, ?_⟩
    ext p a
    simp; tauto

end NameFunctor

variable (ℙ)

/-- ℙ-name for forcing notion of set theory -/
def Name : Type (u + 1) := QPF.Fix (NameFunctor ℙ)

variable {ℙ}

namespace Name

/-- constructor of name -/
noncomputable def mk (x : NameFunctor ℙ (Name ℙ)) : Name ℙ :=
  QPF.Fix.mk x

/-- destructor of name -/
noncomputable def dest (σ : Name ℙ) : NameFunctor ℙ (Name ℙ) := QPF.Fix.dest σ

/-- The underlying fibre of name -/
noncomputable def fibre (σ : Name ℙ) : ℙ → Set (Name ℙ) := σ.dest

instance fibre_small (σ : Name ℙ) (p : ℙ) : Small.{u} (σ.fibre p) := σ.dest.small p

@[simp] lemma fibre_monotone (σ : Name ℙ) : IsSetMonotone (· ≥ ·) σ.fibre := σ.dest.monotone

@[simp] lemma mk_dest (σ : Name ℙ) : .mk σ.dest = σ := QPF.Fix.mk_dest _

@[simp] lemma dest_mk (x : NameFunctor ℙ (Name ℙ)) :
    (mk x).dest = x := QPF.Fix.dest_mk x

@[simp] lemma fibre_mk (f : NameFunctor ℙ (Name ℙ)) : (mk f).fibre p = f p := by simp [fibre]

noncomputable def rec (g : NameFunctor ℙ α → α) : Name ℙ → α := QPF.Fix.rec g

lemma rec_mk (g : NameFunctor ℙ α → α) (x : NameFunctor ℙ (Name ℙ)) :
    rec g (mk x) = g (rec g <$> x) := QPF.Fix.rec_eq _ _

theorem ind
    {P : Name ℙ → Prop}
    (ind : ∀ σ, (∀ p, ∀ τ ∈ σ.fibre p, P τ) → P σ)
    (σ : Name ℙ) : P σ :=
  QPF.Fix.ind P (fun f hf ↦ ind (mk f) (by simpa using hf)) σ

end Name

end LO.FirstOrder.SetTheory
