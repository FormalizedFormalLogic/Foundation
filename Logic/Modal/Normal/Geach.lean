import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness

/-!
  The soundness and (Kripke) completeness of Geach Logic (general term for normal modal logics by characterized by Geach axioms).
-/

namespace LO.Modal.Normal

open Finset

variable {α : Type u} {β : Type u}
variable [Inhabited β]

structure GeachTaple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

abbrev GeachTapleList := List GeachTaple

section Axioms

variable {F : Type u} [StandardModalLogicalConnective F]

abbrev axiomGeach (l : GeachTaple) (p : F) := (◇^[l.i](□^[l.m]p)) ⟶ (□^[l.j](◇^[l.n]p))

abbrev AxiomSet.Geach (l : GeachTaple) : AxiomSet α := { axiomGeach l p | (p) }

namespace AxiomGeach

@[simp] lemma def_axiomT : (𝐓 : AxiomSet α) = AxiomSet.Geach ⟨0, 0, 1, 0⟩ := by aesop;

@[simp] lemma def_axiomB : (𝐁 : AxiomSet α) = AxiomSet.Geach ⟨0, 1, 0, 1⟩ := by aesop;

@[simp] lemma def_axiomD : (𝐃 : AxiomSet α) = AxiomSet.Geach ⟨0, 0, 1, 1⟩ := by aesop;

@[simp] lemma def_axiomFour : (𝟒 : AxiomSet α) = AxiomSet.Geach ⟨0, 2, 1, 0⟩ := by aesop;

@[simp] lemma def_axiom5 : (𝟓 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 0, 1⟩ := by aesop;

@[simp] lemma def_axiomDot2 : (.𝟐 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 1, 1⟩ := by aesop;

@[simp] lemma def_axiomC4 : (𝐂𝟒 : AxiomSet α) = AxiomSet.Geach ⟨0, 1, 2, 0⟩ := by aesop;

@[simp] lemma def_axiomCD : (𝐂𝐃 : AxiomSet α) = AxiomSet.Geach ⟨1, 1, 0, 0⟩ := by aesop;

end AxiomGeach

@[simp]
def GeachLogic : GeachTapleList → AxiomSet β
  | [] => 𝐊
  | x :: xs => (AxiomSet.Geach x) ∪ (GeachLogic xs)

@[simp]
lemma GeachLogic.subsetK {l : GeachTapleList} : (𝐊 : AxiomSet β) ⊆ (GeachLogic l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_right (by assumption);

lemma GeachLogic.subsetK' (h : (GeachLogic l) ⊆ Λ): (𝐊 : AxiomSet β) ⊆ Λ := Set.Subset.trans GeachLogic.subsetK h

class Geach (Λ : AxiomSet β) where
  taples : GeachTapleList
  char : Λ = GeachLogic taples

@[simp]
instance : Geach (𝐊 : AxiomSet β) where
  taples := [];
  char := rfl

@[simp]
instance : Geach (𝐊𝐃 : AxiomSet β) where
  taples := [⟨0, 0, 1, 1⟩];
  char := by simp [AxiomSet.KD]; aesop;

@[simp]
instance : Geach (𝐊𝐓 : AxiomSet β) where
  taples := [⟨0, 0, 1, 0⟩];
  char := by simp [AxiomSet.KT]; aesop;

@[simp]
instance : Geach (𝐊𝟒 : AxiomSet β) where
  taples := [⟨0, 2, 1, 0⟩];
  char := by simp [AxiomSet.K4]; aesop;

@[simp]
instance : Geach (AxiomSet.KT4 : AxiomSet β) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩];
  char := by simp [AxiomSet.KT4]; aesop;

@[simp]
instance : Geach (𝐒𝟒 : AxiomSet β) := inferInstance

@[simp]
instance : Geach (𝐒𝟒.𝟐 : AxiomSet β) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩];
  char := by simp [AxiomSet.S4Dot2, AxiomSet.KT4]; aesop;

@[simp]
instance : Geach (AxiomSet.KT5 : AxiomSet β) where
  taples := [⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩];
  char := by simp [AxiomSet.KT5]; aesop;

@[simp]
instance : Geach (𝐒𝟓 : AxiomSet β) := inferInstance

@[simp]
instance : Geach (𝐊𝐓𝟒𝐁 : AxiomSet β) where
  taples := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩];
  char := by simp [AxiomSet.KT4B]; aesop;

end Axioms

def GeachConfluency (l : GeachTaple) (F : Frame α) := ∀ {x y z}, (F[l.i] x y) ∧ (F[l.j] x z) → ∃ u, (F[l.m] y u) ∧ (F[l.n] z u)

@[simp]
def GeachConfluencyList (l : GeachTapleList) (rel : α → α → Prop) : Prop :=
  match l with
  | [] => True
  | x :: xs => (GeachConfluency x rel) ∧ (GeachConfluencyList xs rel)

namespace GeachConfluency

lemma list_single_iff : (GeachConfluencyList [l] F) ↔ GeachConfluency l F := by simp;

@[simp]
lemma serial_def : (GeachConfluency ⟨0, 0, 1, 1⟩ F) ↔ Serial F := by
  simp [GeachConfluency, Symmetric];
  aesop;

@[simp]
lemma reflexive_def : (GeachConfluency ⟨0, 0, 1, 0⟩ F) ↔ Reflexive F := by
  simp [GeachConfluency, Reflexive];

@[simp]
lemma symmetric_def : (GeachConfluency ⟨0, 1, 0, 1⟩ F) ↔ Symmetric F := by
  simp [GeachConfluency, Symmetric];
  aesop;

@[simp]
lemma transitive_def : (GeachConfluency ⟨0, 2, 1, 0⟩ F) ↔ Transitive F := by
  simp [GeachConfluency, Transitive];
  aesop;

@[simp]
lemma euclidean_def : (GeachConfluency ⟨1, 1, 0, 1⟩ F) ↔ Euclidean F := by
  simp [GeachConfluency, Euclidean];
  aesop;

@[simp]
lemma confluent_def : (GeachConfluency ⟨1, 1, 1, 1⟩ F) ↔ Confluent F := by
  simp [GeachConfluency, Confluent];

@[simp]
lemma extensive_def : (GeachConfluency ⟨0, 1, 0, 0⟩ F) ↔ Extensive F := by
  intros;
  simp [GeachConfluency, Extensive];
  constructor;
  . intro h x y hyz;
    have := h rfl hyz;
    subst this;
    trivial;
  . intro h x y z hxy hxz;
    have := h hxz;
    subst hxy this;
    trivial;

@[simp]
lemma functional_def : Functional F ↔ (GeachConfluency ⟨1, 1, 0, 0⟩ F) := by
  simp [GeachConfluency, Functional];
  aesop

@[simp]
lemma dense_def : Dense F  ↔ (GeachConfluency ⟨0, 1, 2, 0⟩ F) := by
  simp [GeachConfluency, Dense];
  aesop;

end GeachConfluency

section FrameClassDefinability

theorem AxiomGeach.defines (t : GeachTaple) (F : Frame α) : (GeachConfluency t F) ↔ (⊧ᴹ[F] (AxiomSet.Geach t : AxiomSet β)) := by
  simp [AxiomSet.Geach, GeachConfluency];
  constructor;
  . intro h p V x;
    simp only [Formula.Satisfies.imp_def'];
    intro him;
    obtain ⟨y, hy, hpy⟩ := by simpa only [Formula.Satisfies.multidia_def] using him;
    simp;
    intro z hxz;
    obtain ⟨u, ⟨hyu, hzu⟩⟩ := h hy hxz;
    existsi u;
    constructor;
    . exact hzu;
    . simp at hpy;
      exact hpy u hyu;
  . intro h x y z hi hj;
    let M : Model α β := {
      frame := F,
      val := λ v _ => F[t.m] y v
    }
    have him : x ⊩ᴹ[M] ◇^[t.i](□^[t.m](Formula.atom default)) := by aesop;
    have := h (Formula.atom default) M.val x |>.modus_ponens him;
    simp only [Formula.Satisfies.multibox_def] at this;
    obtain ⟨u, hzu, hyu⟩ := by simpa using this z hj;
    existsi u;
    exact ⟨hyu, hzu⟩;

lemma AxiomGeach.frameClassDefinability (t : GeachTaple) : AxiomSetDefinability α β (AxiomSet.Geach t) (GeachConfluency t) := by
  intro F;
  have := @AxiomGeach.defines α β _ t F;
  constructor;
  . intro h p hp; exact this.mp h p hp;
  . aesop;

lemma GeachLogic.frameClassDefinability_aux {ts : GeachTapleList} : AxiomSetDefinability α β (GeachLogic ts) (GeachConfluencyList ts) := by
  induction ts with
  | nil => apply AxiomSet.K.defines;
  | cons t ts ih =>
    simp only [GeachLogic, GeachConfluency];
    apply AxiomSetDefinability.union;
    . apply AxiomGeach.frameClassDefinability;
    . apply ih;

lemma GeachLogic.frameClassDefinability [hG : Geach Λ] : AxiomSetDefinability α β Λ (GeachConfluencyList hG.taples) := by
  have := @GeachLogic.frameClassDefinability_aux α β _ hG.taples;
  rw [←hG.char] at this;
  simpa;

lemma AxiomSet.S4.frameClassDefinability : AxiomSetDefinability α β 𝐒𝟒 (λ F => Reflexive F ∧ Transitive F) := by
  have : AxiomSetDefinability α β 𝐒𝟒 (GeachConfluencyList (Geach.taples 𝐒𝟒)) := by apply GeachLogic.frameClassDefinability;
  simp_all;

end FrameClassDefinability

lemma AxiomSetFrameClass.geach {Λ : AxiomSet β} [hG : Geach Λ] : (𝔽(Λ) : FrameClass α) = (𝔽((GeachLogic hG.taples : AxiomSet β))) := by rw [←hG.char];

namespace CanonicalModel

variable [DecidableEq β]
variable {Λ : AxiomSet β}

open Hilbert Set MaximalConsistentTheory

lemma def_axiomGeach (hK : 𝐊 ⊆ Λ) (hG : (AxiomSet.Geach l) ⊆ Λ) : (GeachConfluency l) (CanonicalModel Λ).frame := by
  have := Deduction.instBoxedNecessitation hK;
  have := Deduction.ofKSubset hK;

  intro Ω₁ Ω₂ Ω₃ h;
  replace ⟨h₁₂, h₂₃⟩ := h;
  have ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory (show Theory.Consistent Λ ((□⁻¹^[l.m]Ω₂.theory) ∪ (□⁻¹^[l.n]Ω₃.theory)) by
    by_contra hInc;
    obtain ⟨Δ₂, Δ₃, hΔ₂, hΔ₃, hUd⟩ := inconsistent_union (by simpa only [Theory.Inconsistent_iff] using hInc);

    have h₂ : □^[l.m](⋀Δ₂) ∈ Ω₂ := by -- TODO: refactor
      apply context_multibox_conj_membership_iff' hK |>.mpr;
      have : □^[l.m](↑Δ₂ : Theory β) ⊆ Ω₂ := subset_premulitimop_iff_multimop_subset hΔ₂;
      simp only [←Finset.premultimop_coe] at this;
      intro p hp;
      exact this $ multimop_mem_coe.mp hp;

    have h₃ : □^[l.n](⋀Δ₃) ∈ Ω₃ := by -- TODO: refactor
      apply context_multibox_conj_membership_iff' hK |>.mpr;
      have : □^[l.n](↑Δ₃ : Theory β) ⊆ Ω₃ := subset_premulitimop_iff_multimop_subset hΔ₃;
      simp only [←Finset.premultimop_coe] at this;
      intro p hp;
      exact this $ multimop_mem_coe.mp hp;

    have : (□^[l.n](⋀Δ₃)) ∉ Ω₃ := by
      have : Ω₁ ⊢ᴹ[Λ]! ◇^[l.i](□^[l.m](⋀Δ₂)) ⟶ □^[l.j](◇^[l.n](⋀Δ₂)) := Deducible.maxm! (by apply hG; simp [AxiomSet.Geach]);
      have : Ω₁ ⊢ᴹ[Λ]! ◇^[l.i](□^[l.m](⋀Δ₂)) := membership_iff.mp $ (multiframe_dia hK |>.mp h₁₂) h₂;
      have : Ω₁ ⊢ᴹ[Λ]! □^[l.j](◇^[l.n](⋀Δ₂)) := (by assumption) ⨀ (by assumption);
      have : □^[l.j](◇^[l.n](⋀Δ₂)) ∈ Ω₁ := membership_iff.mpr this;
      have : ◇^[l.n](⋀Δ₂) ∈ Ω₃ := multiframe_box hK |>.mp h₂₃ (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ◇^[l.n](⋀Δ₂) := membership_iff.mp (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□^[l.n](~(⋀Δ₂))) := (iff_mp'! multidia_duality!) ⨀ (by assumption);
      have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₂ ∪ Δ₃) := by simpa [NegDefinition.neg] using finset_dt!.mp (by simpa using hUd);
      have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₂ ∪ Δ₃) ⟶ ~(⋀Δ₂ ⋏ ⋀Δ₃) := contra₀'! $ iff_mpr'! $ finset_union_conj!;
      have : ∅ ⊢ᴹ[Λ]! (⋀Δ₂ ⋏ ⋀Δ₃) ⟶ ⊥ := (by assumption) ⨀ (by assumption);
      have : ∅ ⊢ᴹ[Λ]! ~(⋀Δ₂ ⋏ ⋀Δ₃) := (contra₀'! (by assumption)) ⨀ (by deduct);
      have : ∅ ⊢ᴹ[Λ]! ⋀Δ₃ ⟶ ~⋀Δ₂ := imp_eq!.mpr $ disj_symm'! $ neg_conj'! (by assumption);
      have : ∅ ⊢ᴹ[Λ]! □^[l.n](⋀Δ₃) ⟶ □^[l.n](~⋀Δ₂) := multibox_distribute_nec'! (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□^[l.n](~⋀Δ₂)) ⟶ ~(□^[l.n](⋀Δ₃)) := weakening! (show ∅ ⊆ Ω₃.theory by simp) $ contra₀'! (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□^[l.n](⋀Δ₃)) := (by assumption) ⨀ (by assumption);
      exact neg_membership_iff.mp $ membership_iff.mpr (by assumption);

    contradiction;
  );
  existsi Ω;
  simp [(multiframe_box hK)];
  constructor;
  . intro p hp;
    apply hΩ;
    have : p ∈ □⁻¹^[l.m]Ω₂ := by simpa [Set.premultibox] using hp;
    simp_all;
  . intro p hp;
    apply hΩ;
    have : p ∈ □⁻¹^[l.n]Ω₃ := by simpa [Set.premultibox] using hp;
    simp_all;

lemma def_logicGeach {l : GeachTapleList} (hG : (GeachLogic l) ⊆ Λ) : (GeachConfluencyList l) (CanonicalModel Λ).frame := by
  induction l with
  | nil => simp;
  | cons head tail ih =>
    simp only [GeachLogic, GeachConfluencyList];
    constructor;
    . exact CanonicalModel.def_axiomGeach (GeachLogic.subsetK' hG) (by aesop);
    . exact ih (by aesop);

end CanonicalModel

variable [DecidableEq β]

def GeachLogic.CanonicalModel (l : GeachTapleList) := Normal.CanonicalModel (GeachLogic l : AxiomSet β)

lemma GeachLogic.membership_frameclass : (CanonicalModel l).frame ∈ (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply frameClassDefinability_aux |>.mp;
  cases l with
  | nil => simp;
  | cons head tail =>
    simp only [GeachConfluency, GeachLogic.CanonicalModel];
    constructor;
    . exact CanonicalModel.def_axiomGeach (by simp) (by simp);
    . exact CanonicalModel.def_logicGeach (by simp);

theorem GeachLogic.kripkeCompletesAux (l : GeachTapleList) : KripkeCompleteness (GeachLogic l : AxiomSet β) (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel l).frame;
  constructor;
  . apply membership_frameclass;
  . existsi (CanonicalModel l).val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

lemma GeachLogic.kripkeCompletes {Λ : AxiomSet β} [hG : Geach Λ] : KripkeCompleteness Λ (𝔽(Λ) : FrameClass (MaximalConsistentTheory Λ)) := by
  rw [hG.char];
  apply GeachLogic.kripkeCompletesAux hG.taples;

theorem LogicK.kripkeCompletes : KripkeCompleteness (𝐊 : AxiomSet β) (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem AxiomSet.KD.kripkeCompletes : KripkeCompleteness (𝐊𝐃 : AxiomSet β) (𝔽((𝐊𝐃 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊𝐃 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem AxiomSet.S4.kripkeCompletes : KripkeCompleteness (𝐒𝟒 : AxiomSet β) (𝔽((𝐒𝟒 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐒𝟒 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem AxiomSet.S4Dot2.kripkeCompletes : KripkeCompleteness (𝐒𝟒.𝟐 : AxiomSet β) (𝔽((𝐒𝟒.𝟐 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐒𝟒.𝟐 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem AxiomSet.S5.kripkeCompletes : KripkeCompleteness (𝐒𝟓 : AxiomSet β) (𝔽((𝐒𝟓 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐒𝟓 : AxiomSet β))) := GeachLogic.kripkeCompletes

end LO.Modal.Normal
