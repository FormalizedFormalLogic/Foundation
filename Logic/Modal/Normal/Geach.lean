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

variable {α : Type u} {β : Type u}
variable [Inhabited β]

abbrev GeachTaple := ℕ × ℕ × ℕ × ℕ

namespace GeachTaple

variable (l : GeachTaple)

abbrev i := l.1

abbrev j := l.2.1

abbrev m := l.2.2.1

abbrev n := l.2.2.2

end GeachTaple

section Axioms

variable {F : Type u} [ModalLogicSymbol F]

@[simp]
def AxiomGeach (l : GeachTaple) (p : F) := (◇[l.i](□[l.m]p)) ⟶ (□[l.j](◇[l.n]p))

def AxiomGeach.set (l : GeachTaple) : AxiomSet α := { AxiomGeach l p | (p) }

namespace AxiomGeach

@[simp] lemma def_axiomT : (𝐓 : AxiomSet α) = AxiomGeach.set (0, 0, 1, 0) := by aesop;

@[simp] lemma def_axiomB : (𝐁 : AxiomSet α) = AxiomGeach.set (0, 1, 0, 1) := by aesop;

@[simp] lemma def_axiomD : (𝐃 : AxiomSet α) = AxiomGeach.set (0, 0, 1, 1) := by aesop;

@[simp] lemma def_axiom4 : (𝟒 : AxiomSet α) = AxiomGeach.set (0, 2, 1, 0) := by aesop;

@[simp] lemma def_axiom5 : (𝟓 : AxiomSet α) = AxiomGeach.set (1, 1, 0, 1) := by aesop;

@[simp] lemma def_axiomDot2 : (.𝟐 : AxiomSet α) = AxiomGeach.set (1, 1, 1, 1) := by aesop;

@[simp] lemma def_axiomC4 : (𝐂𝟒 : AxiomSet α) = AxiomGeach.set (0, 1, 2, 0) := by aesop;

@[simp] lemma def_axiomCD : (𝐂𝐃 : AxiomSet α) = AxiomGeach.set (1, 1, 0, 0) := by aesop;

end AxiomGeach

@[simp]
def GeachLogic : List (GeachTaple) → AxiomSet β
  | [] => 𝐊
  | x :: xs => (AxiomGeach.set x) ∪ (GeachLogic xs)

@[simp]
lemma GeachLogic.subsetK {l : List (GeachTaple)} : (𝐊 : AxiomSet β) ⊆ (GeachLogic l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_right (by assumption);

lemma GeachLogic.subsetK' (h : (GeachLogic l) ⊆ Λ): (𝐊 : AxiomSet β) ⊆ Λ := Set.Subset.trans GeachLogic.subsetK h

class IsGeachLogic (Λ : AxiomSet β) where
  taples : List (GeachTaple)
  char : Λ = GeachLogic taples

@[simp]
instance : IsGeachLogic (𝐊 : AxiomSet β) where
  taples := [];
  char := rfl

@[simp]
instance : IsGeachLogic (𝐊𝐃 : AxiomSet β) where
  taples := [(0, 0, 1, 1)];
  char := by simp [LogicKD]; aesop;

@[simp]
instance : IsGeachLogic (𝐊𝐓 : AxiomSet β) where
  taples := [(0, 0, 1, 0)];
  char := by simp [LogicKT]; aesop;

@[simp]
instance : IsGeachLogic (𝐊𝟒 : AxiomSet β) where
  taples := [(0, 2, 1, 0)];
  char := by simp [LogicK4]; aesop;

@[simp]
instance : IsGeachLogic (LogicKT4 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0)];
  char := by simp [LogicKT4]; aesop;

@[simp]
instance : IsGeachLogic (𝐒𝟒 : AxiomSet β) := inferInstance

@[simp]
instance : IsGeachLogic (𝐒𝟒.𝟐 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0), (1, 1, 1, 1)];
  char := by simp [LogicS4Dot2, LogicKT4]; aesop;

@[simp]
instance : IsGeachLogic (LogicKT5 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (1, 1, 0, 1)];
  char := by simp [LogicKT5]; aesop;

@[simp]
instance : IsGeachLogic (𝐒𝟓 : AxiomSet β) := inferInstance

@[simp]
instance : IsGeachLogic (𝐊𝐓𝟒𝐁 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0), (0, 1, 0, 1)];
  char := by simp [LogicKT4B]; aesop;

end Axioms

@[simp]
def GeachConfluency (l : GeachTaple) (F : Frame α) := ∀ {x y z}, (F[l.i] x y) ∧ (F[l.j] x z) → ∃ u, (F[l.m] y u) ∧ (F[l.n] z u)

@[simp]
def GeachConfluency.list (l : List (GeachTaple)) (rel : α → α → Prop) : Prop :=
  match l with
  | [] => True
  | x :: xs => (GeachConfluency x rel) ∧ (GeachConfluency.list xs rel)

namespace GeachConfluency

lemma list_single_iff : (GeachConfluency.list [l] F) ↔ GeachConfluency l F := by simp;

lemma serial_def : Serial F ↔ (GeachConfluency (0, 0, 1, 1) F) := by
  simp [Symmetric];
  aesop;

lemma reflexive_def : Reflexive F ↔ (GeachConfluency (0, 0, 1, 0) F) := by
  simp [Reflexive];

lemma symmetric_def : Symmetric F ↔ (GeachConfluency (0, 1, 0, 1) F) := by
  simp [Symmetric];
  aesop;

lemma transitive_def : Transitive F ↔ (GeachConfluency (0, 2, 1, 0) F) := by
  simp [Transitive];
  aesop;

lemma euclidean_def : Euclidean F ↔ (GeachConfluency (1, 1, 0, 1) F) := by
  simp [Euclidean];
  aesop;

lemma confluent_def : Confluent F ↔ (GeachConfluency (1, 1, 1, 1) F) := by
  simp [Confluent];

lemma extensive_def : Extensive F ↔ (GeachConfluency (0, 1, 0, 0) F) := by
  intros;
  simp [Extensive];
  constructor;
  . intro h x y z hxy hxz;
    have := h hxz;
    subst hxy this;
    trivial;
  . intro h x y hyz;
    have := h rfl hyz;
    subst this;
    trivial;

lemma functional_def : Functional F ↔ (GeachConfluency (1, 1, 0, 0) F) := by
  simp [Functional];
  aesop

lemma dense_def : Dense F  ↔ (GeachConfluency (0, 1, 2, 0) F) := by
  simp [Dense];
  aesop;

end GeachConfluency

section FrameClassDefinability

theorem AxiomGeach.defines (t : GeachTaple) (F : Frame α) : (GeachConfluency t F) ↔ (⊧ᴹ[F] (AxiomGeach.set t : AxiomSet β)) := by
  simp [AxiomGeach.set];
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
    have him : x ⊩ᴹ[M] ◇[t.i](□[t.m](Formula.atom default)) := by aesop;
    have := h (Formula.atom default) M.val x |>.modus_ponens him;
    simp only [Formula.Satisfies.multibox_def] at this;
    obtain ⟨u, hzu, hyu⟩ := by simpa using this z hj;
    existsi u;
    exact ⟨hyu, hzu⟩;

lemma AxiomGeach.FrameClassDefinability (t : GeachTaple) : FrameClassDefinability α β (AxiomGeach.set t) (GeachConfluency t) := by
  intro F;
  have := @AxiomGeach.defines α β _ t F;
  constructor;
  . intro h p hp; exact this.mp h p hp;
  . aesop;

lemma GeachLogic.FrameClassDefinabilityAux {ts : List (GeachTaple)} : FrameClassDefinability α β (GeachLogic ts) (GeachConfluency.list ts) := by
  induction ts with
  | nil => apply LogicK.FrameClassDefinability;
  | cons t ts ih =>
    simp only [GeachLogic, GeachConfluency, Normal.FrameClassDefinability, AxiomSetFrameClass.union];
    intro F;
    constructor;
    . intro h;
      exact Set.mem_inter (AxiomGeach.FrameClassDefinability t |>.mp h.1) (ih.mp h.2)
    . intro h;
      exact ⟨AxiomGeach.FrameClassDefinability t |>.mpr h.1, ih.mpr h.2⟩;

lemma GeachLogic.FrameClassDefinability [hG : IsGeachLogic Λ] : FrameClassDefinability α β Λ (GeachConfluency.list hG.taples) := by
  have := @GeachLogic.FrameClassDefinabilityAux α β _ hG.taples;
  rw [←hG.char] at this;
  simpa;

lemma LogicS4.FrameClassDefinability : FrameClassDefinability α β 𝐒𝟒 (λ F => Reflexive F ∧ Transitive F) := by
  have : Normal.FrameClassDefinability α β 𝐒𝟒 (GeachConfluency.list (IsGeachLogic.taples 𝐒𝟒)) := by apply GeachLogic.FrameClassDefinability;
  simp_all [GeachConfluency.reflexive_def, GeachConfluency.transitive_def];

end FrameClassDefinability

lemma AxiomSetFrameClass.geach {Λ : AxiomSet β} [hG : IsGeachLogic Λ] : (𝔽(Λ) : FrameClass α) = (𝔽((GeachLogic hG.taples : AxiomSet β))) := by rw [←hG.char];

namespace CanonicalModel

variable [DecidableEq β]
variable {Λ : AxiomSet β}

open Hilbert Set MaximalConsistentTheory

lemma defAxiomGeach (hK : 𝐊 ⊆ Λ) (hG : (AxiomGeach.set l) ⊆ Λ) : (GeachConfluency l) (CanonicalModel Λ).frame := by
  have := Deduction.instBoxedNecessitation hK;
  have := Deduction.ofKSubset hK;

  intro Ω₁ Ω₂ Ω₃ h;
  replace ⟨h₁₂, h₂₃⟩ := h;
  have ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory (show Theory.Consistent Λ ((□⁻¹[l.m]Ω₂.theory) ∪ (□⁻¹[l.n]Ω₃.theory)) by
    by_contra hInc;
    obtain ⟨Δ₂, Δ₃, hΔ₂, hΔ₃, hUd⟩ := inconsistent_union (by simpa only [Theory.Inconsistent_iff] using hInc);

    have h₂ : □[l.m](⋀Δ₂) ∈ Ω₂ := by
      apply context_multibox_conj_membership_iff'.mpr;
      simpa using subset_premulitibox_iff_multibox_subset hΔ₂;

    have h₃ : □[l.n](⋀Δ₃) ∈ Ω₃ := by
      apply context_multibox_conj_membership_iff'.mpr;
      simpa using subset_premulitibox_iff_multibox_subset hΔ₃;

    have : (□[l.n](⋀Δ₃)) ∉ Ω₃ := by
      have : Ω₁ ⊢ᴹ[Λ]! ◇[l.i](□[l.m](⋀Δ₂)) ⟶ □[l.j](◇[l.n](⋀Δ₂)) := Deducible.maxm! (by apply hG; simp [AxiomGeach.set]);
      have : Ω₁ ⊢ᴹ[Λ]! ◇[l.i](□[l.m](⋀Δ₂)) := membership_iff.mp $ (multiframe_dia hK |>.mp h₁₂) h₂;
      have : Ω₁ ⊢ᴹ[Λ]! □[l.j](◇[l.n](⋀Δ₂)) := modus_ponens'! (by assumption) (by assumption);
      have : □[l.j](◇[l.n](⋀Δ₂)) ∈ Ω₁ := membership_iff.mpr this;
      have : ◇[l.n](⋀Δ₂) ∈ Ω₃ := multiframe_box hK |>.mp h₂₃ (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ◇[l.n](⋀Δ₂) := membership_iff.mp (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□[l.n](~(⋀Δ₂))) := modus_ponens'! (iff_mp'! multidia_duality!) (by assumption);
      have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₂ ∪ Δ₃) := by simpa using finset_dt!.mp (by simpa using hUd);
      have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₂ ∪ Δ₃) ⟶ ~(⋀Δ₂ ⋏ ⋀Δ₃) := contra₀'! $ iff_mp'! $ finset_union_conj!;
      have : ∅ ⊢ᴹ[Λ]! (⋀Δ₂ ⋏ ⋀Δ₃) ⟶ ⊥ := modus_ponens'! (by assumption) (by assumption);
      have : ∅ ⊢ᴹ[Λ]! ~(⋀Δ₂ ⋏ ⋀Δ₃) := modus_ponens'! (contra₀'! (by assumption)) (by apply verum!);
      have : ∅ ⊢ᴹ[Λ]! ⋀Δ₃ ⟶ ~⋀Δ₂ := imp_eq!.mpr $ disj_symm'! $ neg_conj'! (by assumption);
      have : ∅ ⊢ᴹ[Λ]! □[l.n](⋀Δ₃) ⟶ □[l.n](~⋀Δ₂) := multibox_distribute_nec'! (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□[l.n](~⋀Δ₂)) ⟶ ~(□[l.n](⋀Δ₃)) := weakening! (show ∅ ⊆ Ω₃.theory by simp) $ contra₀'! (by assumption);
      have : Ω₃ ⊢ᴹ[Λ]! ~(□[l.n](⋀Δ₃)) := modus_ponens'! (by assumption) (by assumption);
      exact neg_membership_iff.mp $ membership_iff.mpr (by assumption);

    contradiction;
  );
  existsi Ω;
  simp [(multiframe_box hK)];
  constructor;
  . intro p hp;
    apply hΩ;
    have : p ∈ □⁻¹[l.m]Ω₂ := by simpa [Set.premultibox] using hp;
    simp_all;
  . intro p hp;
    apply hΩ;
    have : p ∈ □⁻¹[l.n]Ω₃ := by simpa [Set.premultibox] using hp;
    simp_all;

lemma defLogicGeach {l : List (GeachTaple)} (hG : (GeachLogic l) ⊆ Λ) : (GeachConfluency.list l) (CanonicalModel Λ).frame := by
  induction l with
  | nil => simp;
  | cons head tail ih =>
    simp only [GeachLogic, GeachConfluency.list];
    constructor;
    . exact CanonicalModel.defAxiomGeach (GeachLogic.subsetK' hG) (by aesop);
    . exact ih (by aesop);

end CanonicalModel

variable [DecidableEq β]

def GeachLogic.CanonicalModel (l : List (GeachTaple)) := Normal.CanonicalModel (GeachLogic l : AxiomSet β)

lemma GeachLogic.membership_frameclass : (CanonicalModel l).frame ∈ (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply FrameClassDefinabilityAux |>.mp;
  cases l with
  | nil => simp;
  | cons head tail =>
    simp only [GeachConfluency, GeachLogic.CanonicalModel];
    constructor;
    . exact CanonicalModel.defAxiomGeach (by simp) (by simp);
    . exact CanonicalModel.defLogicGeach (by simp);

theorem GeachLogic.kripkeCompletesAux (l : List (GeachTaple)) : KripkeCompleteness (GeachLogic l : AxiomSet β) (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel l).frame;
  constructor;
  . apply membership_frameclass;
  . existsi (CanonicalModel l).val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

lemma GeachLogic.kripkeCompletes {Λ : AxiomSet β} [hG : IsGeachLogic Λ] : KripkeCompleteness Λ (𝔽(Λ) : FrameClass (MaximalConsistentTheory Λ)) := by
  rw [hG.char];
  apply GeachLogic.kripkeCompletesAux hG.taples;

theorem LogicK.kripkeCompletes : KripkeCompleteness (LogicK : AxiomSet β) (𝔽((LogicK : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicK : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicKD.kripkeCompletes : KripkeCompleteness (LogicKD : AxiomSet β) (𝔽((LogicKD : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicKD : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS5.kripkeCompletes : KripkeCompleteness (LogicS5 : AxiomSet β) (𝔽((LogicS5 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS5 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS4.kripkeCompletes : KripkeCompleteness (LogicS4 : AxiomSet β) (𝔽((LogicS4 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS4 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS4Dot2.kripkeCompletes : KripkeCompleteness (LogicS4Dot2 : AxiomSet β) (𝔽((LogicS4Dot2 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS4Dot2 : AxiomSet β))) := GeachLogic.kripkeCompletes

end LO.Modal.Normal
