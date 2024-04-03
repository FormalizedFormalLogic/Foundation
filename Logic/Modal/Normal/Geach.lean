import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Semantics
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

@[simp] def i := l.1
@[simp] def j := l.2.1
@[simp] def m := l.2.2.1
@[simp] def n := l.2.2.2

end GeachTaple

section Axioms

variable {F : Type u} [ModalLogicSymbol F] [Multibox F] [Multidia F]

@[simp]
def AxiomGeach (l : GeachTaple) (p : F) := (◇[l.i](□[l.m]p)) ⟶ (□[l.j](◇[l.n]p))

def AxiomGeach.set (l : GeachTaple) : AxiomSet α := { AxiomGeach l p | (p) }

class IsGeachAxiom (ax : F → F) where
  taple : GeachTaple
  char : ∀ p, ax p = AxiomGeach taple p

@[simp]
instance : IsGeachAxiom (AxiomT : (Formula α) → (Formula α)) where
  taple := (0, 0, 1, 0);
  char := by simp [AxiomT];

@[simp]
instance : IsGeachAxiom (AxiomB : (Formula α) → (Formula α)) where
  taple := (0, 1, 0, 1);
  char := by simp [AxiomB]

@[simp]
instance : IsGeachAxiom (AxiomD : (Formula α) → (Formula α)) where
  taple := (0, 0, 1, 1);
  char := by simp [AxiomD]

@[simp]
instance : IsGeachAxiom (Axiom4 : (Formula α) → (Formula α)) where
  taple := (0, 2, 1, 0);
  char := by simp [Axiom4]

@[simp]
instance : IsGeachAxiom (Axiom5 : (Formula α) → (Formula α)) where
  taple := (1, 1, 0, 1);
  char := by simp [Axiom5];

@[simp]
instance : IsGeachAxiom (AxiomDot2 : (Formula α) → (Formula α)) where
  taple := (1, 1, 1, 1)
  char := by simp [AxiomDot2]

@[simp]
instance : IsGeachAxiom (AxiomC4 : (Formula α) → (Formula α)) where
  taple := (0, 1, 2, 0);
  char := by simp [AxiomC4]

@[simp]
instance : IsGeachAxiom (AxiomTc : (Formula α) → (Formula α)) where
  taple := (0, 1, 0, 0)
  char := by simp [AxiomTc]

@[simp]
instance : IsGeachAxiom (AxiomCD : (Formula α) → (Formula α)) where
  taple := (1, 1, 0, 0);
  char := by simp [AxiomCD]

@[simp]
lemma eq_IsGeachAxiom [hG : IsGeachAxiom ax] : ({ ax p | p } : AxiomSet α) = (AxiomGeach.set hG.taple) := by
  simp [hG.char];
  aesop;

@[simp]
def GeachLogic : List (GeachTaple) → AxiomSet β
  | [] => 𝐊
  | x :: xs => (GeachLogic xs) ∪ (AxiomGeach.set x)

@[simp]
lemma GeachLogic.subsetK {l : List (GeachTaple)} : (𝐊 : AxiomSet β) ⊆ (GeachLogic l) := by
  induction l with
  | nil => simp;
  | cons => simp; apply Set.subset_union_of_subset_left (by assumption);

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
  char := by simp [LogicKD]; aesop;

@[simp]
instance : IsGeachLogic (𝐊𝟒 : AxiomSet β) where
  taples := [(0, 2, 1, 0)];
  char := by aesop;

@[simp]
instance : IsGeachLogic (𝐒𝟒 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0)];
  char := by simp [LogicKT4]; aesop;

@[simp]
instance : IsGeachLogic (𝐒𝟒.𝟐 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0), (1, 1, 1, 1)];
  char := by simp [LogicS4Dot2]; sorry; -- aesop;

@[simp]
instance : IsGeachLogic (𝐒𝟓 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (1, 1, 0, 1)];
  char := by simp [LogicKT5]; aesop;

@[simp]
instance : IsGeachLogic (𝐊𝐓𝟒𝐁 : AxiomSet β) where
  taples := [(0, 0, 1, 0), (0, 2, 1, 0), (0, 1, 0, 1)];
  char := by simp [LogicKT4B]; aesop;

end Axioms

@[simp]
def GeachConfluencyAux (l : GeachTaple) (F : Frame α) := ∀ {x y z}, (F[l.i] x y) ∧ (F[l.j] x z) → ∃ u, (F[l.m] y u) ∧ (F[l.n] z u)

@[simp]
def GeachConfluency (l : List (GeachTaple)) (rel : α → α → Prop) : Prop :=
  match l with
  | [] => True
  | x :: xs => (GeachConfluencyAux x rel) ∧ (GeachConfluency xs rel)

class IsGeachConfluency (P : (α → α → Prop) → Prop) where
  taples : List (GeachTaple)
  char : ∀ (rel : α → α → Prop), P rel ↔ GeachConfluency taples rel

section GeachConfluency

@[simp]
instance : IsGeachConfluency (@Serial α) where
  taples := [(0, 0, 1, 1)];
  char := by simp [Symmetric]; aesop

@[simp]
instance : IsGeachConfluency (@Reflexive α) where
  taples := [(0, 0, 1, 0)];
  char := by simp [Reflexive];

@[simp]
instance : IsGeachConfluency (@Symmetric α) where
  taples := [(0, 1, 0, 1)];
  char := by simp [Symmetric]; aesop;

@[simp]
instance : IsGeachConfluency (@Transitive α) where
  taples := [(0, 2, 1, 0)];
  char := by simp [Transitive]; aesop

@[simp]
instance : IsGeachConfluency (@Euclidean α) where
  taples := [(1, 1, 0, 1)];
  char := by simp [Euclidean]; aesop

@[simp]
instance : IsGeachConfluency (@Confluent α) where
  taples := [(1, 1, 1, 1)]
  char := by simp [Confluent];

@[simp]
instance : IsGeachConfluency (@Extensive α) where
  taples := [(0, 1, 0, 0)];
  char := by
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

@[simp]
instance : IsGeachConfluency (@Functional α) where
  taples := [(1, 1, 0, 0)];
  char := by simp [Functional]; aesop

@[simp]
instance : IsGeachConfluency (@Dense α) where
  taples := [(0, 1, 2, 0)];
  char := by simp [Dense]; aesop

lemma subset_GeachConfluency (h : l₁ ⊆ l₂) : (GeachConfluency l₂ F) → (GeachConfluency l₁ F) := by
  induction l₁ with
  | nil => simp;
  | cons x xs ih => sorry;

end GeachConfluency

theorem AxiomGeach.defines (F : Frame α) : (GeachConfluencyAux l F) ↔ (⊧ᴹ[F] (AxiomGeach.set l : AxiomSet β)) := by
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
      val := λ v _ => F[l.m] y v
    }
    have him : x ⊩ᴹ[M] ◇[l.i](□[l.m](Formula.atom default)) := by aesop;
    have := h (Formula.atom default) M.val x |>.modus_ponens him;
    simp only [Formula.Satisfies.multibox_def] at this;
    obtain ⟨u, hzu, hyu⟩ := by simpa using this z hj;
    existsi u;
    exact ⟨hyu, hzu⟩;

lemma AxiomGeach.FrameClassDefinability : @FrameClassDefinability α β (AxiomGeach.set t) (GeachConfluencyAux t) := by
  intro F;
  have := @AxiomGeach.defines α β _ t F;
  constructor;
  . intro h p hp; exact this.mp h p hp;
  . aesop;

lemma GeachLogic.FrameClassDefinability {l : List (GeachTaple)} : @FrameClassDefinability α β (GeachLogic l) (GeachConfluency l) := by
  induction l with
  | nil => apply LogicK.FrameClassDefinability;
  | cons head tail ih =>
    simp only [GeachLogic, GeachConfluency, Normal.FrameClassDefinability, AxiomSetFrameClass.union];
    intro F;
    constructor;
    . intro h;
      exact Set.mem_inter (ih.mp h.2) (AxiomGeach.FrameClassDefinability.mp h.1)
    . intro h;
      exact ⟨AxiomGeach.FrameClassDefinability.mpr h.2, ih.mpr h.1⟩;

lemma AxiomSetFrameClass.geach
  {Λ : AxiomSet β}
  [hG : IsGeachLogic Λ]
  : (𝔽(Λ) : FrameClass α) = (𝔽((GeachLogic hG.taples : AxiomSet β))) := by
  exact Set.eq_of_subset_of_subset
    (by
      intro F hF;
      apply GeachLogic.FrameClassDefinability |>.mp;
      sorry;
    )
    (by
      intro F hF;
      have := GeachLogic.FrameClassDefinability |>.mpr hF;
      sorry;
    );

lemma AxiomSetFrameClass.geach_subset (h : l₁ ⊆ l₂) : (𝔽((GeachLogic l₂ : AxiomSet β)) : FrameClass α) ⊆ 𝔽((GeachLogic l₁ : AxiomSet β)) := by
  intro F hF;
  have := GeachLogic.FrameClassDefinability |>.mpr hF;
  apply GeachLogic.FrameClassDefinability |>.mp;
  exact subset_GeachConfluency h this;

lemma AxiomSetFrameClass.geach_subset' (h : l₁ ⊆ l₂) : (𝔽(𝐊 ∪ (GeachLogic l₂ : AxiomSet β)) : FrameClass α) ⊆ 𝔽(𝐊 ∪ (GeachLogic l₁ : AxiomSet β)) := by
  repeat rw [AxiomSetFrameClass.union];
  gcongr;
  apply geach_subset h;

namespace CanonicalModel

variable [DecidableEq β]
variable {Λ : AxiomSet β} (hK : 𝐊 ⊆ Λ)

lemma defAxiomGeach (hG : (AxiomGeach.set l) ⊆ Λ) : (GeachConfluencyAux l) (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ Ω₃ h;
  replace ⟨h₁₂, h₂₃⟩ := h;
  replace h₁₂ : ∀ {p : Formula β}, p ∈ Ω₂ → ◇[GeachTaple.i l]p ∈ Ω₁ := multiframe_dia.mp h₁₂;
  replace h₂₃ : ∀ {p : Formula β}, p ∈ Ω₃ → ◇[GeachTaple.j l]p ∈ Ω₁ := multiframe_dia.mp h₂₃;
  let U := (□[l.m]Ω₂) ∪ (□[l.n]Ω₃);
  have ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory (show Theory.Consistent Λ U by sorry);
  existsi Ω;
  simp [multiframe_box];
  constructor;
  . intro p hp;
    apply hΩ;
    left;
    sorry;
  . intro p hp;
    apply hΩ;
    right;
    sorry;

lemma defLogicGeach {l : List (GeachTaple)} (hG : (GeachLogic l) ⊆ Λ) : (GeachConfluency l) (CanonicalModel Λ).frame := by
  induction l with
  | nil => simp;
  | cons head tail ih =>
    simp only [GeachLogic, GeachConfluency];
    constructor;
    . apply CanonicalModel.defAxiomGeach; aesop;
    . exact ih (by aesop);

end CanonicalModel

variable [DecidableEq β]

def GeachLogic.CanonicalModel (l : List (GeachTaple)) := Normal.CanonicalModel (GeachLogic l : AxiomSet β)

lemma GeachLogic.membership_frameclass : (CanonicalModel l).frame ∈ (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply FrameClassDefinability.mp;
  cases l with
  | nil => simp;
  | cons head tail =>
    simp only [GeachConfluency, GeachLogic.CanonicalModel];
    constructor;
    . exact CanonicalModel.defAxiomGeach (by simp);
    . exact CanonicalModel.defLogicGeach (by simp);

theorem GeachLogic.kripkeCompletesAux (l : List (GeachTaple)) : Completeness (GeachLogic l : AxiomSet β) (𝔽((GeachLogic l : AxiomSet β)) : FrameClass (MaximalConsistentTheory (GeachLogic l : AxiomSet β))) := by
  apply completeness_def.mpr;
  intro Γ hConsisΓ;
  let ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory hConsisΓ;
  existsi (CanonicalModel l).frame;
  constructor;
  . apply membership_frameclass;
  . existsi (CanonicalModel l).val, Ω;
    apply truthlemma' (by simp) |>.mpr;
    assumption;

lemma GeachLogic.kripkeCompletes {Λ : AxiomSet β} [hG : IsGeachLogic Λ] : Completeness Λ (𝔽(Λ) : FrameClass (MaximalConsistentTheory Λ)) := by
  rw [hG.char];
  apply GeachLogic.kripkeCompletesAux hG.taples;

theorem LogicK.kripkeCompletes : Completeness (LogicK : AxiomSet β) (𝔽((LogicK : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicK : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicKD.kripkeCompletes : Completeness (LogicKD : AxiomSet β) (𝔽((LogicKD : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicKD : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS5.kripkeCompletes : Completeness (LogicS5 : AxiomSet β) (𝔽((LogicS5 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS5 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS4.kripkeCompletes : Completeness (LogicS4 : AxiomSet β) (𝔽((LogicS4 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS4 : AxiomSet β))) := GeachLogic.kripkeCompletes

theorem LogicS4Dot2.kripkeCompletes : Completeness (LogicS4Dot2 : AxiomSet β) (𝔽((LogicS4Dot2 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (LogicS4Dot2 : AxiomSet β))) := GeachLogic.kripkeCompletes

end LO.Modal.Normal
