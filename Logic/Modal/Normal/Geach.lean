import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

@[simp] def AxiomGeach (p: Formula α) (i j m n : ℕ) := (◇[i](□[m]p)) ⟶ (□[j](◇[n]p))

@[simp] def AxiomGeach.set (i j m n : ℕ) : AxiomSet α := { AxiomGeach p i j m n | (p) }

variable {α : Type u} {β : Type u}
variable [Inhabited β]

/--
variable (rel : α → α → Prop)
local infix:95 "≺" => rel
-/

@[simp]
def Access (rel : Frame α) : ℕ → α → α → Prop
| 0 => (· = ·)
| n + 1 => λ x y => ∃ z, (rel x z ∧ Access rel n z y)

@[simp]
def GeachConfluency (i j m n : ℕ) (F : Frame α) := ∀ {x y z}, (Access F i x y) ∧ (Access F j x z) → ∃ u, (Access F m y u) ∧ (Access F n z u)

namespace Formula

@[simp] lemma multibox_zero : (□[0]p) = p := by simp [multibox];
@[simp] lemma multibox_succ {n : ℕ} : (□[(n + 1)]p) = (□(□[n]p)) := by simp [multibox];

@[simp] lemma multidia_zero : (◇[0]p) = p := by simp [multidia];
@[simp] lemma multidia_succ {n : ℕ} : (◇[(n + 1)]p) = (◇(◇[n]p)) := by simp [multidia];

namespace Satisfies

variable {M : Model α β} {p : Formula β}

@[simp]
lemma multibox_def : (w ⊩ᴹ[M] □[n]p) ↔ (∀ v, (Access M.frame n) w v → (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

@[simp]
lemma multidia_def : (w ⊩ᴹ[M] ◇[n]p) ↔ (∃ v, Access M.frame n w v ∧ (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

end Satisfies

end Formula

theorem Geach.defines (F : Frame α) : (GeachConfluency i j m n F) ↔ (⊧ᴹ[F] (AxiomGeach.set i j m n : AxiomSet β)) := by
  simp;
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
      val := λ v _ => Access F m y v
    }
    have him : x ⊩ᴹ[M] ◇[i]□[m](Formula.atom default) := by aesop;
    have := h (Formula.atom default) M.val x |>.modus_ponens him;
    simp only [Formula.Satisfies.multibox_def] at this;
    obtain ⟨u, hzu, hyu⟩ := by simpa using this z hj;
    existsi u;
    exact ⟨hyu, hzu⟩;

lemma _root_.Serial.geach : Serial rel ↔ GeachConfluency 0 0 1 1 rel := by
  simp [Serial];

lemma AxiomD.geach : AxiomD p = AxiomGeach p 0 0 1 1 := rfl

@[simp]
lemma AxiomD.set.geach : (AxiomD.set : AxiomSet β) = AxiomGeach.set 0 0 1 1 := rfl

lemma AxiomD.defines' : (Serial F) ↔ (⊧ᴹ[F] (AxiomD.set : AxiomSet β)) := by
  rw [Serial.geach, AxiomD.set.geach];
  apply Geach.defines;


lemma AxiomT.geach : AxiomT p = AxiomGeach p 0 0 1 0 := rfl

@[simp]
lemma AxiomT.set.geach : (AxiomT.set : AxiomSet β) = AxiomGeach.set 0 0 1 0 := rfl

lemma _root_.Reflexive.geach : Reflexive rel ↔ GeachConfluency 0 0 1 0 rel := by
  simp [Reflexive];

lemma AxiomT.defines' : (Reflexive F) ↔ (⊧ᴹ[F] (AxiomT.set : AxiomSet β)) := by
  rw [Reflexive.geach, AxiomT.set.geach];
  apply Geach.defines;


lemma AxiomB.geach : AxiomB p = AxiomGeach p 0 1 0 1 := rfl

@[simp]
lemma AxiomB.set.geach : (AxiomB.set : AxiomSet β) = AxiomGeach.set 0 1 0 1 := rfl

lemma _root_.Symmetric.geach : Symmetric rel ↔ GeachConfluency 0 1 0 1 rel := by
  simp [Symmetric];
  aesop;

lemma AxiomB.defines' : (Symmetric F) ↔ (⊧ᴹ[F] (AxiomB.set : AxiomSet β)) := by
  rw [Symmetric.geach, AxiomB.set.geach];
  apply Geach.defines;


lemma Axiom4.geach : Axiom4 p = AxiomGeach p 0 2 1 0 := rfl

@[simp]
lemma Axiom4.set.geach : (Axiom4.set : AxiomSet β) = AxiomGeach.set 0 2 1 0 := rfl

lemma _root_.Transitive.geach : Transitive rel ↔ GeachConfluency 0 2 1 0 rel := by
  simp [Transitive];
  aesop;

lemma Axiom4.defines' : (Transitive F) ↔ (⊧ᴹ[F] (Axiom4.set : AxiomSet β)) := by
  rw [Transitive.geach, Axiom4.set.geach];
  apply Geach.defines;


lemma Axiom5.geach : Axiom5 p = AxiomGeach p 1 1 0 1 := rfl

@[simp]
lemma Axiom5.set.geach : (Axiom5.set : AxiomSet β) = AxiomGeach.set 1 1 0 1 := rfl

lemma _root_.Euclidean.geach : Euclidean rel ↔ GeachConfluency 1 1 0 1 rel := by
  simp [Euclidean];
  aesop;

lemma Axiom5.defines' : (Euclidean F) ↔ (⊧ᴹ[F] (Axiom5.set : AxiomSet β)) := by
  rw [Euclidean.geach, Axiom5.set.geach];
  apply Geach.defines;


lemma AxiomDot2.geach : AxiomDot2 p = AxiomGeach p 1 1 1 1 := rfl

@[simp]
lemma AxiomDot2.set.geach : (AxiomDot2.set : AxiomSet β) = AxiomGeach.set 1 1 1 1 := rfl

lemma _root_.Confluent.geach : Confluent rel ↔ GeachConfluency 1 1 1 1 rel := by simp [Confluent];

lemma AxiomDot2.defines' : (Confluent F) ↔ (⊧ᴹ[F] (AxiomDot2.set : AxiomSet β)) := by
  rw [Confluent.geach, AxiomDot2.set.geach];
  apply Geach.defines;


def AxiomTc [ModalLogicSymbol F] (p : F) := p ⟶ □p

def AxiomTc.set : AxiomSet α := { AxiomTc p | p }

notation "𝐓𝐜" => AxiomTc.set

@[simp] lemma AxiomTc.set.include : (AxiomTc p) ∈ 𝐓𝐜 := by simp [set];

@[simp]
lemma AxiomTc.set.geach : (AxiomTc.set : AxiomSet β) = AxiomGeach.set 0 1 0 0 := rfl

def _root_.Extensive (F : α → α → Prop) := ∀ ⦃x y⦄, F x y → x = y

lemma _root_.Extensive.geach : Extensive rel ↔ GeachConfluency 0 1 0 0 rel := by
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

lemma AxiomTc.defines' : (Extensive F) ↔ (⊧ᴹ[F] (AxiomTc.set : AxiomSet β)) := by
  rw [Extensive.geach, AxiomTc.set.geach];
  apply Geach.defines;


lemma _root_.Functional.geach : Functional rel ↔ GeachConfluency 1 1 0 0 rel := by simp [Functional]; aesop;

lemma AxiomCD.geach : AxiomCD p = AxiomGeach p 1 1 0 0 := rfl

@[simp]
lemma AxiomCD.set.geach : (AxiomCD.set : AxiomSet β) = AxiomGeach.set 1 1 0 0 := rfl

lemma AxiomCD.defines' : (Functional F) ↔ (⊧ᴹ[F] (AxiomCD.set : AxiomSet β)) := by
  rw [Functional.geach, AxiomCD.set.geach];
  apply Geach.defines;


lemma AxiomC4.geach : AxiomC4 p = AxiomGeach p 0 1 2 0 := rfl

@[simp]
lemma AxiomC4.set.geach : (AxiomC4.set : AxiomSet β) = AxiomGeach.set 0 1 2 0 := rfl

lemma _root_.Dense.geach : Dense rel ↔ GeachConfluency 0 1 2 0 rel := by
  simp [Dense];
  aesop;

lemma AxiomC4.defines' : (Dense F) ↔ (⊧ᴹ[F] (AxiomC4.set : AxiomSet β)) := by
  rw [Dense.geach, AxiomC4.set.geach];
  apply Geach.defines;


@[simp]
def GeachLogic : List (ℕ × ℕ × ℕ × ℕ) → Set (Formula α)
  | [] => 𝐊
  | (i, j, m, n) :: xs => (GeachLogic xs) ∪ (AxiomGeach.set i j m n)

lemma LogicK.geach : (LogicK : AxiomSet β) = (GeachLogic []) := rfl

lemma LogicKD.geach : (LogicKD : AxiomSet β) = (GeachLogic [(0, 0, 1, 1)]) := by simp [LogicKD];

def LogicKT : AxiomSet α := 𝐊 ∪ 𝐓

lemma LogicKT.geach : (LogicKT : AxiomSet β) = (GeachLogic [(0, 0, 1, 0)]) := by simp [LogicKT];

lemma LogicKT4.geach : (LogicKT4 : AxiomSet β) = (GeachLogic [(0, 0, 1, 0), (0, 2, 1, 0)]) := by
  simp [LogicKT4];
  aesop;

lemma LogicS4.geach : (LogicS4 : AxiomSet β) = (GeachLogic [(0, 0, 1, 0), (0, 2, 1, 0)]) := by apply LogicKT4.geach;

lemma LogicS4Dot2.geach : (LogicS4Dot2 : AxiomSet β) = (GeachLogic [(0, 0, 1, 0), (0, 2, 1, 0), (1, 1, 1, 1)]) := by
  simp [LogicKT4, LogicS4Dot2];
  aesop;

lemma LogicS5.geach : (LogicS5 : AxiomSet β) = (GeachLogic [(0, 0, 1, 0), (1, 1, 0, 1)]) := by
  simp [LogicKT5];
  aesop;


@[simp]
def GeachConfluency.list (l : List (ℕ × ℕ × ℕ × ℕ)) (rel : α → α → Prop) : Prop :=
  match l with
  | [] => True
  | (i, j, m, n) :: xs => (GeachConfluency i j m n rel) ∧ (GeachConfluency.list xs rel)


lemma AxiomGeach.FrameClassDefinability {i j m n : ℕ} : @FrameClassDefinability α β (AxiomGeach.set i j m n) (GeachConfluency i j m n) := by
  intro F;
  have := @Geach.defines α β _ i j m n F;
  constructor;
  . intro h p hp; exact this.mp h p hp;
  . aesop;

lemma GeachLogic.FrameClassDefinability {l : List (ℕ × ℕ × ℕ × ℕ)} : @FrameClassDefinability α β (GeachLogic l) (GeachConfluency.list l) := by
  induction l with
  | nil => simp; apply LogicK.FrameClassDefinability;
  | cons head tail ih =>
    simp only [GeachLogic, GeachConfluency.list, Normal.FrameClassDefinability, AxiomSetFrameClass.union];
    intro F;
    constructor;
    . intro h;
      exact Set.mem_inter (ih.mp h.2) (AxiomGeach.FrameClassDefinability.mp h.1)
    . intro h;
      exact ⟨AxiomGeach.FrameClassDefinability.mpr h.2, ih.mpr h.1⟩;

end LO.Modal.Normal
