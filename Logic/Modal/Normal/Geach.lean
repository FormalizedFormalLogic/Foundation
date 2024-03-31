import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

@[simp] lemma Formula.multibox_zero : (□[0]p) = p := by simp [multibox];
@[simp] lemma Formula.multibox_succ {n : ℕ} : (□[(n + 1)]p) = (□(□[n]p)) := by simp [multibox];

@[simp] lemma Formula.multidia_zero : (◇[0]p) = p := by simp [multidia];
@[simp] lemma Formula.multidia_succ {n : ℕ} : (◇[(n + 1)]p) = (◇(◇[n]p)) := by simp [multidia];

/-- `◇ⁱ□ᵐp ⟶ □ʲ◇ⁿq`   -/
def Geach' (p q : Formula α) : (i : ℕ) → (j : ℕ) → (m : ℕ) → (n : ℕ) → Formula α
  | 0,     0,     0,     0     => p ⟶ q
  | i + 1, 0,     0,     0     => Geach' (◇p) q i 0 0 0
  | i,     j + 1, 0,     0     => Geach' p (□q) i j 0 0
  | i,     j,     m + 1, 0     => Geach' (□p) q i j m 0
  | i,     j,     m,     n + 1 => Geach' p (◇q) i j m n

@[simp] def Geach (p: Formula α) (i j m n : ℕ) := (◇[i](□[m]p)) ⟶ (□[j](◇[n]p))

@[simp] def Geach.set (i j m n : ℕ) : AxiomSet α := { Geach p i j m n | (p) }

namespace Geach

variable (p : Formula α)

lemma def_AxiomT : AxiomT p = Geach p 0 0 1 0 := rfl

lemma def_AxiomB : AxiomB p = Geach p 0 1 0 1 := rfl

lemma def_AxiomD : AxiomD p = Geach p 0 0 1 1 := rfl

lemma def_Axiom4 : Axiom4 p = Geach p 0 2 1 0 := rfl

lemma def_Axiom5 : Axiom5 p = Geach p 1 1 0 1 := rfl

lemma def_AxiomDot2 : AxiomDot2 p = Geach p 1 1 1 1 := rfl

lemma def_AxiomCD : AxiomCD p = Geach p 1 1 0 0 := rfl

lemma def_AxiomC4 : AxiomC4 p = Geach p 0 1 2 0 := rfl

end Geach

section BinaryRelations

variable {α : Type u}

@[simp]
def Access (rel : α → α → Prop) : ℕ → α → α → Prop
| 0 => λ x y => x = y
| n + 1 => λ x y => ∃ z, (rel x z ∧ Access rel n z y)

variable (rel : α → α → Prop)

local notation:80 x:95 "≺[" i "]" y:95  => Access rel i x y

@[simp]
def GeachConfluency (i j m n : ℕ) := ∀ {x y z}, x ≺[i] y ∧ x ≺[j] z → ∃ u, y ≺[m] u ∧ z ≺[n] u

namespace GeachConfluency

lemma def_Serial : GeachConfluency rel 0 0 1 1  ↔ Serial rel := by
  simp [Serial];

lemma def_Reflexive : GeachConfluency rel 0 0 1 0 ↔ Reflexive rel := by
  simp [Reflexive];

lemma def_Symmetric : GeachConfluency rel 0 1 0 1 ↔ Symmetric rel := by
  simp [Symmetric];
  aesop;

lemma def_Transitive : GeachConfluency rel 0 2 1 0 ↔ Transitive rel := by
  simp [Transitive];
  aesop;

lemma def_Euclidean : GeachConfluency rel 1 1 0 1 ↔ Euclidean rel := by
  simp [Euclidean];
  aesop;

def _root_.Extensive := ∀ x y, rel x y → x = y

lemma def_Extensive : GeachConfluency rel 0 1 0 0 ↔ Extensive rel := by
  simp [Extensive];
  constructor;
  . intro h x y hyz;
    have := h rfl hyz;
    subst this;
    trivial;
  . intro h x y z hxy hxz;
    have := h x z hxz;
    subst hxy this;
    trivial;

end GeachConfluency

end BinaryRelations

@[simp]
lemma Formula.Satisfies.multibox_def {M : Model α β} {p : Formula β} : (w ⊩ᴹ[M] □[n]p) ↔ (∀ v, (Access M.frame n) w v → (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

@[simp]
lemma Formula.Satisfies.multidia_def {M : Model α β} {p : Formula β} : (w ⊩ᴹ[M] ◇[n]p) ↔ (∃ v, Access M.frame n w v ∧ (v ⊩ᴹ[M] p)) := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih => aesop;

variable (F : Frame α)

variable [Inhabited β]

lemma Geach.defines : (GeachConfluency F i j m n) ↔ (⊧ᴹ[F] (Geach.set i j m n : AxiomSet β)) := by
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
    -- have hm : ∀ w, Access F m y w → y ⊩ᴹ[M] □[m](Formula.atom default) := by simp;
    have him : x ⊩ᴹ[M] ◇[i]□[m](Formula.atom default) := by aesop;
    have := h (Formula.atom default) M.val x |>.modus_ponens him;
    simp only [Formula.Satisfies.multibox_def] at this;
    obtain ⟨u, hzu, hyu⟩ := by simpa using this z hj;
    existsi u;
    exact ⟨hyu, hzu⟩;

end LO.Modal.Normal
