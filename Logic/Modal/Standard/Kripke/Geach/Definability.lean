import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

open System
open System.Axioms (Geach)

variable [Inhabited W] [Inhabited α]

def Kripke.GeachConfluent (l : Geach.Taple) : Kripke.FrameProperty α := λ F => ∀ {x y z}, (F^[l.i] x y) ∧ (F^[l.j] x z) → ∃ u, (F^[l.m] y u) ∧ (F^[l.n] z u)

@[simp]
def Kripke.MultiGeachConfluent (l : List Geach.Taple) : Kripke.FrameProperty α :=
  match l with
  | [] => λ _ => True
  | x :: xs => λ F => (GeachConfluent x F) ∧ (MultiGeachConfluent xs F)

namespace Kripke.GeachConfluent

variable {F : Kripke.Frame W α}

@[simp]
lemma serial_def : (GeachConfluent ⟨0, 0, 1, 1⟩ F) ↔ Serial F := by
  simp [GeachConfluent, Symmetric];
  aesop;

@[simp]
lemma reflexive_def : (GeachConfluent ⟨0, 0, 1, 0⟩ F) ↔ Reflexive F := by
  simp [GeachConfluent, Reflexive];

@[simp]
lemma symmetric_def : (GeachConfluent ⟨0, 1, 0, 1⟩ F) ↔ Symmetric F := by
  simp [GeachConfluent, Symmetric];
  aesop;

@[simp]
lemma transitive_def : (GeachConfluent ⟨0, 2, 1, 0⟩ F) ↔ Transitive F := by
  simp [GeachConfluent, Transitive];
  aesop;

@[simp]
lemma euclidean_def : (GeachConfluent ⟨1, 1, 0, 1⟩ F) ↔ Euclidean F := by
  simp [GeachConfluent, Euclidean];
  aesop;

@[simp]
lemma confluent_def : (GeachConfluent ⟨1, 1, 1, 1⟩ F) ↔ Confluent F := by
  simp [GeachConfluent, Confluent];

@[simp]
lemma extensive_def : (GeachConfluent ⟨0, 1, 0, 0⟩ F) ↔ Extensive F := by
  intros;
  simp [GeachConfluent, Extensive];
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
lemma functional_def : Functional F ↔ (GeachConfluent ⟨1, 1, 0, 0⟩ F) := by
  simp [GeachConfluent, Functional];
  aesop

@[simp]
lemma dense_def : Dense F  ↔ (GeachConfluent ⟨0, 1, 2, 0⟩ F) := by
  simp [GeachConfluent, Dense];
  aesop;

lemma multiframe_trivial_frame : (@Multiframe PUnit α inferInstance (λ _ _ => True) n x y) ↔ (x = y) := by induction n <;> simp_all;

@[simp]
lemma trivial_frame : GeachConfluent (W := PUnit) (α := α) t (λ _ _ => True) := by simp [GeachConfluent, multiframe_trivial_frame];

end Kripke.GeachConfluent

namespace Kripke.MultiGeachConfluent

@[simp]
lemma trivial_frame : MultiGeachConfluent (W := PUnit) (α := α) l (λ _ _ => True) := by induction l <;> simp [MultiGeachConfluent, *];

end Kripke.MultiGeachConfluent


open Kripke
open Formula Formula.Kripke
open AxiomSet

variable {Ax : AxiomSet α}

instance AxiomSet.Geach.definability (t) : Definability (α := α) 𝗴𝗲(t) (GeachConfluent t) where
  defines W _ F := by
    simp [AxiomSet.Geach, GeachConfluent, Geach];
    constructor;
    . intro h x y z hi hj;
      let M : Model W α := {
        frame := F,
        valuation := λ v _ => F^[t.m] y v
      }
      have him : (M, x) ⊧ ◇^[t.i](□^[t.m](Formula.atom default)) := by
        apply Satisfies.multidia_def.mpr;
        existsi y;
        constructor;
        . simpa;
        . apply Satisfies.multibox_def.mpr; aesop;
      have : (M, x) ⊧ □^[t.j](◇^[t.n]atom default) := (Semantics.Tarski.realize_imp.mp (h (Formula.atom default) M.valuation x)) him;
      have : (M, z) ⊧ ◇^[t.n]atom default := Satisfies.multibox_def.mp this z hj;
      obtain ⟨u, hzu, hyu⟩ := Satisfies.multidia_def.mp this;
      existsi u;
      exact ⟨hyu, hzu⟩;
    . intro h p V w;
      simp only [Semantics.Tarski.realize_imp, Satisfies.multibox_def];
      intro him;
      obtain ⟨y, hy, hpy⟩ := Satisfies.multidia_def.mp him;
      intro z hxz;
      obtain ⟨u, hyu, hzu⟩ := h hy hxz;
      apply Satisfies.multidia_def.mpr;
      existsi u;
      constructor;
      . assumption;
      . exact Satisfies.multibox_def.mp hpy u hyu;

instance AxiomSet.IsGeach.definability [Ax.IsGeach] : Definability Ax (Kripke.GeachConfluent (IsGeach.taple Ax)) where
  defines W _ F := by convert (AxiomSet.Geach.definability _ |>.defines W F); exact IsGeach.char;

instance AxiomSet.MultiGeach.definability (l) : Definability (α := α) 𝗚𝗲(l) (Kripke.MultiGeachConfluent l) where
  defines W _ F := by
    induction l with
    | nil => apply AxiomSet.K.definability.defines;
    | cons t ts ih =>
      simp only [MultiGeach.iff_cons, Semantics.RealizeSet.union_iff, MultiGeachConfluent];
      constructor;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact AxiomSet.Geach.definability t |>.defines W F |>.mp ht;
        . apply ih.mp hts;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact AxiomSet.Geach.definability t |>.defines W F |>.mpr ht;
        . apply ih.mpr hts;

namespace Kripke

variable {L : DeductionParameter α} [L.HasNec]

instance instGeachDefinability [geach : L.IsGeach] : Definability Ax(L) (Kripke.MultiGeachConfluent geach.taples) := by
  convert AxiomSet.MultiGeach.definability (α := α) geach.taples;
  simp;

instance : FiniteFrameClass.Nonempty (α := α) 𝔽(𝗚𝗲(l))ꟳ where
  W := PUnit;
  W_inhabited := inferInstance;
  W_finite := inferInstance;
  existsi := by
    existsi (λ _ _ => True);
    apply iff_definability_memAxiomSetFrameClass (AxiomSet.MultiGeach.definability l) |>.mpr;
    simp only [MultiGeachConfluent.trivial_frame];

instance : FrameClass.Nonempty (α := α) 𝔽(𝗚𝗲(l)) := inferInstance

instance : System.Consistent (𝐆𝐞(l) : DeductionParameter α) := inferInstance

instance [geach : L.IsGeach] : FrameClass.Nonempty 𝔽(Ax(L)) := by rw [geach.char]; infer_instance

instance [L.IsGeach] : System.Consistent L := inferInstance

instance : System.Consistent (𝐒𝟒 : DeductionParameter α) := inferInstance

instance : System.Consistent (𝐒𝟓 : DeductionParameter α) := inferInstance

instance : Definability (α := α) Ax(𝐒𝟒) (λ F => Reflexive F ∧ Transitive F) := by simpa using instGeachDefinability (L := 𝐒𝟒)

/-

instance AxiomSet.S5.definability : Definability (α := α) 𝐒𝟓 (λ F => Reflexive F ∧ Euclidean F) := by
  simpa using AxiomSet.IsGeachLogic.definability (Ax := 𝐒𝟓);
-/

end Kripke

end LO.Modal.Standard
