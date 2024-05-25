import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

open System
open System.Axioms (Geach)

variable {W α : Type*} [Inhabited α]
variable {Λ : AxiomSet α}

def Kripke.GeachConfluent (l : Geach.Taple) (F : Kripke.Frame W α) := ∀ {x y z}, (F^[l.i] x y) ∧ (F^[l.j] x z) → ∃ u, (F^[l.m] y u) ∧ (F^[l.n] z u)

@[simp]
def Kripke.MultiGeachConfluent (l : List Geach.Taple) (F : Kripke.Frame W α) : Prop :=
  match l with
  | [] => True
  | x :: xs => (GeachConfluent x F) ∧ (MultiGeachConfluent xs F)

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

end Kripke.GeachConfluent

open Kripke
open Formula Formula.Kripke

instance AxiomSet.Geach.definability (t) : AxiomSetDefinability W (𝐠𝐞(t) : AxiomSet α) (GeachConfluent t) where
  defines F := by
    simp [AxiomSet.Geach, GeachConfluent, Geach];
    constructor;
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

instance AxiomSet.GeachLogic.definability (l) : AxiomSetDefinability W (𝐆𝐞(l) : AxiomSet α) (Kripke.MultiGeachConfluent l) where
  defines F := by
    induction l with
    | nil => apply AxiomSet.K.definability.defines;
    | cons t ts ih =>
      simp [Kripke.MultiGeachConfluent];
      constructor;
      . rintro ⟨ht, hts⟩;
        constructor;
        . apply AxiomSet.Geach.definability t |>.defines F |>.mp ht;
        . apply ih.mp hts;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact AxiomSet.Geach.definability t |>.defines F |>.mpr ht;
        . apply ih.mpr hts;

instance AxiomSet.IsGeach.definability  [hG : Λ.IsGeach] : AxiomSetDefinability W Λ (Kripke.MultiGeachConfluent hG.taples) where
  defines F := by convert (AxiomSet.GeachLogic.definability _ |>.defines F); exact hG.char;

instance AxiomSet.S4.definability : AxiomSetDefinability (α := α) W 𝐒𝟒 (λ F => Reflexive F ∧ Transitive F) := by simpa using AxiomSet.IsGeach.definability (Λ := 𝐒𝟒)

instance AxiomSet.S5.definability : AxiomSetDefinability (α := α) W 𝐒𝟓 (λ F => Reflexive F ∧ Euclidean F) := by simpa using AxiomSet.IsGeach.definability (Λ := 𝐒𝟓)

instance : Set.Nonempty 𝔽((𝐒𝟒 : AxiomSet α), W) := by
  existsi (λ _ _ => True);
  apply iff_definability_memAxiomSetFrameClass (AxiomSet.S4.definability) |>.mp;
  simp [Reflexive, Transitive];

end LO.Modal.Standard
