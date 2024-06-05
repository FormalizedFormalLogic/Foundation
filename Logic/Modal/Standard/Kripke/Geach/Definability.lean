import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

open System
open System.Axioms (Geach)

namespace Kripke

variable [Inhabited α]

def GeachConfluent (t : Geach.Taple) : FrameProperty := λ F => ∀ {x y z : F.World}, (x ≺^[t.i] y) ∧ (x ≺^[t.j] z) → ∃ u, (y ≺^[t.m] u) ∧ (z ≺^[t.n] u)

@[simp]
def MultiGeachConfluent (ts : List Geach.Taple) : FrameProperty :=
  match ts with
  | [] => λ _ => True
  | t :: ts => λ F => (GeachConfluent t F) ∧ (MultiGeachConfluent ts F)

namespace GeachConfluent

variable {F : Frame}

@[simp] lemma serial_def : (GeachConfluent ⟨0, 0, 1, 1⟩ F) ↔ Serial F.Rel := by simp [GeachConfluent, Symmetric]; aesop;

@[simp] lemma reflexive_def : (GeachConfluent ⟨0, 0, 1, 0⟩ F) ↔ Reflexive F.Rel := by simp [GeachConfluent, Reflexive];

@[simp] lemma symmetric_def : (GeachConfluent ⟨0, 1, 0, 1⟩ F) ↔ Symmetric F.Rel := by simp [GeachConfluent, Symmetric]; aesop;

@[simp] lemma transitive_def : (GeachConfluent ⟨0, 2, 1, 0⟩ F) ↔ Transitive F.Rel := by simp [GeachConfluent, Transitive]; aesop;

@[simp] lemma euclidean_def : (GeachConfluent ⟨1, 1, 0, 1⟩ F) ↔ Euclidean F.Rel := by simp [GeachConfluent, Euclidean];

@[simp] lemma confluent_def : (GeachConfluent ⟨1, 1, 1, 1⟩ F) ↔ Confluent F.Rel := by simp [GeachConfluent, Confluent];

@[simp]
lemma extensive_def : (GeachConfluent ⟨0, 1, 0, 0⟩ F) ↔ Extensive F.Rel := by
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

@[simp] lemma functional_def : (GeachConfluent ⟨1, 1, 0, 0⟩ F) ↔ Functional F.Rel := by simp [GeachConfluent, Functional]; aesop

@[simp] lemma dense_def : (GeachConfluent ⟨0, 1, 2, 0⟩ F)  ↔ Dense F.Rel := by simp [GeachConfluent, Dense]; aesop;

@[simp]
lemma terminal_frame : GeachConfluent t Frame.terminal.toFrame := by simp [GeachConfluent, Frame.terminal.relItr.mpr];

end GeachConfluent


namespace MultiGeachConfluent

@[simp]
lemma terminal_frame : MultiGeachConfluent ts Frame.terminal.toFrame := by
  induction ts with
  | nil => simp;
  | cons t ts ih =>
    constructor;
    . exact Kripke.GeachConfluent.terminal_frame;
    . exact ih;

end MultiGeachConfluent


open Kripke
open Formula Formula.Kripke
open AxiomSet

variable {Ax : AxiomSet α}

instance AxiomSet.Geach.definability (t) : Definability (α := α) 𝗴𝗲(t) (GeachConfluent t) where
  defines F := by
    simp [AxiomSet.Geach, GeachConfluent];
    constructor;
    . intro h x y z hi hj;
      let M : Model α := { Frame := F, Valuation := λ v _ => y ≺^[t.m] v }
      have him_x : Satisfies M x (◇^[t.i](□^[t.m](Formula.atom default))) := by
        apply Satisfies.multidia_def.mpr;
        existsi y;
        constructor;
        . simpa;
        . apply Satisfies.multibox_def.mpr; aesop;
      have hjn_x : Satisfies M x (□^[t.j](◇^[t.n]atom default)) := Kripke.Satisfies.mdp (h (Formula.atom default) M.Valuation x) him_x;
      have hn_z : Satisfies M z (◇^[t.n]atom default) := Satisfies.multibox_def.mp hjn_x z hj;
      obtain ⟨u, hzu, hyu⟩ := Satisfies.multidia_def.mp hn_z;
      existsi u;
      exact ⟨hyu, hzu⟩;
    . intro h p V x;
      simp [AxiomSet.Geach];
      intro y hxy hm z hxz;
      obtain ⟨u, hyu, hzu⟩ := h hxy hxz;
      use u;
      constructor;
      . assumption;
      . exact hm u hyu;

instance AxiomSet.MultiGeach.definability (ts) : Definability (α := α) 𝗚𝗲(ts) (Kripke.MultiGeachConfluent ts) where
  defines F := by
    induction ts with
    | nil => apply AxiomSet.K.definability.defines;
    | cons t ts ih =>
      simp only [MultiGeach.iff_cons, Semantics.RealizeSet.union_iff, MultiGeachConfluent];
      constructor;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact AxiomSet.Geach.definability t |>.defines F |>.mp ht;
        . apply ih.mp hts;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact AxiomSet.Geach.definability t |>.defines F |>.mpr ht;
        . apply ih.mpr hts;

variable {L : DeductionParameter α} [L.HasNec]

instance instGeachDefinability [geach : L.IsGeach] : Definability Ax(L) (Kripke.MultiGeachConfluent geach.taples) := by
  convert AxiomSet.MultiGeach.definability (α := α) geach.taples;
  simp;

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(𝗚𝗲(l)) : FiniteFrameClass' α) := by
  existsi Frame.terminal;
  apply iff_definability_memAxiomSetFrameClass (AxiomSet.MultiGeach.definability l) |>.mpr;
  exact MultiGeachConfluent.terminal_frame;

instance : FrameClass.IsNonempty (𝔽(𝗚𝗲(l)) : FrameClass' α) := inferInstance

instance : System.Consistent (𝐆𝐞(l) : DeductionParameter α) := inferInstance

instance [geach : L.IsGeach] : FrameClass.IsNonempty 𝔽(Ax(L)) := by rw [geach.char]; infer_instance;

instance [L.IsGeach] : System.Consistent L := inferInstance

instance : System.Consistent (𝐒𝟒 : DeductionParameter α) := inferInstance

instance : System.Consistent (𝐒𝟓 : DeductionParameter α) := inferInstance

instance : Definability (α := α) Ax(𝐒𝟒) (λ F => Reflexive F.Rel ∧ Transitive F.Rel) := by simpa using instGeachDefinability (L := 𝐒𝟒)

instance : Definability (α := α) Ax(𝐒𝟓) (λ F => Reflexive F.Rel ∧ Euclidean F.Rel) := by simpa using instGeachDefinability (L := 𝐒𝟓);

end Kripke

end LO.Modal.Standard
