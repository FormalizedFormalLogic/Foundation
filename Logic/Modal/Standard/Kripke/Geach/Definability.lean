import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

open System
open System.Axioms (Geach)

def GeachConfluent' (t : Geach.Taple) (R : α → α → Prop) := ∀ {x y z : α}, (RelItr R t.i x y) ∧ (RelItr R t.j x z) → ∃ u, (RelItr R t.m y u) ∧ (RelItr R t.n z u)

namespace GeachConfluent'

variable {R : α → α → Prop}

@[simp]
lemma serial_def : (GeachConfluent' ⟨0, 0, 1, 1⟩ R) ↔ Serial R := by simp [GeachConfluent', Symmetric]; aesop;

@[simp]
lemma reflexive_def : (GeachConfluent' ⟨0, 0, 1, 0⟩ R) ↔ Reflexive R := by simp [GeachConfluent', Reflexive];

@[simp]
lemma symmetric_def : (GeachConfluent' ⟨0, 1, 0, 1⟩ R) ↔ Symmetric R := by
  simp [GeachConfluent', Symmetric]; aesop;

@[simp]
lemma transitive_def : (GeachConfluent' ⟨0, 2, 1, 0⟩ R) ↔ Transitive R := by simp [GeachConfluent', Transitive]; aesop;

@[simp]
lemma euclidean_def : (GeachConfluent' ⟨1, 1, 0, 1⟩ R) ↔ Euclidean R := by simp [GeachConfluent', Euclidean];

@[simp]
lemma confluent_def : (GeachConfluent' ⟨1, 1, 1, 1⟩ R) ↔ Confluent R := by simp [GeachConfluent', Confluent];

@[simp]
lemma extensive_def : (GeachConfluent' ⟨0, 1, 0, 0⟩ R) ↔ Extensive R := by
  simp [GeachConfluent', Extensive];
  constructor;
  . intro h x y Rxy;
    have := h rfl Rxy;
    subst_vars;
    trivial;
  . intro h x y z Exy Rxz;
    have := h Rxz;
    subst_vars;
    trivial;

@[simp]
lemma functional_def : (GeachConfluent' ⟨1, 1, 0, 0⟩ R) ↔ Functional R := by simp [GeachConfluent', Functional]; aesop

@[simp]
lemma dense_def : (GeachConfluent' ⟨0, 1, 2, 0⟩ R)  ↔ Dense R := by simp [GeachConfluent', Dense]; aesop;

@[simp]
lemma satisfies_eq : GeachConfluent' (α := α) t (· = ·) := by simp [GeachConfluent'];

end GeachConfluent'


def MultiGeachConfluent' (ts : List Geach.Taple) (R : α → α → Prop) : Prop :=
  match ts with
  | [] => True
  | t :: ts => (GeachConfluent' t R) ∧ (MultiGeachConfluent' ts R)

namespace MultiGeachConfluent'

@[simp]
lemma satisfies_eq : MultiGeachConfluent' (α := α) ts (· = ·) := by
  induction ts <;> simp_all [MultiGeachConfluent'];

end MultiGeachConfluent'


namespace Kripke

abbrev GeachConfluentFrameClass (t : Geach.Taple) (α) : FrameClass α := { F | (GeachConfluent' t) F }

abbrev MultiGeachConfluentFrameClass (ts : List Geach.Taple) (α) : FrameClass α := { F | MultiGeachConfluent' ts F }

@[simp]
lemma MultiGeachConfluentFrameClass.def_nil : MultiGeachConfluentFrameClass [] α = AllFrameClass α := by
  simp [MultiGeachConfluentFrameClass, MultiGeachConfluent']

open Formula (atom kripke_satisfies)
open Formula.kripke_satisfies (multibox_def multidia_def)

variable [Inhabited α]

instance {t : Geach.Taple} : 𝗴𝗲(t).DefinesKripkeFrameClass (GeachConfluentFrameClass t α) where
  defines := by
    intro F;
    constructor;
    . rintro h x y z ⟨hi, hj⟩;
      simp at h;
      let M : Model α := { Frame := F, Valuation := λ v _ => y ≺^[t.m] v }
      have him_x : kripke_satisfies M x (◇^[t.i](□^[t.m](atom default))) := by
        apply kripke_satisfies.multidia_def.mpr;
        existsi y;
        constructor;
        . simpa;
        . apply kripke_satisfies.multibox_def.mpr; aesop;
      have hjn_x : kripke_satisfies M x (□^[t.j](◇^[t.n](atom default))) := h (Formula.atom default) M.Valuation x him_x;
      have hn_z : kripke_satisfies M z (◇^[t.n](atom default)) := kripke_satisfies.multibox_def.mp hjn_x z hj;
      obtain ⟨u, hzu, hyu⟩ := kripke_satisfies.multidia_def.mp hn_z;
      existsi u;
      exact ⟨hyu, hzu⟩;
    . simp [AxiomSet.Geach, Axioms.Geach, kripke_satisfies];
      intro h p V x him;
      simp [multibox_def, multidia_def];
      intro z rxz;
      obtain ⟨y, rxy, hbp⟩ := multidia_def.mp him;
      obtain ⟨u, ryu, rzu⟩ := h ⟨rxy, rxz⟩;
      use u;
      constructor;
      . assumption;
      . exact (multibox_def.mp hbp) _ ryu;

instance {ts : List Geach.Taple} : 𝗚𝗲(ts).DefinesKripkeFrameClass (MultiGeachConfluentFrameClass ts α) where
  defines := by
    induction ts with
    | nil => simp;
    | cons t ts ih =>
      have : 𝗴𝗲(t).DefinesKripkeFrameClass (GeachConfluentFrameClass t α) := inferInstance;
      simp_all only [Semantics.RealizeSet.union_iff, AxiomSet.MultiGeach.iff_cons, MultiGeachConfluentFrameClass];
      intro F;
      constructor;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact this.defines.mp ht;
        . simpa using hts;
      . rintro ⟨ht, hts⟩;
        constructor;
        . exact this.defines.mpr ht;
        . simpa using hts;

instance : (MultiGeachConfluentFrameClass ts α).IsNonempty where
  nonempty := by
    use (TerminalFrame α);
    exact MultiGeachConfluent'.satisfies_eq;

instance : System.Consistent (𝐆𝐞(ts) : DeductionParameter α) := consistent (𝔽 := MultiGeachConfluentFrameClass ts α)

instance {Λ : DeductionParameter α} [geach : Λ.IsGeach] : System.Consistent Λ := by rw [geach.char]; infer_instance;

instance : System.Consistent (𝐒𝟒 : DeductionParameter α) := inferInstance

instance : System.Consistent (𝐒𝟓 : DeductionParameter α) := inferInstance

/-
abbrev PreorderFrameClass (α) : FrameClass α := { F | Reflexive F ∧ Transitive F }

instance : Ax(𝐒𝟒).DefinesKripkeFrameClass (PreorderFrameClass α) := by simpa using instGeachDefinability (L := 𝐒𝟒)

instance : Definability (α := α) Ax(𝐒𝟓) (λ F => Reflexive F.Rel ∧ Euclidean F.Rel) := by simpa using instGeachDefinability (L := 𝐒𝟓);

instance : Definability (α := α) Ax(𝐓𝐫𝐢𝐯) (λ F => Reflexive F.Rel ∧ Extensive F.Rel) := by simpa using instGeachDefinability (L := 𝐓𝐫𝐢𝐯);
-/

end Kripke

end LO.Modal.Standard
