import Foundation.Modal.Modality.Basic
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal.Logic.S4

open Entailment
open Modality
open Formula
open Kripke

instance box_box_eq_box : (□□-) ↭[Logic.S4] (□-)  := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0);
    simp;
  . infer_instance;

instance dia_dia_eq_dia : (◇◇-) ↭[Logic.S4] (◇-)  := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := 0); simp;
  . apply translation_of_axiomInstance (a := 0); simp;

instance dia_box_dia_to_dia : (◇□◇-) ⇝[Logic.S4] (◇-) := by
  constructor;
  intro a;
  suffices Kripke.FrameClass.S4 ⊧ ◇□◇(atom a) ➝ ◇(atom a) by
    simpa [S4.Kripke.preorder];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  intro V x hx;
  obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp hx;
  have := hy y F.refl;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp this;

  apply Satisfies.dia_def.mpr;
  use z;
  constructor;
  . exact F.trans Rxy Ryz;
  . assumption;

instance box_dia_box_dia_eq_box_dia : (□◇□◇-) ↭[Logic.S4] (□◇-) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . constructor;
    intro a;
    apply imply_box_distribute'!;
    apply dia_box_dia_to_dia.translate;
  . constructor;
    intro a;
    suffices Kripke.FrameClass.S4 ⊧ □◇(atom a) ➝ □◇□◇(atom a) by
      simpa [S4.Kripke.preorder];
    intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    intro V x hx y Rxy;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor;
    . simp;
    . intro z Ryz;
      apply hx;
      apply F.trans Rxy Ryz;

instance dia_box_dia_box_eq_dia_box : (◇□◇□-) ↭[Logic.S4] (◇□-) := by
  constructor;
  intro a;
  suffices Kripke.FrameClass.S4 ⊧ (◇□◇□(atom a)) ⭤ (◇□(atom a)) by
    simpa [S4.Kripke.preorder];
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Satisfies.iff_def.mpr;
  constructor;
  . intro h;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
    have := hy y F.refl;
    obtain ⟨z, Rxz, hz⟩ := Satisfies.dia_def.mp this;
    apply Satisfies.dia_def.mpr;
    use z;
    constructor;
    . apply F.trans Rxy Rxz;
    . assumption;
  . intro h;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor;
    . simpa;
    . intro z Ryz;
      apply Satisfies.dia_def.mpr;
      use z;
      constructor;
      . simp;
      . intro w Rzw;
        apply hy;
        exact F.trans Ryz Rzw;

end LO.Modal.Logic.S4
