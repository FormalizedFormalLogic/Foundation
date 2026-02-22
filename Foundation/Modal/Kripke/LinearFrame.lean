module

public import Foundation.Modal.Kripke.Root

@[expose] public section

namespace LO.Modal.Kripke

abbrev natLT : Kripke.Frame where
  World := ℕ
  Rel := (· < ·)

namespace natLT

instance : IsTrans _ natLT := by
  dsimp only [natLT];
  infer_instance;

instance : natLT.IsSerial := ⟨by
  intro x;
  use x + 1;
  omega;
⟩

instance : natLT.IsPiecewiseConnected := ⟨by
  rintro x y z Rxy Ryx;
  rcases lt_trichotomy y z with Rxy | rfl | rxy <;> tauto;
⟩

abbrev min : natLT.World := 0

instance : natLT.IsRooted := ⟨natLT.min, by grind⟩

end natLT


abbrev natLE : Kripke.Frame where
  World := ℕ
  Rel := (· ≤ ·)

namespace natLE

instance : IsTrans _ natLE := by
  dsimp only [natLE];
  infer_instance;

instance : Std.Refl natLE := by
  dsimp only [natLE];
  infer_instance;

abbrev min : natLE.World := 0

instance : natLE.IsRooted := ⟨0, by grind⟩

end natLE


abbrev finLT (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· < ·)

namespace finLT

variable {n : ℕ} [NeZero n]

instance : Finite (finLT n) := by
  dsimp only [finLT];
  infer_instance;

end finLT


abbrev finLE (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· ≤ ·)

namespace finLE

variable {n : ℕ} [NeZero n]

instance : Finite (finLT n) := by
  dsimp only [finLT];
  infer_instance;

instance : IsTrans _ (finLE n) := by
  dsimp only [finLE];
  infer_instance;

instance : Std.Refl (finLE n) := by
  dsimp only [finLE];
  infer_instance;

instance : Std.Antisymm (finLE n) := by
  dsimp only [finLE];
  infer_instance;

end finLE



section

open Formula Formula.Kripke

/-- Goldblatt, Exercise 8.1 (1) -/
lemma natLT_validates_AxiomZ : natLT ⊧ (Axioms.Z (.atom 0)) := by
  intro V x hx₁ hx₂ y lt_xy;
  obtain ⟨z, lt_xz, hz⟩ := Satisfies.dia_def.mp hx₂;
  rcases lt_trichotomy y z with (lt_yz | rfl | lt_zy);
  . rcases or_not_of_imp (hx₁ y lt_xy) with _ | hy;
    . assumption;
    . exfalso;
      obtain ⟨⟨u, u_ioc⟩, hu₁, hu⟩ := @WellFounded.has_min (α := Finset.Ioc y z) (· > ·)
        (Finite.wellFounded_of_trans_of_irrefl _)
        ({ u | ¬Satisfies ⟨natLT, V⟩ u (.atom 0) })
        (by
          replace hy := Satisfies.box_def.not.mp hy;
          push_neg at hy;
          obtain ⟨u, lt_yu, hu⟩ := hy;
          refine ⟨⟨u, ?_⟩, ?_⟩;
          . apply Finset.mem_Ioc.mpr;
            constructor;
            . tauto;
            . by_contra hC;
              exact hu $ hz _ $ not_le.mp hC;
          . tauto;
        )
      have ⟨lt_yu, le_uz⟩ := Finset.mem_Ioc.mp u_ioc;
      have := not_imp_not.mpr (hx₁ u (lt_trans lt_xy lt_yu)) hu₁;
      replace this := Satisfies.box_def.not.mp this;
      push_neg at this;
      obtain ⟨v, lt_uv, hv⟩ := this;
      have := hu ⟨v, ?_⟩ hv;
      . contradiction;
      . by_contra hC;
        apply hv;
        apply hz;
        replace hC := Finset.mem_Ioc.not.mp hC;
        push_neg at hC;
        apply hC;
        exact lt_trans lt_yu lt_uv;
  . apply hx₁ <;> assumption;
  . apply hz;
    assumption;

/-- Goldblatt, Exercise 8.9 -/
lemma natLE_validates_AxiomDum : natLE ⊧ (Axioms.Dum (.atom 0)) := by
  intro V x hx₁ hx₂;
  obtain ⟨y, le_xy, hy⟩ := Satisfies.dia_def.mp hx₂;
  rcases lt_or_eq_of_le le_xy with (le_xy | rfl);
  . rcases or_not_of_imp (hx₁ x (by omega)) with _ | hx₃;
    . assumption;
    . by_contra hx;
      obtain ⟨⟨u, u_ioc⟩, hu₁, hu⟩ := @WellFounded.has_min (α := Finset.Ioo x y) (· > ·)
        (Finite.wellFounded_of_trans_of_irrefl _)
        ({ u | ¬Satisfies ⟨natLT, V⟩ u (.atom 0) })
        (by
          replace hx₃ := Satisfies.box_def.not.mp hx₃;
          push_neg at hx₃;
          obtain ⟨u, lt_xu, hu⟩ := hx₃;
          replace lt_xu : x < u := by
            rcases (lt_or_eq_of_le lt_xu) with h | rfl;
            . assumption;
            . exfalso;
              replace hu := Satisfies.imp_def₂.not.mp hu;
              push_neg at hu;
              exact hx $ hu.1;
          replace hu := Satisfies.imp_def₂.not.mp hu;
          push_neg at hu;
          obtain ⟨hu₁, hu₂⟩ := hu;
          replace hu₂ := Satisfies.box_def.not.mp hu₂;
          push_neg at hu₂;
          obtain ⟨v, lt_uv, hv⟩ := hu₂;
          replace lt_uv : u < v := by
            rcases (lt_or_eq_of_le lt_uv) with h | rfl;
            . assumption;
            . contradiction;;
          refine ⟨⟨v, ?_⟩, ?_⟩;
          . apply Finset.mem_Ioo.mpr;
            constructor;
            . exact lt_trans lt_xu lt_uv;
            . by_contra hC;
              replace le_yv := not_lt.mp hC;
              apply hv;
              apply hy;
              exact le_yv;
          . tauto;
        )
      have ⟨lt_xu, lt_uy⟩ := Finset.mem_Ioo.mp u_ioc;
      have hu₂ := hx₁ u (le_of_lt lt_xu);
      have := not_imp_not.mpr hu₂ hu₁;
      replace this := Satisfies.box_def.not.mp this;
      push_neg at this;
      obtain ⟨v, lt_uv, hv⟩ := this;
      replace lt_uv : u < v := by
        rcases (lt_or_eq_of_le lt_uv) with h | rfl;
        . assumption;
        . exfalso;
          replace hv := Satisfies.imp_def₂.not.mp hv;
          push_neg at hv;
          exact hu₁ hv.1;
      replace hv := Satisfies.imp_def₂.not.mp hv;
      push_neg at hv;
      obtain ⟨hv₁, hv₂⟩ := hv;
      replace hv₂ := Satisfies.box_def.not.mp hv₂;
      push_neg at hv₂;
      obtain ⟨w, lt_vw, hw⟩ := hv₂;
      replace lt_vw : v < w := by
        rcases (lt_or_eq_of_le lt_vw) with h | rfl;
        . assumption;
        . contradiction;
      have : u < w := lt_trans lt_uv lt_vw;
      have := hu ⟨w, ?_⟩ hw;
      . contradiction;
      . apply Finset.mem_Ioo.mpr;
        constructor;
        . exact lt_trans (lt_trans lt_xu lt_uv) lt_vw;
        . by_contra hC;
          apply hw;
          apply hy;
          exact not_lt.mp hC;
  . apply hx₁ x (by tauto);
    intro y lt_xy hy₂ z lt_yz;
    apply hy;
    omega;

end

end LO.Modal.Kripke
end
