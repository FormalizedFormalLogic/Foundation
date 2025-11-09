import Foundation.InterpretabilityLogic.Logic.Basic
import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J1
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J2
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J5
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M
import Foundation.InterpretabilityLogic.Hilbert.Axiom
import Batteries.Tactic.Instances

namespace LO.InterpretabilityLogic

open
  LO.Entailment
  LO.Modal.Entailment
  LO.InterpretabilityLogic.Entailment

protected inductive Hilbert.Minimal {α} (Ax : Axiom α) : Logic α
| protected axm {φ} (s : Substitution _) : φ ∈ Ax → Hilbert.Minimal Ax (φ⟦s⟧)
| protected mdp {φ ψ}     : Hilbert.Minimal Ax (φ ➝ ψ) → Hilbert.Minimal Ax φ → Hilbert.Minimal Ax ψ
| protected nec {φ}       : Hilbert.Minimal Ax φ → Hilbert.Minimal Ax (□φ)
| protected R1 {φ ψ χ}    : Hilbert.Minimal Ax (φ ➝ ψ) → Hilbert.Minimal Ax (χ ▷ φ ➝ χ ▷ ψ)
| protected R2 {φ ψ χ}    : Hilbert.Minimal Ax (φ ➝ ψ) → Hilbert.Minimal Ax (ψ ▷ χ ➝ φ ▷ χ)
| protected implyK φ ψ    : Hilbert.Minimal Ax $ Axioms.ImplyK φ ψ
| protected implyS φ ψ χ  : Hilbert.Minimal Ax $ Axioms.ImplyS φ ψ χ
| protected ec φ ψ        : Hilbert.Minimal Ax $ Axioms.ElimContra φ ψ
| protected axiomK φ ψ    : Hilbert.Minimal Ax $ Modal.Axioms.K φ ψ
| protected axiomL φ      : Hilbert.Minimal Ax $ Modal.Axioms.L φ

namespace Hilbert.Minimal

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind ⇒]
lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : Hilbert.Minimal Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply Minimal.axm s h;

@[grind ⇒]
lemma axm'! {φ} (h : φ ∈ Ax) : Hilbert.Minimal Ax ⊢ φ := by simpa using axm! (idSubstitution _) h;

instance : Entailment.Lukasiewicz (Hilbert.Minimal Ax) where
  implyK _ _ := by constructor; apply Hilbert.Minimal.implyK;
  implyS _ _ _ := by constructor; apply Hilbert.Minimal.implyS;
  elimContra _ _ := by constructor; apply Hilbert.Minimal.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Minimal.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Modal.Entailment.GL (Hilbert.Minimal Ax) where
  nec h := by constructor; apply Hilbert.Minimal.nec; exact h.1;
  K φ ψ := by constructor; apply Hilbert.Minimal.axiomK;
  L φ := by constructor; apply Hilbert.Minimal.axiomL;

instance : InterpretabilityLogic.Entailment.HasRule1 (Hilbert.Minimal Ax) where
  R1! h := by
    constructor;
    apply Hilbert.Minimal.R1;
    exact h.1;

instance : InterpretabilityLogic.Entailment.HasRule2 (Hilbert.Minimal Ax) where
  R2! h := by
    constructor;
    apply Hilbert.Minimal.R2;
    exact h.1;

instance : Logic.Substitution (Hilbert.Minimal Ax) where
  subst {φ} s h := by
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih        => simpa using Minimal.axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply Minimal.mdp ihφψ ihφ;
    | nec hφ ihφ          => apply Minimal.nec ihφ;
    | R1 hφψ ihφψ         => apply Minimal.R1 ihφψ;
    | R2 hφψ ihφψ         => apply Minimal.R2 ihφψ;
    | implyK φ ψ          => apply Minimal.implyK;
    | implyS φ ψ χ        => apply Minimal.implyS;
    | ec φ ψ              => apply Minimal.ec;
    | axiomK φ ψ          => apply Minimal.axiomK;
    | axiomL φ            => apply Minimal.axiomL;

protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert.Minimal Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert.Minimal Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.Minimal Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Hilbert.Minimal Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (R1       : ∀ {φ ψ χ}, {hφψ : (Hilbert.Minimal Ax) ⊢ φ ➝ ψ} → motive (φ ➝ ψ) hφψ → motive (χ ▷ φ ➝ χ ▷ ψ) (by grind))
  (R2       : ∀ {φ ψ χ}, {hφψ : (Hilbert.Minimal Ax) ⊢ φ ➝ ψ} → motive (φ ➝ ψ) hφψ → motive (ψ ▷ χ ➝ φ ▷ χ) (by grind))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  (axiomK   : ∀ {φ ψ}, motive (Modal.Axioms.K φ ψ) $ by simp)
  (axiomL   : ∀ {φ}, motive (Modal.Axioms.L φ) $ by simp)
  : ∀ {φ}, (d : Hilbert.Minimal Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | R1 hφψ ihφψ => apply R1; exact ihφψ (Logic.iff_provable.mpr hφψ);
  | R2 hφψ ihφψ => apply R2; exact ihφψ (Logic.iff_provable.mpr hφψ);
  | _ => grind

lemma weakerThan_of_provable_axioms (hs : Hilbert.Minimal Ax₂ ⊢* Ax₁) : (Hilbert.Minimal Ax₁) ⪯ (Hilbert.Minimal Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.Minimal.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | R1 ihφψ => grind;
  | R2 ihφψ => grind;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.Minimal Ax₁) ⪯ (Hilbert.Minimal Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.Minimal.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance [Ax.HasJ1] : InterpretabilityLogic.Entailment.HasAxiomJ1 (Hilbert.Minimal Ax) where
  J1! {φ ψ} := by
    constructor;
    simpa [HasJ1.ne_pq] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J1 (.atom (HasJ1.p Ax)) (.atom (HasJ1.q Ax)))
      (s := λ b => if (HasJ1.p Ax) = b then φ else if (HasJ1.q Ax) = b then ψ else (.atom b))
      (HasJ1.mem_J1);

instance [Ax.HasJ2] : InterpretabilityLogic.Entailment.HasAxiomJ2 (Hilbert.Minimal Ax) where
  J2! {φ ψ χ} := by
    constructor;
    simpa [HasJ2.ne_pq, HasJ2.ne_qr, HasJ2.ne_rp.symm] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J2 (.atom (HasJ2.p Ax)) (.atom (HasJ2.q Ax)) (.atom (HasJ2.r Ax)))
      (s := λ b =>
        if (HasJ2.p Ax) = b then φ
        else if (HasJ2.q Ax) = b then ψ
        else if (HasJ2.r Ax) = b then χ
        else (.atom b))
      $ HasJ2.mem_J2;

instance [Ax.HasJ2Plus] : InterpretabilityLogic.Entailment.HasAxiomJ2Plus (Hilbert.Minimal Ax) where
  J2Plus! {φ ψ χ} := by
    constructor;
    simpa [HasJ2Plus.ne_pq, HasJ2Plus.ne_qr, HasJ2Plus.ne_rp.symm] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J2Plus (.atom (HasJ2Plus.p Ax)) (.atom (HasJ2Plus.q Ax)) (.atom (HasJ2Plus.r Ax)))
      (s := λ b =>
        if (HasJ2Plus.p Ax) = b then φ
        else if (HasJ2Plus.q Ax) = b then ψ
        else if (HasJ2Plus.r Ax) = b then χ
        else (.atom b))
      $ HasJ2Plus.mem_J2Plus;

instance [Ax.HasJ3] : InterpretabilityLogic.Entailment.HasAxiomJ3 (Hilbert.Minimal Ax) where
  J3! {φ ψ χ} := by
    constructor;
    simpa [HasJ3.ne_pq, HasJ3.ne_qr, HasJ3.ne_rp.symm] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J3 (.atom (HasJ3.p Ax)) (.atom (HasJ3.q Ax)) (.atom (HasJ3.r Ax)))
      (s := λ b =>
        if (HasJ3.p Ax) = b then φ
        else if (HasJ3.q Ax) = b then ψ
        else if (HasJ3.r Ax) = b then χ
        else (.atom b))
      $ HasJ3.mem_J3;

instance [Ax.HasJ4] : InterpretabilityLogic.Entailment.HasAxiomJ4 (Hilbert.Minimal Ax) where
  J4! {φ ψ} := by
    constructor;
    simpa [HasJ4.ne_pq] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J4 (.atom (HasJ4.p Ax)) (.atom (HasJ4.q Ax)))
      (s := λ b => if (HasJ4.p Ax) = b then φ else if (HasJ4.q Ax) = b then ψ else (.atom b))
      (HasJ4.mem_J4);

instance [Ax.HasJ4Plus] : InterpretabilityLogic.Entailment.HasAxiomJ4Plus (Hilbert.Minimal Ax) where
  J4Plus! {φ ψ χ} := by
    constructor;
    simpa [HasJ4Plus.ne_pq, HasJ4Plus.ne_qr, HasJ4Plus.ne_rp.symm] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J4Plus (.atom (HasJ4Plus.p Ax)) (.atom (HasJ4Plus.q Ax)) (.atom (HasJ4Plus.r Ax)))
      (s := λ b =>
        if (HasJ4Plus.p Ax) = b then φ
        else if (HasJ4Plus.q Ax) = b then ψ
        else if (HasJ4Plus.r Ax) = b then χ
        else (.atom b))
      $ HasJ4Plus.mem_J4Plus;

instance [Ax.HasJ5] : InterpretabilityLogic.Entailment.HasAxiomJ5 (Hilbert.Minimal Ax) where
  J5! {φ} := by
    constructor;
    simpa using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.J5 (.atom (HasJ5.p Ax)))
      (s := λ b => if (HasJ5.p Ax) = b then φ else (.atom b))
      (HasJ5.mem_J5);

instance [Ax.HasJ6] : InterpretabilityLogic.Entailment.HasAxiomJ6 (Hilbert.Minimal Ax) where
  J6! {φ} := by
    constructor;
    simpa using Hilbert.Minimal.axm (φ := InterpretabilityLogic.Axioms.J6 (.atom (HasJ6.p Ax)))
      (s := λ b => if (HasJ6.p Ax) = b then φ else (.atom b))
      (HasJ6.mem_J6);

instance [Ax.HasM] : InterpretabilityLogic.Entailment.HasAxiomM (Hilbert.Minimal Ax) where
  M! {φ ψ χ} := by
    constructor;
    simpa [HasM.ne_pq, HasM.ne_qr, HasM.ne_rp.symm] using Hilbert.Minimal.axm
      (φ := InterpretabilityLogic.Axioms.M (.atom (HasM.p Ax)) (.atom (HasM.q Ax)) (.atom (HasM.r Ax)))
      (s := λ b =>
        if (HasM.p Ax) = b then φ
        else if (HasM.q Ax) = b then ψ
        else if (HasM.r Ax) = b then χ
        else (.atom b))
      $ HasM.mem_M;

end

end Hilbert.Minimal


section

open Hilbert.Minimal


protected abbrev ILMinus.axioms : Axiom ℕ := {
  InterpretabilityLogic.Axioms.J3 (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.J6 (.atom 0)
}
namespace ILMinus.axioms
instance : ILMinus.axioms.HasJ3 where p := 0; q := 1; r := 2;
instance : ILMinus.axioms.HasJ6 where p := 0;
end ILMinus.axioms
protected abbrev ILMinus := Hilbert.Minimal ILMinus.axioms
instance : Entailment.ILMinus InterpretabilityLogic.ILMinus where


section

namespace Hilbert.Minimal

inductive AxiomName | J1 | J2 | J2Plus | J4 | J4Plus | J5 | M deriving DecidableEq

variable {l : List AxiomName}

@[grind]
def buildAxioms (l : List AxiomName) : Axiom ℕ :=
  ILMinus.axioms ∪
    (if l.contains .J1 then { InterpretabilityLogic.Axioms.J1 (.atom 0) (.atom 1) } else ∅) ∪
    (if l.contains .J2 then { InterpretabilityLogic.Axioms.J2 (.atom 0) (.atom 1) (.atom 2) } else ∅) ∪
    (if l.contains .J2Plus then { InterpretabilityLogic.Axioms.J2Plus (.atom 0) (.atom 1) (.atom 2) } else ∅) ∪
    (if l.contains .J4 then { InterpretabilityLogic.Axioms.J4 (.atom 0) (.atom 1) } else ∅) ∪
    (if l.contains .J4Plus then { InterpretabilityLogic.Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2) } else ∅) ∪
    (if l.contains .J5 then { InterpretabilityLogic.Axioms.J5 (.atom 0) } else ∅) ∪
    (if l.contains .M then { InterpretabilityLogic.Axioms.M (.atom 0) (.atom 1) (.atom 2) } else ∅)


example : buildAxioms [.J1, .J2] = {
  Axioms.J1 (.atom 0) (.atom 1),
  Axioms.J2 (.atom 0) (.atom 1) (.atom 2),
  Axioms.J3 (.atom 0) (.atom 1) (.atom 2),
  Axioms.J6 (.atom 0)
} := by ext A; simp [Hilbert.Minimal.buildAxioms]; grind;

instance buildAxioms.instHasJ3 : (buildAxioms l).HasJ3 where
  p := 0; q := 1; r := 2;
  mem_J3 := by simp only [buildAxioms]; simp;

instance buildAxioms.instHasJ6 : (buildAxioms l).HasJ6 where
  p := 0;
  mem_J6 := by simp only [buildAxioms]; simp;

instance buildAxioms.instHasJ1 (h : l.contains .J1 := by decide) : (buildAxioms l).HasJ1 where
  p := 0; q := 1;
  mem_J1 := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasJ2 (h : l.contains .J2 := by decide) : (buildAxioms l).HasJ2 where
  p := 0; q := 1; r := 2;
  mem_J2 := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasJ2Plus (h : l.contains .J2Plus := by decide) : (buildAxioms l).HasJ2Plus where
  p := 0; q := 1; r := 2;
  mem_J2Plus := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasJ4 (h : l.contains .J4 := by decide) : (buildAxioms l).HasJ4 where
  p := 0; q := 1;
  mem_J4 := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasJ4Plus (h : l.contains .J4Plus := by decide) : (buildAxioms l).HasJ4Plus where
  p := 0; q := 1; r := 2;
  mem_J4Plus := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasJ5 (h : l.contains .J5 := by decide) : (buildAxioms l).HasJ5 where
  p := 0;
  mem_J5 := by simp only [buildAxioms, h]; simp;

instance buildAxioms.instHasM (h : l.contains .M := by decide) : (buildAxioms l).HasM where
  p := 0; q := 1; r := 2;
  mem_M := by simp only [buildAxioms, h]; simp;

open Lean in
macro "defineILMinus" name:ident "[" xs:ident,* "]" : command => do
  let xs ← xs.getElems.mapM $ λ stx => pure (Lean.mkIdentFrom stx stx.getId)
  let axiomsName := mkIdent (name.getId ++ `axioms)
  let logicName := mkIdent name.getId

  -- TODO: replace nop operation `(section end)
  let instJ1     ← if xs.contains (mkIdent `J1)     then `(command| instance : Axiom.HasJ1 $axiomsName := buildAxioms.instHasJ1)         else `(section end)
  let instJ2     ← if xs.contains (mkIdent `J2)     then `(command| instance : Axiom.HasJ2 $axiomsName := buildAxioms.instHasJ2)         else `(section end)
  let instJ2Plus ← if xs.contains (mkIdent `J2Plus) then `(command| instance : Axiom.HasJ2Plus $axiomsName := buildAxioms.instHasJ2Plus) else `(section end)
  let instJ4     ← if xs.contains (mkIdent `J4)     then `(command| instance : Axiom.HasJ4 $axiomsName := buildAxioms.instHasJ4)         else `(section end)
  let instJ4Plus ← if xs.contains (mkIdent `J4Plus) then `(command| instance : Axiom.HasJ4Plus $axiomsName := buildAxioms.instHasJ4Plus) else `(section end)
  let instJ5     ← if xs.contains (mkIdent `J5)     then `(command| instance : Axiom.HasJ5 $axiomsName := buildAxioms.instHasJ5)         else `(section end)
  let instM      ← if xs.contains (mkIdent `M)      then `(command| instance : Axiom.HasM $axiomsName := buildAxioms.instHasM)           else `(section end)

  let instILMinusJ1     ← if xs.contains (mkIdent `J1)     then `(command| instance : Entailment.ILMinus_J1 $logicName where)     else `(section end)
  let instILMinusJ2     ← if xs.contains (mkIdent `J2)     then `(command| instance : Entailment.ILMinus_J2 $logicName where)     else `(section end)
  let instILMinusJ2Plus ← if xs.contains (mkIdent `J2Plus) then `(command| instance : Entailment.ILMinus_J2Plus $logicName where) else `(section end)
  let instILMinusJ4     ← if xs.contains (mkIdent `J4)     then `(command| instance : Entailment.ILMinus_J4 $logicName where)     else `(section end)
  let instILMinusJ4Plus ← if xs.contains (mkIdent `J4Plus) then `(command| instance : Entailment.ILMinus_J4Plus $logicName where) else `(section end)
  let instILMinusJ5     ← if xs.contains (mkIdent `J5)     then `(command| instance : Entailment.ILMinus_J5 $logicName where)     else `(section end)
  let instILMinusM      ← if xs.contains (mkIdent `M)      then `(command| instance : Entailment.ILMinus_M $logicName where)      else `(section end)

  `(
    protected abbrev $axiomsName := buildAxioms [$[$xs],*]

    namespace $axiomsName

    $instJ1
    $instJ2
    $instJ2Plus
    $instJ4
    $instJ4Plus
    $instJ5
    $instM

    end $axiomsName

    -- TODO: make protected
    abbrev $logicName := Hilbert.Minimal $axiomsName

    namespace $logicName
    $instILMinusJ1
    $instILMinusJ2
    $instILMinusJ2Plus
    $instILMinusJ4
    $instILMinusJ4Plus
    $instILMinusJ5
    $instILMinusM
    end $logicName
  )

end Hilbert.Minimal

open Hilbert.Minimal AxiomName

-- Veltman complete
defineILMinus ILMinus_J1 [J1]
defineILMinus ILMinus_J1_J2 [J1, J2]
defineILMinus ILMinus_J1_J2_J5 [J1, J2, J5]
defineILMinus ILMinus_J1_J4Plus [J1, J4Plus]
defineILMinus ILMinus_J1_J4Plus_J5 [J1, J4Plus, J5]
defineILMinus ILMinus_J1_J5 [J1, J5]
defineILMinus ILMinus_J2Plus [J2Plus]
defineILMinus ILMinus_J2Plus_J5 [J2Plus, J5]
defineILMinus ILMinus_J4Plus [J4Plus]
defineILMinus ILMinus_J4Plus_J5 [J4Plus, J5]
defineILMinus ILMinus_J5 [J5]

-- Veltman incomplete
defineILMinus ILMinus_J1_J4 [J1, J4]
defineILMinus ILMinus_J1_J4_J5 [J1, J4, J5]
defineILMinus ILMinus_J2 [J2]
defineILMinus ILMinus_J2_J4Plus [J2, J4Plus]
defineILMinus ILMinus_J2_J4Plus_J5 [J2, J4Plus, J5]
defineILMinus ILMinus_J2_J5 [J2, J5]
defineILMinus ILMinus_J4 [J4]
defineILMinus ILMinus_J4_J5 [J4, J5]

-- ?
defineILMinus ILMinus_M [M]

end

end

end LO.InterpretabilityLogic
