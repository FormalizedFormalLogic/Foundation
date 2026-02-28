module

public import Foundation.Modal.Entailment.GL
public import Foundation.Modal.Entailment.Grz
public import Foundation.Modal.Entailment.K4Hen
public import Foundation.Modal.Entailment.K4Henkin
public import Foundation.Modal.Entailment.S5Grz
public import Foundation.Modal.Hilbert.Axiom
public import Foundation.Modal.Logic.Basic
public import Foundation.Modal.Logic.Basic
public import Foundation.Propositional.Entailment.Cl.Łukasiewicz

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.Normal2 {α} (Ax : Set (Formula α)) : Logic α
| axm {φ}       : φ ∈ Ax → Normal2 Ax φ
| mdp {φ ψ}     : Normal2 Ax (φ ➝ ψ) → Normal2 Ax φ → Normal2 Ax ψ
| nec {φ}       : Normal2 Ax φ → Normal2 Ax (□φ)
| implyK φ ψ    : Normal2 Ax $ Axioms.ImplyK φ ψ
| implyS φ ψ χ  : Normal2 Ax $ Axioms.ImplyS φ ψ χ
| ec φ ψ        : Normal2 Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.Normal2

variable {Ax Ax₁ Ax₂ : Axiom α}

instance : Entailment.Łukasiewicz (Hilbert.Normal2 Ax) where
  implyK {_ _} := by constructor; apply Hilbert.Normal2.implyK;
  implyS {_ _ _} := by constructor; apply Hilbert.Normal2.implyS;
  elimContra {_ _} := by constructor; apply Hilbert.Normal2.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Normal2.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.Normal2 Ax) where
  nec h := by constructor; apply Hilbert.Normal2.nec; exact h.1;

lemma axm' {φ} : φ ∈ Ax → Hilbert.Normal2 Ax ⊢ φ := fun h ↦ ⟨⟨axm h⟩⟩

protected lemma rec!
  {motive   : (φ : Formula α) → (Normal2 Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α}, (h : φ ∈ Ax) → motive φ (axm' h))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Normal2 Ax) ⊢ φ ➝ ψ} → {hφ : (Normal2 Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Normal2 Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : Normal2 Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm h => apply axm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | implyK φ ψ => apply implyK;
  | implyS φ ψ χ => apply implyS;
  | ec φ ψ => apply ec;

open Axiom


section

inductive buildAxioms.Symbol
  | B
  | C4
  | CD
  | D
  | Dum
  | Five
  | Four
  | Grz
  | H
  | Hen
  | K
  | L
  | McK
  | Mk
  | P
  | Point2
  | Point3
  | Point4
  | T
  | Tc
  | Ver
  | WeakPoint2
  | WeakPoint3
  | Z
deriving DecidableEq

def buildAxioms (α : Type*) (l : List buildAxioms.Symbol)
  : Set (Formula α) :=
    (if l.contains .B          then { Axioms.B φ            | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .C4         then { Axioms.C4 φ           | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .CD         then { Axioms.CD φ           | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .D          then { Axioms.D φ            | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Dum        then { Axioms.Dum φ          | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Five       then { Axioms.Five φ         | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Four       then { Axioms.Four φ         | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Grz        then { Axioms.Grz φ          | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .H          then { Axioms.H φ            | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Hen        then { Axioms.Hen φ          | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .K          then { Axioms.K φ ψ          | (φ : Formula α) (ψ : Formula α) } else ∅) ∪
    (if l.contains .L          then { Axioms.L φ            | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .McK        then { Axioms.McK φ          | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Mk         then { Axioms.Mk φ ψ         | (φ : Formula α) (ψ : Formula α) } else ∅) ∪
    (if l.contains .P          then { Axioms.P }                                                else ∅) ∪
    (if l.contains .Point2     then { Axioms.Point2 φ       | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Point3     then { Axioms.Point3 φ ψ     | (φ : Formula α) (ψ : Formula α) } else ∅) ∪
    (if l.contains .T          then { Axioms.T φ            | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Tc         then { Axioms.Tc φ           | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .Ver        then { Axioms.Ver φ          | (φ : Formula α) }                 else ∅) ∪
    (if l.contains .WeakPoint2 then { Axioms.WeakPoint2 φ ψ | (φ : Formula α) (ψ : Formula α) } else ∅) ∪
    (if l.contains .WeakPoint3 then { Axioms.WeakPoint3 φ ψ | (φ : Formula α) (ψ : Formula α) } else ∅) ∪
    (if l.contains .Z          then { Axioms.Z φ            | (φ : Formula α) }                 else ∅)

variable {l : List buildAxioms.Symbol} {φ ψ χ : Formula α}

protected lemma buildAxioms.mem_axiomK (h : .K ∈ l := by decide) : Axioms.K φ ψ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomD (h : .D ∈ l := by decide) : Axioms.D φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomT (h : .T ∈ l := by decide) : Axioms.T φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomB (h : .B ∈ l := by decide) : Axioms.B φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomFour (h : .Four ∈ l := by decide) : Axioms.Four φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomFive (h : .Five ∈ l := by decide) : Axioms.Five φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomPoint2 (h : .Point2 ∈ l := by decide) : Axioms.Point2 φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomPoint3 (h : .Point3 ∈ l := by decide) : Axioms.Point3 φ ψ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomGrz (h : .Grz ∈ l := by decide) : Axioms.Grz φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

protected lemma buildAxioms.mem_axiomL (h : .L ∈ l := by decide) : Axioms.L φ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

attribute [simp, grind <=]
  buildAxioms.mem_axiomK
  buildAxioms.mem_axiomD
  buildAxioms.mem_axiomT
  buildAxioms.mem_axiomB
  buildAxioms.mem_axiomFour
  buildAxioms.mem_axiomFive
  buildAxioms.mem_axiomPoint2
  buildAxioms.mem_axiomPoint3
  buildAxioms.mem_axiomGrz
  buildAxioms.mem_axiomL

end

end Hilbert.Normal2


section


open Lean in
macro "defineModalLogic" name:ident "[" xs:ident,* "]" : command => do
  let xs ← xs.getElems.mapM $ λ stx => pure (Lean.mkIdentFrom stx stx.getId)

  let logicName := mkIdent (name.getId.appendAfter "'")

  let instHasAxiomK ←
    if xs.contains (mkIdent `K)
    then `(command| instance {α} : Entailment.HasAxiomK ($logicName α) where K φ ψ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomD ←
    if xs.contains (mkIdent `D)
    then `(command| instance {α} : Entailment.HasAxiomD ($logicName α) where D φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomT ←
    if xs.contains (mkIdent `T)
    then `(command| instance {α} : Entailment.HasAxiomT ($logicName α) where T φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomB ←
    if xs.contains (mkIdent `B)
    then `(command| instance {α} : Entailment.HasAxiomB ($logicName α) where B φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomFour ←
    if xs.contains (mkIdent `Four)
    then `(command| instance {α} : Entailment.HasAxiomFour ($logicName α) where Four φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomFive ←
    if xs.contains (mkIdent `Five)
    then `(command| instance {α} : Entailment.HasAxiomFive ($logicName α) where Five φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomPoint2 ←
    if xs.contains (mkIdent `Point2)
    then `(command| instance {α} : Entailment.HasAxiomPoint2 ($logicName α) where Point2 φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomPoint3 ←
    if xs.contains (mkIdent `Point3)
    then `(command| instance {α} : Entailment.HasAxiomPoint3 ($logicName α) where Point3 φ ψ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomGrz ←
    if xs.contains (mkIdent `Grz)
    then `(command| instance {α} : Entailment.HasAxiomGrz ($logicName α) where Grz φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomL ←
    if xs.contains (mkIdent `L)
    then `(command| instance {α} : Entailment.HasAxiomL ($logicName α) where L φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)

  `(
    abbrev $logicName (α : Type*) := Hilbert.Normal2 $ Hilbert.Normal2.buildAxioms α [$[$xs],*]

    namespace $logicName

    $instHasAxiomK
    $instHasAxiomT
    $instHasAxiomD
    $instHasAxiomPoint2
    $instHasAxiomPoint3
    $instHasAxiomGrz
    $instHasAxiomL
    $instHasAxiomB
    $instHasAxiomFour
    $instHasAxiomFive

    end $logicName
  )

open Hilbert.Normal2.buildAxioms.Symbol

defineModalLogic Dum         [K, T, Four, Dum]
defineModalLogic DumPoint2   [K, T, Four, Dum, Point2]
defineModalLogic DumPoint3   [K, T, Four, Dum, Point3]
defineModalLogic GL          [K, L]
defineModalLogic GLPoint2    [K, L, WeakPoint2]
defineModalLogic GLPoint3    [K, L, WeakPoint3]
defineModalLogic Grz         [K, Grz]
defineModalLogic GrzPoint2   [K, Grz, Point2]
defineModalLogic GrzPoint3   [K, Grz, Point3]
defineModalLogic K           [K]
defineModalLogic K4          [K, Four]
defineModalLogic K45         [K, Four, Five]
defineModalLogic K4Hen       [K, Four, Hen]
defineModalLogic K4McK       [K, Four, McK]
defineModalLogic K4Point2    [K, Four, WeakPoint2]
defineModalLogic K4Point3    [K, Four, WeakPoint3]
defineModalLogic K5          [K, Five]
defineModalLogic KB          [K, B]
defineModalLogic KB4         [K, B, Four]
defineModalLogic KB5         [K, B, Five]
defineModalLogic KD          [K, D]
defineModalLogic KD4         [K, D, Four]
defineModalLogic KD45        [K, D, Four, Five]
defineModalLogic KD4Point3Z  [K, D, Four, Point3, Z]
defineModalLogic KD5         [K, D, Five]
defineModalLogic KDB         [K, D, B]
defineModalLogic KHen        [K, Hen]
defineModalLogic KT          [K, T]
defineModalLogic KT4B        [K, T, Four, B]
defineModalLogic KTB         [K, T, B]
defineModalLogic KTc         [K, Tc]
defineModalLogic KTMk        [K, T, Mk]
defineModalLogic N           []
defineModalLogic NP          [P]
defineModalLogic S4          [K, T, Four]
defineModalLogic S4H         [K, T, Four, H]
defineModalLogic S4McK       [K, T, Four, McK]
defineModalLogic S4Point2    [K, T, Four, Point2]
defineModalLogic S4Point2McK [K, T, Four, Point2, McK]
defineModalLogic S4Point3    [K, T, Four, Point3]
defineModalLogic S4Point3McK [K, T, Four, Point3, McK]
defineModalLogic S4Point4    [K, T, Four, Point4]
defineModalLogic S4Point4McK [K, T, Four, Point4, McK]
defineModalLogic S5          [K, T, Five]
defineModalLogic S5Grz       [K, T, Five, Grz]
defineModalLogic Triv        [K, T, Tc]
defineModalLogic Ver         [K, Ver]

end

end LO.Modal

end
