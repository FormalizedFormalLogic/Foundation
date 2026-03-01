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

lemma weakerThan_of_provable_axioms (hs : Normal2 Ax₂ ⊢* Ax₁) : (Normal2 Ax₁) ⪯ (Normal2 Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Normal2.rec! with
  | axm h => apply hs; assumption;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

@[grind <=]
lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Normal2 Ax₁) ⪯ (Normal2 Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  exact Normal2.axm' $ h hφ;

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
deriving DecidableEq, Repr

def buildAxioms.Symbol.arity : buildAxioms.Symbol → ℕ
  | K
  | Mk
  | Point3
  | WeakPoint2
  | WeakPoint3 => 2
  | P => 0
  | _ => 1

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

namespace buildAxioms

variable {l : List buildAxioms.Symbol} {φ ψ χ : Formula α}

@[grind <=]
lemma subset_of_subset (h : l₁ ⊆ l₂) : buildAxioms α l₁ ⊆ buildAxioms α l₂ := by
  intro A hA;
  simp only [buildAxioms, List.contains_eq_mem, decide_eq_true_eq, Set.mem_union,
    Set.mem_ite_empty_right, Set.mem_setOf_eq, Set.mem_singleton_iff] at hA ⊢;
  repeat rw [or_assoc] at hA;
  rcases hA with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
  grind only [= List.subset_def];

lemma mem_axiomK (h : .K ∈ l := by decide) : Axioms.K φ ψ ∈ buildAxioms α l := by
  simp only [buildAxioms, Set.mem_union, Set.mem_ite_empty_right, Set.mem_setOf_eq];
  grind;

/-
attribute [simp, grind <=]
  mem_axiomB
  mem_axiomC4
  mem_axiomCD
  mem_axiomD
  mem_axiomDum
  mem_axiomFive
  mem_axiomFour
  mem_axiomGrz
  mem_axiomH
  mem_axiomHen
  mem_axiomK
  mem_axiomL
  mem_axiomMcK
  mem_axiomMk
  mem_axiomP
  mem_axiomPoint2
  mem_axiomPoint3
  mem_axiomPoint4
  mem_axiomT
  mem_axiomTc
  mem_axiomVer
  mem_axiomWeakPoint2
  mem_axiomWeakPoint3
  mem_axiomZ
-/

end buildAxioms

end

section

open Lean Elab Command Term Meta Qq
open buildAxioms

local elab "#defineModalLogic" name:ident axioms:term : command => do
  let logicName := `_root_.LO.Modal |>.append name.getId

  -- let axioms ← axioms.getElems.mapM $ λ stx => pure (Lean.mkIdentFrom stx stx.getId)

  dbg_trace logicName
  dbg_trace axioms

  elabCommand (←`(protected abbrev $(mkIdent logicName) (α) := Hilbert.Normal2 $ Hilbert.Normal2.buildAxioms α $axioms))
  -- elabCommand (←`(#eval String.toSlice $axioms))

  /-
  if axioms.contains (mkIdent `K) then elabCommand (←`(
    instance {α} : Entailment.HasAxiomK ($(mkIdent logicName) α) := ⟨by intros; constructor; apply Hilbert.Normal2.axm $ mem_axiomK⟩
  ))
  -/

  /-
  if axioms.contains (mkIdent `D) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomD ($logicName α) where D φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `T) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomT ($logicName α) where T φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `B) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomB ($logicName α) where B φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `Four) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomFour ($logicName α) where Four φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `Five) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomFive ($logicName α) where Five φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `Point2) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomPoint2 ($logicName α) where Point2 φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `Point3) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomPoint3 ($logicName α) where Point3 φ ψ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `Grz) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomGrz ($logicName α) where Grz φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `L) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomL ($logicName α) where L φ := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `P) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomP ($logicName α) where P := by constructor; apply Hilbert.Normal2.axm; simp))
  if axioms.contains (mkIdent `McK) then
    elabCommand (←`(instance {α} : Entailment.HasAxiomMcK ($logicName α) where McK φ := by constructor; apply Hilbert.Normal2.axm; simp))
  -/


open Hilbert.Normal2.buildAxioms.Symbol

whatsnew in
#defineModalLogic Dum         [.K, .T, .Four, .Dum]
#defineModalLogic DumPoint2   [.K, .T, .Four, .Dum, .Point2]
#defineModalLogic DumPoint3   [.K, .T, .Four, .Dum, .Point3]
#defineModalLogic GL          [.K, .L]
#defineModalLogic GLPoint2    [.K, .L, .WeakPoint2]
#defineModalLogic GLPoint3    [.K, .L, .WeakPoint3]
#defineModalLogic Grz         [.K, .Grz]
#defineModalLogic GrzPoint2   [.K, .Grz, .Point2]
#defineModalLogic GrzPoint3   [.K, .Grz, .Point3]
#defineModalLogic K           [.K]
#defineModalLogic K4          [.K, .Four]
#defineModalLogic K45         [.K, .Four, .Five]
#defineModalLogic K4Hen       [.K, .Four, .Hen]
#defineModalLogic K4McK       [.K, .Four, .McK]
#defineModalLogic K4Point2    [.K, .Four, .WeakPoint2]
#defineModalLogic K4Point2Z   [.K, .Four, .WeakPoint2, .Z]
#defineModalLogic K4Point3    [.K, .Four, .WeakPoint3]
#defineModalLogic K4Point3Z   [.K, .Four, .WeakPoint3, .Z]
#defineModalLogic K4Z         [.K, .Four, .Z]
#defineModalLogic K5          [.K, .Five]
#defineModalLogic KB          [.K, .B]
#defineModalLogic KB4         [.K, .B, .Four]
#defineModalLogic KB5         [.K, .B, .Five]
#defineModalLogic KD          [.K, .D]
#defineModalLogic KD4         [.K, .D, .Four]
#defineModalLogic KD45        [.K, .D, .Four, .Five]
#defineModalLogic KD4Point3Z  [.K, .D, .Four, .Point3, .Z]
#defineModalLogic KD5         [.K, .D, .Five]
#defineModalLogic KDB         [.K, .D, .B]
#defineModalLogic KHen        [.K, .Hen]
#defineModalLogic KP          [.K, .P]
#defineModalLogic KT          [.K, .T]
#defineModalLogic KT4B        [.K, .T, .Four, .B]
#defineModalLogic KTB         [.K, .T, .B]
#defineModalLogic KTc         [.K, .Tc]
#defineModalLogic KTMk        [.K, .T, .Mk]
#defineModalLogic N           []
#defineModalLogic NP          [.P]
#defineModalLogic S4          [.K, .T, .Four]
#defineModalLogic S4H         [.K, .T, .Four, .H]
#defineModalLogic S4McK       [.K, .T, .Four, .McK]
#defineModalLogic S4Point2    [.K, .T, .Four, .Point2]
#defineModalLogic S4Point2McK [.K, .T, .Four, .Point2, .McK]
#defineModalLogic S4Point3    [.K, .T, .Four, .Point3]
#defineModalLogic S4Point3McK [.K, .T, .Four, .Point3, .McK]
#defineModalLogic S4Point4    [.K, .T, .Four, .Point4]
#defineModalLogic S4Point4McK [.K, .T, .Four, .Point4, .McK]
#defineModalLogic S5          [.K, .T, .Five]
#defineModalLogic S5Grz       [.K, .T, .Five, .Grz]
#defineModalLogic Triv        [.K, .T, .Tc]
#defineModalLogic Ver         [.K, .Ver]

/-
open Lean
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
  let instHasAxiomP ←
    if xs.contains (mkIdent `P)
    then `(command| instance {α} : Entailment.HasAxiomP ($logicName α) where P := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomMcK ←
    if xs.contains (mkIdent `McK)
    then `(command| instance {α} : Entailment.HasAxiomMcK ($logicName α) where McK φ := by constructor; apply Hilbert.Normal2.axm; simp)
    else `(section end)
  let instHasAxiomTc ←
    if xs.contains (mkIdent `Tc)
    then `(command| instance {α} : Entailment.HasAxiomTc ($logicName α) where Tc φ := by constructor; apply Hilbert.Normal2.axm; simp)
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
    $instHasAxiomP
    $instHasAxiomMcK
    $instHasAxiomTc

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
defineModalLogic K4Point2Z   [K, Four, WeakPoint2, Z]
defineModalLogic K4Point3    [K, Four, WeakPoint3]
defineModalLogic K4Point3Z   [K, Four, WeakPoint3, Z]
defineModalLogic K4Z         [K, Four, Z]
defineModalLogic K5          [K, Five]
defineModalLogic KB          [K, B]
defineModalLogic KP          [K, P]
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

section

open Hilbert.Normal2

variable {α}

instance [DecidableEq α] {L : Logic α} [L.IsNormal] : (Modal.K' α) ⪯ L := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.Normal2.rec! with
  | axm h =>
    rcases (by simpa [Hilbert.Normal2.buildAxioms] using h) with (⟨_, _, rfl⟩)
    . simp;
  | nec hφ => apply nec! hφ;
  | mdp hφψ hφ => exact mdp! hφψ hφ
  | implyK | implyS | ec => simp;


instance : Entailment.KP (Modal.KP' α) where
instance : Entailment.KD (Modal.KD' α) where

instance [DecidableEq α] : Modal.KP' α ≊ Modal.KD' α := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms;
    rintro φ hφ;
    rcases (by simpa [Hilbert.Normal2.buildAxioms] using hφ) with (rfl | ⟨_, _, rfl⟩) <;> simp;
  . apply weakerThan_of_provable_axioms;
    rintro φ hφ;
    rcases (by simpa [Hilbert.Normal2.buildAxioms] using hφ) with (⟨_, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;


instance : Entailment.S5Grz (Modal.S5Grz' α) where
instance : Entailment.Triv (Modal.Triv' α) where

instance [DecidableEq α] : Modal.S5Grz' α ≊ Modal.Triv' α := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms;
    rintro φ hφ;
    rcases (by simpa [Hilbert.Normal2.buildAxioms, or_assoc] using hφ) with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [axiomK!, axiomT!, axiomFive!, axiomGrz!];
  . apply weakerThan_of_provable_axioms;
    rintro φ hφ;
    rcases (by simpa [Hilbert.Normal2.buildAxioms, or_assoc] using hφ) with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp only [axiomK!, axiomT!, axiomTc!];


noncomputable instance  [DecidableEq α] [Modal.K4McK' α ⪯ Hilbert.Normal2 Ax] : Entailment.K4McK (Hilbert.Normal2 Ax) where
  K _ _ := Entailment.WeakerThan.pbl (𝓢 := Modal.K4McK' α) axiomK! |>.some
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Modal.K4McK' α) axiomFour! |>.some
  McK _ := Entailment.WeakerThan.pbl (𝓢 := Modal.K4McK' α) axiomMcK! |>.some
-/

end

end Hilbert.Normal2

end LO.Modal

end
