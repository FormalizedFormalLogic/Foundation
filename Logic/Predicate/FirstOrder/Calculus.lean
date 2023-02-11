import Logic.Predicate.FirstOrder.Language
import Mathlib.Data.Finset.Sort

universe u v

namespace FirstOrder
open SubFormula
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def shifts (Δ : Finset (SyntacticSubFormula L n)) :
  Finset (SyntacticSubFormula L n) := Δ.map shiftEmb

@[simp] lemma mem_shifts_iff (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shift p ∈ shifts Δ ↔ p ∈ Δ :=
  Finset.mem_map' _

@[simp] lemma shifts_ss (Δ Γ : Finset (SyntacticSubFormula L n)) :
    shifts Δ ⊆ shifts Γ ↔ Δ ⊆ Γ := Finset.map_subset_map

inductive Derivation : Finset (SyntacticFormula L) → Type u
| AxL     : ∀ (Δ : Finset (SyntacticFormula L)) {k} (r : L.rel k) (v : Fin k → SyntacticTerm L),
    rel r v ∈ Δ → nrel r v ∈ Δ → Derivation Δ
| verum   : ∀ (Δ : Finset (SyntacticFormula L)), ⊤ ∈ Δ → Derivation Δ
| orLeft  : ∀ (Δ : Finset (SyntacticFormula L)) (p q : SyntacticFormula L),
    Derivation (insert p Δ) → Derivation (insert (p ⋎ q) Δ)
| orRight : ∀ (Δ : Finset (SyntacticFormula L)) (p q : SyntacticFormula L),
    Derivation (insert q Δ) → Derivation (insert (p ⋎ q) Δ)
| and     : ∀ (Δ : Finset (SyntacticFormula L)) (p q : SyntacticFormula L),
    Derivation (insert p Δ) → Derivation (insert q Δ) → Derivation (insert (p ⋏ q) Δ)
| all     : ∀ (Δ : Finset (SyntacticFormula L)) (p : SyntacticSubFormula L 1),
    Derivation (insert (push p) (shifts Δ)) → Derivation (insert (∀' p) Δ)
| ex      : ∀ (Δ : Finset (SyntacticFormula L)) (t : SyntacticTerm L) (p : SyntacticSubFormula L 1),
    Derivation (insert (subst t p) Δ) → Derivation (insert (∃' p) Δ)

instance : HasVdash (Finset (SyntacticFormula L)) (Type _) := ⟨Derivation⟩

structure provable (T : Theory L ℕ) (p : SyntacticFormula L) where
  leftHand : Finset (SyntacticFormula L)
  hleftHand : ↑leftHand ⊆ SubFormula.neg '' T
  derivation : ⊩ insert p leftHand

namespace Derivation
variable {Δ Γ : Finset (SyntacticFormula L)}

section Repr
variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)]

protected unsafe def repr : {Δ : Finset (SyntacticFormula L)} → Derivation Δ → String
  | _, AxL Δ r v _ _ =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(AxL)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (rel r v) ++ ", " ++ reprStr (nrel r v) ++ ", " ++
      reprStr (Δ \ {rel r v, nrel r v}) ++ "$}\n\n"
  | _, verum Δ _     =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(Verum)}\n" ++
      "\\UnaryInfC{$\\Vdash \\top," ++ reprStr Δ ++ "$}\n\n"
  | _, orLeft Δ p q d =>
      d.repr ++
      "\\RightLabel{\\scriptsize(OrLeft)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (p ⋎ q) ++ "," ++ reprStr Δ ++ "$}\n\n"
  | _, orRight Δ p q d =>
      d.repr ++
      "\\RightLabel{\\scriptsize(OrRight)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (p ⋎ q) ++ "," ++ reprStr Δ ++ "$}\n\n"
  | _, and Δ p q dp dq =>
      dp.repr ++
      dq.repr ++
      "\\RightLabel{\\scriptsize(And)}\n" ++
      "\\BinaryInfC{$\\Vdash " ++ reprStr (p ⋏ q) ++ ", " ++ reprStr Δ ++ "$}\n\n"
  | _, all Δ p d =>
      d.repr ++
      "\\RightLabel{\\scriptsize(All)}\n" ++
      "\\UnaryInfC{$\\Vdash" ++ reprStr (∀' p) ++ ", " ++ reprStr Δ ++ "$}\n\n"
  | _, ex Δ _ p d =>
      d.repr ++
      "\\RightLabel{\\scriptsize(Exists)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (∃' p) ++ ", " ++ reprStr Δ ++ "$}\n\n"

unsafe instance : Repr (Derivation Δ) where
  reprPrec d _ := d.repr

def dtest := @AxL Language.equal _ _
  { ∀' ∃' SubFormula.nrel! Language.equal 2 Language.EqRel.equal (&0 :> #1 :> Fin.nil),
    SubFormula.rel! Language.equal 2 Language.EqRel.equal (&0 :> &1 :> Fin.nil),
    SubFormula.nrel! Language.equal 2 Language.EqRel.equal (&0 :> &1 :> Fin.nil) }
  2 Language.EqRel.equal (&0 :> &1 :> Fin.nil) (by simp) (by simp)

end Repr

protected def cast (d : ⊩ Δ) (e : Δ = Γ) : ⊩ Γ := cast (by rw[e]) d

def weakening : ∀ {Δ}, ⊩ Δ → ∀ {Γ : Finset (SyntacticFormula L)}, Δ ⊆ Γ → ⊩ Γ
  | _, AxL Δ r v hrel hnrel, Γ, h => AxL Γ r v (h hrel) (h hnrel)
  | _, verum Δ htop,         Γ, h => verum Γ (h htop)
  | _, orLeft Δ p q d,       Γ, h =>
      have : ⊩ insert p Γ := weakening d (Finset.insert_subset_insert p (Finset.insert_subset.mp h).2)
      have : ⊩ insert (p ⋎ q) Γ := orLeft Γ p q this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)
  | _, orRight Δ p q d,      Γ, h =>
      have : ⊩ insert q Γ := weakening d (Finset.insert_subset_insert q (Finset.insert_subset.mp h).2)
      have : ⊩ insert (p ⋎ q) Γ := orRight Γ p q this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)    
  | _, and Δ p q dp dq,      Γ, h =>
      have dp : ⊩ insert p Γ := weakening dp (Finset.insert_subset_insert p (Finset.insert_subset.mp h).2) 
      have dq : ⊩ insert q Γ := weakening dq (Finset.insert_subset_insert q (Finset.insert_subset.mp h).2) 
      have : ⊩ insert (p ⋏ q) Γ := and Γ p q dp dq
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)    
  | _, all Δ p d,            Γ, h =>
      have : ⊩ insert (push p) (shifts Γ) := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊩ insert (∀' p) Γ := all Γ p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)      
  | _, ex Δ t p d,           Γ, h =>
      have : ⊩ insert (subst t p) Γ := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊩ insert (∃' p) Γ := ex Γ t p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)     

end Derivation

end FirstOrder

