import Logic.Predicate.FirstOrder.Language
import Logic.Predicate.Coding

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

inductive Derivation : Finset (SyntacticFormula L) → Type _
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
    Derivation (insert (free p) (shifts Δ)) → Derivation (insert (∀' p) Δ)
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
      have : ⊩ insert (free p) (shifts Γ) := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊩ insert (∀' p) Γ := all Γ p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)      
  | _, ex Δ t p d,           Γ, h =>
      have : ⊩ insert (subst t p) Γ := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊩ insert (∃' p) Γ := ex Γ t p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)     

section Hom
variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.func k)] [∀ k, DecidableEq (L₁.rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.func k)] [∀ k, DecidableEq (L₂.rel k)]
  {Δ₁ Γ₁ : Finset (SyntacticFormula L₁)}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)} :
     shifts (Finset.image Φ.onSubFormula₁ Δ) = (Finset.image Φ.onSubFormula₁ (shifts Δ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, SubFormula.onSubFormula₁_shift]

def onDerivation (Φ : L₁ →ᵥ L₂) : ∀ {Δ : Finset (SyntacticFormula L₁)}, ⊩ Δ → ⊩ Finset.image Φ.onSubFormula₁ Δ
  | _, AxL Δ r v hrel hnrel =>
      AxL _ (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
        (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h            => verum _ (by simpa using Finset.mem_image_of_mem Φ.onSubFormula₁ h)
  | _, orLeft Δ p q d       =>
      have : ⊩ insert (Φ.onSubFormula₁ p ⋎ Φ.onSubFormula₁ q) (Finset.image Φ.onSubFormula₁ Δ) :=
        orLeft _ _ _ (Derivation.cast (onDerivation Φ d) (by simp))
      Derivation.cast this (by simp)
  | _, orRight Δ p q d      =>
      have : ⊩ insert (Φ.onSubFormula₁ p ⋎ Φ.onSubFormula₁ q) (Finset.image Φ.onSubFormula₁ Δ) :=
        orRight _ _ _ (Derivation.cast (onDerivation Φ d) (by simp))
      Derivation.cast this (by simp) 
  | _, and Δ p q dp dq      =>
      have : ⊩ insert (Φ.onSubFormula₁ p ⋏ Φ.onSubFormula₁ q) (Finset.image Φ.onSubFormula₁ Δ) :=
        and _ _ _ (Derivation.cast (onDerivation Φ dp) (by simp)) (Derivation.cast (onDerivation Φ dq) (by simp))
      Derivation.cast this (by simp)
  | _, all Δ p d            =>
      have : ⊩ insert (∀' Φ.onSubFormula₁ p) (Finset.image Φ.onSubFormula₁ Δ) :=
        all _ _ (by simpa[←SubFormula.onSubFormula₁_free, shifts_image] using onDerivation Φ d)
      Derivation.cast this (by simp)
  | _, ex Δ t p d           =>
      have : ⊩ insert (∃' Φ.onSubFormula₁ p) (Finset.image Φ.onSubFormula₁ Δ) :=
        ex _ (Φ.onSubTerm t) _ (by simpa[←SubFormula.onSubFormula₁_subst] using onDerivation Φ d)
      Derivation.cast this (by simp)

end Hom

variable [∀ k, Encodable (L.func k)] {μ : Type _} [Encodable μ]

def decomp : Finset (SyntacticTerm L) → SyntacticFormula L → Finset (SyntacticFormula L) → Option (Set $ Finset $ SyntacticFormula L)
| _, rel _ _,  _ => none
| _, nrel _ _, _ => none
| _, ⊤,        _ => some ∅
| _, ⊥,        _ => none
| _, p ⋏ q,    Γ => some { insert p Γ, insert q Γ }
| _, p ⋎ q,    Γ => some { insert q (insert p Γ) }
| _, ∀' p,     Γ => some { insert (SubFormula.free p) (shifts Γ) }
| s, ∃' p,     Γ => some { s.image (subst · p) ∪ Γ }

#check SubFormula.rel! Language.equal 2 Language.EqRel.equal (#0 :> #0 :> Fin.nil)

#eval SubTerm.toNat (SubTerm.func! (μ := ℕ) (n := 0) Language.ring 2 Language.RingFunc.add (&0 :> &1 :> Fin.nil))


#eval @instanceEnum Language.ring _ _ _
  (SubFormula.rel! Language.ring 2 Language.RingRel.le (#0 :> #0 :> Fin.nil)) 2

end Derivation

end FirstOrder

