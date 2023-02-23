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

lemma shifts_insert (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shifts (insert p Δ) = insert (shift p) (shifts Δ) :=
  by simp[shifts, shiftEmb_eq_shift]

inductive Derivation : Finset (SyntacticFormula L) → Type _
| AxL   : ∀ (Δ : Finset (SyntacticFormula L)) {k} (r : L.rel k) (v : Fin k → SyntacticTerm L),
    rel r v ∈ Δ → nrel r v ∈ Δ → Derivation Δ
| verum : ∀ (Δ : Finset (SyntacticFormula L)), ⊤ ∈ Δ → Derivation Δ
| or  : ∀ (Δ : Finset (SyntacticFormula L)) (p q : SyntacticFormula L),
    Derivation (insert q $ insert p Δ) → Derivation (insert (p ⋎ q) Δ)
| and   : ∀ (Δ : Finset (SyntacticFormula L)) (p q : SyntacticFormula L),
    Derivation (insert p Δ) → Derivation (insert q Δ) → Derivation (insert (p ⋏ q) Δ)
| all   : ∀ (Δ : Finset (SyntacticFormula L)) (p : SyntacticSubFormula L 1),
    Derivation (insert (free p) (shifts Δ)) → Derivation (insert (∀' p) Δ)
| ex    : ∀ (Δ : Finset (SyntacticFormula L)) (t : SyntacticTerm L) (p : SyntacticSubFormula L 1),
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
  | _, AxL Δ _ _ _ _ =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(AxL)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr Δ ++ "$}\n\n"
  | _, verum Δ _     =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr Δ ++ "$}\n\n"
  | _, or Δ p q d =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (insert (p ⋎ q) Δ) ++ "$}\n\n"
  | _, and Δ p q dp dq =>
      dp.repr ++
      dq.repr ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$\\Vdash " ++ reprStr (insert (p ⋏ q) Δ) ++ "$}\n\n"
  | _, all Δ p d =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (insert (∀' p) Δ) ++ "$}\n\n"
  | _, ex Δ _ p d =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$\\Vdash " ++ reprStr (insert (∃' p) Δ) ++ "$}\n\n"

unsafe instance : Repr (⊩ Δ) where
  reprPrec d _ := d.repr

end Repr

protected def cast (d : Derivation Δ) (e : Δ = Γ) : ⊩ Γ := cast (by simp[HasVdash.vdash, e]) d

def weakening : ∀ {Δ}, ⊩ Δ → ∀ {Γ : Finset (SyntacticFormula L)}, Δ ⊆ Γ → ⊩ Γ
  | _, AxL Δ r v hrel hnrel, Γ, h => AxL Γ r v (h hrel) (h hnrel)
  | _, verum Δ htop,         Γ, h => verum Γ (h htop)
  | _, or Δ p q d,       Γ, h =>
      have : ⊩ insert q (insert p Γ) :=
        weakening d (Finset.insert_subset_insert q $ Finset.insert_subset_insert p (Finset.insert_subset.mp h).2)
      have : ⊩ insert (p ⋎ q) Γ := or Γ p q this
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

def or' {p q : SyntacticFormula L} (h : p ⋎ q ∈ Δ) (d : ⊩ insert q (insert p Δ)) : ⊩ Δ :=
  weakening (or Δ p q d) (by simp[Finset.insert_subset, h])

def and' {p q : SyntacticFormula L} (h : p ⋏ q ∈ Δ) (dp : ⊩ insert p Δ) (dq : ⊩ insert q Δ) : ⊩ Δ :=
  weakening (and Δ p q dp dq) (by simp[Finset.insert_subset, h])  

def all' {p : SyntacticSubFormula L 1} (h : ∀' p ∈ Δ) (d : ⊩ insert (free p) (shifts Δ)) : ⊩ Δ :=
  weakening (all Δ p d) (by simp[Finset.insert_subset, h])

def ex' {p : SyntacticSubFormula L 1} (t : SyntacticTerm L) (h : ∃' p ∈ Δ)
  (d : ⊩ insert (subst t p) Δ) : ⊩ Δ :=
  weakening (ex Δ t p d) (by simp[Finset.insert_subset, h])

def em {p : SyntacticFormula L} {Δ : Finset (SyntacticFormula L)} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊩ Δ := by
  induction p using SubFormula.formulaRec generalizing Δ
  case hverum    => exact verum Δ hpos
  case hfalsum   => exact verum Δ hneg
  case hrel r v  => exact AxL Δ r v hpos hneg 
  case hnrel r v => exact AxL Δ r v hneg hpos 
  case hall p ih =>
    exact all' hpos $ ex' (p := ~ shift p) &0
      (by simp; exact Or.inr (by simpa[-Finset.mem_map, shiftEmb_eq_shift] using Finset.mem_map_of_mem shiftEmb hneg))
      (by simpa using ih (by simp) (by simp))
  case hex p ih =>
    simp at hneg
    exact all' hneg $ ex' (p := shift p) &0
      (by simp; exact Or.inr (by simpa[-Finset.mem_map, shiftEmb_eq_shift] using Finset.mem_map_of_mem shiftEmb hpos))
      (by simpa using ih (by simp) (by simp))
  case hand p q ihp ihq =>
    simp at hneg
    exact or' hneg $ and' (p := p) (q := q) (by simp[hpos]) (ihp (by simp) (by simp)) (ihq (by simp) (by simp))
  case hor p q ihp ihq =>
    simp at hneg
    exact or' hpos $ and' (p := ~p) (q := ~q) (by simp[hneg]) (ihp (by simp) (by simp)) (ihq (by simp) (by simp))

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
  | _, or Δ p q d           =>
      have : ⊩ insert (Φ.onSubFormula₁ p ⋎ Φ.onSubFormula₁ q) (Finset.image Φ.onSubFormula₁ Δ) :=
        or _ _ _ (Derivation.cast (onDerivation Φ d) (by simp))
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

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSubFormula L 1)
  (h : ⊩ (v.map (subst · p)).toFinset ∪ Γ) : ⊩ insert (∃' p) Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (Finset.subset_insert _ Γ)
  · exact Derivation.cast (ih (Γ := insert (∃' p) Γ)
      (Derivation.cast (ex _ t p h) (by ext r; simp))) (by simp)


def deriveList? (tmax : ℕ) : ℕ → (Γ : List (SyntacticFormula L)) → Option (⊩ Γ.toFinset)
  | 0,     _      => none
  | _ + 1, []     => none
  | s + 1, p :: Γ => if h : ~p ∈ Γ then some (em (p := p) (by simp) (by simp[h]))
      else match p with
      | ⊤        => some $ verum _ (by simp)
      | ⊥        => (deriveList? tmax s Γ).map (fun d => weakening d (by simpa using Finset.subset_insert ⊥ Γ.toFinset))
      | rel r v  => (deriveList? tmax s $ Γ ++ [rel r v]).map (fun d => d.cast $ by ext; simp; tauto)
      | nrel r v => (deriveList? tmax s $ Γ ++ [nrel r v]).map (fun d => d.cast $ by ext; simp; tauto)
      | p ⋎ q    => (deriveList? tmax s (Γ ++ [p, q])).map
          fun d => (or Γ.toFinset p q (d.cast $ by ext; simp; tauto)).cast (by ext; simp)
      | p ⋏ q    => (deriveList? tmax s (Γ ++ [p])).bind fun dp => (deriveList? tmax s (Γ ++ [q])).map
          fun dq => (and Γ.toFinset p q (dp.cast $ by ext; simp[or_comm]) (dq.cast $ by ext; simp[or_comm])).cast 
            (by ext; simp[or_comm])
      | ∀' p     => (deriveList? tmax s (Γ.map shift ++ [free p])).map
          fun d => (all (Γ.toFinset) p (d.cast $ by ext; simp[shifts, shiftEmb, or_comm])).cast (by simp)
      | ∃' p     => (deriveList? tmax s (Γ ++ [∃' p] ++ (SubTerm.enumLtList tmax).map (subst · p))).map
          fun d => (exOfInstances (Γ := insert (∃' p) Γ.toFinset) (SubTerm.enumLtList tmax)
            p (d.cast $ by ext; simp[or_comm])).cast (by ext; simp)

def derive? (tmax s : ℕ) (p : SyntacticFormula L) : Option (⊩ ({p} : Finset (SyntacticFormula L))) :=
  deriveList? tmax s [p]


variable (p q : SyntacticFormula Language.equal)

#eval derive? 8 32 (L := Language.equal) 
  (SubFormula.rel! Language.equal 2 Language.EqRel.equal ![&0, &1] ⟶
   (∃' ∃' SubFormula.rel! Language.equal 2 Language.EqRel.equal ![#0, #1]))

#eval derive? 32 32 (L := Language.equal) 
  (SubFormula.rel! Language.equal 2 Language.EqRel.equal ![&0, &1] ⟶
   (∃' ∃' SubFormula.rel! Language.equal 2 Language.EqRel.equal ![#0, #1]))

#eval derive? 32 32 (L := Language.equal) 
  ((∀' ∀' SubFormula.rel! Language.equal 2 Language.EqRel.equal ![#0, #1]) ⋎
   (∃' ∃' ~ SubFormula.rel! Language.equal 2 Language.EqRel.equal ![#0, #1]))

#eval derive? 32 32 (L := Language.relational (fun _ => ℕ)) 
  ((( SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 0 ![] ⟶ 
      SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 1 ![]) ⟶
    SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 0 ![]) ⟶
  SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 0 ![])

#eval derive? 32 32 (L := Language.relational (fun _ => ℕ)) 
  ((( SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 0 ![] ⋎
      SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 1 ![]) ⟶
    ( SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 1 ![] ⋎
      SubFormula.rel! (Language.relational (fun _ => ℕ)) 0 0 ![])))

#eval derive? 4 32 (L := Language.relational (fun _ => ℕ)) 
  (∀' ( SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0] ⋎
        SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 1 ![#0]) ⟶
   ∀' ( SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 1 ![#0] ⋎
        SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0]))


#eval derive? 4 32 (L := Language.relational (fun _ => ℕ)) 
  ( ∀'(SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0] ⟶
    ∃' SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0]))

end Derivation

end FirstOrder

