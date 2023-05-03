import Logic.Predicate.FirstOrder.Language
import Logic.Predicate.Coding

universe u v

namespace FirstOrder

abbrev Sequent (L : Language.{u}) := Finset (SyntacticFormula L)

open SubFormula
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def shifts (Δ : Finset (SyntacticSubFormula L n)) :
  Finset (SyntacticSubFormula L n) := Δ.map shiftEmb

lemma shifts_eq_image (Δ : Finset (SyntacticSubFormula L n)) : shifts Δ = Δ.image shift := Finset.map_eq_image _ _

@[simp] lemma mem_shifts_iff {p : SyntacticSubFormula L n} {Δ : Finset (SyntacticSubFormula L n)} :
    shift p ∈ shifts Δ ↔ p ∈ Δ :=
  Finset.mem_map' _

@[simp] lemma shifts_ss (Δ Γ : Finset (SyntacticSubFormula L n)) :
    shifts Δ ⊆ shifts Γ ↔ Δ ⊆ Γ := Finset.map_subset_map

lemma shifts_insert (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shifts (insert p Δ) = insert (shift p) (shifts Δ) :=
  by simp[shifts, shiftEmb_eq_shift]

lemma shifts_erase (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shifts (Δ.erase p) = (shifts Δ).erase (shift p) :=
  by simp[shifts, shiftEmb_eq_shift]

inductive DerivationCutRestricted (P : SyntacticFormula L → Prop) : Sequent L → Type u
| axL   : ∀ (Δ : Sequent L) {k} (r : L.rel k) (v : Fin k → SyntacticTerm L),
    rel r v ∈ Δ → nrel r v ∈ Δ → DerivationCutRestricted P Δ
| verum : ∀ (Δ : Sequent L), ⊤ ∈ Δ → DerivationCutRestricted P Δ
| or    : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    DerivationCutRestricted P (insert p $ insert q Δ) → DerivationCutRestricted P (insert (p ⋎ q) Δ)
| and   : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    DerivationCutRestricted P (insert p Δ) → DerivationCutRestricted P (insert q Δ) → DerivationCutRestricted P (insert (p ⋏ q) Δ)
| all   : ∀ (Δ : Sequent L) (p : SyntacticSubFormula L 1),
    DerivationCutRestricted P (insert (free p) (shifts Δ)) → DerivationCutRestricted P (insert (∀' p) Δ)
| ex    : ∀ (Δ : Sequent L) (t : SyntacticTerm L) (p : SyntacticSubFormula L 1),
    DerivationCutRestricted P (insert (⟦↦ t⟧ p) Δ) → DerivationCutRestricted P (insert (∃' p) Δ)
| cut   : ∀ (Δ Γ : Sequent L) (p : SyntacticFormula L), P p →
    DerivationCutRestricted P (insert p Δ) → DerivationCutRestricted P (insert (~p) Γ) → DerivationCutRestricted P (Δ ∪ Γ)

notation :45 "⊢ᶜ[" P "] " Γ:45 => DerivationCutRestricted P Γ

abbrev Derivation : Sequent L → Type u := DerivationCutRestricted (fun _ => False)
prefix:45 "⊢ᵀ " => Derivation

abbrev DerivationCut : Sequent L → Type u := DerivationCutRestricted (fun _ => True)

prefix:45 "⊢ᶜ " => DerivationCut

abbrev DerivationClx (c : ℕ) : Sequent L → Type u := DerivationCutRestricted (·.complexity < c)

notation :45 "⊢ᶜ[< " c "] " Γ:45 => DerivationClx c Γ

abbrev DerivationList (G : List (SyntacticFormula L)) := ⊢ᶜ G.toFinset

abbrev Derivation₁ (p : SyntacticFormula L) := ⊢ᶜ ({p} : Sequent L)

abbrev Derivation.Valid (σ : Sentence L) := ⊢ᵀ ({emb σ} : Sequent L)

structure Proof (T : Theory L) (σ : Sentence L) where
  leftHand : Finset (Sentence L)
  hleftHand : ↑leftHand ⊆ SubFormula.neg '' T
  derivation : ⊢ᶜ ((insert σ leftHand).image emb : Sequent L)

instance : HasTurnstile (Sentence L) (Type u) := ⟨Proof⟩

namespace DerivationCutRestricted
variable {P : SyntacticFormula L → Prop} {Δ Δ₁ Δ₂ Γ : Sequent L}

def length : {Δ : Sequent L} → DerivationCutRestricted P Δ → ℕ 
  | _, axL Δ _ _ _ _     => 0
  | _, verum Δ _         => 0
  | _, or _ _ _ d        => d.length.succ
  | _, and _ _ _ dp dq   => (max dp.length dq.length).succ
  | _, all _ _ d         => d.length.succ
  | _, ex _ _ _ d        => d.length.succ
  | _, cut _ _ _ _ dp dn => (max dp.length dn.length).succ

section

@[simp] lemma length_axL {k} {r : L.rel k} {v} (hpos : rel r v ∈ Δ) (hneg : nrel r v ∈ Δ) :
  (axL (P := P) Δ r v hpos hneg).length = 0 := rfl

@[simp] lemma length_verum (h : ⊤ ∈ Δ) : (verum (P := P) Δ h).length = 0 := rfl

@[simp] lemma length_and {p q} (dp : ⊢ᶜ[P] insert p Δ) (dq : ⊢ᶜ[P] insert q Δ) : (and Δ p q dp dq).length = (max dp.length dq.length).succ := rfl

@[simp] lemma length_or {p q} (d : ⊢ᶜ[P] (insert p $ insert q Δ)) : (or Δ p q d).length = d.length.succ := rfl

@[simp] lemma length_all {p} (d : ⊢ᶜ[P] insert (free p) (shifts Δ)) : (all Δ p d).length = d.length.succ := rfl

@[simp] lemma length_ex {t} {p} (d : ⊢ᶜ[P] insert (substs ![t] p) Δ) : (ex Δ t p d).length = d.length.succ := rfl

@[simp] lemma length_cut {p} (hp : P p) (dp : ⊢ᶜ[P] insert p Δ) (dn : ⊢ᶜ[P] insert (~p) Γ) :
  (cut _ _ p hp dp dn).length = (max dp.length dn.length).succ := rfl

end

section Repr
variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)]

protected unsafe def repr : {Δ : Sequent L} → ⊢ᶜ[P] Δ → String
  | _, axL Δ _ _ _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, verum Δ _       =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, or Δ p q d      =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\lor$L)}\n" ++
      "\\UnaryInfC{$" ++ reprStr (insert p $ insert q Δ) ++ "$}\n\n"
  | _, and Δ p q dp dq =>
      dp.repr ++
      dq.repr ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr (insert (p ⋏ q) Δ) ++ "$}\n\n"
  | _, all Δ p d       =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr (insert (∀' p) Δ) ++ "$}\n\n"
  | _, ex Δ _ p d      =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr (insert (∃' p) Δ) ++ "$}\n\n"
  | _, cut Δ Γ _ _ dp dn =>
      dp.repr ++
      dn.repr ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr (Δ ∪ Γ) ++ "$}\n\n"     

unsafe instance : Repr (⊢ᶜ[P] Δ) where reprPrec d _ := d.repr

end Repr

protected def cast (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) : ⊢ᶜ[P] Γ := cast (by simp[HasVdash.vdash, e]) d

def cast₀ (d : ⊢ᵀ Δ) (e : Δ = Γ) : ⊢ᵀ Γ := d.cast e

@[simp] lemma length_cast (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) : (d.cast e).length = d.length := by rcases e with rfl; simp[DerivationCutRestricted.cast]

def cutWeakening {P Q : SyntacticFormula L → Prop} (h : ∀ p, P p → Q p) : ∀ {Δ}, ⊢ᶜ[P] Δ → ⊢ᶜ[Q] Δ
  | _, axL Δ r v hpos hneg  => axL Δ r v hpos hneg
  | _, verum Δ h            => verum Δ h
  | _, and Δ p q dp dq      => and Δ p q (dp.cutWeakening h) (dq.cutWeakening h)
  | _, or Δ p q d           => or Δ p q (d.cutWeakening h)
  | _, all Δ p d            => all Δ p (d.cutWeakening h)
  | _, ex Δ t p d           => ex Δ t p (d.cutWeakening h)
  | _, cut Δ₁ Δ₂ p hp d₁ d₂ => cut Δ₁ Δ₂ p (h p hp) (d₁.cutWeakening h) (d₂.cutWeakening h) 

@[simp] lemma lengtgh_cutWeakening {P Q : SyntacticFormula L → Prop} (h : ∀ p, P p → Q p) {Δ} (d : ⊢ᶜ[P] Δ) :
    (d.cutWeakening h).length = d.length := by induction d <;> simp[*, cutWeakening]

def ofLe {i j : ℕ} (h : i ≤ j) : ⊢ᶜ[< i] Δ → ⊢ᶜ[< j] Δ := cutWeakening (fun _ hp => lt_of_lt_of_le hp h)

def cutWeakeningCut (d : ⊢ᶜ[P] Δ) : ⊢ᶜ Δ := d.cutWeakening (by simp)

def weakening : ∀ {Δ}, ⊢ᶜ[P] Δ → ∀ {Γ : Sequent L}, Δ ⊆ Γ → ⊢ᶜ[P] Γ
  | _, axL Δ r v hrel hnrel, Γ, h => axL Γ r v (h hrel) (h hnrel)
  | _, verum Δ htop,         Γ, h => verum Γ (h htop)
  | _, or Δ p q d,           Γ, h =>
      have : ⊢ᶜ[P] (insert p $ insert q Γ) :=
        weakening d (Finset.insert_subset_insert p $ Finset.insert_subset_insert q (Finset.insert_subset.mp h).2)
      have : ⊢ᶜ[P] insert (p ⋎ q) Γ := or Γ p q this
      this.cast (by simp; exact (Finset.insert_subset.mp h).1)
  | _, and Δ p q dp dq,      Γ, h =>
      have dp : ⊢ᶜ[P] insert p Γ := dp.weakening (Finset.insert_subset_insert p (Finset.insert_subset.mp h).2) 
      have dq : ⊢ᶜ[P] insert q Γ := dq.weakening (Finset.insert_subset_insert q (Finset.insert_subset.mp h).2) 
      have : ⊢ᶜ[P] insert (p ⋏ q) Γ := and Γ p q dp dq
      this.cast (by simp; exact (Finset.insert_subset.mp h).1)    
  | _, all Δ p d,            Γ, h =>
      have : ⊢ᶜ[P] insert (free p) (shifts Γ) := d.weakening (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊢ᶜ[P] insert (∀' p) Γ := all Γ p this
      this.cast (by simp; exact (Finset.insert_subset.mp h).1)      
  | _, ex Δ t p d,           Γ, h =>
      have : ⊢ᶜ[P] insert (⟦↦ t⟧ p) Γ := d.weakening (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊢ᶜ[P] insert (∃' p) Γ := ex Γ t p this
      this.cast (by simp; exact (Finset.insert_subset.mp h).1)     
  | _, cut Δ₁ Δ₂ p hp d₁ d₂, Γ, h =>
      have d₁ : ⊢ᶜ[P] insert p Γ := d₁.weakening (Finset.insert_subset_insert _ (Finset.union_subset_left h))
      have d₂ : ⊢ᶜ[P] insert (~p) Γ := d₂.weakening (Finset.insert_subset_insert _ (Finset.union_subset_right h))
      (cut Γ Γ p hp d₁ d₂).cast (by simp)

@[simp] lemma length_weakening {Δ} (d : ⊢ᶜ[P] Δ) {Γ : Sequent L} (h : Δ ⊆ Γ) : (d.weakening h).length = d.length :=
  by induction d generalizing Γ <;> simp[*, weakening]

def or' {p q : SyntacticFormula L} (h : p ⋎ q ∈ Δ) (d : ⊢ᶜ[P] (insert p $ insert q $ Δ.erase (p ⋎ q))) : ⊢ᶜ[P] Δ :=
  (or _ p q d).cast (by simp[Finset.insert_erase h])

def and' {p q : SyntacticFormula L} (h : p ⋏ q ∈ Δ) (dp : ⊢ᶜ[P] insert p (Δ.erase (p ⋏ q))) (dq : ⊢ᶜ[P] insert q (Δ.erase (p ⋏ q))) : ⊢ᶜ[P] Δ :=
  (and _ p q dp dq).cast (by simp[Finset.insert_erase h])

def all' {p : SyntacticSubFormula L 1} (h : ∀' p ∈ Δ) (d : ⊢ᶜ[P] insert (free p) (shifts $ Δ.erase (∀' p))) : ⊢ᶜ[P] Δ :=
  (all _ p d).cast (by simp[Finset.insert_erase h])

def ex' {p : SyntacticSubFormula L 1} (t : SyntacticTerm L) (h : ∃' p ∈ Δ)
  (d : ⊢ᶜ[P] insert (⟦↦ t⟧ p) (Δ.erase (∃' p))) : ⊢ᶜ[P] Δ :=
  (ex _ t p d).cast (by simp[Finset.insert_erase h])

def cutCut {p} (d₁ : ⊢ᶜ insert p Δ) (d₂ : ⊢ᶜ insert (~p) Γ) : ⊢ᶜ Δ ∪ Γ := cut Δ Γ p trivial d₁ d₂

def cutClx {i} {p} (d₁ : ⊢ᶜ[< i] insert p Δ) (d₂ : ⊢ᶜ[< i] insert (~p) Γ) (hp : p.complexity < i) :
    ⊢ᶜ[< i] Δ ∪ Γ := cut Δ Γ p hp d₁ d₂

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {p q : SyntacticFormula L} : ¬~p = p ⋏ q :=
ne_of_ne_complexity (by simp)

def em {p : SyntacticFormula L} {Δ : Sequent L} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᶜ[P] Δ := by
  induction p using SubFormula.formulaRec generalizing Δ
  case hverum           => exact verum Δ hpos
  case hfalsum          => exact verum Δ hneg
  case hrel r v         => exact axL Δ r v hpos hneg 
  case hnrel r v        => exact axL Δ r v hneg hpos 
  case hall p ih        =>
    exact all' hpos $ ex' (p := ~ shift p) &0
      (by simp; exact Or.inr (by simp[shifts, shiftEmb_eq_shift]; exact ⟨_, hneg, by simp⟩))
      (ih (by simp; exact Or.inr $ ne_of_ne_complexity $ by simp[shift]) (by simp))
  case hex p ih         =>
    simp at hneg
    exact all' hneg $ ex' (p := shift p) &0
      (by simp; exact Or.inr (by simp[shifts, shiftEmb_eq_shift]; exact ⟨_, hpos, by simp⟩))
      (ih (by simp) (by simp; exact Or.inr $ ne_of_ne_complexity $ by simp[shift]))
  case hand p q ihp ihq =>
    simp at hneg
    exact or' hneg (and' (p := p) (q := q) (by simp[hpos])
      (ihp (by simp) (by simp; exact Or.inr $ ne_of_ne_complexity (by simp)))
      (ihq (by simp) (by simp; exact Or.inr $ ne_of_ne_complexity (by simp))))
  case hor p q ihp ihq  =>
    simp at hneg
    exact or' hpos (and' (p := ~p) (q := ~q) (by simp[hneg])
      (ihp (by simp; exact Or.inr $ ne_of_ne_complexity (by simp)) (by simp))
      (ihq (by simp; exact Or.inr $ ne_of_ne_complexity (by simp)) (by simp)))   

section Hom

variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.func k)] [∀ k, DecidableEq (L₁.rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.func k)] [∀ k, DecidableEq (L₂.rel k)]
  {Δ₁ Γ₁ : Finset (SyntacticFormula L₁)}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)} :
     shifts (Δ.image Φ.onSubFormula₁) = (Finset.image Φ.onSubFormula₁ (shifts Δ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, SubFormula.onSubFormula₁_shift]

def lHom (Φ : L₁ →ᵥ L₂) {P₁ : SyntacticFormula L₁ → Prop} {P₂ : SyntacticFormula L₂ → Prop} (h : ∀ p, P₁ p → P₂ (Φ.onSubFormula₁ p)):
    ∀ {Δ : Finset (SyntacticFormula L₁)}, ⊢ᶜ[P₁] Δ → ⊢ᶜ[P₂] Finset.image Φ.onSubFormula₁ Δ
  | _, axL Δ r v hrel hnrel =>
      axL _ (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
        (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h            => verum _ (by simpa using Finset.mem_image_of_mem Φ.onSubFormula₁ h)
  | _, or Δ p q d           =>
      have : ⊢ᶜ[P₂] insert (Φ.onSubFormula₁ p ⋎ Φ.onSubFormula₁ q) (Δ.image Φ.onSubFormula₁) :=
        or _ _ _ ((d.lHom Φ h).cast (by simp))
      this.cast (by simp)
  | _, and Δ p q dp dq      =>
      have : ⊢ᶜ[P₂] insert (Φ.onSubFormula₁ p ⋏ Φ.onSubFormula₁ q) (Δ.image Φ.onSubFormula₁) :=
        and _ _ _ ((dp.lHom Φ h).cast (by simp)) ((dq.lHom Φ h).cast (by simp))
      this.cast (by simp)
  | _, all Δ p d            =>
      have : ⊢ᶜ[P₂] insert (∀' Φ.onSubFormula₁ p) (Δ.image Φ.onSubFormula₁) :=
        all _ _ ((d.lHom Φ h).cast (by simp[←SubFormula.onSubFormula₁_free, shifts_image]))
      this.cast (by simp)
  | _, ex Δ t p d           =>
      have : ⊢ᶜ[P₂] insert (∃' Φ.onSubFormula₁ p) (Δ.image Φ.onSubFormula₁) :=
        ex _ (Φ.onSubTerm t) _ ((d.lHom Φ h).cast (by simp[SubFormula.onSubFormula₁_substs, Matrix.constant_eq_singleton]))
      this.cast (by simp)
  | _, cut Δ Γ p hp dΔ dΓ   =>
      have : ⊢ᶜ[P₂] (Δ.image Φ.onSubFormula₁) ∪ (Γ.image Φ.onSubFormula₁) :=
        cut _ _ (Φ.onSubFormula₁ p) (h p hp) ((dΔ.lHom Φ h).cast (by simp)) ((dΓ.lHom Φ h).cast (by simp))
      this.cast (by simp[Finset.image_union])

def lHom₀ (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)}  (d : ⊢ᵀ Δ) : ⊢ᵀ Finset.image Φ.onSubFormula₁ Δ :=
  d.lHom Φ (fun _ x => x)

end Hom

private lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticSubFormula L 1) :
    free (rewrite (fun x => SubTerm.bShift (f x)) p) = rewrite (&0 :>ₙ fun x => SubTerm.shift (f x)) (free p) := by
  simp[free, bind_bind, Matrix.vecConsLast_vecEmpty]; congr; funext x
  simp[SubTerm.free, SubTerm.bShift, SubTerm.shift, SubTerm.map, SubTerm.bind_bind, eq_finZeroElim]

private lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticFormula L) :
    shift (rewrite f p) = rewrite (&0 :>ₙ fun x => SubTerm.shift (f x)) (shift p) := by
  simp[shift, map, rewrite, bind_bind]; congr

private lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (p : SyntacticSubFormula L 1) :
    rewrite f (⟦↦ t⟧ p) = ⟦↦ t.bind SubTerm.bvar f⟧ (rewrite (SubTerm.bShift ∘ f) p) := by
  simp[substs, bind_bind, Fin.eq_zero, SubTerm.bShift, SubTerm.map, SubTerm.bind_bind, eq_finZeroElim]

protected def rewrite (h : ∀ f p, P p → P (rewrite f p)) : ∀ {Δ : Sequent L}, ⊢ᶜ[P] Δ → ∀ (f : ℕ → SyntacticTerm L), ⊢ᶜ[P] Δ.image (rewrite f)
  | _, axL Δ r v hrel hnrel, f => axL _ r (fun i => (v i).bind SubTerm.bvar f) (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h,            _ => verum _ (Finset.mem_image_of_mem _ h)
  | _, or Δ p q d,           f =>
    have : ⊢ᶜ[P] insert (rewrite f p ⋎ rewrite f q) (Δ.image (rewrite f)) := or _ _ _ ((d.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, and Δ p q dp dq,      f =>
    have : ⊢ᶜ[P] insert (rewrite f p ⋏ rewrite f q) (Δ.image (rewrite f)) := and _ _ _ ((dp.rewrite h f).cast (by simp)) ((dq.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, all Δ p d,            f =>
    have : ⊢ᶜ[P] (insert (free p) (shifts Δ)).image (rewrite (&0 :>ₙ fun x => SubTerm.shift (f x))).toFun := d.rewrite h (&0 :>ₙ fun x => (f x).shift)
    have : ⊢ᶜ[P] insert (∀' (rewrite (SubTerm.bShift ∘ f)) p) (Δ.image (rewrite f).toFun) :=
      all _ _ (this.cast (by simp[free_rewrite_eq, shift_rewrite_eq, shifts_eq_image, Finset.image_image, Function.comp]))
    this.cast (by simp)
  | _, ex Δ t p d,           f =>
    have : ⊢ᶜ[P] (insert (⟦↦ t⟧ p) Δ).image (rewrite f) := d.rewrite h f 
    have : ⊢ᶜ[P] insert (∃' rewrite (SubTerm.bShift ∘ f) p) (Δ.image (rewrite f)) := 
      ex _ (SubTerm.bind SubTerm.bvar f t) _ (this.cast (by simp[rewrite_subst_eq])) 
    this.cast (by simp)
  | _, cut Δ Γ p hp dΔ dΓ,   f =>
    have dΔ : ⊢ᶜ[P] insert (rewrite f p) (Δ.image $ rewrite f) := (dΔ.rewrite h f).cast (by simp)
    have dΓ : ⊢ᶜ[P] insert (~rewrite f p) (Γ.image $ rewrite f) := (dΓ.rewrite h f).cast (by simp)
    (cut _ _ (rewrite f p) (h f p hp) dΔ dΓ).cast (by simp[Finset.image_union])

def rewrite₀ {Δ : Sequent L} (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) : ⊢ᵀ Δ.image (rewrite f) := d.rewrite (by simp) f

def rewriteClx {i} {Δ : Sequent L} (d : ⊢ᶜ[< i] Δ) (f : ℕ → SyntacticTerm L) : ⊢ᶜ[< i] Δ.image (rewrite f) := d.rewrite (by simp) f

def rewriteCut {Δ : Sequent L} (d : ⊢ᶜ Δ) (f : ℕ → SyntacticTerm L) : ⊢ᶜ Δ.image (rewrite f) := d.rewrite (by simp) f

@[simp] lemma length_rewrite (h) (d : ⊢ᶜ[P] Δ) (f : ℕ → SyntacticTerm L) : (d.rewrite h f).length = d.length :=
  by induction d generalizing f <;> simp[*, DerivationCutRestricted.rewrite]

@[simp] lemma length_rewrite₀ (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) : (d.rewrite₀ f).length = d.length :=
  d.length_rewrite _ f

protected def map (h : ∀ f p, P p → P (rewrite f p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) (f : ℕ → ℕ) : ⊢ᶜ[P] Δ.image (map₀ f) := d.rewrite h _

protected def shift (h : ∀ f p, P p → P (rewrite f p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) : ⊢ᶜ[P] (shifts Δ) :=
  (d.map h Nat.succ).cast (by simp[shifts_eq_image, shift])

private lemma map_subst_eq_free (p : SyntacticSubFormula L 1) (h : ¬p.fvar? m) :
    map₀ (fun x => if x = m then 0 else x + 1) (⟦↦ &m⟧ p) = free p := by
  simp[free, substs, map₀, map, bind_bind, Fin.eq_zero, Matrix.vecConsLast_vecEmpty, Matrix.constant_eq_singleton]
  exact bind_eq_of_funEqOn _ _ _ _ (by intro x hx; simp; rintro rfl; contradiction)

private lemma image_map₀_eq_shifts (Δ : Finset $ SyntacticFormula L) (h : ∀ p ∈ Δ, ¬p.fvar? m) :
    Δ.image (map₀ (fun x => if x = m then 0 else x + 1)) = shifts Δ := by 
  simp[shifts_eq_image]; apply Finset.image_congr
  simp[Set.EqOn]; intro p hp;
  simp[shift, map₀, map]
  exact bind_eq_of_funEqOn _ _ _ _ (by intro x hx; simp; rintro rfl; have := h p hp; contradiction)

def genelalizeByNewver (h : ∀ f p, P p → P (rewrite f p)) {p : SyntacticSubFormula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᶜ[P] insert (⟦↦ &m⟧ p) Δ) : ⊢ᶜ[P] insert (∀' p) Δ := by
  have : ⊢ᶜ[P] insert (free p) (shifts Δ) :=
    (d.map h (fun x => if x = m then 0 else x + 1)).cast (by simp[map_subst_eq_free p hp, image_map₀_eq_shifts Δ hΔ])
  exact all Δ p this

def genelalizeByNewver₀ {p : SyntacticSubFormula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᵀ insert (⟦↦ &m⟧ p) Δ) : ⊢ᵀ insert (∀' p) Δ := d.genelalizeByNewver (by simp) hp hΔ

def genelalizeByNewverCut {p : SyntacticSubFormula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᶜ insert (⟦↦ &m⟧ p) Δ) : ⊢ᶜ insert (∀' p) Δ := d.genelalizeByNewver (by simp) hp hΔ

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSubFormula L 1)
  (h : ⊢ᶜ[P] (v.map (substs ![·] p)).toFinset ∪ Γ) : ⊢ᶜ[P] insert (∃' p) Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (Finset.subset_insert _ Γ)
  · exact (ih (Γ := insert (∃' p) Γ)
      ((ex _ t p h).cast (by ext r; simp))).cast (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (p : SyntacticSubFormula L 1)
  (h : ⊢ᶜ[P] (insert (∃' p) $ (v.map (substs ![·] p)).toFinset ∪ Γ)) : ⊢ᶜ[P] insert (∃' p) Γ :=
  (exOfInstances (Γ := insert (∃' p) Γ) v p (h.cast $ by simp)).cast (by simp)

end DerivationCutRestricted

end FirstOrder
