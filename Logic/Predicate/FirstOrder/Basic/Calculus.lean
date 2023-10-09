import Logic.Predicate.FirstOrder.Basic.Formula.Formula

namespace LO

namespace FirstOrder

abbrev Sequent (L : Language.{u}) := Finset (SyntacticFormula L)

open Subformula
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def shifts (Δ : Finset (SyntacticSubformula L n)) :
  Finset (SyntacticSubformula L n) := Δ.map shiftEmb

lemma shifts_eq_image (Δ : Finset (SyntacticSubformula L n)) : shifts Δ = Δ.image Rew.shiftl := Finset.map_eq_image _ _

@[simp] lemma mem_shifts_iff {p : SyntacticSubformula L n} {Δ : Finset (SyntacticSubformula L n)} :
    Rew.shiftl p ∈ shifts Δ ↔ p ∈ Δ :=
  Finset.mem_map' _

@[simp] lemma shifts_ss (Δ Γ : Finset (SyntacticSubformula L n)) :
    shifts Δ ⊆ shifts Γ ↔ Δ ⊆ Γ := Finset.map_subset_map

lemma shifts_insert (p : SyntacticSubformula L n) (Δ : Finset (SyntacticSubformula L n)) :
    shifts (insert p Δ) = insert (Rew.shiftl p) (shifts Δ) :=
  by simp[shifts, shiftEmb_eq_shift]

lemma shifts_union (Δ Γ : Finset (SyntacticSubformula L n)) :
    shifts (Δ ∪ Γ) = (shifts Δ) ∪ (shifts Γ) :=
  by simp[shifts, shiftEmb_eq_shift, Finset.map_union]

@[simp] lemma shifts_emb (s : Finset (Subsentence L n)) :
    shifts (s.image Rew.embl) = s.image Rew.embl := by
  simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, ←Rew.hom_comp_app]

lemma shifts_erase (p : SyntacticSubformula L n) (Δ : Finset (SyntacticSubformula L n)) :
    shifts (Δ.erase p) = (shifts Δ).erase (Rew.shiftl p) :=
  by simp[shifts, shiftEmb_eq_shift]

inductive DerivationCR (P : SyntacticFormula L → Prop) : Sequent L → Type u
| axL   : ∀ (Δ : Sequent L) {k} (r : L.rel k) (v : Fin k → SyntacticTerm L),
    rel r v ∈ Δ → nrel r v ∈ Δ → DerivationCR P Δ
| verum : ∀ (Δ : Sequent L), ⊤ ∈ Δ → DerivationCR P Δ
| or    : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    DerivationCR P (insert p $ insert q Δ) → DerivationCR P (insert (p ⋎ q) Δ)
| and   : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    DerivationCR P (insert p Δ) → DerivationCR P (insert q Δ) → DerivationCR P (insert (p ⋏ q) Δ)
| all   : ∀ (Δ : Sequent L) (p : SyntacticSubformula L 1),
    DerivationCR P (insert (Rew.free.hom p) (shifts Δ)) → DerivationCR P (insert (∀' p) Δ)
| ex    : ∀ (Δ : Sequent L) (t : SyntacticTerm L) (p : SyntacticSubformula L 1),
    DerivationCR P (insert ([→ t].hom p) Δ) → DerivationCR P (insert (∃' p) Δ)
| cut   : ∀ (Δ Γ : Sequent L) (p : SyntacticFormula L), P p →
    DerivationCR P (insert p Δ) → DerivationCR P (insert (~p) Γ) → DerivationCR P (Δ ∪ Γ)

scoped notation :45 "⊢ᶜ[" P "] " Γ:45 => DerivationCR P Γ

abbrev Derivation : Sequent L → Type u := DerivationCR (fun _ => False)

scoped prefix:45 "⊢ᵀ " => Derivation

abbrev DerivationC : Sequent L → Type u := DerivationCR (fun _ => True)

scoped prefix:45 "⊢ᶜ " => DerivationC

abbrev DerivationClx (c : ℕ) : Sequent L → Type u := DerivationCR (·.complexity < c)

scoped notation :45 "⊢ᶜ[< " c "] " Γ:45 => DerivationClx c Γ

abbrev DerivationList (G : List (SyntacticFormula L)) := ⊢ᶜ G.toFinset

abbrev Derivation₁ (p : SyntacticFormula L) := ⊢ᶜ ({p} : Sequent L)

abbrev Derivation.Valid (σ : Sentence L) := ⊢ᵀ ({Rew.embl σ} : Sequent L)

namespace DerivationCR
variable {P : SyntacticFormula L → Prop} {Δ Δ₁ Δ₂ Γ : Sequent L}

def length : {Δ : Sequent L} → DerivationCR P Δ → ℕ 
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

@[simp] lemma length_all {p} (d : ⊢ᶜ[P] insert (Rew.freel p) (shifts Δ)) : (all Δ p d).length = d.length.succ := rfl

@[simp] lemma length_ex {t} {p} (d : ⊢ᶜ[P] insert ([→ t].hom p) Δ) : (ex Δ t p d).length = d.length.succ := rfl

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
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr (insert (p ⋎ q) Δ) ++ "$}\n\n"
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

@[simp] lemma length_cast (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) : (d.cast e).length = d.length := by rcases e with rfl; simp[DerivationCR.cast]

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
        weakening d (Finset.insert_subset_insert p $ Finset.insert_subset_insert q (Finset.insert_subset_iff.mp h).2)
      have : ⊢ᶜ[P] insert (p ⋎ q) Γ := or Γ p q this
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)
  | _, and Δ p q dp dq,      Γ, h =>
      have dp : ⊢ᶜ[P] insert p Γ := dp.weakening (Finset.insert_subset_insert p (Finset.insert_subset_iff.mp h).2) 
      have dq : ⊢ᶜ[P] insert q Γ := dq.weakening (Finset.insert_subset_insert q (Finset.insert_subset_iff.mp h).2) 
      have : ⊢ᶜ[P] insert (p ⋏ q) Γ := and Γ p q dp dq
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)    
  | _, all Δ p d,            Γ, h =>
      have : ⊢ᶜ[P] insert (Rew.freel p) (shifts Γ) := d.weakening (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset_iff.mp h).2)
      have : ⊢ᶜ[P] insert (∀' p) Γ := all Γ p this
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)      
  | _, ex Δ t p d,           Γ, h =>
      have : ⊢ᶜ[P] insert ([→ t].hom p) Γ := d.weakening (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset_iff.mp h).2)
      have : ⊢ᶜ[P] insert (∃' p) Γ := ex Γ t p this
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)     
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

def all' {p : SyntacticSubformula L 1} (h : ∀' p ∈ Δ) (d : ⊢ᶜ[P] insert (Rew.freel p) (shifts $ Δ.erase (∀' p))) : ⊢ᶜ[P] Δ :=
  (all _ p d).cast (by simp[Finset.insert_erase h])

def ex' {p : SyntacticSubformula L 1} (t : SyntacticTerm L) (h : ∃' p ∈ Δ)
  (d : ⊢ᶜ[P] insert ([→ t].hom p) (Δ.erase (∃' p))) : ⊢ᶜ[P] Δ :=
  (ex _ t p d).cast (by simp[Finset.insert_erase h])

def cCut {p} (d₁ : ⊢ᶜ insert p Δ) (d₂ : ⊢ᶜ insert (~p) Γ) : ⊢ᶜ Δ ∪ Γ := cut Δ Γ p trivial d₁ d₂

def cutClx {i} {p} (d₁ : ⊢ᶜ[< i] insert p Δ) (d₂ : ⊢ᶜ[< i] insert (~p) Γ) (hp : p.complexity < i) :
    ⊢ᶜ[< i] Δ ∪ Γ := cut Δ Γ p hp d₁ d₂

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {p q : SyntacticFormula L} : ¬~p = p ⋏ q :=
ne_of_ne_complexity (by simp)

def em {p : SyntacticFormula L} {Δ : Sequent L} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᶜ[P] Δ := by
  induction p using Subformula.formulaRec generalizing Δ
  case hverum           => exact verum Δ hpos
  case hfalsum          => exact verum Δ hneg
  case hrel r v         => exact axL Δ r v hpos hneg 
  case hnrel r v        => exact axL Δ r v hneg hpos 
  case hall p ih        =>
    exact all' hpos $ ex' (p := ~Rew.shift.hom p) &0
      (by simp; exact Or.inr (by simp[shifts, shiftEmb_eq_shift]; exact ⟨_, hneg, by simp⟩))
      (ih (by simp; exact Or.inr $ ne_of_ne_complexity $ by simp[Rew.shift]) (by simp))
  case hex p ih         =>
    simp at hneg
    exact all' hneg $ ex' (p := Rew.shift.hom p) &0
      (by simp; exact Or.inr (by simp[shifts, shiftEmb_eq_shift]; exact ⟨_, hpos, by simp⟩))
      (ih (by simp) (by simp; exact Or.inr $ ne_of_ne_complexity $ by simp[Rew.shift]))
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

def elimFalsum : {Δ : Sequent L} → ⊢ᶜ[P] Δ → ⊢ᶜ[P] Δ.erase ⊥
  | _, axL Δ r v hpos hneg => axL _ r v (by simp[hpos]) (by simp[hneg])
  | _, verum Δ h           => verum _ (by simp[h])
  | _, and Δ p q dp dq     =>
    have dp : ⊢ᶜ[P] insert p (Δ.erase ⊥) := dp.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dq : ⊢ᶜ[P] insert q (Δ.erase ⊥) := dq.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (and _ p q dp dq).cast (by simp[Finset.erase_insert_of_ne])
  | _, or Δ p q d          =>
    have : ⊢ᶜ[P] (insert p $ insert q $ Δ.erase ⊥) :=
      d.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (or _ _ _ this).cast (by simp[Finset.erase_insert_of_ne])
  | _, all Δ p d           =>
    have : ⊢ᶜ[P] (insert (Rew.freel p) (shifts $ Δ.erase ⊥)) :=
      d.elimFalsum.weakening
        (by {simp[Finset.subset_iff, shifts_eq_image]; rintro x hx (rfl | ⟨y, hy, rfl⟩); { exact Or.inl rfl };
             { exact Or.inr ⟨y, ⟨by rintro rfl; simp at hx, hy⟩, rfl⟩ } } )
    (all _ _ this).cast (by simp[Finset.erase_insert_of_ne])
  | _, ex Δ t p d          =>
    have : ⊢ᶜ[P] (insert ([→ t].hom p) $ Δ.erase ⊥) := d.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (ex _ t p this).cast (by simp[Finset.erase_insert_of_ne])
  | _, cut Δ Γ p hp dΔ dΓ  =>
    have dΔ : ⊢ᶜ[P] (insert p $ Δ.erase ⊥) := dΔ.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    have dΓ : ⊢ᶜ[P] (insert (~p) $ Γ.erase ⊥) := dΓ.elimFalsum.weakening (by simp[Finset.subset_iff]; rintro x hx (rfl | hhx) <;> simp[*])
    (cut _ _ p hp dΔ dΓ).cast (by simp[Finset.erase_union])

section Hom

variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.func k)] [∀ k, DecidableEq (L₁.rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.func k)] [∀ k, DecidableEq (L₂.rel k)]
  {Δ₁ Γ₁ : Finset (SyntacticFormula L₁)}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)} :
     shifts (Δ.image $ Subformula.lMap Φ) = (Finset.image (Subformula.lMap Φ) (shifts Δ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, Subformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {P₁ : SyntacticFormula L₁ → Prop} {P₂ : SyntacticFormula L₂ → Prop} (h : ∀ p, P₁ p → P₂ (Subformula.lMap Φ p)):
    ∀ {Δ : Finset (SyntacticFormula L₁)}, ⊢ᶜ[P₁] Δ → ⊢ᶜ[P₂] Δ.image (Subformula.lMap Φ)
  | _, axL Δ r v hrel hnrel =>
      axL _ (Φ.rel r) (fun i => (v i).lMap Φ)
        (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h            => verum _ (by simpa using Finset.mem_image_of_mem (Subformula.lMap Φ) h)
  | _, or Δ p q d           =>
      have : ⊢ᶜ[P₂] insert (Subformula.lMap Φ p ⋎ Subformula.lMap Φ q) (Δ.image (Subformula.lMap Φ)) :=
        or _ _ _ ((d.lMap Φ h).cast (by simp))
      this.cast (by simp)
  | _, and Δ p q dp dq      =>
      have : ⊢ᶜ[P₂] insert (Subformula.lMap Φ p ⋏ Subformula.lMap Φ q) (Δ.image (Subformula.lMap Φ)) :=
        and _ _ _ ((dp.lMap Φ h).cast (by simp)) ((dq.lMap Φ h).cast (by simp))
      this.cast (by simp)
  | _, all Δ p d            =>
      have : ⊢ᶜ[P₂] insert (∀' Subformula.lMap Φ p) (Δ.image (Subformula.lMap Φ)) :=
        all _ _ ((d.lMap Φ h).cast (by simp[←Subformula.lMap_free, shifts_image]))
      this.cast (by simp)
  | _, ex Δ t p d           =>
      have : ⊢ᶜ[P₂] insert (∃' Subformula.lMap Φ p) (Δ.image (Subformula.lMap Φ)) :=
        ex _ (Subterm.lMap Φ t) _ ((d.lMap Φ h).cast (by simp[Subformula.lMap_substs, Matrix.constant_eq_singleton]))
      this.cast (by simp)
  | _, cut Δ Γ p hp dΔ dΓ   =>
      have : ⊢ᶜ[P₂] (Δ.image (Subformula.lMap Φ)) ∪ (Γ.image (Subformula.lMap Φ)) :=
        cut _ _ (Subformula.lMap Φ p) (h p hp) ((dΔ.lMap Φ h).cast (by simp)) ((dΓ.lMap Φ h).cast (by simp))
      this.cast (by simp[Finset.image_union])

def lMap₀ (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)} (d : ⊢ᵀ Δ) : ⊢ᵀ Δ.image (Subformula.lMap Φ) :=
  d.lMap Φ (fun _ x => x)

def lMapCut (Φ : L₁ →ᵥ L₂) {Δ : Finset (SyntacticFormula L₁)} (d : ⊢ᶜ Δ) : ⊢ᶜ Δ.image (Subformula.lMap Φ) :=
  d.lMap Φ (fun _ x => x)

end Hom

private lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticSubformula L 1) :
    Rew.freel (Rew.rewritel (fun x => Rew.bShift (f x)) p) = Rew.rewritel (&0 :>ₙ fun x => Rew.shift (f x)) (Rew.freel p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app, Fin.eq_zero])

private lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticFormula L) :
    Rew.shiftl (Rew.rewritel f p) = Rew.rewritel (&0 :>ₙ fun x => Rew.shift (f x)) (Rew.shiftl p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app])

private lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (p : SyntacticSubformula L 1) :
    Rew.rewritel f ([→ t].hom p) = [→ Rew.rewrite f t].hom (Rew.rewritel (Rew.bShift ∘ f) p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app])

protected def rewrite (h : ∀ f p, P p → P (Rew.rewritel f p)) :
    ∀ {Δ : Sequent L}, ⊢ᶜ[P] Δ → ∀ (f : ℕ → SyntacticTerm L), ⊢ᶜ[P] Δ.image (Rew.rewritel f)
  | _, axL Δ r v hrel hnrel, f =>
    axL _ r (fun i => Rew.rewrite f (v i))
      (by simpa[(Rew.rewrite f).rel] using Finset.mem_image_of_mem (Rew.rewritel f) hrel)
      (by simpa[(Rew.rewrite f).nrel] using Finset.mem_image_of_mem (Rew.rewritel f) hnrel)
  | _, verum Δ h,            f => verum _ (by simpa using Finset.mem_image_of_mem (Rew.rewritel f) h)
  | _, or Δ p q d,           f =>
    have : ⊢ᶜ[P] insert (Rew.rewritel f p ⋎ Rew.rewritel f q) (Δ.image (Rew.rewritel f)) := or _ _ _ ((d.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, and Δ p q dp dq,      f =>
    have : ⊢ᶜ[P] insert (Rew.rewritel f p ⋏ Rew.rewritel f q) (Δ.image (Rew.rewritel f)) := and _ _ _ ((dp.rewrite h f).cast (by simp)) ((dq.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, all Δ p d,            f =>
    have : ⊢ᶜ[P] (insert (Rew.freel p) (shifts Δ)).image (Rew.rewritel (&0 :>ₙ fun x => Rew.shift (f x))) := d.rewrite h (&0 :>ₙ fun x => Rew.shift (f x))
    have : ⊢ᶜ[P] insert (∀' (Rew.rewritel (Rew.bShift ∘ f)) p) (Δ.image (Rew.rewritel f)) :=
      all _ _ (this.cast (by simp[free_rewrite_eq, shift_rewrite_eq, shifts_eq_image, Finset.image_image, Function.comp]))
    this.cast (by simp[Rew.q_rewrite])
  | _, ex Δ t p d,           f =>
    have : ⊢ᶜ[P] (insert ([→ t].hom p) Δ).image (Rew.rewritel f) := d.rewrite h f 
    have : ⊢ᶜ[P] insert (∃' Rew.rewritel (Rew.bShift ∘ f) p) (Δ.image (Rew.rewritel f)) := 
      ex _ (Rew.rewrite f t) _ (this.cast (by simp[rewrite_subst_eq])) 
    this.cast (by simp[Rew.q_rewrite])
  | _, cut Δ Γ p hp dΔ dΓ,   f =>
    have dΔ : ⊢ᶜ[P] insert (Rew.rewritel f p) (Δ.image $ Rew.rewritel f) := (dΔ.rewrite h f).cast (by simp)
    have dΓ : ⊢ᶜ[P] insert (~Rew.rewritel f p) (Γ.image $ Rew.rewritel f) := (dΓ.rewrite h f).cast (by simp)
    (cut _ _ (Rew.rewritel f p) (h f p hp) dΔ dΓ).cast (by simp[Finset.image_union])

def rewrite₀ {Δ : Sequent L} (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) : ⊢ᵀ Δ.image (Rew.rewritel f) := d.rewrite (by simp) f

def rewriteClx {i} {Δ : Sequent L} (d : ⊢ᶜ[< i] Δ) (f : ℕ → SyntacticTerm L) : ⊢ᶜ[< i] Δ.image (Rew.rewritel f) := d.rewrite (by simp) f

def rewriteCut {Δ : Sequent L} (d : ⊢ᶜ Δ) (f : ℕ → SyntacticTerm L) : ⊢ᶜ Δ.image (Rew.rewritel f) := d.rewrite (by simp) f

@[simp] lemma length_rewrite (h) (d : ⊢ᶜ[P] Δ) (f : ℕ → SyntacticTerm L) : (d.rewrite h f).length = d.length :=
  by induction d generalizing f <;> simp[*, DerivationCR.rewrite]

@[simp] lemma length_rewrite₀ (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) : (d.rewrite₀ f).length = d.length :=
  d.length_rewrite _ f

protected def map (h : ∀ f p, P p → P (Rew.rewritel f p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) (f : ℕ → ℕ) : ⊢ᶜ[P] Δ.image (Rew.rewriteMapl f) := d.rewrite h _

protected def shift (h : ∀ f p, P p → P (Rew.rewritel f p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) : ⊢ᶜ[P] (shifts Δ) :=
  (d.map h Nat.succ).cast (by simp[shifts_eq_image]; congr)

private lemma map_subst_eq_free (p : SyntacticSubformula L 1) (h : ¬p.fvar? m) :
    Rew.rewriteMapl (fun x => if x = m then 0 else x + 1) ([→ &m].hom p) = Rew.freel p := by
  simp[←Rew.hom_comp_app];
  exact Subformula.rew_eq_of_funEqOn (by simp[Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp[Rew.comp_app]; rintro rfl; contradiction)

private lemma image_map₀_eq_shifts (Δ : Finset $ SyntacticFormula L) (h : ∀ p ∈ Δ, ¬p.fvar? m) :
    Δ.image (Rew.rewriteMapl (fun x => if x = m then 0 else x + 1)) = shifts Δ := by 
  simp[shifts_eq_image]; apply Finset.image_congr
  intro p hp; exact rew_eq_of_funEqOn₀ (by intro x hx; simp; rintro rfl; have := h p hp; contradiction)

def genelalizeByNewver (h : ∀ f p, P p → P (Rew.rewritel f p)) {p : SyntacticSubformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᶜ[P] insert ([→ &m].hom p) Δ) : ⊢ᶜ[P] insert (∀' p) Δ := by
  have : ⊢ᶜ[P] insert (Rew.freel p) (shifts Δ) :=
    (d.map h (fun x => if x = m then 0 else x + 1)).cast (by simp[map_subst_eq_free p hp, image_map₀_eq_shifts Δ hΔ])
  exact all Δ p this

def genelalizeByNewver₀ {p : SyntacticSubformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᵀ insert ([→ &m].hom p) Δ) : ⊢ᵀ insert (∀' p) Δ := d.genelalizeByNewver (by simp) hp hΔ

def genelalizeByNewverCut {p : SyntacticSubformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᶜ insert ([→ &m].hom p) Δ) : ⊢ᶜ insert (∀' p) Δ := d.genelalizeByNewver (by simp) hp hΔ

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSubformula L 1)
  (h : ⊢ᶜ[P] (v.map (Rew.substsl ![·] p)).toFinset ∪ Γ) : ⊢ᶜ[P] insert (∃' p) Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (Finset.subset_insert _ Γ)
  · exact (ih (Γ := insert (∃' p) Γ)
      ((ex _ t p h).cast (by ext r; simp))).cast (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (p : SyntacticSubformula L 1)
  (h : ⊢ᶜ[P] (insert (∃' p) $ (v.map (Rew.substsl ![·] p)).toFinset ∪ Γ)) : ⊢ᶜ[P] insert (∃' p) Γ :=
  (exOfInstances (Γ := insert (∃' p) Γ) v p (h.cast $ by simp)).cast (by simp)

end DerivationCR

structure DerivationCRWA (P : SyntacticFormula L → Prop) (T : Theory L) (Δ : Sequent L) where
  leftHand : Finset (Sentence L)
  hleftHand : ↑leftHand ⊆ (~·) '' T
  derivation : ⊢ᶜ[P] Δ ∪ (leftHand.image Rew.embl)

scoped notation :45 T " ⊢ᶜ[" P "] " Γ:45 => DerivationCRWA P T Γ

abbrev DerivationWA (T : Theory L) (Δ : Sequent L) := DerivationCRWA (fun _ => False) T Δ

scoped infix:45 " ⊢ᵀ " => DerivationWA

abbrev DerivationCWA (T : Theory L) (Δ : Sequent L) := DerivationCRWA (fun _ => True) T Δ

scoped infix:45 " ⊢' " => DerivationCWA

instance Proof : Logic.System (Sentence L) where
  Bew := fun T σ => T ⊢' {Rew.embl σ}
  axm := fun {f σ} hσ =>
    { leftHand := {~σ}
      hleftHand := by simp[hσ]
      derivation := DerivationCR.em (p := Rew.embl σ) (by simp) (by simp) }
  weakening' := fun {T U} f h b =>
    { leftHand := b.leftHand,
      hleftHand := Set.Subset.trans b.hleftHand (Set.image_subset _ h),
      derivation := b.derivation }

def DerivationCRWA.toDerivationCWA {T : Theory L} {Δ} (b : T ⊢ᶜ[P] Δ) : T ⊢' Δ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation := b.derivation.cutWeakening (by simp)

def DerivationCWA.toDerivationCWA {T : Theory L} {σ : Sentence L} (b : T ⊢ σ) : T ⊢' {Rew.embl σ} := b

def DerivationCRWA.toProof {T : Theory L} {σ : Sentence L} (b : T ⊢ᶜ[P] {Rew.embl σ}) : T ⊢ σ :=
  b.toDerivationCWA

def DerivationCWA.toDerivationWA {T : Theory L} {σ : Sentence L} (b : T ⊢ σ) : T ⊢' {Rew.embl σ} := b

def DerivationCR.toDerivationCRWA
  {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L} (b : ⊢ᶜ[P] Δ) : T ⊢ᶜ[P] Δ where
  leftHand := ∅
  hleftHand := by simp
  derivation := b.cast (by simp)

namespace DerivationCRWA

variable {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L}

def kernel (b : DerivationCRWA P T Δ) := b.leftHand.image (~·)

lemma neg_mem {b : T ⊢ᶜ[P] Δ} (hσ : σ ∈ b.leftHand) : ~σ ∈ T := by
  have : ∃ q ∈ T, ~q = σ := b.hleftHand hσ; rcases this with ⟨q, hq, rfl⟩; simp[hq]

@[simp] lemma kernel_subset (b : T ⊢ᶜ[P] Δ) : ↑(b.kernel) ⊆ T := by
  simp[kernel]; intros p hp; exact neg_mem hp

lemma compact {p} (b : T ⊢ᶜ[P] p) : b.kernel ⊢ᶜ[P] p where
  leftHand := b.leftHand
  hleftHand := by simp[kernel, ←Set.image_comp]
  derivation := b.derivation

def verum (h : ⊤ ∈ Δ) : T ⊢ᶜ[P] Δ := (DerivationCR.verum _ (by simp[h])).toDerivationCRWA

def axL {k} (r : L.rel k) (v : Fin k → SyntacticTerm L) (h : rel r v ∈ Δ) (nh : nrel r v ∈ Δ) : T ⊢ᶜ[P] Δ :=
  (DerivationCR.axL Δ r v h nh).toDerivationCRWA

protected def and {p₁ p₂} (h : p₁ ⋏ p₂ ∈ Δ) (b₁ : T ⊢ᶜ[P] insert p₁ Δ) (b₂ : T ⊢ᶜ[P] insert p₂ Δ) :
    T ⊢ᶜ[P] Δ where
  leftHand := b₁.leftHand ∪ b₂.leftHand
  hleftHand := by simp[b₁.hleftHand, b₂.hleftHand]
  derivation :=
    let d : ⊢ᶜ[P] insert (p₁ ⋏ p₂) (Δ ∪ (b₁.leftHand ∪ b₂.leftHand).image Rew.embl) :=
      DerivationCR.and (Δ ∪ (b₁.leftHand ∪ b₂.leftHand).image Rew.embl) p₁ p₂
        (b₁.derivation.weakening (by intro x; simp; rintro (rfl | hx | ⟨σ, hσ, rfl⟩); { simp }; { simp[hx] }; { exact Or.inr $ Or.inr ⟨σ, Or.inl hσ, rfl⟩ } ))
        (b₂.derivation.weakening (by intro x; simp; rintro (rfl | hx | ⟨σ, hσ, rfl⟩); { simp }; { simp[hx] }; { exact Or.inr $ Or.inr ⟨σ, Or.inr hσ, rfl⟩ } ))
    d.cast (Finset.insert_eq_of_mem (by simp[h]))

protected def or {p₁ p₂} (h : p₁ ⋎ p₂ ∈ Δ) (b : T ⊢ᶜ[P] insert p₁ (insert p₂ Δ)) : T ⊢ᶜ[P] Δ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let d : ⊢ᶜ[P] insert (p₁ ⋎ p₂) (Δ ∪ b.leftHand.image Rew.embl) :=
      DerivationCR.or (Δ ∪ b.leftHand.image Rew.embl) p₁ p₂ (b.derivation.cast (by simp[Finset.insert_union]))
    d.cast (Finset.insert_eq_of_mem (by simp[h]))

protected def all {p} (h : ∀' p ∈ Δ)
  (b : T ⊢ᶜ[P] (insert (Rew.freel p) (shifts Δ))) : T ⊢ᶜ[P] Δ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let d₁ : ⊢ᶜ[P] insert (Rew.freel p) (shifts $ Δ ∪ b.leftHand.image Rew.embl) := b.derivation.cast (by simp[shifts_union])
    let d₂ : ⊢ᶜ[P] insert (∀' p) (Δ ∪ b.leftHand.image Rew.embl):= d₁.all
    d₂.cast (Finset.insert_eq_of_mem $ by simp[h])

protected def ex {p} {t} (h : ∃' p ∈ Δ)
  (b : T ⊢ᶜ[P] (insert ([→ t].hom p) Δ)) : T ⊢ᶜ[P] Δ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    let d₁ : ⊢ᶜ[P] insert ([→ t].hom p) (Δ ∪ b.leftHand.image Rew.embl) := by simpa using b.derivation
    let d₂ : ⊢ᶜ[P] insert (∃' p) (Δ ∪ b.leftHand.image Rew.embl) := DerivationCR.ex _ t p d₁
    d₂.cast (Finset.insert_eq_of_mem $ by simp[h])

protected def id {σ} (hσ : σ ∈ T) (b : T ⊢ᶜ[P] insert (~Rew.embl σ) Δ) : T ⊢ᶜ[P] Δ where
  leftHand := insert (~σ) b.leftHand
  hleftHand := by simp[Set.insert_subset_iff, b.hleftHand, hσ]
  derivation := b.derivation.cast (by ext ; simp)

def cast {Δ₁ Δ₂ : Sequent L} (h : Δ₁ = Δ₂) (b : T ⊢ᶜ[P] Δ₁) : T ⊢ᶜ[P] Δ₂ := by rw[h] at b; exact b

def weakeningRight {Δ₁ Δ₂ : Sequent L} (h : Δ₁ ⊆ Δ₂) (b : T ⊢ᶜ[P] Δ₁) : T ⊢ᶜ[P] Δ₂ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation := b.derivation.weakening (Finset.union_subset_union_left h)

def weakeningLeft {T U : Theory L} (h : T ⊆ U) (b : T ⊢ᶜ[P] Δ) : U ⊢ᶜ[P] Δ where
  leftHand := b.leftHand
  hleftHand := Set.Subset.trans b.hleftHand (Set.image_subset _ h)
  derivation := b.derivation

def deduction {σ} (b : insert σ T ⊢ᶜ[P] Δ) : T ⊢ᶜ[P] insert (~Rew.embl σ) Δ where
  leftHand := Finset.erase b.leftHand (~σ)
  hleftHand := by simp; exact subset_trans b.hleftHand (by simp; intro σ; simp)
  derivation := b.derivation.weakening
    (by rw[Finset.insert_union, ←Finset.union_insert, Finset.image_erase (f := Rew.embl) Rew.embl_Injective]
        simp[-Finset.insert_union, -Finset.union_insert]
        exact Finset.union_subset_union_right (Finset.insert_erase_subset _ _)) 
  
def resolution {σ} (b : T ⊢ᶜ[P] insert (Rew.embl σ) Δ) : insert (~σ) T ⊢ᶜ[P] Δ where
  leftHand := insert σ b.leftHand
  hleftHand := by simp[Set.image_insert_eq]; exact Set.insert_subset_insert b.hleftHand
  derivation := b.derivation.cast (by rw[Finset.insert_union, ←Finset.union_insert, Finset.image_insert])

def elimFalsum (b : T ⊢ᶜ[P] Δ) : T ⊢ᶜ[P] Δ.erase ⊥ where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation :=
    b.derivation.elimFalsum.weakening (by simp[Finset.erase_union_distrib]; exact Finset.union_subset_union_right (Finset.erase_subset _ _))

def byAxiom {σ} (hσ : σ ∈ T) (h : Rew.embl σ ∈ Δ) : T ⊢ᶜ[P] Δ where
  leftHand := {~σ}
  hleftHand := by simp[hσ]
  derivation := DerivationCR.em (p := Rew.embl σ) (by simp[h]) (by simp)

protected def em {p} (hp : p ∈ Δ) (hn : ~p ∈ Δ) : T ⊢ᶜ[P] Δ := (DerivationCR.em hp hn).toDerivationCRWA

def and' {p₁ p₂} (b₁ : T ⊢ᶜ[P] insert p₁ Δ) (b₂ : T ⊢ᶜ[P] insert p₂ Δ) : T ⊢ᶜ[P] insert (p₁ ⋏ p₂) Δ :=
  let b₁' : T ⊢ᶜ[P] insert p₁ (insert (p₁ ⋏ p₂) Δ) := b₁.weakeningRight (by simp[Finset.Insert.comm p₁, Finset.subset_insert])
  let b₂' : T ⊢ᶜ[P] insert p₂ (insert (p₁ ⋏ p₂) Δ) := b₂.weakeningRight (by simp[Finset.Insert.comm p₂, Finset.subset_insert])
  b₁'.and (by simp) b₂'

def or' {p q} (b : T ⊢ᶜ[P] insert p (insert q Δ)) : T ⊢ᶜ[P] insert (p ⋎ q) Δ :=
  let b' : T ⊢ᶜ[P] (insert p $ insert q $ insert (p ⋎ q) Δ) := b.weakeningRight (by simp[Finset.Insert.comm _ (p ⋎ q), Finset.subset_insert])
  b'.or (by simp)

def all' {p} (b : T ⊢ᶜ[P] insert (Rew.freel p) (shifts Δ)) : T ⊢ᶜ[P] insert (∀' p) Δ :=
  let b' : T ⊢ᶜ[P] (insert (Rew.freel p) $ shifts $ insert (∀' p) Δ) :=
    b.weakeningRight (by simp[Finset.Insert.comm (Rew.freel p), shifts_insert, Finset.subset_insert])
  b'.all (by simp)

def ex' {p} {t : SyntacticTerm L} (b : T ⊢ᶜ[P] insert ([→ t].hom p) Δ) : T ⊢ᶜ[P] insert (∃' p) Δ :=
  let b' : T ⊢ᶜ[P] insert ([→ t].hom p) (insert (∃' p) Δ) :=
    b.weakeningRight (by simp[Finset.Insert.comm ([→ t].hom p), shifts_insert, Finset.subset_insert])
  b'.ex (by simp)

def cCut {p} (b₁ : T ⊢' insert p Δ) (b₂ : T ⊢' insert (~p) Γ) : T ⊢' Δ ∪ Γ where
  leftHand := b₁.leftHand ∪ b₂.leftHand
  hleftHand := by simp[b₁.hleftHand, b₂.hleftHand]
  derivation := by
    have b₁' : ⊢ᶜ insert p (Δ ∪ b₁.leftHand.image Rew.embl) := by simpa using b₁.derivation
    have b₂' : ⊢ᶜ insert (~p) (Γ ∪ b₂.leftHand.image Rew.embl) := by simpa using b₂.derivation
    exact (b₁'.cCut b₂').cast (by simp only [←Finset.union_assoc, Finset.union_comm _ Γ, Finset.image_union])

def cCut' {p} (b₁ : T ⊢' insert p Δ) (b₂ : T ⊢' insert (~p) Δ) : T ⊢' Δ := (b₁.cCut b₂).cast (by simp)

protected def rewrite (f : ℕ → SyntacticTerm L) {T : Theory L} {Δ : Sequent L} (b : T ⊢' Δ) :
    T ⊢' Δ.image (Rew.rewritel f) where
  leftHand := b.leftHand
  hleftHand := b.hleftHand
  derivation := (b.derivation.rewriteCut f).cast
    (by simp[Finset.image_union, Finset.image_image, Rew.hom_comp_eq]; congr; ext q; simp[←Rew.hom_comp_app])

variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.func k)] [∀ k, DecidableEq (L₁.rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.func k)] [∀ k, DecidableEq (L₂.rel k)]

protected def lMap (Φ : L₁ →ᵥ L₂) {T : Theory L₁} {Δ : Sequent L₁} (b : T ⊢' Δ) :
    Theory.lMap Φ T ⊢' Δ.image (Subformula.lMap Φ) where
  leftHand := b.leftHand.image (Subformula.lMap Φ)
  hleftHand := by
    simp; intro σ hσ
    have : ∃ τ ∈ T, ~τ = σ := by simpa using b.hleftHand hσ;
    rcases this with ⟨τ, hτ, rfl⟩
    simpa using Set.mem_image_of_mem _ hτ
  derivation :=
    (b.derivation.lMapCut Φ).cast
    (by simp[Finset.image_union, Finset.image_image]; congr; ext x; simp[Subformula.lMap_emb])

end DerivationCRWA

theorem System.compact (T : Theory L) :
    Logic.System.Consistent T ↔ ∀ T' : Finset (Sentence L), (T' : Theory L) ⊆ T → Logic.System.Consistent (T' : Theory L) :=
  ⟨fun c u hu => c.of_subset hu, fun h => ⟨fun b => (h b.kernel (by simp)).false b.compact⟩⟩

lemma consistent_iff_empty_sequent {T : Theory L} :
    Logic.System.Consistent T ↔ IsEmpty (T ⊢' ∅) :=
  ⟨by contrapose; simp[Logic.System.Consistent]; intro b; exact ⟨b.weakeningRight (by simp)⟩,
   by contrapose; simp[Logic.System.Consistent]; intro b; exact ⟨b.elimFalsum.cast (by simp)⟩⟩

lemma provable_iff_inConsistent {T : Theory L} :
    Nonempty (T ⊢ σ) ↔ ¬Logic.System.Consistent (insert (~σ) T) :=
  ⟨by rintro ⟨b⟩; simp[consistent_iff_empty_sequent]
      have : T ⊢' insert (Rew.embl σ) ∅ := b
      exact ⟨this.resolution⟩,
   by simp[consistent_iff_empty_sequent]; intro b
      exact ⟨by simpa using b.deduction⟩⟩

variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.func k)] [∀ k, DecidableEq (L₁.rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.func k)] [∀ k, DecidableEq (L₂.rel k)]

def System.lMap (Φ : L₁ →ᵥ L₂) {T : Theory L₁} {σ : Sentence L₁} (b : T ⊢ σ) :
    Theory.lMap Φ T ⊢ Subformula.lMap Φ σ := by simpa[Subformula.lMap_emb] using b.lMap Φ

lemma inConsistent_lMap (Φ : L₁ →ᵥ L₂) {T : Theory L₁} :
    ¬Logic.System.Consistent T → ¬Logic.System.Consistent (Theory.lMap Φ T) := by
  simp[Logic.System.Consistent]; intro b; exact ⟨by simpa using System.lMap Φ b⟩

end FirstOrder

end LO
