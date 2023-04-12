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

@[simp] lemma mem_shifts_iff (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shift p ∈ shifts Δ ↔ p ∈ Δ :=
  Finset.mem_map' _

@[simp] lemma shifts_ss (Δ Γ : Finset (SyntacticSubFormula L n)) :
    shifts Δ ⊆ shifts Γ ↔ Δ ⊆ Γ := Finset.map_subset_map

lemma shifts_insert (p : SyntacticSubFormula L n) (Δ : Finset (SyntacticSubFormula L n)) :
    shifts (insert p Δ) = insert (shift p) (shifts Δ) :=
  by simp[shifts, shiftEmb_eq_shift]

inductive Derivation : Sequent L → Type _
| axL   : ∀ (Δ : Sequent L) {k} (r : L.rel k) (v : Fin k → SyntacticTerm L),
    rel r v ∈ Δ → nrel r v ∈ Δ → Derivation Δ
| verum : ∀ (Δ : Sequent L), ⊤ ∈ Δ → Derivation Δ
| or    : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    Derivation (insert p $ insert q Δ) → Derivation (insert (p ⋎ q) Δ)
| and   : ∀ (Δ : Sequent L) (p q : SyntacticFormula L),
    Derivation (insert p Δ) → Derivation (insert q Δ) → Derivation (insert (p ⋏ q) Δ)
| all   : ∀ (Δ : Sequent L) (p : SyntacticSubFormula L 1),
    Derivation (insert (free p) (shifts Δ)) → Derivation (insert (∀' p) Δ)
| ex    : ∀ (Δ : Sequent L) (t : SyntacticTerm L) (p : SyntacticSubFormula L 1),
    Derivation (insert (subst t p) Δ) → Derivation (insert (∃' p) Δ)

prefix:45 "⊢ᵀ " => Derivation

abbrev DerivationList (G : List (SyntacticFormula L)) := ⊢ᵀ G.toFinset

abbrev Derivation₁ (p : SyntacticFormula L) := ⊢ᵀ ({p} : Sequent L)

abbrev Derivation.Valid (σ : Sentence L) := ⊢ᵀ ({emb σ} : Sequent L)

structure Proof (T : Theory L) (σ : Sentence L) where
  leftHand : Finset (Sentence L)
  hleftHand : ↑leftHand ⊆ SubFormula.neg '' T
  derivation : ⊢ᵀ ((insert σ leftHand).image emb : Sequent L)

instance : HasTurnstile (Sentence L) (Type u) := ⟨Proof⟩

namespace Derivation
variable {Δ Γ : Sequent L}

section Repr
variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)]

protected unsafe def repr : {Δ : Sequent L} → Derivation Δ → String
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

unsafe instance : Repr (⊢ᵀ Δ) where
  reprPrec d _ := d.repr

end Repr

protected def cast (d : Derivation Δ) (e : Δ = Γ) : ⊢ᵀ Γ := cast (by simp[HasVdash.vdash, e]) d

def weakening : ∀ {Δ}, ⊢ᵀ Δ → ∀ {Γ : Sequent L}, Δ ⊆ Γ → ⊢ᵀ Γ
  | _, axL Δ r v hrel hnrel, Γ, h => axL Γ r v (h hrel) (h hnrel)
  | _, verum Δ htop,         Γ, h => verum Γ (h htop)
  | _, or Δ p q d,           Γ, h =>
      have : ⊢ᵀ (insert p $ insert q Γ) :=
        weakening d (Finset.insert_subset_insert p $ Finset.insert_subset_insert q (Finset.insert_subset.mp h).2)
      have : ⊢ᵀ insert (p ⋎ q) Γ := or Γ p q this
      this.cast (by simp; exact (Finset.insert_subset.mp h).1)
  | _, and Δ p q dp dq,      Γ, h =>
      have dp : ⊢ᵀ insert p Γ := weakening dp (Finset.insert_subset_insert p (Finset.insert_subset.mp h).2) 
      have dq : ⊢ᵀ insert q Γ := weakening dq (Finset.insert_subset_insert q (Finset.insert_subset.mp h).2) 
      have : ⊢ᵀ insert (p ⋏ q) Γ := and Γ p q dp dq
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)    
  | _, all Δ p d,            Γ, h =>
      have : ⊢ᵀ insert (free p) (shifts Γ) := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊢ᵀ insert (∀' p) Γ := all Γ p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)      
  | _, ex Δ t p d,           Γ, h =>
      have : ⊢ᵀ insert (subst t p) Γ := weakening d (Finset.insert_subset_insert _ $ by simpa using (Finset.insert_subset.mp h).2)
      have : ⊢ᵀ insert (∃' p) Γ := ex Γ t p this
      Derivation.cast this (by simp; exact (Finset.insert_subset.mp h).1)     

--def or' {p q : SyntacticFormula L} (h : p ⋎ q ∈ Δ) (d : ⊢ᵀ insert p Δ) : ⊢ᵀ Δ :=
--  weakening (or Δ p q d) (by simp[Finset.insert_subset, h])

def or' {p q : SyntacticFormula L} (h : p ⋎ q ∈ Δ) (d : ⊢ᵀ (insert p $ insert q $ Δ.erase (p ⋎ q))) : ⊢ᵀ Δ :=
  (or _ p q d).cast (by simp[Finset.insert_erase h])

def and' {p q : SyntacticFormula L} (h : p ⋏ q ∈ Δ) (dp : ⊢ᵀ insert p (Δ.erase (p ⋏ q))) (dq : ⊢ᵀ insert q (Δ.erase (p ⋏ q))) : ⊢ᵀ Δ :=
  (and _ p q dp dq).cast (by simp[Finset.insert_erase h])

def all' {p : SyntacticSubFormula L 1} (h : ∀' p ∈ Δ) (d : ⊢ᵀ insert (free p) (shifts $ Δ.erase (∀' p))) : ⊢ᵀ Δ :=
  (all _ p d).cast (by simp[Finset.insert_erase h])

def ex' {p : SyntacticSubFormula L 1} (t : SyntacticTerm L) (h : ∃' p ∈ Δ)
  (d : ⊢ᵀ insert (subst t p) (Δ.erase (∃' p))) : ⊢ᵀ Δ :=
  (ex _ t p d).cast (by simp[Finset.insert_erase h])

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {p q : SyntacticFormula L} : ¬~p = p ⋏ q :=
ne_of_ne_complexity (by simp)

def em {p : SyntacticFormula L} {Δ : Sequent L} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᵀ Δ := by
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
     shifts (Finset.image Φ.onSubFormula₁ Δ) = (Finset.image Φ.onSubFormula₁ (shifts Δ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, SubFormula.onSubFormula₁_shift]

def onDerivation (Φ : L₁ →ᵥ L₂) : ∀ {Δ : Finset (SyntacticFormula L₁)}, ⊢ᵀ Δ → ⊢ᵀ Finset.image Φ.onSubFormula₁ Δ
  | _, axL Δ r v hrel hnrel =>
      axL _ (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
        (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h            => verum _ (by simpa using Finset.mem_image_of_mem Φ.onSubFormula₁ h)
  | _, or Δ p q d           =>
      have : ⊢ᵀ insert (Φ.onSubFormula₁ p ⋎ Φ.onSubFormula₁ q) (Δ.image Φ.onSubFormula₁) :=
        or _ _ _ ((onDerivation Φ d).cast (by simp))
      this.cast (by simp)
  | _, and Δ p q dp dq      =>
      have : ⊢ᵀ insert (Φ.onSubFormula₁ p ⋏ Φ.onSubFormula₁ q) (Finset.image Φ.onSubFormula₁ Δ) :=
        and _ _ _ ((onDerivation Φ dp).cast (by simp)) ((onDerivation Φ dq).cast (by simp))
      this.cast (by simp)
  | _, all Δ p d            =>
      have : ⊢ᵀ insert (∀' Φ.onSubFormula₁ p) (Finset.image Φ.onSubFormula₁ Δ) :=
        all _ _ (by simpa[←SubFormula.onSubFormula₁_free, shifts_image] using onDerivation Φ d)
      this.cast (by simp)
  | _, ex Δ t p d           =>
      have : ⊢ᵀ insert (∃' Φ.onSubFormula₁ p) (Finset.image Φ.onSubFormula₁ Δ) :=
        ex _ (Φ.onSubTerm t) _ (by simpa[←SubFormula.onSubFormula₁_subst] using onDerivation Φ d)
      this.cast (by simp)

end Hom

private lemma free_bind₀_eq (f : ℕ → SyntacticTerm L) (p : SyntacticSubFormula L 1) :
    free (bind₀ (fun x => SubTerm.bShift (f x)) p) = bind₀ (&0 :>ₙ fun x => SubTerm.shift (f x)) (free p) := by
  simp[free, bind_bind, Matrix.vecConsLast_vecEmpty]; congr; funext x
  simp[SubTerm.free, SubTerm.bShift, SubTerm.shift, SubTerm.map, SubTerm.bind_bind, eq_finZeroElim]

private lemma shift_bind₀_eq (f : ℕ → SyntacticTerm L) (p : SyntacticFormula L) :
    shift (bind₀ f p) = bind₀ (&0 :>ₙ fun x => SubTerm.shift (f x)) (shift p) := by
  simp[shift, map, bind₀, bind_bind]; congr

private lemma bind₀_subst_eq (f : ℕ → SyntacticTerm L) (t) (p : SyntacticSubFormula L 1) :
    bind₀ f (subst t p) = subst (t.bind SubTerm.bvar f) (bind₀ (SubTerm.bShift ∘ f) p) := by
  simp[subst, bind_bind, Fin.eq_zero, SubTerm.bShift, SubTerm.map, SubTerm.bind_bind, eq_finZeroElim]; congr

def onBind : ∀ {Δ : Sequent L}, ⊢ᵀ Δ → ∀ (f : ℕ → SyntacticTerm L), ⊢ᵀ Δ.image (bind₀ f)
  | _, axL Δ r v hrel hnrel, f => axL _ r (fun i => (v i).bind SubTerm.bvar f) (Finset.mem_image_of_mem _ hrel) (Finset.mem_image_of_mem _ hnrel)
  | _, verum Δ h,            _ => verum _ (Finset.mem_image_of_mem _ h)
  | _, or Δ p q d,           f =>
    have : ⊢ᵀ insert (bind₀ f p ⋎ bind₀ f q) (Δ.image (bind₀ f)) := or _ _ _ ((onBind d f).cast (by simp))
    this.cast (by simp)
  | _, and Δ p q dp dq,      f =>
    have : ⊢ᵀ insert (bind₀ f p ⋏ bind₀ f q) (Δ.image (bind₀ f)) := and _ _ _ ((onBind dp f).cast (by simp)) ((onBind dq f).cast (by simp))
    this.cast (by simp)
  | _, all Δ p d,            f =>
    have : ⊢ᵀ (insert (free p) (shifts Δ)).image (bind₀ (&0 :>ₙ fun x => SubTerm.shift (f x))).toFun := onBind d (&0 :>ₙ fun x => (f x).shift)
    have : ⊢ᵀ insert (∀' (bind₀ (SubTerm.bShift ∘ f)) p) (Δ.image (bind₀ f).toFun) :=
      all _ _ (by simpa[free_bind₀_eq, shift_bind₀_eq, shifts_eq_image, Finset.image_image, Function.comp] using this)
    this.cast (by simp)
  | _, ex Δ t p d,           f =>
    have : ⊢ᵀ (insert (subst t p) Δ).image (bind₀ f) := onBind d f 
    have : ⊢ᵀ insert (∃' bind₀ (SubTerm.bShift ∘ f) p) (Δ.image (bind₀ f)) := 
      ex _ (SubTerm.bind SubTerm.bvar f t) _ (by simpa[bind₀_subst_eq] using this) 
    this.cast (by simp)

def onMap {Δ : Sequent L} (d : ⊢ᵀ Δ) (f : ℕ → ℕ) : ⊢ᵀ Δ.image (map₀ f) := onBind d _

private lemma map_subst_eq_free (p : SyntacticSubFormula L 1) (h : ¬p.fvar? m) :
    map₀ (fun x => if x = m then 0 else x + 1) (subst &m p) = free p := by
  simp[free, subst, map₀, map, bind_bind, Fin.eq_zero, Matrix.vecConsLast_vecEmpty, Matrix.constant_eq_singleton]
  exact bind_eq_of_funEqOn _ _ _ _ (by intro x hx; simp; rintro rfl; contradiction)

private lemma image_map₀_eq_shifts (Δ : Finset $ SyntacticFormula L) (h : ∀ p ∈ Δ, ¬p.fvar? m) :
    Δ.image (map₀ (fun x => if x = m then 0 else x + 1)) = shifts Δ := by 
  simp[shifts_eq_image]; apply Finset.image_congr
  simp[Set.EqOn]; intro p hp;
  simp[shift, map₀, map]
  exact bind_eq_of_funEqOn _ _ _ _ (by intro x hx; simp; rintro rfl; have := h p hp; contradiction)

def genelalizeByNewver {p : SyntacticSubFormula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᵀ insert (subst &m p) Δ) : ⊢ᵀ insert (∀' p) Δ := by
  have : ⊢ᵀ insert (free p) (shifts Δ) := by
    simpa[map_subst_eq_free p hp, image_map₀_eq_shifts Δ hΔ] using onMap d (fun x => if x = m then 0 else x + 1)
  exact all Δ p this

variable [∀ k, Encodable (L.func k)] {μ : Type _} [Encodable μ]

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSubFormula L 1)
  (h : ⊢ᵀ (v.map (subst · p)).toFinset ∪ Γ) : ⊢ᵀ insert (∃' p) Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (Finset.subset_insert _ Γ)
  · exact Derivation.cast (ih (Γ := insert (∃' p) Γ)
      (Derivation.cast (ex _ t p h) (by ext r; simp))) (by simp)

end Derivation

end FirstOrder
