import Logic.Logic.Calculus
import Logic.FirstOrder.Basic.Syntax.Formula

namespace LO

namespace FirstOrder

abbrev Sequent (L : Language) := List (SyntacticFormula L)

open Semiformula
variable {L : Language}

def shifts (Δ : List (SyntacticSemiformula L n)) :
  List (SyntacticSemiformula L n) := Δ.map Rew.shift.hom

local postfix:max "⁺" => shifts

@[simp] lemma mem_shifts_iff {p : SyntacticSemiformula L n} {Δ : List (SyntacticSemiformula L n)} :
    Rew.shift.hom p ∈ Δ⁺ ↔ p ∈ Δ :=
  List.mem_map_of_injective Rew.shift.hom_injective

@[simp] lemma shifts_ss (Δ Γ : List (SyntacticSemiformula L n)) :
    Δ⁺ ⊆ Γ⁺ ↔ Δ ⊆ Γ := List.map_subset_iff _ Rew.shift.hom_injective

lemma shifts_cons (p : SyntacticSemiformula L n) (Δ : List (SyntacticSemiformula L n)) :
    (p :: Δ)⁺ = Rew.shift.hom p :: Δ⁺ := by simp[shifts]

lemma shifts_union (Δ Γ : List (SyntacticSemiformula L n)) :
    (Δ ++ Γ)⁺ = Δ⁺ ++ Γ⁺ := by simp[shifts]

@[simp] lemma shifts_emb (Γ : List (Semisentence L n)) :
    (Γ.map Rew.emb.hom)⁺ = Γ.map Rew.emb.hom := by
  simp[shifts, Function.comp, ←Rew.hom_comp_app]

inductive DerivationCR (P : SyntacticFormula L → Prop) : Sequent L → Type u
| axL (Δ) {k} (r : L.Rel k) (v) :
    DerivationCR P (rel r v :: nrel r v :: Δ)
| verum (Δ) : DerivationCR P (⊤ :: Δ)
| or {Δ p q} :
    DerivationCR P (p :: q :: Δ) → DerivationCR P (p ⋎ q :: Δ)
| and {Δ p q} :
    DerivationCR P (p :: Δ) → DerivationCR P (q :: Δ) → DerivationCR P (p ⋏ q :: Δ)
| all {Δ p} :
    DerivationCR P (Rew.free.hom p :: Δ⁺) → DerivationCR P ((∀' p) :: Δ)
| ex {Δ p} (t) :
    DerivationCR P (p/[t] :: Δ) → DerivationCR P ((∃' p) :: Δ)
| wk {Δ Γ} : DerivationCR P Δ → Δ ⊆ Γ → DerivationCR P Γ
| cut {Δ p} : P p →
    DerivationCR P (p :: Δ) → DerivationCR P (~p :: Δ) → DerivationCR P Δ

scoped notation :45 "⊢ᶜ[" P "] " Γ:45 => DerivationCR P Γ

abbrev Derivation : Sequent L → Type u := DerivationCR (fun _ => False)

scoped prefix:45 "⊢ᵀ " => Derivation


abbrev DerivationClx (c : ℕ) : Sequent L → Type u := DerivationCR (·.complexity < c)

scoped notation :45 "⊢ᶜ[< " c "] " Γ:45 => DerivationClx c Γ

abbrev DerivationC : Sequent L → Type u := DerivationCR (fun _ => True)

instance : OneSided (SyntacticFormula L) := ⟨DerivationC⟩

instance : OneSided (Sentence L) := ⟨fun Γ ↦ ⊢¹ (Γ.map Rew.emb.hom : Sequent L)⟩

namespace DerivationCR
variable {P : SyntacticFormula L → Prop} {Δ Δ₁ Δ₂ Γ : Sequent L} {p q r : SyntacticFormula L}

def length : {Δ : Sequent L} → DerivationCR P Δ → ℕ
  | _, axL _ _ _   => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max dp.length dq.length).succ
  | _, all d       => d.length.succ
  | _, ex _ d      => d.length.succ
  | _, wk d _      => d.length.succ
  | _, cut _ dp dn => (max dp.length dn.length).succ

section

@[simp] lemma length_axL {k} {r : L.Rel k} {v} :
  (axL (P := P) Δ r v).length = 0 := rfl

@[simp] lemma length_verum : (verum (P := P) Δ).length = 0 := rfl

@[simp] lemma length_and {p q} (dp : ⊢ᶜ[P] p :: Δ) (dq : ⊢ᶜ[P] q :: Δ) :
    (and dp dq).length = (max dp.length dq.length).succ := rfl

@[simp] lemma length_or {p q} (d : ⊢ᶜ[P] (p :: q :: Δ)) : (or d).length = d.length.succ := rfl

@[simp] lemma length_all {p} (d : ⊢ᶜ[P] Rew.free.hom p :: Δ⁺) : (all d).length = d.length.succ := rfl

@[simp] lemma length_ex {t} {p} (d : ⊢ᶜ[P] p/[t] :: Δ) : (ex t d).length = d.length.succ := rfl

@[simp] lemma length_wk (d : ⊢ᶜ[P] Δ) (h : Δ ⊆ Γ) : (wk d h).length = d.length.succ := rfl

@[simp] lemma length_cut {p} (hp : P p) (dp : ⊢ᶜ[P] p :: Δ) (dn : ⊢ᶜ[P] (~p) :: Δ) :
  (cut hp dp dn).length = (max dp.length dn.length).succ := rfl

end

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected unsafe def repr : {Δ : Sequent L} → ⊢ᶜ[P] Δ → String
  | _, axL Δ _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, verum Δ       =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, @or _ _ Δ p q d      =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((p ⋎ q) :: Δ) ++ "$}\n\n"
  | _, @and _ _ Δ p q dp dq =>
      dp.repr ++
      dq.repr ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((p ⋏ q) :: Δ) ++ "$}\n\n"
  | _, @all _ _ Δ p d       =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀' p) :: Δ) ++ "$}\n\n"
  | _, @ex _ _ Δ p _ d      =>
      d.repr ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃' p) :: Δ) ++ "$}\n\n"
  | _, @wk _ _ _ Γ d _      =>
      d.repr ++
      "\\RightLabel{\\scriptsize(wk)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | _, @cut _ _ Δ _ _ dp dn =>
      dp.repr ++
      dn.repr ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Δ ++ "$}\n\n"

unsafe instance : Repr (⊢ᶜ[P] Δ) where reprPrec d _ := d.repr

end Repr

protected abbrev cast (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) : ⊢ᶜ[P] Γ := cast (congrArg (DerivationCR P) e) d

def cast₀ (d : ⊢ᵀ Δ) (e : Δ = Γ) : ⊢ᵀ Γ := d.cast e

@[simp] lemma cast_eq (d : ⊢ᶜ[P] Δ) (e : Δ = Δ) : d.cast e = d := rfl

@[simp] lemma length_cast (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) :
    (d.cast e).length = d.length := by rcases e with rfl; simp[DerivationCR.cast]

@[simp] lemma length_cast' (d : ⊢ᶜ[P] Δ) (e : Δ = Γ) :
    (cast (congrArg (DerivationCR P) e) d).length = d.length := by rcases e with rfl; simp[DerivationCR.cast]

def cutWeakening {P Q : SyntacticFormula L → Prop} (h : ∀ p, P p → Q p) : ∀ {Δ}, ⊢ᶜ[P] Δ → ⊢ᶜ[Q] Δ
  | _, axL Δ r v    => axL Δ r v
  | _, verum Δ      => verum Δ
  | _, and dp dq    => and (dp.cutWeakening h) (dq.cutWeakening h)
  | _, or d         => or (d.cutWeakening h)
  | _, all d        => all (d.cutWeakening h)
  | _, ex t d       => ex t (d.cutWeakening h)
  | _, wk d ss      => wk (d.cutWeakening h) ss
  | _, cut hp d₁ d₂ => cut (h _ hp) (d₁.cutWeakening h) (d₂.cutWeakening h)

@[simp] lemma lengtgh_cutWeakening {P Q : SyntacticFormula L → Prop} (h : ∀ p, P p → Q p) {Δ} (d : ⊢ᶜ[P] Δ) :
    (d.cutWeakening h).length = d.length := by induction d <;> simp[*, cutWeakening]

def ofLe {i j : ℕ} (h : i ≤ j) : ⊢ᶜ[< i] Δ → ⊢ᶜ[< j] Δ := cutWeakening (fun _ hp => lt_of_lt_of_le hp h)

def cutWeakeningCut (d : ⊢ᶜ[P] Δ) : ⊢¹ Δ := d.cutWeakening (by simp)

alias weakening := wk

def verum' (h : ⊤ ∈ Δ) : ⊢ᶜ[P] Δ := (verum Δ).wk (by simp[h])

def axL' {k} (r : L.Rel k) (v)
    (h : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) : ⊢ᶜ[P] Δ := (axL Δ r v).wk (by simp[h, hn])

def cCut (d₁ : ⊢¹ p :: Δ) (d₂ : ⊢¹ ~p :: Δ) : ⊢¹ Δ := cut trivial d₁ d₂

def cutClx {i p} (d₁ : ⊢ᶜ[< i] p :: Δ) (d₂ : ⊢ᶜ[< i] ~p :: Δ) (hp : p.complexity < i) :
    ⊢ᶜ[< i] Δ := cut hp d₁ d₂

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {p q : SyntacticFormula L} : ¬~p = p ⋏ q :=
ne_of_ne_complexity (by simp)

def em {p : SyntacticFormula L} {Δ : Sequent L} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᶜ[P] Δ := by
  induction p using Semiformula.formulaRec generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hrel r v         => exact axL' r v hpos hneg
  case hnrel r v        => exact axL' r v hneg hpos
  case hall p ih        =>
    have : ⊢ᶜ[P] ~Rew.free.hom p :: Rew.free.hom p :: Δ⁺ := ih (by simp) (by simp)
    have : ⊢ᶜ[P] (~Rew.shift.hom p)/[&0] :: Rew.free.hom p :: Δ⁺ :=
      this.cast (by simp[←Rew.hom_comp_app])
    have : ⊢ᶜ[P] Rew.free.hom p :: Δ⁺ := (ex &0 this).wk
      (by simp; right;
          have := mem_shifts_iff.mpr hneg
          rwa [Rew.ex, Rew.q_shift, LogicSymbol.HomClass.map_neg] at this)
    exact this.all.wk (by simp[hpos])
  case hex p ih         =>
    have : ⊢ᶜ[P] Rew.free.hom p :: ~Rew.free.hom p :: Δ⁺ := ih (by simp) (by simp)
    have : ⊢ᶜ[P] (Rew.shift.hom p)/[&0] :: ~Rew.free.hom p :: Δ⁺ :=
      this.cast (by simp[←Rew.hom_comp_app])
    have : ⊢ᶜ[P] Rew.free.hom (~p) :: Δ⁺ := (ex &0 this).wk
      (by simp; right;
          have := mem_shifts_iff.mpr hpos
          rwa [Rew.ex, Rew.q_shift] at this)
    exact this.all.wk (by simp[hneg])
  case hand p q ihp ihq =>
    have ihp : ⊢ᶜ[P] p :: ~p :: ~q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢ᶜ[P] q :: ~p :: ~q :: Δ := ihq (by simp) (by simp)
    have : ⊢ᶜ[P] ~p :: ~q :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor p q ihp ihq  =>
    have ihp : ⊢ᶜ[P] ~p :: p :: q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢ᶜ[P] ~q :: p :: q :: Δ := ihq (by simp) (by simp)
    have : ⊢ᶜ[P] p :: q :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

-- def elimFalsum (d : ⊢ᶜ[P] (⊥ :: Δ)) : ⊢ᶜ[P] Δ := by

section Hom

variable
  {L₁ : Language} [∀ k, DecidableEq (L₁.Func k)] [∀ k, DecidableEq (L₁.Rel k)]
  {L₂ : Language} [∀ k, DecidableEq (L₂.Func k)] [∀ k, DecidableEq (L₂.Rel k)]
  {Δ₁ Γ₁ : Finset (SyntacticFormula L₁)}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map $ .lMap Φ)⁺ = ((Δ⁺).map (.lMap Φ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) {P₁ : SyntacticFormula L₁ → Prop} {P₂ : SyntacticFormula L₂ → Prop}
    (h : ∀ p, P₁ p → P₂ (.lMap Φ p)):
    ∀ {Δ}, ⊢ᶜ[P₁] Δ → ⊢ᶜ[P₂] Δ.map (.lMap Φ)
  | _, axL Δ r v            =>
      by simp[Semiformula.lMap_rel, Semiformula.lMap_nrel]; exact axL _ _ _
  | _, verum Δ              => by simpa using verum _
  | _, @or _ _ Δ p q d      => by
      have : ⊢ᶜ[P₂] .lMap Φ p ⋎ .lMap Φ q :: Δ.map (.lMap Φ) :=
        or (by simpa using d.lMap Φ h)
      exact this.cast (by simp)
  | _, @and _ _ Δ p q dp dq =>
      have : ⊢ᶜ[P₂] .lMap Φ p ⋏ .lMap Φ q :: (Δ.map (.lMap Φ)) :=
        and ((dp.lMap Φ h).cast (by simp)) ((dq.lMap Φ h).cast (by simp))
      this.cast (by simp)
  | _, @all _ _ Δ p d       =>
      have : ⊢ᶜ[P₂] (∀' .lMap Φ p) :: (Δ.map (.lMap Φ)) :=
        all ((d.lMap Φ h).cast (by simp[←Semiformula.lMap_free, shifts_image]))
      this.cast (by simp)
  | _, @ex _ _ Δ p t d      =>
      have : ⊢ᶜ[P₂] (∃' .lMap Φ p) :: (Δ.map (.lMap Φ)) :=
        ex (Semiterm.lMap Φ t)
          ((d.lMap Φ h).cast (by simp[Semiformula.lMap_substs, Matrix.constant_eq_singleton]))
      this.cast (by simp)
  | _, @wk _ _ Δ Γ d ss     => (d.lMap Φ h).wk (List.map_subset _ ss)
  | _, @cut _ _ Δ p hp d dn =>
      have : ⊢ᶜ[P₂] (Δ.map (.lMap Φ)) :=
        cut (h p hp) ((d.lMap Φ h).cast (by simp)) ((dn.lMap Φ h).cast (by simp))
      this.cast (by simp[Finset.image_union])

def lMap₀ (Φ : L₁ →ᵥ L₂) {Δ : Sequent L₁} (d : ⊢ᵀ Δ) : ⊢ᵀ Δ.map (.lMap Φ) :=
  d.lMap Φ (fun _ x => x)

def lMapCut (Φ : L₁ →ᵥ L₂) {Δ : Sequent L₁} (d : ⊢¹ Δ) : ⊢¹ (Δ.map (.lMap Φ) : Sequent L₂) :=
  d.lMap Φ (fun _ x => x)

end Hom

private lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticSemiformula L 1) :
    Rew.free.hom ((Rew.rewrite (fun x => Rew.bShift (f x))).hom p) =
    (Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x))).hom (Rew.free.hom p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app, Fin.eq_zero])

private lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (p : SyntacticFormula L) :
    Rew.shift.hom ((Rew.rewrite f).hom p) = (Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x))).hom (Rew.shift.hom p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app])

private lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (p : SyntacticSemiformula L 1) :
    (Rew.rewrite f).hom ([→ t].hom p) = [→ Rew.rewrite f t].hom ((Rew.rewrite (Rew.bShift ∘ f)).hom p) := by
  simp[←Rew.hom_comp_app]; exact Rew.hom_ext' (by ext x <;> simp[Rew.comp_app])

protected def rewrite (h : ∀ f p, P p → P ((Rew.rewrite f).hom p)) :
    ∀ {Δ : Sequent L}, ⊢ᶜ[P] Δ → ∀ (f : ℕ → SyntacticTerm L), ⊢ᶜ[P] Δ.map (Rew.rewrite f).hom
  | _, axL Δ r v,            f =>
    (axL (Δ.map ((Rew.rewrite f).hom)) r (fun x => Rew.rewrite f (v x))).cast
      (by simp[Rew.rel, Rew.nrel])
  | _, verum Δ,              f => (verum (Δ.map ((Rew.rewrite f).hom))).cast (by simp)
  | _, @or _ _ Δ p q d,      f =>
    have : ⊢ᶜ[P] (Rew.rewrite f).hom p ⋎ (Rew.rewrite f).hom q :: Δ.map ((Rew.rewrite f).hom) :=
      or ((d.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, @and _ _ Δ p q dp dq, f =>
    have : ⊢ᶜ[P] (Rew.rewrite f).hom p ⋏ (Rew.rewrite f).hom q :: Δ.map ((Rew.rewrite f).hom) :=
      and ((dp.rewrite h f).cast (by simp)) ((dq.rewrite h f).cast (by simp))
    this.cast (by simp)
  | _, @all _ _ Δ p d,       f =>
    have : ⊢ᶜ[P] ((Rew.free.hom p) :: Δ⁺).map (Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x))).hom :=
      d.rewrite h (&0 :>ₙ fun x => Rew.shift (f x))
    have : ⊢ᶜ[P] (∀' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      all (this.cast (by simp[free_rewrite_eq, shifts, shift_rewrite_eq, Finset.image_image, Function.comp]))
    this.cast (by simp[Rew.q_rewrite])
  | _, @ex _ _ Δ p t d,      f =>
    have : ⊢ᶜ[P] (p/[t] :: Δ).map ((Rew.rewrite f).hom) := d.rewrite h f
    have : ⊢ᶜ[P] (∃' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      ex (Rew.rewrite f t) (this.cast (by simp[rewrite_subst_eq]))
    this.cast (by simp[Rew.q_rewrite])
  | _, @wk _ _ Δ Γ d ss,     f => (d.rewrite h f).wk (List.map_subset _ ss)
  | _, @cut _ _ Δ p hp d dn, f =>
    have dΔ : ⊢ᶜ[P] ((Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := (d.rewrite h f).cast (by simp)
    have dΓ : ⊢ᶜ[P] (~(Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := (dn.rewrite h f).cast (by simp)
    (cut (h f p hp) dΔ dΓ).cast (by simp)

def rewrite₀ {Δ : Sequent L} (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) :
    ⊢ᵀ Δ.map ((Rew.rewrite f).hom) := d.rewrite (by simp) f

def rewriteClx {i} {Δ : Sequent L} (d : ⊢ᶜ[< i] Δ) (f : ℕ → SyntacticTerm L) :
    ⊢ᶜ[< i] Δ.map ((Rew.rewrite f).hom) := d.rewrite (by simp) f

def rewriteCut {Δ : Sequent L} (d : ⊢¹ Δ) (f : ℕ → SyntacticTerm L) :
    ⊢¹ Δ.map ((Rew.rewrite f).hom) := d.rewrite (by simp) f

@[simp] lemma length_rewrite (h) (d : ⊢ᶜ[P] Δ) (f : ℕ → SyntacticTerm L) :
    (d.rewrite h f).length = d.length := by
  induction d generalizing f <;> simp[*, DerivationCR.rewrite, -List.map_cons]
  case axL => rw[length_cast] <;> simp[Rew.rel, Rew.nrel]
  case all => rw[length_cast] <;> simp[Rew.q_rewrite, *]
  case ex => rw[length_cast] <;> simp[Rew.q_rewrite, *]

@[simp] lemma length_rewrite₀ (d : ⊢ᵀ Δ) (f : ℕ → SyntacticTerm L) : (d.rewrite₀ f).length = d.length :=
  d.length_rewrite _ f

protected def map (h : ∀ f p, P p → P ((Rew.rewrite f).hom p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) (f : ℕ → ℕ) :
    ⊢ᶜ[P] Δ.map (Rew.rewriteMap f).hom := d.rewrite h _

protected def shift (h : ∀ f p, P p → P ((Rew.rewrite f).hom p)) {Δ : Sequent L} (d : ⊢ᶜ[P] Δ) :
    ⊢ᶜ[P] Δ⁺ :=
  (d.map h Nat.succ).cast (by simp[shifts]; congr)

private lemma map_subst_eq_free (p : SyntacticSemiformula L 1) (h : ¬p.fvar? m) :
    (Rew.rewriteMap (fun x => if x = m then 0 else x + 1)).hom (p/[&m]) = Rew.free.hom p := by
  simp[←Rew.hom_comp_app];
  exact Semiformula.rew_eq_of_funEqOn (by simp[Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp[Rew.comp_app]; rintro rfl; contradiction)

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ p ∈ Δ, ¬p.fvar? m) :
    Δ.map (Rew.rewriteMap (fun x => if x = m then 0 else x + 1)).hom = Δ⁺ := by
  simp[shifts]; apply List.map_congr
  intro p hp; exact rew_eq_of_funEqOn₀ (by intro x hx; simp; rintro rfl; have := h p hp; contradiction)

def genelalizeByNewver (h : ∀ f p, P p → P ((Rew.rewrite f).hom p))
    {p : SyntacticSemiformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
    (d : ⊢ᶜ[P] p/[&m] :: Δ) : ⊢ᶜ[P] (∀' p) :: Δ := by
  have : ⊢ᶜ[P] (Rew.free.hom p) :: Δ⁺ :=
    (d.map h (fun x => if x = m then 0 else x + 1)).cast
    (by simp[map_subst_eq_free p hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def genelalizeByNewver₀ {p : SyntacticSemiformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢ᵀ p/[&m] :: Δ) : ⊢ᵀ (∀' p) :: Δ := d.genelalizeByNewver (by simp) hp hΔ

def genelalizeByNewverCut {p : SyntacticSemiformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
  (d : ⊢¹ p/[&m] :: Δ) : ⊢¹ (∀' p) :: Δ := d.genelalizeByNewver (by simp) hp hΔ

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSemiformula L 1)
  (h : ⊢ᶜ[P] v.map (p/[·]) ++ Γ) : ⊢ᶜ[P] (∃' p) :: Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (List.subset_cons _ _)
  · exact (ih (Γ := (∃' p) :: Γ)
      ((ex t h).wk (by simp; exact List.subset_append_of_subset_right _ (List.subset_cons _ _)))).wk
        (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (p : SyntacticSemiformula L 1)
  (h : ⊢ᶜ[P] (∃' p) :: v.map (p/[·]) ++ Γ) : ⊢ᶜ[P] (∃' p) :: Γ :=
  (exOfInstances (Γ := (∃' p) :: Γ) v p
    (h.wk $ by simp; exact List.subset_append_of_subset_right _ (List.subset_cons _ _))).wk
    (by simp)

def toTait {Γ : List (Sentence L)} (d : ⊢¹ (Γ.map Rew.emb.hom : Sequent L)) : ⊢¹ Γ := d

def ofTait {Γ : List (Sentence L)} (d : ⊢¹ Γ) : ⊢¹ (Γ.map Rew.emb.hom : Sequent L) := d

def toOneSided {Δ : List (Sentence L)} (b : ⊢ᶜ[P] Δ.map Rew.emb.hom) : ⊢¹ Δ := b.cutWeakening (by simp)

end DerivationCR

instance : Tait (SyntacticFormula L) where
  verum := fun Δ => DerivationCR.verum Δ
  and := fun dp dq => (dp.and dq).cast (by simp)
  or := fun d => d.or.cast (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => DerivationCR.em hp hn

instance : Tait.Cut (SyntacticFormula L) := ⟨DerivationCR.cCut⟩

instance : Tait (Sentence L) where
  verum := fun Δ =>
    have d := DerivationCR.verum (P := fun _ => True) (Δ.map Rew.emb.hom)
    DerivationCR.toTait (d.cast $ by simp)
  and := fun {σ π Δ} dσ dπ =>
    let dσ : ⊢¹ Rew.emb.hom σ :: Δ.map Rew.emb.hom := DerivationCR.ofTait dσ
    let dπ : ⊢¹ Rew.emb.hom π :: Δ.map Rew.emb.hom := DerivationCR.ofTait dπ
    DerivationCR.toTait ((dσ.and dπ).cast $ by simp)
  or := fun {σ π Δ} d =>
    let d : ⊢¹ Rew.emb.hom σ :: Rew.emb.hom π :: Δ.map Rew.emb.hom := DerivationCR.ofTait d
    DerivationCR.toTait (d.or.cast $ by simp)
  wk := fun {Δ Δ'} d ss =>
    d.wk (List.map_subset _ ss)
  em := fun {σ Δ} hp hn =>
    DerivationCR.toTait
      (DerivationCR.em (p := Rew.emb.hom σ)
        (List.mem_map_of_mem _ hp) (by simpa using List.mem_map_of_mem Rew.emb.hom hn))

instance : Tait.Cut (Sentence L) := ⟨fun {Δ σ} dp dn =>
  DerivationCR.toTait (DerivationCR.cCut (p := Rew.emb.hom σ)
    (DerivationCR.ofTait dp) ((DerivationCR.ofTait dn).cast $ by simp))⟩

def oneSidedEquiv {Δ : List (Sentence L)} :
    ⊢¹ Δ ≃ ⊢¹ (Δ.map Rew.emb.hom : Sequent L) := Equiv.refl _

def twoSidedEquiv {Γ Δ : List (Sentence L)} :
    Γ ⊢² Δ ≃ (Γ.map Rew.emb.hom : Sequent L) ⊢² Δ.map Rew.emb.hom :=
  Tait.equiv.trans <| oneSidedEquiv.trans <| Equiv.trans (by simp[Function.comp]; exact Equiv.refl _) Tait.equiv.symm

abbrev DisjconseqTr (T : Theory L) (Γ : Sequent L) : Type _ := Rew.emb.hom '' T ⊢' Γ

scoped infix: 45 " ⊢'' " => DisjconseqTr

lemma proofToSyntactic {T : Theory L} {σ} (b : T ⊢ σ) :
    Rew.emb.hom '' T ⊢ (Rew.emb.hom σ : SyntacticFormula L) :=
  ⟨_, by simp; intro σ hσ; exact ⟨σ, b.antecedent_ss σ hσ, rfl⟩, twoSidedEquiv b.derivation⟩

lemma toProof {T : Theory L} {σ} (b : Rew.emb.hom '' T ⊢ (Rew.emb.hom σ : SyntacticFormula L)) :
    T ⊢ σ := by
  rcases Gentzen.proofEquivDerivation b with ⟨⟨Δ, hΔ⟩, d⟩
  have : ∀ p ∈ Δ, ∃ σ ∈ T, Rew.emb.hom σ = p := by simpa using hΔ
  choose f hf using this
  let Δ' := Δ.pmap f (by simp)
  have : Δ'.map Rew.emb.hom ⊢² [σ].map Rew.emb.hom := by
    rw[show Δ'.map Rew.emb.hom = Δ from by simp[List.map_pmap, hf]]; exact d
  exact Gentzen.toDisjconseq (twoSidedEquiv.symm this) (by simp; rintro σ p hp rfl; exact (hf p hp).1)

namespace Gentzen

variable {Γ Δ : Sequent L}

def genelalizeByNewver {p : SyntacticSemiformula L 1}
    (hp : ¬p.fvar? m) (hΓ : ∀ q ∈ Γ, ¬q.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m) :
    Γ ⊢² p/[&m] :: Δ → Γ ⊢² (∀' p) :: Δ := fun d ↦
  Tait.toConsRight <| DerivationCR.genelalizeByNewverCut hp
    (by simp; rintro q (⟨q, hq, rfl⟩ | hq)
        · simpa[Semiformula.fvar?] using hΓ q (by simp[hq])
        · simpa using hΔ q (by simp[hq]))
    (Tait.ofConsRight d)

def specialize {p : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    Γ ⊢² p/[t] :: Δ → Γ ⊢² (∃' p) :: Δ := fun d ↦
  Tait.toConsRight <| DerivationCR.ex t (Tait.ofConsRight d)

def lMap (Φ : L₁ →ᵥ L₂) {Γ Δ : Sequent L₁} (b : Γ ⊢² Δ) :
    Γ.map (Semiformula.lMap Φ) ⊢² Δ.map (Semiformula.lMap Φ) :=
  Tait.equiv.symm ((DerivationCR.lMapCut Φ b).cast $ by simp[Function.comp])

def lMap' (Φ : L₁ →ᵥ L₂) {Γ Δ : List (Sentence L₁)} (b : Γ ⊢² Δ) :
    Γ.map (Semiformula.lMap Φ) ⊢² Δ.map (Semiformula.lMap Φ) :=
  Tait.equiv.symm ((DerivationCR.lMapCut Φ b).cast $ by simp[Function.comp, lMap_emb])

end Gentzen

namespace System

variable {T : Theory L} {Γ Δ : Sequent L}

def genelalizeByNewver {p : SyntacticSemiformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m) :
    T ⊢'' p/[&m] :: Δ → T ⊢'' (∀' p) :: Δ := fun d ↦
  let ⟨Γ, d⟩ := Gentzen.DisjconseqEquivDerivation d
  Gentzen.DisjconseqEquivDerivation.symm ⟨Γ,
    Gentzen.genelalizeByNewver hp
      (by intro q hq
          have : ∃ σ ∈ T, Rew.emb.hom σ = q := by simpa using Γ.prop q hq
          rcases this with ⟨σ, _, rfl⟩; simp[Semiformula.fvar?])
      hΔ d⟩

def specialize {p : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    T ⊢'' p/[t] :: Δ → T ⊢'' (∃' p) :: Δ := fun d ↦
  let ⟨Γ, d⟩ := Gentzen.DisjconseqEquivDerivation d
  Gentzen.DisjconseqEquivDerivation.symm ⟨Γ, Gentzen.specialize t d⟩

variable (Φ : L₁ →ᵥ L₂) {T : Theory L₁}

def lMap {σ : Sentence L₁} (b : T ⊢ σ) :
    Theory.lMap Φ T ⊢ Semiformula.lMap Φ σ :=
  Gentzen.toDisjconseq (by simpa using Gentzen.lMap' Φ b.derivation)
    (by simp; intro σ hσ; exact Set.mem_image_of_mem _ (b.antecedent_ss σ hσ) )

lemma inconsistent_lMap : ¬System.Consistent T → ¬System.Consistent (T.lMap Φ) := by
  simp[System.Consistent]; intro b; exact ⟨by simpa using lMap Φ b⟩

end System

end FirstOrder

end LO
