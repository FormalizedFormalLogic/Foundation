import Logic.Logic.Calculus
import Logic.FirstOrder.Basic.Syntax.Rew

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

inductive Derivation : Sequent L → Type _
| axL (Δ) {k} (r : L.Rel k) (v) : Derivation (rel r v :: nrel r v :: Δ)
| verum (Δ)    : Derivation (⊤ :: Δ)
| or {Δ p q}   : Derivation (p :: q :: Δ) → Derivation (p ⋎ q :: Δ)
| and {Δ p q}  : Derivation (p :: Δ) → Derivation (q :: Δ) → Derivation (p ⋏ q :: Δ)
| all {Δ p}    : Derivation (Rew.free.hom p :: Δ⁺) → Derivation ((∀' p) :: Δ)
| ex {Δ p} (t) : Derivation (p/[t] :: Δ) → Derivation ((∃' p) :: Δ)
| wk {Δ Γ}     : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| cut {Δ p}    : Derivation (p :: Δ) → Derivation (~p :: Δ) → Derivation Δ

instance : OneSided (SyntacticFormula L) := ⟨Derivation⟩

instance : OneSided (Sentence L) := ⟨fun Γ ↦ ⊢¹ (Γ.map Rew.emb.hom : Sequent L)⟩

namespace Derivation
variable {Δ Δ₁ Δ₂ Γ : Sequent L} {p q r : SyntacticFormula L}

inductive CutRestricted (C : Set (SyntacticFormula L)) : {Δ : Sequent L} → ⊢¹ Δ → Prop
| axL (Δ) {k} (r : L.Rel k) (v)                 : CutRestricted C (axL Δ r v)
| verum (Δ)                                     : CutRestricted C (verum Δ)
| or {Δ p q} {d : ⊢¹ p :: q :: Δ}               : CutRestricted C d → CutRestricted C d.or
| and {Δ p q} {dp : ⊢¹ p :: Δ} {dq : ⊢¹ q :: Δ} : CutRestricted C dp → CutRestricted C dq → CutRestricted C (dp.and dq)
| all {Δ p} {d : ⊢¹ Rew.free.hom p :: Δ⁺}       : CutRestricted C d → CutRestricted C d.all
| ex {Δ p} (t) {d : ⊢¹ p/[t] :: Δ}              : CutRestricted C d → CutRestricted C d.ex
| wk {Δ Γ} {d : ⊢¹ Δ} (ss : Δ ⊆ Γ)              : CutRestricted C d → CutRestricted C (d.wk ss)
| cut {Δ p} {dp : ⊢¹ p :: Δ} {dn : ⊢¹ ~p :: Δ}  : CutRestricted C dp → CutRestricted C dn → p ∈ C → CutRestricted C (dp.cut dn)

def CutFree {Δ : Sequent L} (d : ⊢¹ Δ) : Prop := CutRestricted ∅ d

namespace CutRestricted
variable {C C' : Set (SyntacticFormula L)} {Δ Γ : Sequent L} {p q : SyntacticFormula L}

attribute [simp] CutRestricted.axL CutRestricted.verum

@[simp] lemma or' {d : ⊢¹ p :: q :: Δ} : CutRestricted C (@Derivation.or _ Δ _ _ d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.or⟩

@[simp] lemma and' {dp : ⊢¹ p :: Δ} {dq : ⊢¹ q :: Δ} :
    CutRestricted C (@Derivation.and _ Δ _ _ dp dq) ↔ CutRestricted C dp ∧ CutRestricted C dq :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by rintro ⟨dp, dq⟩; exact CutRestricted.and dp dq⟩

@[simp] lemma all' {p} {d : ⊢¹ Rew.free.hom p :: Δ⁺} : CutRestricted C (@Derivation.all _ Δ _ d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.all⟩

@[simp] lemma ex' {p} (t) {d : ⊢¹ p/[t] :: Δ} : CutRestricted C (@Derivation.ex _ Δ _ _ d) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.ex t⟩

@[simp] lemma wk' {d : ⊢¹ Δ} {ss : Δ ⊆ Γ} : CutRestricted C (@Derivation.wk _ Δ Γ d ss) ↔ CutRestricted C d :=
  ⟨by rintro ⟨⟩; assumption, CutRestricted.wk ss⟩

@[simp] lemma cut' {dp : ⊢¹ p :: Δ} {dn : ⊢¹ ~p :: Δ} :
    CutRestricted C (@Derivation.cut _ Δ p dp dn) ↔ p ∈ C ∧ CutRestricted C dp ∧ CutRestricted C dn :=
  ⟨by { rintro ⟨⟩; constructor; { assumption }; constructor <;> assumption },
   by rintro ⟨h, dp, dq⟩; exact CutRestricted.cut dp dq h⟩

lemma of_subset (d : ⊢¹ Δ) (ss : C ⊆ C') : CutRestricted C d → CutRestricted C' d := by
  induction d <;> simp[*]
  case and _ _ _ _ ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩
  case or _ _ _ _ ih => exact ih
  case all _ _ _ _ ih => exact ih
  case ex _ _ _ _ ih => exact ih
  case wk _ _ _ _ ih => exact ih
  case cut _ _ _ ihp ihn =>
    intro h hp hn; exact ⟨ss h, ihp hp, ihn hn⟩

end CutRestricted

def length : {Δ : Sequent L} → ⊢¹ Δ → ℕ
  | _, axL _ _ _   => 0
  | _, verum _     => 0
  | _, or d        => d.length.succ
  | _, and dp dq   => (max (length dp) (length dq)).succ
  | _, all d       => d.length.succ
  | _, ex _ d      => d.length.succ
  | _, wk d _      => d.length.succ
  | _, cut dp dn => (max (length dp) (length dn)).succ

section length

@[simp] lemma length_axL {k} {r : L.Rel k} {v} :
  length (axL Δ r v) = 0 := rfl

@[simp] lemma length_verum : length (verum Δ) = 0 := rfl

@[simp] lemma length_and {p q} (dp : ⊢¹ p :: Δ) (dq : ⊢¹ q :: Δ) :
    length (and dp dq) = (max (length dp) (length dq)).succ := rfl

@[simp] lemma length_or {p q} (d : ⊢¹ p :: q :: Δ) : length (or d) = d.length.succ := rfl

@[simp] lemma length_all {p} (d : ⊢¹ Rew.free.hom p :: Δ⁺) : length (all d) = d.length.succ := rfl

@[simp] lemma length_ex {t} {p} (d : ⊢¹ p/[t] :: Δ) : length (ex t d) = d.length.succ := rfl

@[simp] lemma length_wk (d : ⊢¹ Δ) (h : Δ ⊆ Γ) : length (wk d h) = d.length.succ := rfl

@[simp] lemma length_cut {p} (dp : ⊢¹ p :: Δ) (dn : ⊢¹ (~p) :: Δ) :
  length (cut dp dn) = (max (length dp) (length dn)).succ := rfl

end length

section Repr
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

protected unsafe def repr : {Δ : Sequent L} → ⊢¹ Δ → String
  | _, axL Δ _ _   =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize(axL)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, verum Δ       =>
      "\\AxiomC{}\n" ++
      "\\RightLabel{\\scriptsize($\\top$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Δ ++ "$}\n\n"
  | _, @or _ Δ p q d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\lor$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((p ⋎ q) :: Δ) ++ "$}\n\n"
  | _, @and _ Δ p q dp dq =>
      Derivation.repr dp ++
      Derivation.repr dq ++
      "\\RightLabel{\\scriptsize($\\land$)}\n" ++
      "\\BinaryInfC{$" ++ reprStr ((p ⋏ q) :: Δ) ++ "$}\n\n"
  | _, @all _ Δ p d       =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\forall$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∀' p) :: Δ) ++ "$}\n\n"
  | _, @ex _ Δ p _ d      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize($\\exists$)}\n" ++
      "\\UnaryInfC{$" ++ reprStr ((∃' p) :: Δ) ++ "$}\n\n"
  | _, @wk _ _ Γ d _      =>
      Derivation.repr d ++
      "\\RightLabel{\\scriptsize(wk)}\n" ++
      "\\UnaryInfC{$" ++ reprStr Γ ++ "$}\n\n"
  | _, @cut _ Δ _ dp dn =>
      Derivation.repr dp ++
      Derivation.repr dn ++
      "\\RightLabel{\\scriptsize(Cut)}\n" ++
      "\\BinaryInfC{$" ++ reprStr Δ ++ "$}\n\n"

unsafe instance : Repr (⊢¹ Δ) where reprPrec d _ := Derivation.repr d

end Repr

protected abbrev cast (d : ⊢¹ Δ) (e : Δ = Γ) : ⊢¹ Γ := cast (congrArg Derivation e) d

@[simp] lemma cast_eq (d : ⊢¹ Δ) (e : Δ = Δ) : Derivation.cast d e = d := rfl

@[simp] lemma length_cast (d : ⊢¹ Δ) (e : Δ = Γ) :
    length (Derivation.cast d e) = length d := by rcases e with rfl; simp[Derivation.cast]

@[simp] lemma length_cast' (d : ⊢¹ Δ) (e : Δ = Γ) :
    length (cast (congrArg Derivation e) d) = length d := by rcases e with rfl; simp[Derivation.cast]

@[simp] lemma CutRestricted.cast {C : Set (SyntacticFormula L)} {Δ Γ : Sequent L} {e : Δ = Γ} {d : ⊢¹ Δ} :
    CutRestricted C (Derivation.cast d e) ↔ CutRestricted C d := by rcases e with ⟨rfl⟩; simp

@[simp] lemma CutFree.cast {Δ Γ : Sequent L} {e : Δ = Γ} {d : ⊢¹ Δ} :
    CutFree (Derivation.cast d e) ↔ CutFree d := by rcases e with ⟨rfl⟩; simp

alias weakening := wk

def verum' (h : ⊤ ∈ Δ) : ⊢¹ Δ := (verum Δ).wk (by simp[h])

def axL' {k} (r : L.Rel k) (v)
    (h : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) : ⊢¹ Δ := (axL Δ r v).wk (by simp[h, hn])

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

private lemma neg_ne_and {p q : SyntacticFormula L} : ¬~p = p ⋏ q :=
ne_of_ne_complexity (by simp)

def em {p : SyntacticFormula L} {Δ : Sequent L} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢¹ Δ := by
  induction p using Semiformula.formulaRec generalizing Δ <;> simp at hneg
  case hverum           => exact verum' hpos
  case hfalsum          => exact verum' hneg
  case hrel r v         => exact axL' r v hpos hneg
  case hnrel r v        => exact axL' r v hneg hpos
  case hall p ih        =>
    have : ⊢¹ ~Rew.free.hom p :: Rew.free.hom p :: Δ⁺ := ih (by simp) (by simp)
    have : ⊢¹ (~Rew.shift.hom p)/[&0] :: Rew.free.hom p :: Δ⁺ :=
      Derivation.cast this (by simp[←Rew.hom_comp_app])
    have : ⊢¹ Rew.free.hom p :: Δ⁺ := (ex &0 this).wk
      (by simp; right;
          have := mem_shifts_iff.mpr hneg
          rwa [Rew.ex, Rew.q_shift, LogicalConnective.HomClass.map_neg] at this)
    exact this.all.wk (by simp[hpos])
  case hex p ih         =>
    have : ⊢¹ Rew.free.hom p :: ~Rew.free.hom p :: Δ⁺ := ih (by simp) (by simp)
    have : ⊢¹ (Rew.shift.hom p)/[&0] :: ~Rew.free.hom p :: Δ⁺ :=
      Derivation.cast this (by simp[←Rew.hom_comp_app])
    have : ⊢¹ Rew.free.hom (~p) :: Δ⁺ := (ex &0 this).wk
      (by simp; right;
          have := mem_shifts_iff.mpr hpos
          rwa [Rew.ex, Rew.q_shift] at this)
    exact this.all.wk (by simp[hneg])
  case hand p q ihp ihq =>
    have ihp : ⊢¹ p :: ~p :: ~q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢¹ q :: ~p :: ~q :: Δ := ihq (by simp) (by simp)
    have : ⊢¹ ~p :: ~q :: Δ := (ihp.and ihq).wk (by simp[hpos])
    exact this.or.wk (by simp[hneg])
  case hor p q ihp ihq  =>
    have ihp : ⊢¹ ~p :: p :: q :: Δ := ihp (by simp) (by simp)
    have ihq : ⊢¹ ~q :: p :: q :: Δ := ihq (by simp) (by simp)
    have : ⊢¹ p :: q :: Δ := (ihp.and ihq).wk (by simp[hneg])
    exact this.or.wk (by simp[hpos])

section Hom

variable {L₁ : Language} {L₂ : Language}
  {Δ₁ Γ₁ : Finset (SyntacticFormula L₁)}

lemma shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map $ .lMap Φ)⁺ = ((Δ⁺).map (.lMap Φ)) :=
  by simp[shifts, shiftEmb, Finset.map_eq_image, Finset.image_image, Function.comp, Semiformula.lMap_shift]

def lMap (Φ : L₁ →ᵥ L₂) : ∀ {Δ}, ⊢¹ Δ → ⊢¹ (Δ.map (.lMap Φ) : Sequent L₂)
  | _, axL Δ r v          =>
      by simp[Semiformula.lMap_rel, Semiformula.lMap_nrel]; exact axL _ _ _
  | _, verum Δ            => by simpa using verum _
  | _, @or _ Δ p q d      => by
      have : ⊢¹ (.lMap Φ p ⋎ .lMap Φ q :: Δ.map (.lMap Φ) : Sequent L₂) :=
        or (by simpa using lMap Φ d)
      exact Derivation.cast this (by simp)
  | _, @and _ Δ p q dp dq =>
      have : ⊢¹ (.lMap Φ p ⋏ .lMap Φ q :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
      Derivation.cast this (by simp)
  | _, @all _ Δ p d       =>
      have : ⊢¹ ((∀' .lMap Φ p) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        all (Derivation.cast (lMap Φ d) (by simp[←Semiformula.lMap_free, shifts_image]))
      Derivation.cast this (by simp)
  | _, @ex _ Δ p t d      =>
      have : ⊢¹ ((∃' .lMap Φ p) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
        ex (Semiterm.lMap Φ t)
          (Derivation.cast (lMap Φ d) (by simp[Semiformula.lMap_substs, Matrix.constant_eq_singleton]))
      Derivation.cast this (by simp)
  | _, @wk _ Δ Γ d ss     => (lMap Φ d).wk (List.map_subset _ ss)
  | _, @cut _ Δ p d dn    =>
      have : ⊢¹ (Δ.map (.lMap Φ) : Sequent L₂) :=
        cut (p := .lMap Φ p) (Derivation.cast (lMap Φ d) (by simp)) (Derivation.cast (lMap Φ dn) (by simp))
      Derivation.cast this (by simp[Finset.image_union])

lemma CutRestricted.lMap {C : Set (SyntacticFormula L₂)} {Δ : Sequent L₁} (Φ : L₁ →ᵥ L₂) (d : ⊢¹ Δ) :
    CutRestricted C (lMap Φ d) ↔ CutRestricted (.lMap Φ ⁻¹' C) d := by
  induction d <;> simp[Derivation.lMap, *]

@[simp] lemma CutFree.lMap {Δ : Sequent L₁} (Φ : L₁ →ᵥ L₂) (d : ⊢¹ Δ) :
    CutFree (lMap Φ d) ↔ CutFree d := by simp[CutFree, CutRestricted.lMap]

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

attribute [simp] Rew.q_rewrite

def rewrite : ∀ {Δ}, ⊢¹ Δ → ∀ (f : ℕ → SyntacticTerm L), ⊢¹ Δ.map (Rew.rewrite f).hom
  | _, axL Δ r v,          f => by simp[Rew.rel, Rew.nrel]; exact axL _ _ _
  | _, verum Δ,            f => Derivation.cast (verum (Δ.map ((Rew.rewrite f).hom))) (by simp)
  | _, @or _ Δ p q d,      f =>
    have : ⊢¹ (Rew.rewrite f).hom p ⋎ (Rew.rewrite f).hom q :: Δ.map ((Rew.rewrite f).hom) :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | _, @and _ Δ p q dp dq, f =>
    have : ⊢¹ (Rew.rewrite f).hom p ⋏ (Rew.rewrite f).hom q :: Δ.map ((Rew.rewrite f).hom) :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | _, @all _ Δ p d,       f =>
    have : ⊢¹ ((Rew.free.hom p) :: Δ⁺).map (Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x))).hom :=
      rewrite d (&0 :>ₙ fun x => Rew.shift (f x))
    have : ⊢¹ (∀' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      all (Derivation.cast this (by simp[free_rewrite_eq, shifts, shift_rewrite_eq, Finset.image_image, Function.comp]))
    Derivation.cast this (by simp[Rew.q_rewrite])
  | _, @ex _ Δ p t d,      f =>
    have : ⊢¹ (p/[t] :: Δ).map ((Rew.rewrite f).hom) := rewrite d f
    have : ⊢¹ (∃' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      ex (Rew.rewrite f t) (Derivation.cast this (by simp[rewrite_subst_eq]))
    Derivation.cast this (by simp[Rew.q_rewrite])
  | _, @wk _ Δ Γ d ss,     f => (rewrite d f).wk (List.map_subset _ ss)
  | _, @cut _ Δ p d dn,    f =>
    have dΔ : ⊢¹ ((Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := Derivation.cast (rewrite d f) (by simp)
    have dΓ : ⊢¹ (~(Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΔ dΓ) (by simp)

lemma CutRestricted.rewrite {C : Set (SyntacticFormula L)}
    (hC : ∀ f : ℕ → SyntacticTerm L, ∀ p, p ∈ C → (Rew.rewrite f).hom p ∈ C)
    {Δ : Sequent L} (f : ℕ → SyntacticTerm L) {d : ⊢¹ Δ} :
    CutRestricted C d → CutRestricted C (rewrite d f) := by
  induction d generalizing f <;> simp[-List.map_cons, Derivation.rewrite, *]
  case axL _ _ _ _ => simp[Rew.rel, Rew.nrel]
  case and _ _ _ ihp ihq => intro hp hq; exact ⟨ihp _ hp, ihq _ hq⟩
  case or _ _ ih => intro h; exact ih _ h
  case all _ _ _ ih =>
    rw [CutRestricted.cast, CutRestricted.all', CutRestricted.cast]
    exact ih _; simp
  case ex _ _ _ ih =>
    rw [CutRestricted.cast, CutRestricted.ex', CutRestricted.cast]
    exact ih _; simp
  case wk _ _ ih => intro h; exact ih _ h
  case cut _ _ ih ihn => intro hp h hn; exact ⟨hC _ _ hp, ih _ h, ihn _ hn⟩

@[simp] lemma length_rewrite (d : ⊢¹ Δ) (f : ℕ → SyntacticTerm L) :
    length (rewrite d f) = length d := by
  induction d generalizing f <;> simp[*, Derivation.rewrite, -List.map_cons]
  case axL => simp[Rew.rel, Rew.nrel]
  case all => rw[length_cast] <;> simp[Rew.q_rewrite, *]
  case ex => rw[length_cast] <;> simp[Rew.q_rewrite, *]

protected def map {Δ : Sequent L} (d : ⊢¹ Δ) (f : ℕ → ℕ) :
    ⊢¹ Δ.map (Rew.rewriteMap f).hom := rewrite d (fun x ↦ &(f x))

protected def shift {Δ : Sequent L} (d : ⊢¹ Δ) :
    ⊢¹ Δ⁺ := Derivation.cast (Derivation.map d Nat.succ) (by simp[shifts]; congr)

private lemma map_subst_eq_free (p : SyntacticSemiformula L 1) (h : ¬p.fvar? m) :
    (Rew.rewriteMap (fun x => if x = m then 0 else x + 1)).hom (p/[&m]) = Rew.free.hom p := by
  simp[←Rew.hom_comp_app];
  exact Semiformula.rew_eq_of_funEqOn (by simp[Rew.comp_app, Fin.eq_zero])
    (fun x hx => by simp[Rew.comp_app]; rintro rfl; contradiction)

private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ p ∈ Δ, ¬p.fvar? m) :
    Δ.map (Rew.rewriteMap (fun x => if x = m then 0 else x + 1)).hom = Δ⁺ := by
  simp[shifts]; apply List.map_congr
  intro p hp; exact rew_eq_of_funEqOn₀ (by intro x hx; simp; rintro rfl; have := h p hp; contradiction)

def genelalizeByNewver
    {p : SyntacticSemiformula L 1} (hp : ¬p.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m)
    (d : ⊢¹ p/[&m] :: Δ) : ⊢¹ (∀' p) :: Δ := by
  have : ⊢¹ (Rew.free.hom p) :: Δ⁺ :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
    (by simp[map_subst_eq_free p hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this

def exOfInstances (v : List (SyntacticTerm L)) (p : SyntacticSemiformula L 1)
  (h : ⊢¹ v.map (p/[·]) ++ Γ) : ⊢¹ (∃' p) :: Γ := by
  induction' v with t v ih generalizing Γ <;> simp at h
  · exact weakening h (List.subset_cons _ _)
  · exact (ih (Γ := (∃' p) :: Γ)
      ((ex t h).wk (by simp; exact List.subset_append_of_subset_right _ (List.subset_cons _ _)))).wk
        (by simp)

def exOfInstances' (v : List (SyntacticTerm L)) (p : SyntacticSemiformula L 1)
  (h : ⊢¹ (∃' p) :: v.map (p/[·]) ++ Γ) : ⊢¹ (∃' p) :: Γ :=
  (exOfInstances (Γ := (∃' p) :: Γ) v p
    (h.wk $ by simp; exact List.subset_append_of_subset_right _ (List.subset_cons _ _))).wk
    (by simp)

def toTait {Γ : List (Sentence L)} (d : ⊢¹ (Γ.map Rew.emb.hom : Sequent L)) : ⊢¹ Γ := d

def ofTait {Γ : List (Sentence L)} (d : ⊢¹ Γ) : ⊢¹ (Γ.map Rew.emb.hom : Sequent L) := d

def toOneSided {Δ : List (Sentence L)} (d : ⊢¹ (Δ.map Rew.emb.hom : Sequent L)) : ⊢¹ Δ := d

end Derivation

instance : Tait (SyntacticFormula L) where
  verum := fun Δ => Derivation.verum Δ
  and := fun dp dq => Derivation.cast (dp.and dq) (by simp)
  or := fun d => Derivation.cast d.or (by simp)
  wk := fun d ss => d.wk ss
  em := fun hp hn => Derivation.em hp hn

instance : Tait.Cut (SyntacticFormula L) := ⟨Derivation.cut⟩

instance : Tait (Sentence L) where
  verum := fun Δ =>
    have d := Derivation.verum (Δ.map Rew.emb.hom)
    Derivation.toTait (Derivation.cast d $ by simp)
  and := fun {σ π Δ} dσ dπ =>
    let dσ : ⊢¹ Rew.emb.hom σ :: Δ.map Rew.emb.hom := Derivation.ofTait dσ
    let dπ : ⊢¹ Rew.emb.hom π :: Δ.map Rew.emb.hom := Derivation.ofTait dπ
    Derivation.toTait (Derivation.cast (dσ.and dπ) $ by simp)
  or := fun {σ π Δ} d =>
    let d : ⊢¹ Rew.emb.hom σ :: Rew.emb.hom π :: Δ.map Rew.emb.hom := Derivation.ofTait d
    Derivation.toTait (Derivation.cast d.or $ by simp)
  wk := fun {Δ Δ'} d ss =>
    d.wk (List.map_subset _ ss)
  em := fun {σ Δ} hp hn =>
    Derivation.toTait
      (Derivation.em (p := Rew.emb.hom σ)
        (List.mem_map_of_mem _ hp) (by simpa using List.mem_map_of_mem Rew.emb.hom hn))

instance : Tait.Cut (Sentence L) := ⟨fun {Δ σ} dp dn =>
  Derivation.toTait (Derivation.cut (p := Rew.emb.hom σ)
    (Derivation.ofTait dp) (Derivation.cast (Derivation.ofTait dn) $ by simp))⟩

def oneSidedEquiv {Δ : List (Sentence L)} :
    ⊢¹ Δ ≃ ⊢¹ (Δ.map Rew.emb.hom : Sequent L) := Equiv.refl _

def twoSidedEquiv {Γ Δ : List (Sentence L)} :
    Γ ⊢² Δ ≃ (Γ.map Rew.emb.hom : Sequent L) ⊢² Δ.map Rew.emb.hom :=
  Tait.equiv.trans <| oneSidedEquiv.trans <| Equiv.trans (by simp[Function.comp]; exact Equiv.refl _) Tait.equiv.symm

abbrev DisjconseqTr (T : Theory L) (Γ : Sequent L) : Type _ := (Rew.emb.hom '' T : SyntacticTheory L) ⊢' Γ

scoped infix: 45 " ⊢'' " => DisjconseqTr

def proofToSyntactic {T : Theory L} {σ} (b : T ⊢ σ) :
    (Rew.emb.hom '' T : SyntacticTheory L) ⊢ (Rew.emb.hom σ : SyntacticFormula L) :=
  ⟨_, by simp; intro σ hσ; exact ⟨σ, Gentzen.Disjconseq.subset b σ hσ, rfl⟩, twoSidedEquiv b.derivation⟩

noncomputable def toProof {T : Theory L} {σ} (b : (Rew.emb.hom '' T : SyntacticTheory L) ⊢ (Rew.emb.hom σ : SyntacticFormula L)) :
    T ⊢ σ := by
  rcases Gentzen.proofEquivDerivation b with ⟨⟨Δ, hΔ⟩, d⟩
  have : ∀ p ∈ Δ, ∃ σ ∈ T, Rew.emb.hom σ = p := by simpa using hΔ
  choose f hf using this
  let Δ' := Δ.pmap f (by simp)
  have : Δ'.map Rew.emb.hom ⊢² ([σ].map Rew.emb.hom : List (SyntacticFormula L)) := by
    rw[show Δ'.map Rew.emb.hom = Δ from by simp [Δ', List.map_pmap, hf]]; exact d
  exact Gentzen.toDisjconseq (twoSidedEquiv.symm this) (by simp [Δ']; rintro σ p hp rfl; exact (hf p hp).1)

namespace Gentzen

variable {Γ Δ : Sequent L}

def genelalizeByNewver {p : SyntacticSemiformula L 1}
    (hp : ¬p.fvar? m) (hΓ : ∀ q ∈ Γ, ¬q.fvar? m) (hΔ : ∀ q ∈ Δ, ¬q.fvar? m) :
    Γ ⊢² p/[&m] :: Δ → Γ ⊢² (∀' p) :: Δ := fun d ↦
  Tait.toConsRight <| Derivation.genelalizeByNewver hp
    (by simp; rintro q (⟨q, hq, rfl⟩ | hq)
        · simpa[Semiformula.fvar?] using hΓ q (by simp[hq])
        · simpa using hΔ q (by simp[hq]))
    (Tait.ofConsRight d)

def specialize {p : SyntacticSemiformula L 1} (t : SyntacticTerm L) :
    Γ ⊢² p/[t] :: Δ → Γ ⊢² (∃' p) :: Δ := fun d ↦
  Tait.toConsRight <| Derivation.ex t (Tait.ofConsRight d)

def lMap (Φ : L₁ →ᵥ L₂) {Γ Δ : Sequent L₁} (b : Γ ⊢² Δ) :
    Γ.map (Semiformula.lMap Φ) ⊢² Δ.map (Semiformula.lMap Φ) :=
  Tait.equiv.symm (Derivation.cast (Derivation.lMap Φ b) $ by simp[Function.comp])

def lMap' (Φ : L₁ →ᵥ L₂) {Γ Δ : List (Sentence L₁)} (b : Γ ⊢² Δ) :
    Γ.map (Semiformula.lMap Φ) ⊢² Δ.map (Semiformula.lMap Φ) :=
  Tait.equiv.symm (Derivation.cast (Derivation.lMap Φ b) $ by simp[Function.comp, lMap_emb])

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
    (by simp; intro σ hσ; exact Set.mem_image_of_mem _ (Gentzen.Disjconseq.subset b σ hσ) )

lemma inconsistent_lMap : System.Inconsistent T → System.Inconsistent (T.lMap Φ) := by
  simp [System.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨by simpa using lMap Φ b⟩

end System

namespace Theory

instance {T U : Theory L} : T ≼ T + U := System.Axiomatized.subtheoryOfSubset (by simp [add_def])

instance {T U : Theory L} : U ≼ T + U := System.Axiomatized.subtheoryOfSubset (by simp [add_def])

end Theory

end FirstOrder

end LO
