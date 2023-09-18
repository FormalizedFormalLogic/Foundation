import Logic.Predicate.FirstOrder.Basic.Formula.Formula
import Logic.Predicate.FirstOrder.Basic.Formula.Elab
import Logic.Vorspiel.W

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v}

inductive UTerm (L : Language.{u}) (μ : Type v)
  | bvar : ℕ → UTerm L μ
  | fvar : μ → UTerm L μ
  | func : ∀ {arity}, L.func arity → (Fin arity → UTerm L μ) → UTerm L μ

inductive UFormula (L : Language.{u}) (μ : Type v) : Type (max u v) where
  | verum  : UFormula L μ
  | falsum : UFormula L μ
  | rel    : {arity : ℕ} → L.rel arity → (Fin arity → UTerm L μ) → UFormula L μ
  | nrel   : {arity : ℕ} → L.rel arity → (Fin arity → UTerm L μ) → UFormula L μ
  | and    : UFormula L μ → UFormula L μ → UFormula L μ
  | or     : UFormula L μ → UFormula L μ → UFormula L μ
  | all    : UFormula L μ → UFormula L μ
  | ex     : UFormula L μ → UFormula L μ

namespace UTerm

instance : Inhabited (UTerm L μ) := ⟨bvar 0⟩

def elim {γ : Type*}
  (b : ℕ → γ) (e : μ → γ) (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) : UTerm L μ → γ
  | bvar x   => b x
  | fvar x   => e x
  | func f v => u f (fun i => elim b e u (v i))

def elimv {σ γ : Type*} (fs : σ → σ)
  (b : σ → ℕ → γ) (e : σ → μ → γ) (u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) : σ → UTerm L μ → γ
  | z, bvar x   => b z x
  | z, fvar x   => e z x
  | z, func f v => u z f (fun i => elimv fs b e u (fs z) (v i))

lemma elim_eq_elimv {b : ℕ → γ} {e : μ → γ} {u : {k : ℕ} → L.func k → (Fin k → γ) → γ} :
    elim b e u = elimv id (fun _ => b) (fun _ => e) (fun _ => u) () := by
  funext t; induction t <;> simp[elim, elimv, *]
  
lemma elim_eq_elimv' {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ} :
    (fun x => elim (b x) (e x) (u x)) = elimv id b e u := by
  funext x t; induction t <;> simp[elim, elimv, *]

lemma elimv_eq_elimv {fs : σ → τ → τ} {b : σ → τ → ℕ → γ} {e : σ → τ → μ → γ} {u : σ → τ → {k : ℕ} → L.func k → (Fin k → γ) → γ} :
    (fun x => elimv (fs x) (b x) (e x) (u x)) =
    fun x z => elimv (fun (p : σ × τ) => (p.1, fs p.1 p.2)) (fun (p : σ × τ) => b p.1 p.2) (fun (p : σ × τ) => e p.1 p.2) (fun (p : σ × τ) => u p.1 p.2) (x, z) := by
  funext z x t; induction t generalizing z x <;> simp[elimv, *]

def bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : UTerm L μ₁ → UTerm L μ₂
  | bvar x   => b x
  | fvar x   => e x
  | func f v => func f (fun i => (v i).bind b e)

def rewrite (e : μ₁ → UTerm L μ₂) : UTerm L μ₁ → UTerm L μ₂ := bind bvar e

def bShifts (k : ℕ) : UTerm L μ → UTerm L μ := bind (fun x => bvar (x + k)) fvar

def substAt (z : ℕ) (t : UTerm L μ) : UTerm L μ → UTerm L μ :=
  bind (fun x => if x < z then bvar x else if x = z then t else bvar x.pred) fvar

def bv : UTerm L μ → ℕ
  | bvar x   => x + 1
  | fvar _   => 0
  | func _ v => Finset.sup Finset.univ (fun i => (v i).bv)

def substLast (u : UTerm L μ) : UTerm L μ → UTerm L μ := fun t => substAt t.bv.pred u t

@[simp] lemma bv_bvar : bv (bvar x : UTerm L μ) = x + 1 := rfl

@[simp] lemma bv_fvar : bv (fvar x : UTerm L μ) = 0 := rfl

@[simp] lemma substAt_bvar (z) (u : UTerm L μ) : substAt z u (bvar z) = u := by simp[substLast, substAt, bind]

@[simp] lemma substAt_bvar_fin (z) (u : UTerm L μ) (x : Fin z) :
    substAt z u (bvar x) = bvar x := by simp[substLast, substAt, bind]

@[simp] lemma substAt_fvar (z) (u : UTerm L μ) : substAt z u (fvar x) = fvar x := by simp[substLast, substAt, bind]

@[simp] lemma substAt_func {k} (f : L.func k) (v : Fin k → UTerm L μ) :
    substAt z u (func f v) = func f (fun i => substAt z u (v i)) := by simp[substLast, substAt, bind]

@[simp] lemma subtype_val_bv_le (t : { t : UTerm L μ // t.bv ≤ n }) : t.val.bv ≤ n := t.property

lemma bv_bind {b : ℕ → UTerm L μ₂} {e : μ₁ → UTerm L μ₂} (t : UTerm L μ₁)
  (hb : ∀ x < t.bv, (b x).bv ≤ m) (he : ∀ x, (e x).bv ≤ m) : (bind b e t).bv ≤ m := by
  induction t
  case bvar => simp[bind, bv] at hb ⊢; exact hb _ (Nat.lt_succ_self _)
  case fvar => simp[bind, bv] at he ⊢; exact he _
  case func k f v ih =>
    simp[bind, bv]; intro i; exact ih i (fun x hx => hb x (by simp[bv]; exact ⟨i, hx⟩))

lemma bv_rewrite {e : μ₁ → UTerm L μ₂} {t : UTerm L μ₁} (ht : t.bv ≤ m) (he : ∀ x, (e x).bv ≤ m) : (rewrite e t).bv ≤ m :=
  bv_bind t (fun x hx => by simp; exact lt_of_lt_of_le hx ht) he

lemma bv_substLast {t u : UTerm L μ} (ht : t.bv ≤ n + 1) (hu : u.bv ≤ n) : (substLast u t).bv ≤ n :=
  bv_bind _ (fun x hx => by
    have : x < (bv t).pred ∨ x = (bv t).pred ∨ x > (bv t).pred := Nat.lt_trichotomy _ _
    rcases this with (lt | rfl | lt)
    · simp[lt]
      have : x < n := by simpa using lt_of_lt_of_le lt (Nat.pred_le_pred ht)
      exact this
    · simp[hu]
    · simp[Nat.lt_asymm lt, Nat.ne_of_gt lt]
      have : x ≤ t.bv.pred := Nat.le_pred_of_lt hx
      exact False.elim (Nat.lt_le_antisymm lt this)) (by simp[bv])

def toSubTerm : (t : UTerm L μ) → t.bv ≤ n → SubTerm L μ n
  | bvar x,   h => #⟨x, by simp at h; exact Nat.lt_of_succ_le h⟩
  | fvar x,   _ => &x
  | func f v, h => SubTerm.func f (fun i => toSubTerm (v i) (by simp[bv] at h; exact h i))

def ofSubTerm : SubTerm L μ n → { t : UTerm L μ // t.bv ≤ n }
  | #x               => ⟨bvar x, Nat.succ_le_of_lt x.isLt⟩
  | &x               => ⟨fvar x, by simp⟩
  | SubTerm.func f v => ⟨func f (fun i => ofSubTerm (v i)), by simp[bv]⟩

lemma toSubTerm_ofSubterm {n} (t : SubTerm L μ n) : toSubTerm (ofSubTerm t).1 (ofSubTerm t).2 = t := by
  induction t <;> simp[ofSubTerm, toSubTerm]
  case func f v ih => { funext i; exact ih i }

lemma ofSubTerm_toSubterm {n} (t : UTerm L μ) (h : t.bv ≤ n) : ofSubTerm (toSubTerm t h) = t := by
  induction t <;> simp[ofSubTerm, toSubTerm]
  case func f v ih =>
    funext i
    have h : ∀ i, (v i).bv ≤ n := by simpa[bv] using h
    exact ih i (h i)

def subtEquiv : SubTerm L μ n ≃ { t : UTerm L μ // t.bv ≤ n } where
  toFun := ofSubTerm
  invFun := fun t => toSubTerm t.1 t.2
  left_inv := toSubTerm_ofSubterm
  right_inv := by intro ⟨t, h⟩; ext; simpa using ofSubTerm_toSubterm t h

@[simp] lemma subtEquiv_bvar (x : Fin n) : subtEquiv (#x : SubTerm L μ n) = ⟨bvar x, x.isLt⟩ := rfl

@[simp] lemma subtEquiv_fvar (x : μ) : subtEquiv (&x : SubTerm L μ n) = ⟨fvar x, by simp⟩ := rfl

@[simp] lemma subtEquiv_func {k} (f : L.func k) (v : Fin k → SubTerm L μ n) :
    subtEquiv (SubTerm.func f v) = ⟨func f (fun i => subtEquiv (v i)), by simp[bv]⟩ := rfl

open Encodable Primrec Primrec₂
variable [Primcodable μ] [(k : ℕ) → Primcodable (L.func k)] [UniformlyPrimcodable L.func]

section W

abbrev Node (L : Language.{u}) (μ : Type v) := ℕ ⊕ μ ⊕ (k : ℕ) × L.func k

@[reducible] def Edge (L : Language.{u}) (μ : Type v) : Node L μ → Type
  | (Sum.inl _)                => Empty
  | (Sum.inr $ Sum.inl _)      => Empty
  | (Sum.inr $ Sum.inr ⟨k, _⟩) => Fin k

def toW : UTerm L μ → WType (Edge L μ)
  | bvar x   => ⟨Sum.inl x,                Empty.elim⟩
  | fvar x   => ⟨Sum.inr (Sum.inl x),      Empty.elim⟩
  | func f v => ⟨Sum.inr (Sum.inr ⟨_, f⟩), fun i => (v i).toW⟩

def ofW : WType (Edge L μ) → UTerm L μ
  | ⟨Sum.inl x, _⟩             => bvar x
  | ⟨Sum.inr (Sum.inl x), _⟩   => fvar x
  | ⟨Sum.inr (Sum.inr ⟨_, f⟩), v⟩ => func f (fun i => ofW (v i))

def equivW (L) (μ) : UTerm L μ ≃ WType (Edge L μ) where
  toFun := toW
  invFun := ofW
  left_inv := fun t => by induction t <;> simp[toW, ofW, *]
  right_inv := fun t => by
    induction' t with a v ih
    rcases a with (x | x | _) <;> simp[toW, ofW, *]

instance : Inhabited (WType (Edge L μ)) := ⟨WType.mk (Sum.inl 0) Empty.elim⟩

@[simp] lemma equivW_bvar (x : ℕ) : equivW L μ (bvar x : UTerm L μ) = ⟨Sum.inl x, Empty.elim⟩ := rfl

@[simp] lemma equivW_fvar (x : μ) : equivW L μ (fvar x : UTerm L μ) = ⟨Sum.inr (Sum.inl x), Empty.elim⟩ := rfl

@[simp] lemma equivW_func {k} (f : L.func k) (v : Fin k → UTerm L μ) :
    equivW L μ (func f v) = ⟨Sum.inr (Sum.inr ⟨_, f⟩), fun i => equivW L μ (v i)⟩ := rfl

@[simp] lemma equivW_symm_inr_inr {k} (f : L.func k) (v : Fin k → WType (Edge L μ)) :
    (equivW L μ).symm ⟨Sum.inr (Sum.inr ⟨k, f⟩), v⟩ = func f (fun i => (equivW L μ).symm (v i)) := rfl

instance : (a : Node L μ) → Fintype (Edge L μ a)
  | (Sum.inl _)                => Fintype.ofIsEmpty
  | (Sum.inr $ Sum.inl _)      => Fintype.ofIsEmpty
  | (Sum.inr $ Sum.inr ⟨k, _⟩) => Fin.fintype k

instance : (a : Node L μ) → Primcodable (Edge L μ a)
  | (Sum.inl _)                => Primcodable.empty
  | (Sum.inr $ Sum.inl _)      => Primcodable.empty
  | (Sum.inr $ Sum.inr ⟨_, _⟩) => Primcodable.fin

instance : (a : Node L μ) → DecidableEq (Edge L μ a)
  | (Sum.inl _)                => instDecidableEqEmpty
  | (Sum.inr $ Sum.inl _)      => instDecidableEqEmpty
  | (Sum.inr $ Sum.inr ⟨k, _⟩) => instDecidableEq

instance : PrimrecCard (Edge L μ) where
  card_prim :=
    have : Primrec ((fun a => Sum.casesOn a (fun _ => 0) $ fun c => Sum.casesOn c (fun _ => 0) (fun x => x.1)) : Node L μ → ℕ) :=
      sum_casesOn Primrec.id (const 0) (by apply sum_casesOn snd (const 0) (sigma_fst.comp₂ right))
    this.of_eq (fun c => by rcases c with (_ | _ | _) <;> simp[Edge])

instance primcodable : Primcodable (UTerm L μ) := Primcodable.ofEquiv (WType (Edge L μ)) (equivW L μ)

lemma bvar_primrec : Primrec (bvar : ℕ → UTerm L μ) :=
  (Primrec.of_equiv_iff (equivW L μ)).mp (w_mk₀ Sum.inl (fun _ => instIsEmptyEmpty) sum_inl)

lemma fvar_primrec : Primrec (fvar : μ → UTerm L μ) :=
  (Primrec.of_equiv_iff (equivW L μ)).mp (w_mk₀ (Sum.inr $ Sum.inl ·) (fun _ => instIsEmptyEmpty) (sum_inr.comp sum_inl))

def funcL (f : (k : ℕ) × L.func k) (l : List (UTerm L μ)) : Option (UTerm L μ) :=
  if h : l.length = f.1
    then some (func f.2 (fun i => l.get (i.cast h.symm)))
    else none

lemma funcL_primrec :
  Primrec₂ (funcL : (k : ℕ) × L.func k → List (UTerm L μ) → Option (UTerm L μ)) :=
  have : Primrec₂ (fun (a : Node L μ) (l : List (UTerm L μ)) => (WType.mkL a (l.map (equivW L μ))).map (equivW L μ).symm) :=
    option_map
      (w_mkL.comp₂ Primrec₂.left ((list_map Primrec.id (Primrec.of_equiv.comp₂ Primrec₂.right)).comp₂ Primrec₂.right))
      (of_equiv_symm.comp₂ Primrec₂.right)
  have : Primrec₂ (fun f (l : List (UTerm L μ)) => (WType.mkL (Sum.inr $ Sum.inr f) (l.map (equivW L μ))).map (equivW L μ).symm) :=
    this.comp₂ (sum_inr.comp₂ $ sum_inr.comp₂ Primrec₂.left) Primrec₂.right
  this.of_eq (fun ⟨k, f⟩ l => by
      simp[WType.mkL, Edge]
      by_cases hl : l.length = k <;> simp[hl, funcL]
      { funext i; rw[Encodable.fintypeArrowEquivFinArrow_symm_app]; simp; congr })

lemma func_primrec (k) : Primrec₂ (func : L.func k → (Fin k → UTerm L μ) → UTerm L μ) :=
  (Primrec₂.of_equiv_iff (equivW L μ)).mp (by
    have h₁ := w_mkFin (β := Edge L μ)
      (fun f => (Sum.inr $ Sum.inr ⟨k, f⟩) : L.func k → Node L μ)
      (fun _ => Fintype.card_fin k)
      (sum_inr.comp $ sum_inr.comp $ sigma_pair k)
    have h₂ : Primrec (fun v => (fun i => equivW L μ (v i)) : (Fin k → UTerm L μ) → (Fin k → WType (Edge L μ))) :=
      finArrow_map Primrec.of_equiv k
    exact (Primrec₂.comp₂ h₁ Primrec₂.left (h₂.comp₂ Primrec₂.right)).of_eq
      (fun a v => by simp[equivW, toW, Edge]; funext i; rw[Encodable.fintypeArrowEquivFinArrow'_symm_app_fin_arrow]))

private def F (b : σ → ℕ → γ) (e : σ → μ → γ) (u : σ → ((k : ℕ) × L.func k) × List γ → γ) :
    σ → Node L μ × List γ → γ := fun z p =>
  Sum.casesOn p.1 (fun x => b z x) (fun q => Sum.casesOn q (fun x => e z x) (fun f => u z (f, p.2)))

private lemma elimv_eq (fs : σ → σ) (b : σ → ℕ → γ) (e : σ → μ → γ) (u : σ → ((k : ℕ) × L.func k) × List γ → γ) (x t) :
    elimv fs b e (fun x {k} f v => u x (⟨k, f⟩, List.ofFn v)) x t =
    WType.elimvL fs (fun x p l => F b e u x (p, l)) x (equivW L μ t) := by
  induction t generalizing x <;> simp[elimv, WType.elimvL_mk, F, *]
  { simp[Edge]; congr; funext i; rw[fintypeArrowEquivFinArrow_app]; congr; ext; simp[Fin.castIso_eq_cast] }

lemma elimv_primrec_param {τ σ γ} [Primcodable τ] [Primcodable σ] [Primcodable γ] 
  {fs : τ → σ → σ} {b : τ → σ × ℕ → γ} {e : τ → σ × μ → γ} {u : τ → σ × ((k : ℕ) × L.func k) × List γ → γ}
  {s : τ → σ} {g : τ → UTerm L μ}
  (hfs : Primrec₂ fs) (hb : Primrec₂ b) (he : Primrec₂ e)
  (hu : Primrec₂ u) (hs : Primrec s) (hg : Primrec g) :
    Primrec (fun x => elimv (fs x)
      (fun z y => b x (z, y)) (fun z y => e x (z, y)) (fun z {k} f v => u x (z, ⟨k, f⟩, List.ofFn v)) (s x) (g x)) := by
  have hF : Primrec₂ (fun x p =>
    F (fun z y => b x (z, y)) (fun z y => e x (z, y)) (fun z p => u x (z, p)) p.1 p.2
      : τ → σ × (Node L μ × List γ) → γ) := by
    apply to₂' <| (by
      exact sum_casesOn (fst.comp $ snd.comp snd)
        (hb.comp₂ (fst.comp₂ Primrec₂.left) (Primrec₂.pair.comp₂ (fst.comp₂ $ snd.comp₂ Primrec₂.left) Primrec₂.right))
        <| to₂' <| sum_casesOn snd (he.comp₂ (fst.comp₂ $ fst.comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂ (fst.comp₂ $ snd.comp₂ $ fst.comp₂ Primrec₂.left) Primrec₂.right))
        <| hu.comp₂ (fst.comp₂ $ fst.comp₂ Primrec₂.left) (Primrec₂.pair.comp₂ (fst.comp₂ $ snd.comp₂ $ fst.comp₂ Primrec₂.left)
          (Primrec₂.pair.comp₂ Primrec₂.right (snd.comp₂ $ snd.comp₂ $ snd.comp₂ $ fst.comp₂ Primrec₂.left))))
  have := w_elimvL_param (β := Edge L μ) hfs hF hs (of_equiv.comp hg)
  exact this.of_eq <| by
    intro x; simp[elimv_eq]
    have := elimv_eq (fs x) (fun z y => b x (z, y)) (fun z y => e x (z, y)) (fun z p => u x (z, p)) (s x) (g x)
    simp[this]

lemma elimv_primrec_param_opt {τ σ γ} [Primcodable τ] [Primcodable σ] [Primcodable γ] [Inhabited γ]
  {fs : τ → σ → σ} {b : τ → σ × ℕ → γ} {e : τ → σ × μ → γ} {s : τ → σ} {g : τ → UTerm L μ}
  (hfs : Primrec₂ fs) (hb : Primrec₂ b) (he : Primrec₂ e) 
  (u : τ → σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : τ → σ × ((k : ℕ) × L.func k) × List γ → Option γ} (hu : Primrec₂ uOpt)
  (hs : Primrec s) (hg : Primrec g)
  (H : ∀ (x : τ) (z : σ) {k} (f : L.func k) (v : Fin k → γ), uOpt x (z, ⟨k, f⟩, List.ofFn v) = some (u x z f v)) :
    Primrec (fun x => elimv (fs x) (fun z y => b x (z, y)) (fun z y => e x (z, y)) (u x) (s x) (g x)) := 
  (elimv_primrec_param hfs hb he (option_iget.comp₂ hu) hs hg).of_eq <| by intro x; simp[H]

lemma elimv_primrec {σ γ} [Primcodable σ] [Primcodable γ] 
  {fs : σ → σ} {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ}
  (hfs : Primrec fs) (hb : Primrec₂ b) (he : Primrec₂ e) (hu : Primrec₂ u) :
    Primrec₂ (elimv fs b e (fun x {k} f v => u x (⟨k, f⟩, List.ofFn v))) := by
  have hF : Primrec₂ (F b e u) :=
    sum_casesOn (fst.comp snd) (hb.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)
      (sum_casesOn snd (he.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) Primrec₂.right)
        (hu.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) (Primrec₂.pair.comp₂ snd (snd.comp₂ $ snd.comp₂ $ fst.comp₂ $ Primrec₂.left))))
  have : Primrec₂ (fun x t => WType.elimvL fs (fun x p l => F b e u x (p, l)) x (equivW L μ t)) :=
    (w_elimvL hfs hF).comp₂ Primrec₂.left (Primrec.of_equiv.comp snd)
  exact this.of_eq (fun x t => by simp[elimv_eq])

lemma elimv_primrec_opt {σ γ} [Primcodable σ] [Inhabited γ] [Primcodable γ] {fs : σ → σ} {b : σ → ℕ → γ} {e : σ → μ → γ}
  (hfs : Primrec fs) (hb : Primrec₂ b) (he : Primrec₂ e) 
  (u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : σ → ((k : ℕ) × L.func k) × List γ → Option γ} (hu : Primrec₂ uOpt)
  (H : ∀ (x : σ) {k} (f : L.func k) (v : Fin k → γ), uOpt x (⟨k, f⟩, List.ofFn v) = some (u x f v)) :
    Primrec₂ (elimv fs b e u) :=
  (elimv_primrec hfs hb he (option_iget.comp₂ hu)).of_eq (fun x t => by simp[H])

lemma elim_primrec {γ} [Primcodable γ] 
  {b : ℕ → γ} {e : μ → γ} {u : ((k : ℕ) × L.func k) → List γ → γ} (hb : Primrec b) (he : Primrec e) (hu : Primrec₂ u) :
    Primrec (elim b e (fun {k} f v => u ⟨k, f⟩ (List.ofFn v))) := by
  simp[elim_eq_elimv]
  exact (elimv_primrec (σ := Unit) Primrec.id
    (hb.comp₂ Primrec₂.right) (he.comp₂ Primrec₂.right)
      (hu.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))).comp (Primrec.const ()) (Primrec.id)

lemma elim_primrec_opt {γ} [Inhabited γ] [Primcodable γ] {b : ℕ → γ} {e : μ → γ}
  (hb : Primrec b) (he : Primrec e)
  (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : ((k : ℕ) × L.func k) → List γ → Option γ} (hu : Primrec₂ uOpt)
  (H : ∀ {k} (f : L.func k) (v : Fin k → γ), uOpt ⟨k, f⟩ (List.ofFn v) = some (u f v)) :
    Primrec (elim b e u) :=
  (elim_primrec hb he (option_iget.comp₂ hu)).of_eq (fun t => by simp[H])

lemma elim_primrec_param {σ γ} [Primcodable σ] [Primcodable γ] 
  {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ} {g : σ → UTerm L μ}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hu : Primrec₂ u) (hg : Primrec g) :
    Primrec (fun x => elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v)) (g x)) := by
  have : Primrec₂ (fun x => elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v))) := by
    simpa[elim_eq_elimv'] using elimv_primrec (σ := σ) Primrec.id hb he hu
  exact this.comp Primrec.id hg

lemma elim_primrec_param_opt {σ γ} [Primcodable σ] [Inhabited γ] [Primcodable γ] {b : σ → ℕ → γ} {e : σ → μ → γ} {g : σ→ UTerm L μ}
  (hb : Primrec₂ b) (he : Primrec₂ e) 
  (u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : σ → ((k : ℕ) × L.func k) × List γ → Option γ} (hu : Primrec₂ uOpt)
  (hg : Primrec g)
  (H : ∀ (x : σ) {k} (f : L.func k) (v : Fin k → γ), uOpt x (⟨k, f⟩, List.ofFn v) = some (u x f v)) :
    Primrec (fun x => elim (b x) (e x) (u x) (g x)) :=
  (elim_primrec_param hb he (option_iget.comp₂ hu) hg).of_eq <| by intro x; simp[H]

lemma bv_primrec : Primrec (bv : UTerm L μ → ℕ) := by
  have : Primrec (elim (L := L) (μ := μ) Nat.succ (fun _ => 0) fun {k} _ v => (List.ofFn v).sup) :=
    elim_primrec Primrec.succ (Primrec.const 0) ((list_sup nat_max).comp₂ Primrec₂.right)
  exact this.of_eq (fun t => by
    induction t <;> simp[elim, bv, *]
    { simp[List.sup_ofFn] })

variable {μ₁ : Type*} {μ₂ : Type*} [Primcodable μ₁] [Primcodable μ₂]

lemma bind_param_primrec [Primcodable σ] {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂} {g : σ → UTerm L μ₁}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hg : Primrec g) : Primrec (fun x => bind (b x) (e x) (g x)) := by
  have : Primrec₂ (fun _ p => funcL p.1 p.2 : σ → ((k : ℕ) × L.func k) × List (UTerm L μ₂) → Option (UTerm L μ₂)) :=
    funcL_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)
  have := elim_primrec_param_opt hb he (fun _ _ f v => func f v) this hg
    (by intro x k f v; simp[funcL]; congr)
  exact this.of_eq <| by intro x; generalize g x = t; induction t <;> simp[elim, bind, *]

lemma bind_primrec {b : ℕ → UTerm L μ₂} {e : μ₁ → UTerm L μ₂} (hb : Primrec b) (he : Primrec e) :
    Primrec (bind b e) := bind_param_primrec (hb.comp₂ Primrec₂.right) (he.comp₂ Primrec₂.right) Primrec.id

-- lemma substAt_primrec : Primrec₂ (fun p t => substAt p.1 p.2 t : ℕ × UTerm L μ → UTerm L μ → UTerm L μ) :=
--   to₂' <| bind_param_primrec (by {  }) (by {  }) (by {  })

lemma bShifts_primrec : Primrec₂ (bShifts : ℕ → UTerm L μ → UTerm L μ) :=
  to₂' <| bind_param_primrec (bvar_primrec.comp₂ $ nat_add.comp₂ Primrec₂.right (fst.comp₂ Primrec₂.left))
    (fvar_primrec.comp₂ Primrec₂.right) snd

end W

end UTerm

namespace SubTerm

open UTerm Encodable Primrec Primrec₂
variable [Primcodable μ] [(k : ℕ) → Primcodable (L.func k)] [UniformlyPrimcodable L.func]

instance : Primcodable (SubTerm L μ n) :=
  letI : Primcodable { t : UTerm L μ // t.bv ≤ n } := Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  Primcodable.ofEquiv { t : UTerm L μ // t.bv ≤ n } subtEquiv

def bv : SubTerm L μ n → ℕ
  | #x   => x + 1
  | &_   => 0
  | func _ v => Finset.sup Finset.univ (fun i => (v i).bv)

@[simp] lemma bv_le (t : SubTerm L μ n) : t.bv ≤ n := by induction t <;> simp[bv, Nat.add_one_le_iff, *]

def bPrincipal (t : SubTerm L μ (n + 1)) : Prop := t.bv = n + 1

instance : Decidable (bPrincipal t) := instDecidableEq _ _

lemma bPrincipal_iff_not_lt {t : SubTerm L μ (n + 1)} : bPrincipal t ↔ n < t.bv := by
  simp[bPrincipal]
  exact ⟨by intro e; simp[e], by intro h; exact Nat.le_antisymm (bv_le t) h⟩

@[simp] lemma bPrincipal_bvar {x} : bPrincipal (#x : SubTerm L μ (n + 1)) ↔ x = Fin.last n :=
  by simp[bPrincipal, bv]; exact eq_iff_eq_of_cmp_eq_cmp rfl

@[simp] lemma bPrincipal_fvar {x} : ¬bPrincipal (&x : SubTerm L μ (n + 1)) :=
  by simp[bPrincipal, bv]; exact Nat.ne_of_beq_eq_false rfl

@[simp] lemma bPrincipal_func {k} {f : L.func k} {v : Fin k → SubTerm L μ (n + 1)} :
    bPrincipal (func f v) ↔ ∃ i, bPrincipal (v i) := by
  simp[bPrincipal_iff_not_lt, bv]

def substsLast (u : SubTerm L μ n) (t : SubTerm L μ (n + 1)) := Rew.substs ((fun x => #x) <: u) t

lemma substsLast_eq (u : SubTerm L μ n) (t : SubTerm L μ (n + 1)) :
    (subtEquiv (substsLast u t)).val = UTerm.substAt n (subtEquiv u).val (subtEquiv t).val := by
  simp[UTerm.substLast]
  induction t <;> simp[substsLast]
  case bvar x => cases' x using Fin.lastCases with x <;> simp
  case func k f v ih => simp[Rew.func]; funext i; exact ih i

end SubTerm

namespace UFormula

instance : Inhabited (UFormula L μ) := ⟨verum⟩

def elim {γ : Type*}
  (γVerum : γ)
  (γFalsum : γ)
  (γRel : {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ)
  (γNrel : {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ)
  (γAnd : γ → γ → γ)
  (γOr : γ → γ → γ)
  (γAll : γ → γ)
  (γEx : γ → γ) : UFormula L μ → γ
  | verum    => γVerum
  | falsum   => γFalsum
  | rel r v  => γRel r v
  | nrel r v => γNrel r v
  | and p q  => γAnd (p.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx) (q.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx)
  | or p q   => γOr (p.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx) (q.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx)
  | all p    => γAll (p.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx)
  | ex p     => γEx (p.elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx)

def elimv {σ γ : Type*}
  (fs : σ → σ)
  (γVerum : σ → γ)
  (γFalsum : σ → γ)
  (γRel : σ → {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ)
  (γNrel : σ → {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ)
  (γAnd : σ → γ → γ → γ)
  (γOr : σ → γ → γ → γ)
  (γAll : σ → γ → γ)
  (γEx : σ → γ → γ) : σ → UFormula L μ → γ
  | x, verum    => γVerum x
  | x, falsum   => γFalsum x
  | x, rel r v  => γRel x r v
  | x, nrel r v => γNrel x r v
  | x, and p q  => γAnd x
    (p.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))
    (q.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))
  | x, or p q   => γOr x
    (p.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))
    (q.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))
  | x, all p    => γAll x (p.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))
  | x, ex p     => γEx x (p.elimv fs γVerum γFalsum γRel γNrel γAnd γOr γAll γEx (fs x))

lemma elim_eq_elimv
  {γVerum : γ}
  {γFalsum : γ}
  {γRel : {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ}
  {γNrel : {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ}
  {γAnd : γ → γ → γ}
  {γOr : γ → γ → γ}
  {γAll : γ → γ}
  {γEx : γ → γ} :
    elim γVerum γFalsum γRel γNrel γAnd γOr γAll γEx =
    elimv id (fun _ => γVerum) (fun _ => γFalsum)
      (fun _ => γRel) (fun _ => γNrel)
      (fun _ => γAnd) (fun _ => γOr) (fun _ => γAll) (fun _ => γEx) () := by
  funext t; induction t <;> simp[elim, elimv, *]
  
lemma elim_eq_elimv'
  {γVerum : σ → γ}
  {γFalsum : σ → γ}
  {γRel : σ → {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ}
  {γNrel : σ → {k : ℕ} → L.rel k → (Fin k → UTerm L μ) → γ}
  {γAnd : σ → γ → γ → γ}
  {γOr : σ → γ → γ → γ}
  {γAll : σ → γ → γ}
  {γEx : σ → γ → γ} :
    (fun x => elim (γValsum x) (γFerum x) (γRel x) (γNrel x) (γAnd x) (γOr x) (γAll x) (γEx x)) =
    elimv id γValsum γFerum γRel γNrel γAnd γOr γAll γEx := by
  funext x t; induction t <;> simp[elim, elimv, *]

def neg : UFormula L μ → UFormula L μ
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and p q  => or p.neg q.neg
  | or p q   => and p.neg q.neg
  | all p    => ex p.neg
  | ex p     => all p.neg

def bv : UFormula L μ → ℕ
  | verum    => 0
  | falsum   => 0
  | rel _ v  => Finset.sup Finset.univ (fun i => (v i).bv)
  | nrel _ v => Finset.sup Finset.univ (fun i => (v i).bv)
  | and p q  => max p.bv q.bv
  | or p q   => max p.bv q.bv
  | all p    => p.bv.pred
  | ex p     => p.bv.pred

def shiftb (b : ℕ → UTerm L μ) (n : ℕ) : ℕ → UTerm L μ := fun x =>
  if x < n then UTerm.bvar x
  else UTerm.bShifts n (b (x - n))

def bindq (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : ℕ → UFormula L μ₁ → UFormula L μ₂
  | _, verum    => verum
  | _, falsum   => falsum
  | n, rel r v  => rel r (fun i => (v i).bind (shiftb b n) e)
  | n, nrel r v => nrel r (fun i => (v i).bind (shiftb b n) e)
  | n, and p q  => and (p.bindq b e n) (q.bindq b e n)
  | n, or p q   => or (p.bindq b e n) (q.bindq b e n)
  | n, all p    => all (p.bindq b e (n + 1))
  | n, ex p     => ex (p.bindq b e (n + 1))

def bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : UFormula L μ₁ → UFormula L μ₂ := bindq b e 0
/-
lemma bindq_eq_elimv (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) :
  bindq b e n =
  elimv Nat.succ
  (fun _ => verum) (fun _ => falsum)
  (fun n {k} f v => rel r (fun i => (v i).bind (shiftb b n) e))
  (fun n {k} f v => nrel r (fun i => (v i).bind (shiftb b n) e))
  (fun _ p q => and p q)
  (fun _ p q => or p q)
  (fun _ p q => or p q)

-/
def rewrite (e : μ₁ → UTerm L μ₂) : UFormula L μ₁ → UFormula L μ₂
  | verum    => verum
  | falsum   => falsum
  | rel r v  => rel r (fun i => (v i).rewrite e)
  | nrel r v => nrel r (fun i => (v i).rewrite e)
  | and p q  => and (p.rewrite e) (q.rewrite e)
  | or p q   => or (p.rewrite e) (q.rewrite e)
  | all p    => all (p.rewrite e)
  | ex p     => ex (p.rewrite e)

@[simp] lemma bv_verum : bv (verum : UFormula L μ) = 0 := rfl

@[simp] lemma bv_falsum : bv (falsum : UFormula L μ) = 0 := rfl

@[simp] lemma bv_rel {k} (r : L.rel k) (v : Fin k → UTerm L μ) : bv (rel r v) = Finset.sup Finset.univ (fun i => (v i).bv) := rfl

@[simp] lemma bv_nrel {k} (r : L.rel k) (v : Fin k → UTerm L μ) : bv (nrel r v) = Finset.sup Finset.univ (fun i => (v i).bv) := rfl

@[simp] lemma bv_and (p q : UFormula L μ) : (and p q).bv = max p.bv q.bv := rfl

@[simp] lemma bv_or (p q : UFormula L μ) : (or p q).bv = max p.bv q.bv := rfl

@[simp] lemma bv_all (p : UFormula L μ) : (all p).bv = p.bv.pred := rfl

@[simp] lemma bv_ex (p : UFormula L μ) : (ex p).bv = p.bv.pred := rfl

@[simp] lemma subtype_val_le (p : { p : UFormula L μ // p.bv ≤ n }) : p.val.bv ≤ n := p.property

def toSubFormula : {n : ℕ} → (p : UFormula L μ) → p.bv ≤ n → SubFormula L μ n
  | _, verum,    _ => ⊤
  | _, falsum,   _ => ⊥
  | _, rel r v,  h => SubFormula.rel r (fun i => (v i).toSubTerm (by simp at h; exact h i))
  | _, nrel r v, h => SubFormula.nrel r (fun i => (v i).toSubTerm (by simp at h; exact h i))
  | _, and p q,  h => p.toSubFormula (by simp at h; exact h.1) ⋏ q.toSubFormula (by simp at h; exact h.2)
  | _, or p q,   h => p.toSubFormula (by simp at h; exact h.1) ⋎ q.toSubFormula (by simp at h; exact h.2)
  | _, all p,    h => ∀' p.toSubFormula (Nat.le_add_of_sub_le h)
  | _, ex p,     h => ∃' p.toSubFormula (Nat.le_add_of_sub_le h)

def ofSubFormula : {n : ℕ} → SubFormula L μ n → { p : UFormula L μ // p.bv ≤ n }
  | _, ⊤                   => ⟨verum, by simp⟩
  | _, ⊥                   => ⟨falsum, by simp⟩
  | _, SubFormula.rel r v  => ⟨rel r (fun i => (UTerm.ofSubTerm $ v i)), by simp⟩
  | _, SubFormula.nrel r v => ⟨nrel r (fun i => (UTerm.ofSubTerm $ v i)), by simp⟩
  | _, p ⋏ q               => ⟨and (ofSubFormula p) (ofSubFormula q), by simp⟩
  | _, p ⋎ q               => ⟨or (ofSubFormula p) (ofSubFormula q), by simp⟩
  | _, ∀' p                => ⟨all (ofSubFormula p), by simpa using Iff.mpr Nat.pred_le_iff (ofSubFormula p).property⟩
  | _, ∃' p                => ⟨ex (ofSubFormula p), by simpa using Iff.mpr Nat.pred_le_iff (ofSubFormula p).property⟩

lemma toSubFormula_ofSubFormula : ∀ {n : ℕ} (p : SubFormula L μ n), toSubFormula (ofSubFormula p).1 (ofSubFormula p).2 = p
  | _, ⊤                   => rfl
  | _, ⊥                   => rfl
  | _, SubFormula.rel r v  => by simp[ofSubFormula, toSubFormula, UTerm.toSubTerm_ofSubterm]
  | _, SubFormula.nrel r v => by simp[ofSubFormula, toSubFormula, UTerm.toSubTerm_ofSubterm]
  | _, p ⋏ q               => by simp[ofSubFormula, toSubFormula]; exact ⟨toSubFormula_ofSubFormula p, toSubFormula_ofSubFormula q⟩
  | _, p ⋎ q               => by simp[ofSubFormula, toSubFormula]; exact ⟨toSubFormula_ofSubFormula p, toSubFormula_ofSubFormula q⟩
  | _, ∀' p                => by simp[ofSubFormula, toSubFormula]; exact toSubFormula_ofSubFormula p
  | _, ∃' p                => by simp[ofSubFormula, toSubFormula]; exact toSubFormula_ofSubFormula p

lemma ofSubFormula_toSubFormula : ∀ {n : ℕ} (p : UFormula L μ) (h : p.bv ≤ n), ofSubFormula (toSubFormula p h) = p
  | _, verum,    h => rfl
  | _, falsum,   h => rfl
  | _, rel r v,  h => by simp[ofSubFormula, toSubFormula, UTerm.ofSubTerm_toSubterm]
  | _, nrel r v, h => by simp[ofSubFormula, toSubFormula, UTerm.ofSubTerm_toSubterm]
  | _, and p q,  h => by
    simp[ofSubFormula, toSubFormula]
    exact ⟨ofSubFormula_toSubFormula p (by simp at h; exact h.1), ofSubFormula_toSubFormula q (by simp at h; exact h.2)⟩
  | _, or p q,   h => by
    simp[ofSubFormula, toSubFormula]
    exact ⟨ofSubFormula_toSubFormula p (by simp at h; exact h.1), ofSubFormula_toSubFormula q (by simp at h; exact h.2)⟩
  | _, all p,    h => by
    simp[ofSubFormula, toSubFormula]
    exact ofSubFormula_toSubFormula p (by {simp at h; exact Nat.le_add_of_sub_le h })
  | _, ex p,     h => by
    simp[ofSubFormula, toSubFormula]
    exact ofSubFormula_toSubFormula p (by {simp at h; exact Nat.le_add_of_sub_le h })

def subformulaEquivSubtype : SubFormula L μ n ≃ { p : UFormula L μ // p.bv ≤ n } where
  toFun := ofSubFormula
  invFun := fun p => p.1.toSubFormula p.2
  left_inv := toSubFormula_ofSubFormula
  right_inv := fun ⟨p, h⟩ => by ext; simpa using ofSubFormula_toSubFormula p h

open Encodable Primrec Primrec₂
variable [(k : ℕ) → Primcodable (L.func k)] [(k : ℕ) → Primcodable (L.rel k)]
  [UniformlyPrimcodable L.func] [UniformlyPrimcodable L.rel] [Primcodable μ]

section W

abbrev Node (L : Language.{u}) (μ : Type v) :=
  Bool × (((k : ℕ) × L.rel k × (Fin k → UTerm L μ)) ⊕ Unit ⊕ Unit ⊕ Unit)
-- sign × (atomic formula ⊕ ⊤/⊥ ⊕ ⋏/⋎ ⊕ ∀/∃)

instance : Primcodable (Node L μ) := Primcodable.prod

@[reducible] def Edge (L : Language.{u}) (μ : Type v) : Node L μ → Type
  | (_, Sum.inl ⟨_, _, _⟩)              => Empty
  | (_, Sum.inr $ Sum.inl ())           => Empty
  | (_, Sum.inr $ Sum.inr $ Sum.inl ()) => Bool
  | (_, Sum.inr $ Sum.inr $ Sum.inr ()) => Unit

def toW : UFormula L μ → WType (Edge L μ)
  | rel r v  => ⟨(true,  Sum.inl ⟨_, r, v⟩), Empty.elim⟩
  | nrel r v => ⟨(false, Sum.inl ⟨_, r, v⟩), Empty.elim⟩
  | verum    => ⟨(true,  Sum.inr $ Sum.inl ()), Empty.elim⟩
  | falsum   => ⟨(false, Sum.inr $ Sum.inl ()), Empty.elim⟩
  | and p q  => ⟨(true,  Sum.inr $ Sum.inr $ Sum.inl ()), Bool.rec p.toW q.toW⟩
  | or p q   => ⟨(false, Sum.inr $ Sum.inr $ Sum.inl ()), Bool.rec p.toW q.toW⟩
  | all p    => ⟨(true,  Sum.inr $ Sum.inr $ Sum.inr ()), fun _ => p.toW⟩
  | ex p     => ⟨(false, Sum.inr $ Sum.inr $ Sum.inr ()), fun _ => p.toW⟩

def ofW : WType (Edge L μ) → UFormula L μ
  | ⟨(true,  Sum.inl ⟨_, r, v⟩), _⟩              => rel r v
  | ⟨(false, Sum.inl ⟨_, r, v⟩), _⟩              => nrel r v
  | ⟨(true,  Sum.inr $ Sum.inl ()), _⟩           => verum
  | ⟨(false, Sum.inr $ Sum.inl ()), _⟩           => falsum
  | ⟨(true,  Sum.inr $ Sum.inr $ Sum.inl ()), p⟩ => and (ofW $ p false) (ofW $ p true)
  | ⟨(false, Sum.inr $ Sum.inr $ Sum.inl ()), p⟩ => or (ofW $ p false) (ofW $ p true)
  | ⟨(true,  Sum.inr $ Sum.inr $ Sum.inr ()), p⟩ => all (ofW $ p ())
  | ⟨(false, Sum.inr $ Sum.inr $ Sum.inr ()), p⟩ => ex (ofW $ p ())

lemma toW_ofW : ∀ (w : WType (Edge L μ)), toW (ofW w) = w
  | ⟨(true,  Sum.inl ⟨_, r, v⟩), _⟩              => by simp[ofW, toW]
  | ⟨(false, Sum.inl ⟨_, r, v⟩), _⟩              => by simp[ofW, toW]
  | ⟨(true,  Sum.inr $ Sum.inl ()), _⟩           => by simp[ofW, toW]
  | ⟨(false, Sum.inr $ Sum.inl ()), _⟩           => by simp[ofW, toW]
  | ⟨(true,  Sum.inr $ Sum.inr $ Sum.inl ()), w⟩ => by
    simp[ofW, toW, toW_ofW (w false), toW_ofW (w true)]
    ext b; cases b <;> simp
  | ⟨(false, Sum.inr $ Sum.inr $ Sum.inl ()), w⟩ => by
    simp[ofW, toW, toW_ofW (w false), toW_ofW (w true)]
    ext b; cases b <;> simp
  | ⟨(true,  Sum.inr $ Sum.inr $ Sum.inr ()), w⟩ => by simp[ofW, toW, toW_ofW (w ())]
  | ⟨(false, Sum.inr $ Sum.inr $ Sum.inr ()), w⟩ => by simp[ofW, toW, toW_ofW (w ())]

def equivW (L) (μ) : UFormula L μ ≃ WType (Edge L μ) where
  toFun := toW
  invFun := ofW
  left_inv := fun p => by induction p <;> simp[toW, ofW, *]
  right_inv := toW_ofW

@[simp] lemma equivW_verum : (equivW L μ) verum = ⟨(true, Sum.inr $ Sum.inl ()), Empty.elim⟩ := rfl

@[simp] lemma equivW_falsum : (equivW L μ) falsum = ⟨(false, Sum.inr $ Sum.inl ()), Empty.elim⟩ := rfl

@[simp] lemma equivW_rel {k} (r : L.rel k) (v) : (equivW L μ) (rel r v) = ⟨(true, Sum.inl ⟨_, r, v⟩), Empty.elim⟩ := rfl

@[simp] lemma equivW_nrel {k} (r : L.rel k) (v) : (equivW L μ) (nrel r v) = ⟨(false, Sum.inl ⟨_, r, v⟩), Empty.elim⟩ := rfl

@[simp] lemma equivW_and (p q : UFormula L μ) :
    (equivW L μ) (and p q) = ⟨(true, Sum.inr $ Sum.inr $ Sum.inl ()), Bool.rec ((equivW L μ) p) ((equivW L μ) q)⟩ := rfl

@[simp] lemma equivW_or (p q : UFormula L μ) :
    (equivW L μ) (or p q) = ⟨(false, Sum.inr $ Sum.inr $ Sum.inl ()), Bool.rec ((equivW L μ) p) ((equivW L μ) q)⟩ := rfl

@[simp] lemma equivW_all (p : UFormula L μ) :
    (equivW L μ) (all p) = ⟨(true, Sum.inr $ Sum.inr $ Sum.inr ()), fun _ => (equivW L μ) p⟩ := rfl

@[simp] lemma equivW_ex (p : UFormula L μ) :
    (equivW L μ) (ex p) = ⟨(false, Sum.inr $ Sum.inr $ Sum.inr ()), fun _ => (equivW L μ) p⟩ := rfl

@[simp] lemma equivW_symm_true_inl : (equivW L μ).symm ⟨(true, Sum.inl ⟨k, r, v⟩), Empty.elim⟩ = rel r v := rfl

@[simp] lemma equivW_symm_false_inl : (equivW L μ).symm ⟨(false, Sum.inl ⟨k, r, v⟩), Empty.elim⟩ = nrel r v := rfl

@[simp] lemma equivW_symm_true_inr_inr_inl (v : Bool → WType (Edge L μ)) :
    (equivW L μ).symm ⟨(true, Sum.inr $ Sum.inr $ Sum.inl ()), v⟩ = and ((equivW L μ).symm $ v false) ((equivW L μ).symm $ v true) := rfl

@[simp] lemma equivW_symm_false_inr_inr_inl (v : Bool → WType (Edge L μ)) :
    (equivW L μ).symm ⟨(false, Sum.inr $ Sum.inr $ Sum.inl ()), v⟩ = or ((equivW L μ).symm $ v false) ((equivW L μ).symm $ v true) := rfl

@[simp] lemma equivW_symm_true_inr_inr_inr (v : Unit → WType (Edge L μ)) :
    (equivW L μ).symm ⟨(true, Sum.inr $ Sum.inr $ Sum.inr ()), v⟩ = all ((equivW L μ).symm $ v ()) := rfl

@[simp] lemma equivW_symm_false_inr_inr_inr (v : Unit → WType (Edge L μ)) :
    (equivW L μ).symm ⟨(false, Sum.inr $ Sum.inr $ Sum.inr ()), v⟩ = ex ((equivW L μ).symm $ v ()) := rfl

instance : (a : Node L μ) → Fintype (Edge L μ a)
  | (_, Sum.inl ⟨_, _, _⟩)              => Fintype.ofIsEmpty
  | (_, Sum.inr $ Sum.inl ())           => Fintype.ofIsEmpty
  | (_, Sum.inr $ Sum.inr $ Sum.inl ()) => Bool.fintype
  | (_, Sum.inr $ Sum.inr $ Sum.inr ()) => Unique.fintype

instance : (a : Node L μ) → Primcodable (Edge L μ a)
  | (_, Sum.inl ⟨_, _, _⟩)              => Primcodable.empty
  | (_, Sum.inr $ Sum.inl ())           => Primcodable.empty
  | (_, Sum.inr $ Sum.inr $ Sum.inl ()) => Primcodable.bool
  | (_, Sum.inr $ Sum.inr $ Sum.inr ()) => Primcodable.unit

instance : (a : Node L μ) → DecidableEq (Edge L μ a)
  | (_, Sum.inl ⟨_, _, _⟩)              => instDecidableEqEmpty
  | (_, Sum.inr $ Sum.inl ())           => instDecidableEqEmpty
  | (_, Sum.inr $ Sum.inr $ Sum.inl ()) => instDecidableEq
  | (_, Sum.inr $ Sum.inr $ Sum.inr ()) => instDecidableEq

instance : PrimrecCard (Edge L μ) where
  card_prim :=
    have : Primrec
      ( fun a => Sum.casesOn a.2 (fun _ => 0)
        $ fun c => Sum.casesOn c (fun _ => 0)
        $ fun c => Sum.casesOn c (fun _ => 2)
        $ fun _ => 1 : Node L μ → ℕ) :=
      by apply sum_casesOn snd (const 0)
          (by apply sum_casesOn snd (const 0)
                (by apply sum_casesOn snd (const 2) (const 1)))
    this.of_eq (fun (_, c) => by
      rcases c with (_ | c) <;> simp[Edge]
      rcases c with (_ | c) <;> simp[Edge]
      rcases c <;> simp[Edge])

instance primcodable : Primcodable (UFormula L μ) := Primcodable.ofEquiv (WType (Edge L μ)) (equivW L μ)

lemma rel_primrec :
    Primrec (fun p => rel p.2.1 p.2.2 : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → UFormula L μ) := by
  let i : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → Node L μ := fun t => (true, Sum.inl t)
  have : Primrec i := Primrec.pair (Primrec.const true) (sum_inl.comp Primrec.id)
  have : Primrec (fun t => WType.mk (i t) Empty.elim) :=
    w_mk₀ (β := Edge L μ) i (by intros; exact instIsEmptyEmpty) this
  have := (of_equiv_symm (e := equivW L μ)).comp this
  simpa using this

lemma nrel_primrec :
    Primrec (fun p => nrel p.2.1 p.2.2 : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → UFormula L μ) := by
  let i : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → Node L μ := fun t => (false, Sum.inl t)
  have : Primrec i := Primrec.pair (Primrec.const false) (sum_inl.comp Primrec.id)
  have : Primrec (fun t => WType.mk (i t) Empty.elim) :=
    w_mk₀ (β := Edge L μ) i (by intros; exact instIsEmptyEmpty) this
  have := (of_equiv_symm (e := equivW L μ)).comp this
  simpa using this

lemma and_primrec : Primrec₂ (and : UFormula L μ → UFormula L μ → UFormula L μ) := by
  have := w_mk₂ (β := Edge L μ) (fun (_ : Unit) => (true, Sum.inr $ Sum.inr $ Sum.inl ())) (by rintro ⟨⟩; simp[Edge]) (const _)
  have := (Primrec.of_equiv_symm (e := equivW L μ)).comp₂
    ((this.comp₂ (Primrec₂.const ()) Primrec.id.to₂).comp₂
      ((Primrec.of_equiv (e := equivW L μ)).comp₂ Primrec₂.left)
      ((Primrec.of_equiv (e := equivW L μ)).comp₂ Primrec₂.right))
  exact this.of_eq (fun p q => by simp; rw[fintypeEquivFin_false, fintypeEquivFin_true]; simp)

lemma or_primrec : Primrec₂ (or : UFormula L μ → UFormula L μ → UFormula L μ) := by
  have := w_mk₂ (β := Edge L μ) (fun (_ : Unit) => (false, Sum.inr $ Sum.inr $ Sum.inl ())) (by rintro ⟨⟩; simp[Edge]) (const _)
  have := (Primrec.of_equiv_symm (e := equivW L μ)).comp₂
    ((this.comp₂ (Primrec₂.const ()) Primrec.id.to₂).comp₂
      ((Primrec.of_equiv (e := equivW L μ)).comp₂ Primrec₂.left)
      ((Primrec.of_equiv (e := equivW L μ)).comp₂ Primrec₂.right))
  exact this.of_eq (fun p q => by simp; rw[fintypeEquivFin_false, fintypeEquivFin_true]; simp)

lemma all_primrec : Primrec (all : UFormula L μ → UFormula L μ) := by
  have := w_mk₁ (β := Edge L μ) (fun (_ : Unit) => (true, Sum.inr $ Sum.inr $ Sum.inr ())) (by rintro ⟨⟩; simp[Edge]) (const _)
  have := (Primrec.of_equiv_symm (e := equivW L μ)).comp
    ((this.comp (Primrec.const ()) Primrec.id).comp (Primrec.of_equiv (e := equivW L μ)))
  exact this.of_eq (fun p => by simp)

lemma ex_primrec : Primrec (ex : UFormula L μ → UFormula L μ) := by
  have := w_mk₁ (β := Edge L μ) (fun (_ : Unit) => (false, Sum.inr $ Sum.inr $ Sum.inr ())) (by rintro ⟨⟩; simp[Edge]) (const _)
  have := (Primrec.of_equiv_symm (e := equivW L μ)).comp
    ((this.comp (Primrec.const ()) Primrec.id).comp (Primrec.of_equiv (e := equivW L μ)))
  exact this.of_eq (fun p => by simp)

private def F [Inhabited γ]
  (γVerum : σ → γ)
  (γFalsum : σ → γ)
  (γRel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)
  (γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)
  (γAnd : σ → γ × γ → γ)
  (γOr : σ → γ × γ → γ)
  (γAll : σ → γ → γ)
  (γEx : σ → γ → γ) : σ → Node L μ × List γ → γ := fun z p =>
    (Sum.casesOn p.1.2 (fun f => bif p.1.1 then γRel z f else γNrel z f)
    $ fun c => Sum.casesOn c (fun _ => bif p.1.1 then γVerum z else γFalsum z)
    $ fun c => Sum.casesOn c (fun _ => bif p.1.1 then γAnd z (p.2.getI 0, p.2.getI 1) else γOr z (p.2.getI 0, p.2.getI 1))
    $ fun _ => bif p.1.1 then γAll z (p.2.getI 0) else γEx z (p.2.getI 0))

private lemma elimv_eq
  [Inhabited γ]
  (fs : σ → σ)
  (γVerum : σ → γ)
  (γFalsum : σ → γ)
  (γRel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)
  (γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)  
  (γAnd : σ → γ × γ → γ)
  (γOr : σ → γ × γ → γ)
  (γAll : σ → γ → γ)
  (γEx : σ → γ → γ) (x : σ) (p : UFormula L μ) :
    elimv fs γVerum γFalsum
      (fun x {k} f v => γRel x ⟨k, f, v⟩)
      (fun x {k} f v => γNrel x ⟨k, f, v⟩)
      (fun x y₁ y₂ => γAnd x (y₁, y₂))
      (fun x y₁ y₂ => γOr x (y₁, y₂))
      γAll
      γEx x p =
    WType.elimvL fs (fun x p l => F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx x (p, l)) x (equivW L μ p) := by
  induction p generalizing x <;> simp[elimv, WType.elimvL_mk, F, *] <;> congr

lemma elimv_primrec {σ γ} [Primcodable σ] [Primcodable γ] [Inhabited γ]
  {fs : σ → σ}
  {γVerum γFalsum : σ → γ}
  {γRel γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ}
  {γAnd γOr : σ → γ × γ → γ}
  {γAll γEx : σ → γ → γ}
  (hfs : Primrec fs)
  (hVerum : Primrec γVerum)
  (hFalsum : Primrec γFalsum)
  (hRel : Primrec₂ γRel)
  (hNrel : Primrec₂ γNrel)
  (hAnd : Primrec₂ γAnd)
  (hOr : Primrec₂ γOr)
  (hAll : Primrec₂ γAll)
  (hEx : Primrec₂ γEx) :
    Primrec₂
    (elimv fs γVerum γFalsum
      (fun x {k} f v => γRel x ⟨k, f, v⟩)
      (fun x {k} f v => γNrel x ⟨k, f, v⟩)
      (fun x y₁ y₂ => γAnd x (y₁, y₂))
      (fun x y₁ y₂ => γOr x (y₁, y₂))
      γAll γEx) := by
  have hF : Primrec₂ (F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx) :=
    sum_casesOn (snd.comp $ fst.comp snd)
      (Primrec.cond (fst.comp $ fst.comp $ snd.comp fst) (hRel.comp (fst.comp fst) snd) (hNrel.comp (fst.comp fst) snd))
      (sum_casesOn snd
        (by apply Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp fst)
              (hVerum.comp $ fst.comp $ fst.comp fst)
              (hFalsum.comp $ fst.comp $ fst.comp fst))
        (by apply sum_casesOn snd
              (by apply Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp $ fst.comp fst)
                    (hAnd.comp (fst.comp $ fst.comp $ fst.comp fst)
                      (Primrec.pair (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))
                        (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 1))))
                    (hOr.comp (fst.comp $ fst.comp $ fst.comp fst)
                      (Primrec.pair (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))
                        (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 1)))))
              (by apply Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp $ fst.comp fst)
                    (hAll.comp (fst.comp $ fst.comp $ fst.comp fst)
                      (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0)))
                    (hEx.comp (fst.comp $ fst.comp $ fst.comp fst)
                      (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))))))
  have : Primrec₂ (fun x w => WType.elimvL (β := Edge L μ) fs
      (fun x a v => F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx x (a, v)) x (equivW L μ w)) := by
    { have := w_elimvL (β := Edge L μ) hfs hF
      exact this.comp₂ Primrec₂.left (Primrec.of_equiv.comp₂ Primrec₂.right) }
  exact this.of_eq (fun x t => by simp[elimv_eq])
 
lemma elim_primrec {γ} [Primcodable γ] [Inhabited γ]
  (γVerum γFalsum : γ)
  {γRel γNrel : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ}
  {γAnd γOr : γ → γ → γ}
  {γAll γEx : γ → γ}
  (hRel : Primrec γRel)
  (hNrel : Primrec γNrel)
  (hAnd : Primrec₂ γAnd)
  (hOr : Primrec₂ γOr)
  (hAll : Primrec γAll)
  (hEx : Primrec γEx) :
    Primrec (elim γVerum γFalsum (fun {k} f v => γRel ⟨k, f, v⟩) (fun {k} f v => γNrel ⟨k, f, v⟩) γAnd γOr γAll γEx) := by
  have := (elimv_primrec (σ := Unit) Primrec.id
    (Primrec.const γVerum) (Primrec.const γFalsum)
    (hRel.comp₂ Primrec₂.right) (hNrel.comp₂ Primrec₂.right)
    (hAnd.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
    (hOr.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
    (hAll.comp₂ Primrec₂.right) (hEx.comp₂ Primrec₂.right)).comp (Primrec.const ()) Primrec.id
  exact this.of_eq (fun n => by simp[@elim_eq_elimv L μ γ ])

lemma bv_primrec : Primrec (bv : UFormula L μ → ℕ) := by
  have hr : Primrec (fun p => ((List.ofFn p.2.2).map UTerm.bv).sup : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → ℕ) :=
    (list_sup nat_max).comp
      (list_map (by apply sigma_finArrow_list_ofFn.comp (sigma_prod_right (β := L.rel))) (UTerm.bv_primrec.comp₂ Primrec₂.right))
  have hb : Primrec₂ (fun m n => max m n : ℕ → ℕ → ℕ) := Primrec.nat_max
  have hq : Primrec (fun n => n.pred : ℕ → ℕ) := Primrec.pred
  have := elim_primrec 0 0 hr hr hb hb hq hq
  exact this.of_eq (fun p => by
    simp[Function.comp]
    induction p <;> simp[elim, *]
    { simp[List.sup_ofFn] }
    { simp[List.sup_ofFn] })

end W

instance : Primcodable (SubFormula L μ n) :=
  letI : Primcodable { p : UFormula L μ // p.bv ≤ n } := Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  Primcodable.ofEquiv { p : UFormula L μ // p.bv ≤ n } subformulaEquivSubtype

--#eval (encode (“0 = 1” : Sentence Language.oRing))
--935319734277578879273555234912656324244635888525662333723386717104793974747307706000946757839613990108227396487674599112298224133835455479797684718532327704919669033277927248672439400930905780539310948141167795875680399885836866734847451791344024484329550631775805419608027972015818561000739343253563007945350184910033971876879754597654645132096911041199614874696969038805225053580411215684158738776904337761136760151729990515106646661045385956293637

lemma neg_primrec : Primrec (neg : UFormula L μ → UFormula L μ) := by
  have := elim_primrec (L := L) (μ := μ) falsum verum nrel_primrec rel_primrec or_primrec and_primrec ex_primrec all_primrec
  exact this.of_eq (fun p => by simp; induction p <;> simp[elim, neg, *])

/-
lemma bind_primrec : Primrec (neg : UFormula L μ → UFormula L μ) := by
-/

end UFormula

end FirstOrder

end LO