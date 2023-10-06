import Logic.Predicate.FirstOrder.Basic
import Logic.Vorspiel.W

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v}

inductive UTerm (L : Language.{u}) (μ : Type v)
  | bvar : ℕ → UTerm L μ
  | fvar : μ → UTerm L μ
  | func : ∀ {arity}, L.func arity → (Fin arity → UTerm L μ) → UTerm L μ

namespace UTerm

instance : Inhabited (UTerm L μ) := ⟨bvar 0⟩

def elim {γ : Type*}
  (b : ℕ → γ) (e : μ → γ) (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) : UTerm L μ → γ
  | bvar x   => b x
  | fvar x   => e x
  | func f v => u f (fun i => elim b e u (v i))

def bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : UTerm L μ₁ → UTerm L μ₂
  | bvar x   => b x
  | fvar x   => e x
  | func f v => func f (fun i => (v i).bind b e)

def rewrite (e : μ₁ → UTerm L μ₂) : UTerm L μ₁ → UTerm L μ₂ := bind bvar e

def bShifts (k : ℕ) : UTerm L μ → UTerm L μ := bind (fun x => bvar (x + k)) fvar

@[simp] lemma bShifts_zero (t : UTerm L μ) : bShifts 0 t = t := by
  simp[bShifts]
  induction t <;> simp[bind, *]

lemma bind_bind (b₁ : ℕ → UTerm L μ₂) (e₁ : μ₁ → UTerm L μ₂) (b₂ : ℕ → UTerm L μ₃) (e₂ : μ₂ → UTerm L μ₃) :
    bind b₂ e₂ (bind b₁ e₁ t) = bind (fun x => bind b₂ e₂ (b₁ x)) (fun x => bind b₂ e₂ (e₁ x)) t := by
  induction t <;> simp[bind, *]

@[simp] lemma bShifts_bShifts (t : UTerm L μ) (m₁ m₂) : bShifts m₂ (bShifts m₁ t) = bShifts (m₁ + m₂) t := by
  simp[bShifts, bind_bind, bind, add_assoc]

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

lemma bind_eq_bind_of_eq (b₁ b₂ : ℕ → UTerm L μ₂) (e₁ e₂ : μ₁ → UTerm L μ₂) (t : UTerm L μ₁)
  (hb : ∀ x < t.bv, b₁ x = b₂ x) (he : ∀ x, e₁ x = e₂ x) : bind b₁ e₁ t = bind b₂ e₂ t := by
  induction t <;> simp[bind, he]
  case bvar x => exact hb x (by simp)
  case func k f v ih => funext i; exact ih i (fun x hx => hb x (by simp[bv]; exact ⟨i, hx⟩))

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

lemma ofSubTerm_eq_subtEquiv : @ofSubTerm L μ n = subtEquiv := rfl

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
  | (Sum.inr $ Sum.inr ⟨_, _⟩) => instDecidableEq

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

lemma funcL_primrec' (k : ℕ) :
  Primrec₂ (funcL ⟨k, ·⟩ : L.func k → List (UTerm L μ) → Option (UTerm L μ)) :=
  (funcL_primrec.comp₂ ((sigma_pair k).comp₂ Primrec₂.left) Primrec₂.right).of_eq <| by
    intro f l; simp[WType.mkL, Edge]

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

private def F (b : σ → ℕ → γ) (e : σ → μ → γ) (u : σ → ((k : ℕ) × L.func k) × List γ → γ) : σ → Node L μ × List γ → γ := fun z p =>
    Sum.casesOn p.1 (fun x => b z x) (fun q => Sum.casesOn q (fun x => e z x) (fun f => u z (f, p.2)))

private lemma elim_eq {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ} :
    elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v)) t =
    WType.elimL (fun p l => F b e u x (p, l)) (equivW L μ t) := by
  induction t <;> simp[elim, WType.elimL_mk, F, *]
  { simp[Edge]; congr; funext i; rw[fintypeArrowEquivFinArrow_app]; congr; ext; simp[Fin.castIso_eq_cast] }

lemma elim_primrec_param {σ γ} [Primcodable σ] [Primcodable γ] 
  {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ} {t : σ → UTerm L μ}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hu : Primrec₂ u) (ht : Primrec t) :
    Primrec (fun x => elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v)) (t x)) := by
  have hF : Primrec₂ (F b e u) :=
    sum_casesOn (fst.comp snd) (hb.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)
      (sum_casesOn snd (he.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) Primrec₂.right)
        (hu.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) (Primrec₂.pair.comp₂ snd (snd.comp₂ $ snd.comp₂ $ fst.comp₂ $ Primrec₂.left))))
  exact (w_elimL_param hF (Primrec.of_equiv.comp ht)).of_eq (fun x => by simp[elim_eq])

lemma elim_primrec_param_opt {σ γ} [Primcodable σ] [Inhabited γ] [Primcodable γ]
  {b : σ → ℕ → γ} {e : σ → μ → γ} {t : σ → UTerm L μ}
  (hb : Primrec₂ b) (he : Primrec₂ e) 
  (u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : σ → ((k : ℕ) × L.func k) × List γ → Option γ}
  (hu : Primrec₂ uOpt) (ht : Primrec t)
  (H : ∀ (x : σ) {k} (f : L.func k) (v : Fin k → γ), uOpt x (⟨k, f⟩, List.ofFn v) = some (u x f v)) :
    Primrec (fun x => elim (b x) (e x) (u x) (t x)) :=
  (elim_primrec_param hb he (option_iget.comp₂ hu) ht).of_eq (fun _ => by simp[H])

lemma elim_primrec {γ} [Primcodable γ] 
  {b : ℕ → γ} {e : μ → γ} {u : ((k : ℕ) × L.func k) → List γ → γ} (hb : Primrec b) (he : Primrec e) (hu : Primrec₂ u) :
    Primrec (elim b e (fun {k} f v => u ⟨k, f⟩ (List.ofFn v))) :=
  elim_primrec_param (σ := UTerm L μ)
    (hb.comp₂ Primrec₂.right) (he.comp₂ Primrec₂.right) (hu.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
    Primrec.id

lemma elim_primrec_opt {γ} [Inhabited γ] [Primcodable γ] {b : ℕ → γ} {e : μ → γ}
  (hb : Primrec b) (he : Primrec e)
  (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : ((k : ℕ) × L.func k) → List γ → Option γ} (hu : Primrec₂ uOpt)
  (H : ∀ {k} (f : L.func k) (v : Fin k → γ), uOpt ⟨k, f⟩ (List.ofFn v) = some (u f v)) :
    Primrec (elim b e u) :=
  (elim_primrec hb he (option_iget.comp₂ hu)).of_eq (fun t => by simp[H])

lemma bv_primrec : Primrec (bv : UTerm L μ → ℕ) := by
  have : Primrec (elim (L := L) (μ := μ) Nat.succ (fun _ => 0) fun {k} _ v => (List.ofFn v).sup) :=
    elim_primrec Primrec.succ (Primrec.const 0) ((list_sup nat_max).comp₂ Primrec₂.right)
  exact this.of_eq (fun t => by
    induction t <;> simp[elim, bv, *]
    { simp[List.sup_ofFn] })

variable {μ₁ : Type*} {μ₂ : Type*} [Primcodable μ₁] [Primcodable μ₂]

lemma bind_primrec_param [Primcodable σ] {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂} {g : σ → UTerm L μ₁}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hg : Primrec g) : Primrec (fun x => bind (b x) (e x) (g x)) := by
  have : Primrec₂ (fun _ p => funcL p.1 p.2 : σ → ((k : ℕ) × L.func k) × List (UTerm L μ₂) → Option (UTerm L μ₂)) :=
    funcL_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)
  have := elim_primrec_param_opt hb he (fun _ _ f v => func f v) this hg
    (by intro x k f v; simp[funcL]; congr)
  exact this.of_eq <| by intro x; generalize g x = t; induction t <;> simp[elim, bind, *]

lemma bind_primrec {b : ℕ → UTerm L μ₂} {e : μ₁ → UTerm L μ₂} (hb : Primrec b) (he : Primrec e) :
    Primrec (bind b e) := bind_primrec_param (hb.comp₂ Primrec₂.right) (he.comp₂ Primrec₂.right) Primrec.id

lemma bShifts_primrec : Primrec₂ (bShifts : ℕ → UTerm L μ → UTerm L μ) :=
  to₂' <| bind_primrec_param (bvar_primrec.comp₂ $ nat_add.comp₂ Primrec₂.right (fst.comp₂ Primrec₂.left))
    (fvar_primrec.comp₂ Primrec₂.right) snd

end W

end UTerm


namespace SubTerm

open UTerm Encodable Primrec Primrec₂
variable {α : Type*} [Primcodable α]
variable [Primcodable μ] [(k : ℕ) → Primcodable (L.func k)] [UniformlyPrimcodable L.func]

instance : Primcodable (SubTerm L μ n) :=
  letI : Primcodable { t : UTerm L μ // t.bv ≤ n } := Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  Primcodable.ofEquiv { t : UTerm L μ // t.bv ≤ n } subtEquiv

lemma bvar_primrec : Primrec (bvar : Fin n → SubTerm L μ n) := dom_fintype _

lemma fvar_primrec : Primrec (fvar : μ → SubTerm L μ n) :=
  letI : Primcodable { t : UTerm L μ // t.bv ≤ n } := Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  (Primrec.of_equiv_iff subtEquiv).mp <| of_subtype_iff.mp <| by simpa using UTerm.fvar_primrec

def funcL {n} (f : (k : ℕ) × L.func k) (l : List (SubTerm L μ n)) : Option (SubTerm L μ n) :=
  if h : l.length = f.1
    then some (func f.2 (fun i => l.get (i.cast h.symm)))
    else none

lemma funcL_primrec : Primrec₂ (funcL : (k : ℕ) × L.func k → List (SubTerm L μ n) → Option (SubTerm L μ n)) :=
  letI : Primcodable { t : UTerm L μ // t.bv ≤ n } := Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have : Primrec₂ (fun f l => UTerm.funcL f (l.map (subtEquiv ·)) : (k : ℕ) × L.func k → List (SubTerm L μ n) → Option (UTerm L μ)) :=
    UTerm.funcL_primrec.comp₂ Primrec₂.left
      <| to₂' <| list_map snd <| to₂' <| by apply subtype_val.comp <| of_equiv.comp snd
  Primrec₂.encode_iff.mp <| (Primrec.encode.comp₂ this).of_eq <| by
    intro ⟨k, f⟩ l
    simp[funcL, UTerm.funcL]
    by_cases hl : l.length = k <;> simp[hl]
    { simp[Encodable.encode_ofEquiv subtEquiv, Encodable.Subtype.encode_eq]
      funext i; congr }

lemma funcL_primrec' (k) : Primrec₂ (funcL ⟨k, ·⟩ : L.func k → List (SubTerm L μ n) → Option (SubTerm L μ n)) :=
  (funcL_primrec.comp₂ ((sigma_pair k).comp₂ Primrec₂.left) Primrec₂.right).of_eq <| by simp[funcL]

lemma func₁_primrec : Primrec₂ (func · ![·] : L.func 1 → SubTerm L μ n → SubTerm L μ n) :=
  Primrec₂.option_some_iff.mp <|
    have : Primrec₂ (fun f t => funcL ⟨1, f⟩ [t] : L.func 1 → SubTerm L μ n → Option (SubTerm L μ n)) :=
      (funcL_primrec' 1).comp₂ Primrec₂.left (list_cons.comp₂ Primrec₂.right (Primrec₂.const []))
    this.of_eq <| by intro f t; simp[funcL, Matrix.constant_eq_singleton]

lemma func₂_primrec : Primrec₂ (fun f t => func f ![t.1, t.2] : L.func 2 → SubTerm L μ n × SubTerm L μ n → SubTerm L μ n) :=
  Primrec₂.option_some_iff.mp <| by
    have : Primrec₂ (fun f t => funcL ⟨2, f⟩ [t.1, t.2] : L.func 2 → SubTerm L μ n × SubTerm L μ n → Option (SubTerm L μ n)) :=
      (funcL_primrec' 2).comp₂ Primrec₂.left
        <| list_cons.comp₂ (fst.comp₂ Primrec₂.right) <| list_cons.comp₂ (snd.comp₂ Primrec₂.right) (Primrec₂.const [])
    exact this.of_eq <| fun f ⟨t₁, t₂⟩ => by
      simp[funcL]
      funext i; cases i using Fin.cases <;> simp

lemma subtEquiv_bind_eq_bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) (t : SubTerm L μ₁ n₁) :
    (subtEquiv (Rew.bind b e t)).val =
    UTerm.bind (fun x => if hx : x < n₁ then subtEquiv (b ⟨x, hx⟩) else default) (fun x => subtEquiv $ e x) (subtEquiv t) := by
  induction t <;> simp[UTerm.bind]
  case func k f v ih =>
    simp[Rew.func]
    funext i; simp[ih]; rfl

lemma bv_subtEquiv (t : SubTerm L μ n) : (subtEquiv t).val.bv ≤ n := by
  induction t <;> simp[UTerm.bv]
  case bvar x => { exact x.prop }

lemma subtEquiv_bShift_eq_bShift (t : SubTerm L μ k) :
    (subtEquiv (Rew.bShift t)).val = UTerm.bShifts 1 (subtEquiv t) := by
  rw[Rew.eq_bind Rew.bShift, subtEquiv_bind_eq_bind]
  simp[bShifts]
  apply bind_eq_bind_of_eq
  · intro x hx; simp[lt_of_lt_of_le hx (bv_subtEquiv t)]
  · simp

variable {σ : Type*} {μ₁ : Type*} {μ₂ : Type*} [Primcodable μ₁] [Primcodable μ₂] [Primcodable σ]

lemma brew_primrec {b : α → Fin n₁ → SubTerm L μ₂ n₂} (hb : Primrec b) :
    Primrec₂ (fun z x => if hx : x < n₁ then (subtEquiv (b z ⟨x, hx⟩)).val else default) := by
  letI : ∀ n, Primcodable { t : UTerm L μ₂ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have : Primrec₂ (fun z x => (Nat.toFin n₁ x).casesOn default (fun i => (subtEquiv (b z i)).val) : α → ℕ → UTerm L μ₂) :=
    to₂' <| option_casesOn (α := α × ℕ) (nat_toFin.comp snd) (Primrec.const default) <| subtype_val.comp₂ <| of_equiv.comp₂ <|
    to₂' <| finArrow_app (v := fun (p : (α × ℕ) × Fin n₁) => b p.1.1) (hb.comp (fst.comp fst)) snd
  exact this.of_eq <| by
    intro a x; simp[Nat.toFin]
    by_cases hx : x < n₁ <;> simp[hx]

lemma bind_primrec {b : α → Fin n₁ → SubTerm L μ₂ n₂} {e : α → μ₁ → SubTerm L μ₂ n₂} {t : α → SubTerm L μ₁ n₁}
  (hb : Primrec b) (he : Primrec₂ e) (ht : Primrec t) :
    Primrec (fun x => Rew.bind (b x) (e x) (t x)) := by
  letI : ∀ n, Primcodable { t : UTerm L μ₁ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  letI : ∀ n, Primcodable { t : UTerm L μ₂ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have : Primrec (fun z =>
      UTerm.bind (fun x => if hx : x < n₁ then subtEquiv (b z ⟨x, hx⟩) else default) (fun x => subtEquiv $ e z x) (subtEquiv $ t z)
      : α → UTerm L μ₂) :=
    UTerm.bind_primrec_param (brew_primrec hb)
      (subtype_val.comp₂ $ of_equiv.comp₂ $ he.comp₂ Primrec₂.left Primrec₂.right)
      (subtype_val.comp $ of_equiv.comp ht)
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    intro a
    simp[Encodable.encode_ofEquiv subtEquiv, Encodable.Subtype.encode_eq, subtEquiv_bind_eq_bind]

end SubTerm

end FirstOrder

end LO