import Logic.Predicate.FirstOrder.Basic.Formula.Formula
import Logic.Vorspiel.Computability

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

def rank : UTerm L μ → ℕ
  | bvar x   => x + 1
  | fvar _   => 0
  | func _ v => Finset.sup Finset.univ (fun i => (v i).rank)

@[simp] lemma rank_bvar : rank (bvar x : UTerm L μ) = x + 1 := rfl

@[simp] lemma rank_fvar : rank (fvar x : UTerm L μ) = 0 := rfl

@[simp] lemma subtype_val_le (t : { t : UTerm L μ // t.rank ≤ n }) : t.val.rank ≤ n := t.property

def toSubTerm : (t : UTerm L μ) → t.rank ≤ n → SubTerm L μ n
  | bvar x,   h => #⟨x, by simp at h; exact Nat.lt_of_succ_le h⟩
  | fvar x,   _ => &x
  | func f v, h => SubTerm.func f (fun i => toSubTerm (v i) (by simp[rank] at h; exact h i))

def ofSubTerm : SubTerm L μ n → { t : UTerm L μ // t.rank ≤ n }
  | #x               => ⟨bvar x, Nat.succ_le_of_lt x.isLt⟩
  | &x               => ⟨fvar x, by simp⟩
  | SubTerm.func f v => ⟨func f (fun i => ofSubTerm (v i)), by simp[rank]⟩

def subtermEquivSubtype : SubTerm L μ n ≃ { t : UTerm L μ // t.rank ≤ n } where
  toFun := ofSubTerm
  invFun := fun ⟨t, ht⟩ => t.toSubTerm ht
  left_inv := fun t => by
    induction t <;> simp[ofSubTerm, toSubTerm]
    case func f v ih => { funext i; exact ih i }
  right_inv := fun ⟨t, h⟩ => by
    induction t <;> simp[ofSubTerm, toSubTerm]
    case func f v ih =>
      funext i
      have h : ∀ i, (v i).rank ≤ n := by simpa[rank] using h
      have : (h : (v i).rank ≤ n) → ofSubTerm (toSubTerm (v i) h) = ⟨v i, h⟩ := by simpa using ih i
      simpa using congr_arg Subtype.val (this (h i))

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
  | (Sum.inr $ Sum.inr ⟨k, _⟩) => instDecidableEqFin k

open Encodable Primrec Primrec₂
variable [Primcodable μ] [(k : ℕ) → Primcodable (L.func k)] [UniformlyPrimcodable L.func]

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

lemma funcL_primrec :
  Primrec₂ (fun (f : (k : ℕ) × L.func k) (l : List (UTerm L μ)) =>
    if h : l.length = f.1
      then some (func f.2 (fun i => l.get (i.cast h.symm)))
      else none) :=
  have : Primrec₂ (fun (a : Node L μ) (l : List (UTerm L μ)) => (WType.mkL a (l.map (equivW L μ))).map (equivW L μ).symm) :=
    option_map
      (w_mkL.comp₂ Primrec₂.left ((list_map Primrec.id (Primrec.of_equiv.comp₂ Primrec₂.right)).comp₂ Primrec₂.right))
      (of_equiv_symm.comp₂ Primrec₂.right)
  have : Primrec₂ (fun f (l : List (UTerm L μ)) => (WType.mkL (Sum.inr $ Sum.inr f) (l.map (equivW L μ))).map (equivW L μ).symm) :=
    this.comp₂ (sum_inr.comp₂ $ sum_inr.comp₂ Primrec₂.left) Primrec₂.right
  this.of_eq (fun ⟨k, f⟩ l => by
      simp[WType.mkL, Edge]
      by_cases hl : l.length = k <;> simp[hl]
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

def elim {γ : Type _} (b : ℕ → γ) (e : μ → γ) (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) : UTerm L μ → γ
  | bvar x   => b x
  | fvar x   => e x
  | func f v => u f (fun i => elim b e u (v i))

private def F (b : σ → ℕ → γ) (e : σ → μ → γ) (u : σ → ((k : ℕ) × L.func k) × List γ → γ) : σ → Node L μ × List γ → γ := fun z p =>
    Sum.casesOn p.1 (fun x => b z x) (fun q => Sum.casesOn q (fun x => e z x) (fun f => u z (f, p.2)))

private lemma elim_eq {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ} :
    elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v)) t =
    WType.elimL (fun p l => F b e u x (p, l)) (equivW L μ t) := by
  induction t <;> simp[elim, WType.elimL_mk, F, *]
  { simp[Edge]; congr; funext i; rw[fintypeArrowEquivFinArrow_app]; congr; ext; simp[Fin.castIso_eq_cast] }

lemma elim_primrec_param {σ γ} [Primcodable σ] [Primcodable γ] 
  {b : σ → ℕ → γ} {e : σ → μ → γ} {u : σ → ((k : ℕ) × L.func k) × List γ → γ}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hu : Primrec₂ u) :
    Primrec₂ (fun x => elim (b x) (e x) (fun {k} f v => u x (⟨k, f⟩, List.ofFn v))) := by
  have hF : Primrec₂ (F b e u) :=
    sum_casesOn (fst.comp snd) (hb.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)
      (sum_casesOn snd (he.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) Primrec₂.right)
        (hu.comp₂ (fst.comp₂ $ fst.comp₂ $ Primrec₂.left) (Primrec₂.pair.comp₂ snd (snd.comp₂ $ snd.comp₂ $ fst.comp₂ $ Primrec₂.left))))
  have : Primrec₂ (fun x t => WType.elimL (fun p l => F b e u x (p, l)) (equivW L μ t)) :=
    (w_elimL_param hF).comp₂ Primrec₂.left (Primrec.of_equiv.comp snd)
  exact this.of_eq (fun x t => by simp[elim_eq])

lemma elim_primrec_param_opt {σ γ} [Primcodable σ] [Inhabited γ] [Primcodable γ] {b : σ → ℕ → γ} {e : σ → μ → γ}
  (hb : Primrec₂ b) (he : Primrec₂ e) 
  (u : σ → {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : σ → ((k : ℕ) × L.func k) × List γ → Option γ} (hu : Primrec₂ uOpt)
  (H : ∀ (x : σ) {k} (f : L.func k) (v : Fin k → γ), uOpt x (⟨k, f⟩, List.ofFn v) = some (u x f v)) :
    Primrec₂ (fun x => elim (b x) (e x) (u x)) :=
  (elim_primrec_param hb he (option_iget.comp₂ hu)).of_eq (fun x t => by simp[H])

lemma elim_primrec {γ} [Primcodable γ] 
  {b : ℕ → γ} {e : μ → γ} {u : ((k : ℕ) × L.func k) → List γ → γ} (hb : Primrec b) (he : Primrec e) (hu : Primrec₂ u) :
    Primrec (elim b e (fun {k} f v => u ⟨k, f⟩ (List.ofFn v))) := by
  have := elim_primrec_param (σ := Unit)
    (hb.comp₂ Primrec₂.right) (he.comp₂ Primrec₂.right) (hu.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
  exact this.comp (Primrec.const ()) (Primrec.id)

lemma elim_primrec_opt {γ} [Inhabited γ] [Primcodable γ] {b : ℕ → γ} {e : μ → γ}
  (hb : Primrec b) (he : Primrec e)
  (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) {uOpt : ((k : ℕ) × L.func k) → List γ → Option γ} (hu : Primrec₂ uOpt)
  (H : ∀ {k} (f : L.func k) (v : Fin k → γ), uOpt ⟨k, f⟩ (List.ofFn v) = some (u f v)) :
    Primrec (elim b e u) :=
  (elim_primrec hb he (option_iget.comp₂ hu)).of_eq (fun t => by simp[H])

lemma rank_primrec : Primrec (rank : UTerm L μ → ℕ) := by
  have : Primrec (elim (L := L) (μ := μ) Nat.succ (fun _ => 0) fun {k} _ v => (List.ofFn v).sup) :=
    elim_primrec Primrec.succ (Primrec.const 0) ((list_sup nat_max).comp₂ Primrec₂.right)
  exact this.of_eq (fun t => by
    induction t <;> simp[elim, rank, *]
    { simp[List.sup_ofFn] })

instance : Primcodable (SubTerm L μ n) :=
  letI : Primcodable { t : UTerm L μ // t.rank ≤ n } := Primcodable.subtype (nat_le.comp rank_primrec (Primrec.const n))
  Primcodable.ofEquiv { t : UTerm L μ // t.rank ≤ n } subtermEquivSubtype

end W

end UTerm

end FirstOrder

end LO