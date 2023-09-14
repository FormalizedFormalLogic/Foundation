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

def elim {γ : Type _} (b : ℕ → γ) (e : μ → γ) (u : {k : ℕ} → L.func k → (Fin k → γ) → γ) : UTerm L μ → γ
  | bvar x   => b x
  | fvar x   => e x
  | func f v => u f (fun i => elim b e u (v i))

def bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : UTerm L μ₁ → UTerm L μ₂
  | bvar x   => b x
  | fvar x   => e x
  | func f v => func f (fun i => (v i).bind b e)

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

lemma toSubTerm_ofSubterm {n} (t : SubTerm L μ n) : toSubTerm (ofSubTerm t).1 (ofSubTerm t).2 = t := by
  induction t <;> simp[ofSubTerm, toSubTerm]
  case func f v ih => { funext i; exact ih i }

lemma ofSubTerm_toSubterm {n} (t : UTerm L μ) (h : t.rank ≤ n) : ofSubTerm (toSubTerm t h) = t := by
  induction t <;> simp[ofSubTerm, toSubTerm]
  case func f v ih =>
    funext i
    have h : ∀ i, (v i).rank ≤ n := by simpa[rank] using h
    exact ih i (h i)

def subtermEquivSubtype : SubTerm L μ n ≃ { t : UTerm L μ // t.rank ≤ n } where
  toFun := ofSubTerm
  invFun := fun t => toSubTerm t.1 t.2
  left_inv := toSubTerm_ofSubterm
  right_inv := by intro ⟨t, h⟩; ext; simpa using ofSubTerm_toSubterm t h

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

end W

instance : Primcodable (SubTerm L μ n) :=
  letI : Primcodable { t : UTerm L μ // t.rank ≤ n } := Primcodable.subtype (nat_le.comp rank_primrec (Primrec.const n))
  Primcodable.ofEquiv { t : UTerm L μ // t.rank ≤ n } subtermEquivSubtype
end UTerm

namespace UFormula

instance : Inhabited (UFormula L μ) := ⟨verum⟩

def elim {γ : Type _}
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

def rank : UFormula L μ → ℕ
  | verum    => 0
  | falsum   => 0
  | rel _ v  => Finset.sup Finset.univ (fun i => (v i).rank)
  | nrel _ v => Finset.sup Finset.univ (fun i => (v i).rank)
  | and p q  => max p.rank q.rank
  | or p q   => max p.rank q.rank
  | all p    => p.rank.pred
  | ex p     => p.rank.pred

@[simp] lemma rank_verum : rank (verum : UFormula L μ) = 0 := rfl

@[simp] lemma rank_falsum : rank (falsum : UFormula L μ) = 0 := rfl

@[simp] lemma rank_rel {k} (r : L.rel k) (v : Fin k → UTerm L μ) : rank (rel r v) = Finset.sup Finset.univ (fun i => (v i).rank) := rfl

@[simp] lemma rank_nrel {k} (r : L.rel k) (v : Fin k → UTerm L μ) : rank (nrel r v) = Finset.sup Finset.univ (fun i => (v i).rank) := rfl

@[simp] lemma rank_and (p q : UFormula L μ) : (and p q).rank = max p.rank q.rank := rfl

@[simp] lemma rank_or (p q : UFormula L μ) : (or p q).rank = max p.rank q.rank := rfl

@[simp] lemma rank_all (p : UFormula L μ) : (all p).rank = p.rank.pred := rfl

@[simp] lemma rank_ex (p : UFormula L μ) : (ex p).rank = p.rank.pred := rfl

@[simp] lemma subtype_val_le (p : { p : UFormula L μ // p.rank ≤ n }) : p.val.rank ≤ n := p.property

def toSubFormula : {n : ℕ} → (p : UFormula L μ) → p.rank ≤ n → SubFormula L μ n
  | _, verum,    _ => ⊤
  | _, falsum,   _ => ⊥
  | _, rel r v,  h => SubFormula.rel r (fun i => (v i).toSubTerm (by simp at h; exact h i))
  | _, nrel r v, h => SubFormula.nrel r (fun i => (v i).toSubTerm (by simp at h; exact h i))
  | _, and p q,  h => p.toSubFormula (by simp at h; exact h.1) ⋏ q.toSubFormula (by simp at h; exact h.2)
  | _, or p q,   h => p.toSubFormula (by simp at h; exact h.1) ⋎ q.toSubFormula (by simp at h; exact h.2)
  | _, all p,    h => ∀' p.toSubFormula (Nat.le_add_of_sub_le h)
  | _, ex p,     h => ∃' p.toSubFormula (Nat.le_add_of_sub_le h)

def ofSubFormula : {n : ℕ} → SubFormula L μ n → { p : UFormula L μ // p.rank ≤ n }
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

lemma ofSubFormula_toSubFormula : ∀ {n : ℕ} (p : UFormula L μ) (h : p.rank ≤ n), ofSubFormula (toSubFormula p h) = p
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

def subformulaEquivSubtype : SubFormula L μ n ≃ { p : UFormula L μ // p.rank ≤ n } where
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

/-
lemma relL_primrec :
  Primrec₂ (fun (f : (k : ℕ) × L.rel k) (l : List (UTerm L μ)) =>
    if h : l.length = f.1
      then some (rel f.2 (fun i => l.get (i.cast h.symm)))
      else none) := by
  let i : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → Node L μ := fun t => (true, Sum.inl ⟨t.1, t.2.1, t.2.2⟩)
  have : Primrec i := sorry
  have : Primrec (fun t => WType.mk (i t) Empty.elim) :=
    w_mk₀ (β := Edge L μ) i (by intros; exact instIsEmptyEmpty) this
-/

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

private lemma elim_eq
  [Inhabited γ]
  (γVerum : σ → γ)
  (γFalsum : σ → γ)
  (γRel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)
  (γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ)  
  (γAnd : σ → γ × γ → γ)
  (γOr : σ → γ × γ → γ)
  (γAll : σ → γ → γ)
  (γEx : σ → γ → γ) (p : UFormula L μ) :
    elim (γVerum x) (γFalsum x)
      (fun {k} f v => γRel x ⟨k, f, v⟩)
      (fun {k} f v => γNrel x ⟨k, f, v⟩)
      (fun y₁ y₂ => γAnd x (y₁, y₂))
      (fun y₁ y₂ => γOr x (y₁, y₂))
      (γAll x)
      (γEx x) p =
    WType.elimL (fun p l => F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx x (p, l)) (equivW L μ p) := by
  induction p <;> simp[elim, WType.elimL_mk, F, *] <;> congr

lemma elim_primrec_param {σ γ} [Primcodable σ] [Primcodable γ] [Inhabited γ]
  {γVerum γFalsum : σ → γ}
  {γRel γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ}
  {γAnd γOr : σ → γ × γ → γ}
  {γAll γEx : σ → γ → γ}
  (hVerum : Primrec γVerum)
  (hFalsum : Primrec γFalsum)
  (hRel : Primrec₂ γRel)
  (hNrel : Primrec₂ γNrel)
  (hAnd : Primrec₂ γAnd)
  (hOr : Primrec₂ γOr)
  (hAll : Primrec₂ γAll)
  (hEx : Primrec₂ γEx) :
    Primrec₂ (fun x => elim (γVerum x) (γFalsum x)
      (fun {k} f v => γRel x ⟨k, f, v⟩)
      (fun {k} f v => γNrel x ⟨k, f, v⟩)
      (fun y₁ y₂ => γAnd x (y₁, y₂))
      (fun y₁ y₂ => γOr x (y₁, y₂))
      (γAll x)
      (γEx x)) := by {
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
  have : Primrec₂ (fun x p => WType.elimL (fun p l => F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx x (p, l)) (equivW L μ p)) :=
    (w_elimL_param hF).comp₂ Primrec₂.left (Primrec.of_equiv.comp snd)
  exact this.of_eq (fun x t => by simp[elim_eq]) }

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
  have := elim_primrec_param (σ := Unit)
    (Primrec.const γVerum) (Primrec.const γFalsum)
    (hRel.comp₂ Primrec₂.right) (hNrel.comp₂ Primrec₂.right)
    (hAnd.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)) (hOr.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
    (hAll.comp₂ Primrec₂.right) (hEx.comp₂ Primrec₂.right)
  exact this.comp (Primrec.const ()) Primrec.id

lemma rank_primrec : Primrec (rank : UFormula L μ → ℕ) := by
  have hr : Primrec (fun p => ((List.ofFn p.2.2).map UTerm.rank).sup : (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → ℕ) :=
    (list_sup nat_max).comp
      (list_map (by apply sigma_finArrow_list_ofFn.comp (sigma_prod_right (β := L.rel))) (UTerm.rank_primrec.comp₂ Primrec₂.right))
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
  letI : Primcodable { p : UFormula L μ // p.rank ≤ n } := Primcodable.subtype (nat_le.comp rank_primrec (Primrec.const n))
  Primcodable.ofEquiv { p : UFormula L μ // p.rank ≤ n } subformulaEquivSubtype

end UFormula

end FirstOrder

end LO