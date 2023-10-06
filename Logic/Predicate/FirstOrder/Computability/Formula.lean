import Logic.Predicate.FirstOrder.Computability.Term

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v}

inductive UFormula (L : Language.{u}) (μ : Type v) : Type (max u v) where
  | verum  : UFormula L μ
  | falsum : UFormula L μ
  | rel    : {arity : ℕ} → L.rel arity → (Fin arity → UTerm L μ) → UFormula L μ
  | nrel   : {arity : ℕ} → L.rel arity → (Fin arity → UTerm L μ) → UFormula L μ
  | and    : UFormula L μ → UFormula L μ → UFormula L μ
  | or     : UFormula L μ → UFormula L μ → UFormula L μ
  | all    : UFormula L μ → UFormula L μ
  | ex     : UFormula L μ → UFormula L μ

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

def depth : UFormula L μ → ℕ
  | verum    => 0
  | falsum   => 0
  | rel _ _  => 0
  | nrel _ _ => 0
  | and p q  => max p.depth q.depth + 1
  | or p q   => max p.depth q.depth + 1
  | all p    => p.depth + 1
  | ex p     => p.depth + 1

def shiftb (b : ℕ → UTerm L μ) (n : ℕ) : ℕ → UTerm L μ := fun x =>
  if x < n then UTerm.bvar x
  else UTerm.bShifts n (b (x - n))

@[simp] lemma shiftb_zero (b : ℕ → UTerm L μ) : shiftb b 0 = b := by simp[shiftb]

@[simp] lemma shiftb_shiftb_zero (b : ℕ → UTerm L μ) (m₁ m₂) :
    shiftb (shiftb b m₁) m₂ = shiftb b (m₁ + m₂) := by
  simp[shiftb]
  funext x
  by_cases hm₂ : x < m₂
  · have : x < m₁ + m₂ := lt_add_of_nonneg_of_lt (Nat.zero_le m₁) hm₂
    simp[hm₂, this]
  · simp[hm₂]
    by_cases hm₁ : x < m₁ + m₂
    · have : x - m₂ < m₁ := Nat.sub_lt_right_of_lt_add (Nat.not_lt.mp hm₂) hm₁
      simp[hm₁, this, UTerm.bShifts, UTerm.bind]
      exact tsub_add_cancel_of_le (Nat.not_lt.mp hm₂)
    · have : ¬x - m₂ < m₁ := Nat.not_lt.mpr <| Nat.le_sub_of_add_le <| Nat.not_lt.mp hm₁
      simp[hm₁, this, Nat.sub_sub, add_comm]

def bindq (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : ℕ → UFormula L μ₁ → UFormula L μ₂
  | _, verum    => verum
  | _, falsum   => falsum
  | m, rel r v  => rel r (fun i => (v i).bind (shiftb b m) (UTerm.bShifts m $ e ·))
  | m, nrel r v => nrel r (fun i => (v i).bind (shiftb b m) (UTerm.bShifts m $ e ·))
  | m, and p q  => and (p.bindq b e m) (q.bindq b e m)
  | m, or p q   => or (p.bindq b e m) (q.bindq b e m)
  | m, all p    => all (p.bindq b e (m + 1))
  | m, ex p     => ex (p.bindq b e (m + 1))

def bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) : UFormula L μ₁ → UFormula L μ₂ := bindq b e 0

lemma bindq_eq_bind (b : ℕ → UTerm L μ₂) (e : μ₁ → UTerm L μ₂) :
    bindq b e m p = bind (shiftb b m) (UTerm.bShifts m $ e ·) p := by
  induction' p generalizing b e m <;> simp[bind, bindq, *]

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

lemma bind_eq_bind_of_eq (b₁ b₂ : ℕ → UTerm L μ₂) (e₁ e₂ : μ₁ → UTerm L μ₂) (p : UFormula L μ₁)
  (hb : ∀ x < p.bv, b₁ x = b₂ x) (he : ∀ x, e₁ x = e₂ x) : bind b₁ e₁ p = bind b₂ e₂ p := by
  induction p generalizing b₁ b₂ e₁ e₂ <;> simp[bind, bindq, he]
  case rel k r v =>
    funext i
    apply UTerm.bind_eq_bind_of_eq
    · intro x hx; exact hb x (by simp; exact ⟨i, hx⟩)
    · simp 
  case nrel k r v =>
    funext i
    apply UTerm.bind_eq_bind_of_eq
    · intro x hx; exact hb x (by simp; exact ⟨i, hx⟩)
    · simp 
  case and p q ihp ihq =>
    exact ⟨ihp b₁ b₂ e₁ e₂ (fun x hx => hb x (by simp[hx])) he, ihq b₁ b₂ e₁ e₂ (fun x hx => hb x (by simp[hx])) he⟩
  case or p q ihp ihq =>
    exact ⟨ihp b₁ b₂ e₁ e₂ (fun x hx => hb x (by simp[hx])) he, ihq b₁ b₂ e₁ e₂ (fun x hx => hb x (by simp[hx])) he⟩
  case all p ih =>
    simp[bindq_eq_bind]
    apply ih
    · intro x hx
      simp[shiftb]
      cases' x with x <;> simp
      · simp[hb x (by simp; exact Nat.lt_pred_iff.mpr hx)]
    · simp[he]
  case ex p ih =>
    simp[bindq_eq_bind]
    apply ih
    · intro x hx
      simp[shiftb]
      cases' x with x <;> simp
      · simp[hb x (by simp; exact Nat.lt_pred_iff.mpr hx)]
    · simp[he]

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

def subfEquiv : SubFormula L μ n ≃ { p : UFormula L μ // p.bv ≤ n } where
  toFun := ofSubFormula
  invFun := fun p => p.1.toSubFormula p.2
  left_inv := toSubFormula_ofSubFormula
  right_inv := fun ⟨p, h⟩ => by ext; simpa using ofSubFormula_toSubFormula p h

lemma ofSubFormula_eq_subfEquiv : @ofSubFormula L μ n = subfEquiv := rfl

@[simp] lemma subfEquiv_verum : subfEquiv (⊤ : SubFormula L μ n) = ⟨verum, by simp⟩ := rfl

@[simp] lemma subfEquiv_falsum : subfEquiv (⊥ : SubFormula L μ n) = ⟨falsum, by simp⟩ := rfl

@[simp] lemma subfEquiv_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    subfEquiv (SubFormula.rel r v) = ⟨rel r (fun i => UTerm.subtEquiv (v i)), by simp⟩ := rfl

@[simp] lemma subfEquiv_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    subfEquiv (SubFormula.nrel r v) = ⟨nrel r (fun i => UTerm.subtEquiv (v i)), by simp⟩ := rfl

@[simp] lemma subfEquiv_and (p q : SubFormula L μ n) :
    subfEquiv (p ⋏ q) = ⟨and (subfEquiv p) (subfEquiv q), by simp⟩ := rfl

@[simp] lemma subfEquiv_or (p q : SubFormula L μ n) :
    subfEquiv (p ⋎ q) = ⟨or (subfEquiv p) (subfEquiv q), by simp⟩ := rfl

@[simp] lemma subfEquiv_all (p : SubFormula L μ (n + 1)) :
    subfEquiv (∀' p) = ⟨all (subfEquiv p), by simpa using Iff.mpr Nat.pred_le_iff (subfEquiv p).property⟩ := rfl

@[simp] lemma subfEquiv_ex (p : SubFormula L μ (n + 1)) :
    subfEquiv (∃' p) = ⟨ex (subfEquiv p), by simpa using Iff.mpr Nat.pred_le_iff (subfEquiv p).property⟩ := rfl

open Encodable Primrec
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

instance : Inhabited (WType (Edge L μ)) := ⟨WType.mk (true, Sum.inr $ Sum.inl ()) Empty.elim⟩

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

lemma toW_eq_equivW : toW = equivW L μ := rfl

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
      by apply sum_casesOn snd (Primrec₂.const 0)
          (by apply sum_casesOn snd (Primrec₂.const 0)
                (by apply sum_casesOn snd (Primrec₂.const 2) (Primrec₂.const 1)))
    this.of_eq (fun (_, c) => by
      rcases c with (_ | c) <;> simp[Edge]
      rcases c with (_ | c) <;> simp[Edge]
      rcases c <;> simp[Edge])

end W

instance primcodable : Primcodable (UFormula L μ) := Primcodable.ofEquiv (WType (Edge L μ)) (equivW L μ)

lemma qeq {a b c d : α} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = d := by { simp[*] }
#check WType.instEncodableWType

lemma encode_rel {k} (r : L.rel k) (v : Fin k → UTerm L μ) :
    encode (rel r v) = Nat.pair 1 ((Nat.pair 1 $ 2 * k.pair $ (encode r).pair (encode v)).pair 0) := by
  simp[primcodable, Primcodable.ofEquiv_toEncodable,
    Encodable.encode_ofEquiv (equivW L μ), WType.encode_eq, WType.SubWType.ofW, WType.depth]
  have : (WType.depth (β := Edge L μ) (WType.mk (true, Sum.inl ⟨k, r, v⟩) Empty.elim)) = 1 := rfl
  rw[(WType.SubWType.encode_cast · this)]
  suffices : encode (WType.SubWType.ofWType (β := Edge L μ) ⟨(true, Sum.inl ⟨k, r, v⟩), Empty.elim⟩ 1 (by rw[this])) =
    ((Nat.pair 1 (2 * k.pair ((encode r).pair (encode v)))).pair 0)
  { rw[←this]; apply congr_arg; simp }
  simp[WType.SubWType.encode_mk, Encodable.encode_fintypeArrow_isEmpty, Edge]
  rw[encode_prod_val]
  
lemma encode_nrel {k} (r : L.rel k) (v : Fin k → UTerm L μ) :
    encode (nrel r v) = Nat.pair 1 ((Nat.pair 0 $ 2 * k.pair $ (encode r).pair (encode v)).pair 0) := by
  simp[primcodable, Primcodable.ofEquiv_toEncodable,
    Encodable.encode_ofEquiv (equivW L μ), WType.encode_eq, WType.SubWType.ofW, WType.depth]
  have : (WType.depth (β := Edge L μ) (WType.mk (false, Sum.inl ⟨k, r, v⟩) Empty.elim)) = 1 := rfl
  rw[(WType.SubWType.encode_cast · this)]
  suffices : encode (WType.SubWType.ofWType (β := Edge L μ) ⟨(false, Sum.inl ⟨k, r, v⟩), Empty.elim⟩ 1 (by rw[this])) =
    ((Nat.pair 0 (2 * k.pair ((encode r).pair (encode v)))).pair 0)
  { rw[←this]; apply congr_arg; simp }
  simp[WType.SubWType.encode_mk, Encodable.encode_fintypeArrow_isEmpty, Edge]
  rw[encode_prod_val]

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

def relL (r : (k : ℕ) × L.rel k) (l : List (UTerm L μ)) : Option (UFormula L μ) :=
  if h : l.length = r.1
    then some (rel r.2 (fun i => l.get (i.cast h.symm)))
    else none

def nrelL (r : (k : ℕ) × L.rel k) (l : List (UTerm L μ)) : Option (UFormula L μ) :=
  if h : l.length = r.1
    then some (nrel r.2 (fun i => l.get (i.cast h.symm)))
    else none

lemma relL_primrec : Primrec₂ (relL : (k : ℕ) × L.rel k → List (UTerm L μ) → Option (UFormula L μ)) :=
  have : Primrec₂ (fun r l => if l.length = r.1
      then (Nat.pair 1 ((Nat.pair 1 $ 2 * r.1.pair $ (encode r.2).pair (encode l)).pair 0)) + 1 else 0
      : (k : ℕ) × L.rel k → List (UTerm L μ) → ℕ) :=
    to₂' <| Primrec.ite
      (Primrec.eq.comp (list_length.comp snd) (sigma_fst.comp fst))
      (succ.comp $ Primrec₂.natPair.comp (const 1) $
        Primrec₂.natPair.comp
          (Primrec₂.natPair.comp (const 1) $ nat_mul.comp (const 2) $
            Primrec₂.natPair.comp (sigma_fst.comp fst) (Primrec₂.natPair.comp (encode_of_uniform fst) $ Primrec.encode.comp snd))
          (const 0))
      (const 0)
  Primrec₂.encode_iff.mp <| this.of_eq <| by
    rintro ⟨k, r⟩ l
    by_cases hl : l.length = k <;> simp[hl, relL, primcodable, Primcodable.ofEquiv_toEncodable]
    { rcases hl with rfl
      simp[encode_rel, encode_finArrow, List.ofFn_get] }

lemma nrelL_primrec : Primrec₂ (nrelL : (k : ℕ) × L.rel k → List (UTerm L μ) → Option (UFormula L μ)) :=
  have : Primrec₂ (fun r l => if l.length = r.1
      then (Nat.pair 1 ((Nat.pair 0 $ 2 * r.1.pair $ (encode r.2).pair (encode l)).pair 0)) + 1 else 0
      : (k : ℕ) × L.rel k → List (UTerm L μ) → ℕ) :=
    to₂' <| Primrec.ite
      (Primrec.eq.comp (list_length.comp snd) (sigma_fst.comp fst))
      (succ.comp $ Primrec₂.natPair.comp (const 1) $
        Primrec₂.natPair.comp
          (Primrec₂.natPair.comp (const 0) $ nat_mul.comp (const 2) $
            Primrec₂.natPair.comp (sigma_fst.comp fst) (Primrec₂.natPair.comp (encode_of_uniform fst) $ Primrec.encode.comp snd))
          (const 0))
      (const 0)
  Primrec₂.encode_iff.mp <| this.of_eq <| by
    rintro ⟨k, r⟩ l
    by_cases hl : l.length = k <;> simp[hl, nrelL, primcodable, Primcodable.ofEquiv_toEncodable]
    { rcases hl with rfl
      simp[encode_nrel, encode_finArrow, List.ofFn_get] }

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

section elim_primrec

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

private lemma hF {σ γ} [Primcodable σ] [Primcodable γ] [Inhabited γ]
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
  (hEx : Primrec₂ γEx) : Primrec₂ (F γVerum γFalsum γRel γNrel γAnd γOr γAll γEx) :=
    sum_casesOn (snd.comp $ fst.comp snd)
      (Primrec.cond (fst.comp $ fst.comp $ snd.comp fst) (hRel.comp (fst.comp fst) snd) (hNrel.comp (fst.comp fst) snd))
      (sum_casesOn snd
        (to₂' <| Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp fst)
          (hVerum.comp $ fst.comp $ fst.comp fst)
          (hFalsum.comp $ fst.comp $ fst.comp fst))
        (to₂' <| sum_casesOn snd
          (to₂' <| Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp $ fst.comp fst)
            (hAnd.comp (fst.comp $ fst.comp $ fst.comp fst)
              (Primrec.pair (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))
                (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 1))))
            (hOr.comp (fst.comp $ fst.comp $ fst.comp fst)
              (Primrec.pair (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))
                (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 1)))))
          (to₂' <| Primrec.cond (fst.comp $ fst.comp $ snd.comp $ fst.comp $ fst.comp fst)
            (hAll.comp (fst.comp $ fst.comp $ fst.comp fst)
              (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0)))
            (hEx.comp (fst.comp $ fst.comp $ fst.comp fst)
              (list_getI.comp (snd.comp $ snd.comp $ fst.comp $ fst.comp fst) (Primrec.const 0))))))

lemma elim_primrec_param {σ γ} [Primcodable σ] [Primcodable γ] [Inhabited γ]
  {γVerum γFalsum : σ → γ}
  {γRel γNrel : σ → (k : ℕ) × L.rel k × (Fin k → UTerm L μ) → γ}
  {γAnd γOr : σ → γ × γ → γ}
  {γAll γEx : σ → γ → γ}
  {f : σ → UFormula L μ}
  (hVerum : Primrec γVerum)
  (hFalsum : Primrec γFalsum)
  (hRel : Primrec₂ γRel)
  (hNrel : Primrec₂ γNrel)
  (hAnd : Primrec₂ γAnd)
  (hOr : Primrec₂ γOr)
  (hAll : Primrec₂ γAll)
  (hEx : Primrec₂ γEx)
  (hf : Primrec f) :
    Primrec (fun x => elim (γVerum x) (γFalsum x)
      (fun {k} f v => γRel x ⟨k, f, v⟩)
      (fun {k} f v => γNrel x ⟨k, f, v⟩)
      (fun y₁ y₂ => γAnd x (y₁, y₂))
      (fun y₁ y₂ => γOr x (y₁, y₂))
      (γAll x)
      (γEx x)
      (f x)) :=
  (w_elimL_param (hF hVerum hFalsum hRel hNrel hAnd hOr hAll hEx) (Primrec.of_equiv.comp hf)).of_eq (fun _ => by simp[elim_eq])

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
    Primrec (elim γVerum γFalsum (fun {k} f v => γRel ⟨k, f, v⟩) (fun {k} f v => γNrel ⟨k, f, v⟩) γAnd γOr γAll γEx) :=
  elim_primrec_param
    (Primrec.const γVerum) (Primrec.const γFalsum)
    (hRel.comp₂ Primrec₂.right) (hNrel.comp₂ Primrec₂.right)
    (hAnd.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)) (hOr.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
    (hAll.comp₂ Primrec₂.right) (hEx.comp₂ Primrec₂.right) Primrec.id

end elim_primrec

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

lemma depth_primrec : Primrec (depth : UFormula L μ → ℕ) := by
  have := elim_primrec (L := L) (μ := μ) 0 0 (const 0) (const 0) (succ.comp₂ nat_max) (succ.comp₂ nat_max) succ succ
  exact this.of_eq <| fun p => by induction p <;> simp[elim, depth, *]

lemma neg_primrec : Primrec (neg : UFormula L μ → UFormula L μ) := by
  have := elim_primrec (L := L) (μ := μ) falsum verum nrel_primrec rel_primrec or_primrec and_primrec ex_primrec all_primrec
  exact this.of_eq <| fun p => by simp; induction p <;> simp[elim, neg, *]

def inversion : UFormula L μ → Node L μ × List (UFormula L μ)
  | verum    => ((true, Sum.inr $ Sum.inl ()), [])
  | falsum   => ((false, Sum.inr $ Sum.inl ()), [])
  | rel r v  => (((true, Sum.inl ⟨_, r, v⟩), []))
  | nrel r v => (((false, Sum.inl ⟨_, r, v⟩), []))
  | and p q  => (((true, Sum.inr $ Sum.inr $ Sum.inl ()), [p, q]))
  | or p q   => (((false, Sum.inr $ Sum.inr $ Sum.inl ()), [p, q]))
  | all p    => (((true, Sum.inr $ Sum.inr $ Sum.inr ()), [p]))
  | ex p     => (((false, Sum.inr $ Sum.inr $ Sum.inr ()), [p]))

lemma inversion_primrec : Primrec (inversion : UFormula L μ → Node L μ × List (UFormula L μ)) := by
  have : Primrec (fun x => ((WType.inversion (equivW L μ x)).1, (WType.inversion (equivW L μ x)).2.map (equivW L μ).symm)) :=
    Primrec₂.pair.comp (fst.comp $ w_inversion.comp of_equiv)
    <| list_map (snd.comp $ w_inversion.comp of_equiv) (of_equiv_symm.comp₂ Primrec₂.right)
  apply this.of_eq <| fun p => by
    cases p <;> simp[WType.inversion, inversion, toW_eq_equivW]
    case and => rw[fintypeEquivFin_symm_zero, fintypeEquivFin_symm_one]; simp
    case or => rw[fintypeEquivFin_symm_zero, fintypeEquivFin_symm_one]; simp
    case all => rw[fintypeArrowEquivFinArrow_eq]; simp
    case ex => rw[fintypeArrowEquivFinArrow_eq]; simp

section bind_primrec

variable {σ : Type*} {μ₁ : Type*} {μ₂ : Type*} [Primcodable μ₁] [Primcodable μ₂] [Primcodable σ]

private def bindqL : σ × ℕ × UFormula L μ₁ → List (σ × ℕ × UFormula L μ₁) :=
  fun (q : σ × ℕ × UFormula L μ₁) =>
  Sum.casesOn q.2.2.inversion.1.2 (fun _ => [])
  <| fun c => Sum.casesOn c (fun _ => [])
  <| fun c => Sum.casesOn c (fun _ => q.2.2.inversion.2.map (q.1, q.2.1, ·))
  <| fun _ => q.2.2.inversion.2.map (q.1, q.2.1 + 1, ·)

private def bindqG (b : σ → ℕ → UTerm L μ₂) (e : σ → μ₁ → UTerm L μ₂) :
    σ × ℕ × UFormula L μ₁ → List (UFormula L μ₂) → Option (UFormula L μ₂) :=
  fun (q : σ × ℕ × UFormula L μ₁) (l : List (UFormula L μ₂)) =>
  Sum.casesOn q.2.2.inversion.1.2
    (fun t => bif q.2.2.inversion.1.1
      then rel t.2.1 (fun i => (t.2.2 i).bind (shiftb (b q.1) q.2.1) (UTerm.bShifts q.2.1 $ e q.1 ·))
      else nrel t.2.1 (fun i => (t.2.2 i).bind (shiftb (b q.1) q.2.1) (UTerm.bShifts q.2.1 $ e q.1 ·)))
  <| fun c => Sum.casesOn c
    (fun _ => bif q.2.2.inversion.1.1 then some verum else some falsum)
  <| fun c => Sum.casesOn c
    (fun _ => bif q.2.2.inversion.1.1
      then ((l.get? 0).bind $ fun p => (l.get? 1).map $ fun q => and p q)
      else ((l.get? 0).bind $ fun p => (l.get? 1).map $ fun q => or p q))
  <| (fun _ => bif q.2.2.inversion.1.1
      then ((l.get? 0).map $ fun p => all p)
      else ((l.get? 0).map $ fun p => ex p))

private lemma bindqL_primrec : Primrec (bindqL : σ × ℕ × UFormula L μ₁ → List (σ × ℕ × UFormula L μ₁)) :=
  sum_casesOn
    (snd.comp $ fst.comp $ inversion_primrec.comp $ snd.comp snd)
    (Primrec₂.const [])
  <| to₂' <| sum_casesOn snd (Primrec₂.const [])
  <| to₂' <| sum_casesOn snd
    (to₂' <| list_map
      (snd.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp fst)
      (Primrec₂.pair.comp₂ (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ Primrec₂.left)
        (Primrec₂.pair.comp₂ (fst.comp₂ $ snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)
          Primrec₂.right)))
  <| to₂' <| list_map (snd.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp $ fst)
    (Primrec₂.pair.comp₂ (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)
      (Primrec₂.pair.comp₂ (succ.comp₂ $ fst.comp₂ $ snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)
        Primrec₂.right))

private lemma ofFn_dep_FinArrow_primrec :
    Primrec (fun (a : ((σ × ℕ × UFormula L μ₁) × List (UFormula L μ₂)) × Σ k, L.rel k × (Fin k → UTerm L μ₁)) =>
      List.ofFn a.2.2.2) :=
  have : Primrec (fun (a : ((σ × ℕ × UFormula L μ₁) × List (UFormula L μ₂)) × Σ k, L.rel k × (Fin k → UTerm L μ₁)) =>
      (encode a).unpair.2.unpair.2.unpair.2) :=
    (snd.comp $ unpair.comp $ snd.comp $ unpair.comp $ snd.comp $ unpair.comp Primrec.encode)
  (encode_iff.mp $ by
    simp[←encode_finArrow]
    exact this.of_eq <| by rintro ⟨⟨⟨x, m, p⟩, l⟩, ⟨k, r, v⟩⟩; simp)

private lemma relL_finArrow_primrec {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂}
  (hb : Primrec₂ b) (he : Primrec₂ e) :
    Primrec (fun (a : ((σ × ℕ × UFormula L μ₁) × List (UFormula L μ₂)) × Σ k, L.rel k × (Fin k → UTerm L μ₁)) =>
      relL ⟨a.2.1, a.2.2.1⟩
        ((List.ofFn a.2.2.2).map
          (fun t => t.bind (shiftb (b a.1.1.1) a.1.1.2.1)
          (fun x => (e a.1.1.1 x).bShifts a.1.1.2.1)))) :=
    relL_primrec.comp
      (sigma_prod_left.comp snd)
      (list_map
        ofFn_dep_FinArrow_primrec
        (to₂' <| by
          apply UTerm.bind_primrec_param
            (to₂ <| Primrec.ite
              (nat_lt.comp snd (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst))
              (UTerm.bvar_primrec.comp snd)
              (UTerm.bShifts_primrec.comp
                    (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
                    (hb.comp
                      (fst.comp $ fst.comp $ fst.comp $ fst.comp fst)
                      (nat_sub.comp snd (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)))))
            (by apply UTerm.bShifts_primrec.comp
                  (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
                  (he.comp (fst.comp $ fst.comp $ fst.comp $ fst.comp fst) snd))
            snd))

private lemma nrelL_finArrow_primrec {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂}
  (hb : Primrec₂ b) (he : Primrec₂ e) :
    Primrec (fun (a : ((σ × ℕ × UFormula L μ₁) × List (UFormula L μ₂)) × Σ k, L.rel k × (Fin k → UTerm L μ₁)) =>
      nrelL ⟨a.2.1, a.2.2.1⟩
        ((List.ofFn a.2.2.2).map
          (fun t => t.bind (shiftb (b a.1.1.1) a.1.1.2.1)
          (fun x => (e a.1.1.1 x).bShifts a.1.1.2.1)))) :=
    nrelL_primrec.comp
      (sigma_prod_left.comp snd)
      (list_map
        ofFn_dep_FinArrow_primrec
        (to₂' <| by
          apply UTerm.bind_primrec_param
            (to₂ <| Primrec.ite
              (nat_lt.comp snd (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst))
              (UTerm.bvar_primrec.comp snd)
              (UTerm.bShifts_primrec.comp
                    (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
                    (hb.comp
                      (fst.comp $ fst.comp $ fst.comp $ fst.comp fst)
                      (nat_sub.comp snd (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)))))
            (by apply UTerm.bShifts_primrec.comp
                  (fst.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
                  (he.comp (fst.comp $ fst.comp $ fst.comp $ fst.comp fst) snd))
            snd))

private lemma bindqG_primrec {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂}
  (hb : Primrec₂ b) (he : Primrec₂ e) : Primrec₂ (bindqG b e) :=
  to₂' <| sum_casesOn
    (snd.comp $ fst.comp $ inversion_primrec.comp $ snd.comp $ snd.comp fst)
    (to₂' <| Primrec.cond
      (fst.comp $ fst.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp fst)
      (option_some.comp $ option_some_iff.mp $
        (relL_finArrow_primrec hb he).of_eq <| by rintro ⟨⟨⟨x, m, p⟩, l⟩, ⟨k, r, v⟩⟩; simp[relL])
      (option_some.comp $ option_some_iff.mp $
        (nrelL_finArrow_primrec hb he).of_eq <| by rintro ⟨⟨⟨x, m, p⟩, l⟩, ⟨k, r, v⟩⟩; simp[nrelL]))
    <| to₂' <| sum_casesOn snd
      (to₂' <| Primrec.cond
        (fst.comp $ fst.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp fst)
        (Primrec.const _)
        (Primrec.const _))
    <| to₂' <| sum_casesOn snd
      (to₂' <| Primrec.cond
        (fst.comp $ fst.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
        (option_bind
          (list_get?.comp (snd.comp $ fst.comp $ fst.comp fst) (const 0))
          (to₂' <| option_map
            (list_get?.comp (snd.comp $ fst.comp $ fst.comp $ fst.comp fst) (const 1))
            (and_primrec.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right)))
        (option_bind
          (list_get?.comp (snd.comp $ fst.comp $ fst.comp fst) (const 0))
          (to₂' <| option_map
            (list_get?.comp (snd.comp $ fst.comp $ fst.comp $ fst.comp fst) (const 1))
            (or_primrec.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right))))
      <| to₂' <| Primrec.cond
        (fst.comp $ fst.comp $ inversion_primrec.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
        (option_map
          (list_get?.comp (snd.comp $ fst.comp $ fst.comp fst) (const 0))
          (all_primrec.comp₂ Primrec₂.right))
        (option_map
          (list_get?.comp (snd.comp $ fst.comp $ fst.comp fst) (const 0))
          (ex_primrec.comp₂ Primrec₂.right))

lemma bindq_param_primrec {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂} {k : σ → ℕ} {p : σ → UFormula L μ₁}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hk : Primrec k) (hp : Primrec p) : Primrec (fun x => bindq (b x) (e x) (k x) (p x)) :=
    have hm : Primrec (fun (q : σ × ℕ × UFormula L μ₁) => q.2.2.depth) := depth_primrec.comp (snd.comp snd)
    have hl : Primrec (bindqL : σ × ℕ × UFormula L μ₁ → List (σ × ℕ × UFormula L μ₁)) := bindqL_primrec
    have hg : Primrec₂ (bindqG b e : σ × ℕ × UFormula L μ₁ → List (UFormula L μ₂) → Option (UFormula L μ₂)) := bindqG_primrec hb he
    have := strong_rec (fun (q : σ × ℕ × UFormula L μ₁) => bindq (b q.1) (e q.1) q.2.1 q.2.2) hm hl hg
      (by rintro ⟨x₁, m₁, p₁⟩ ⟨x₂, m₂, p₂⟩; simp[bindqL]
          cases p₁ <;> simp[inversion]
          case and => rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp[depth, Nat.lt_succ]
          case or => rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> simp[depth, Nat.lt_succ]
          case all => rintro rfl rfl rfl; simp[depth]
          case ex => rintro rfl rfl rfl; simp[depth])
      (by rintro ⟨x, m, p⟩; simp[bindqL]
          cases p <;> simp[inversion, bindq, bindqG])
    this.comp (Primrec₂.pair.comp Primrec.id <| Primrec₂.pair.comp hk hp)

lemma bind_primrec_param {b : σ → ℕ → UTerm L μ₂} {e : σ → μ₁ → UTerm L μ₂} {p : σ → UFormula L μ₁}
  (hb : Primrec₂ b) (he : Primrec₂ e) (hp : Primrec p) : Primrec (fun x => bind (b x) (e x) (p x)) :=
  bindq_param_primrec hb he (const 0) hp

end bind_primrec

end UFormula

namespace SubFormula

open UTerm UFormula Encodable Primrec
variable {α : Type*} [Primcodable α]
variable [Primcodable μ] [(k : ℕ) → Primcodable (L.func k)] [UniformlyPrimcodable L.func]
  [(k : ℕ) → Primcodable (L.rel k)] [UniformlyPrimcodable L.rel]

instance : Primcodable (SubFormula L μ n) :=
  letI : Primcodable { p : UFormula L μ // p.bv ≤ n } := Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  Primcodable.ofEquiv { p : UFormula L μ // p.bv ≤ n } subfEquiv

--#eval (encode (“0 = 1” : Sentence Language.oRing))
-- 93531973427757887927355523491265632424463588852566233372338671710479397474730770600094675783961399010822739648767459911229822413
-- 38354554797976847185323277049196690332779272486724394009309057805393109481411677958756803998858368667348474517913440244843295506
-- 31775805419608027972015818561000739343253563007945350184910033971876879754597654645132096911041199614874696969038805225053580411
-- 215684158738776904337761136760151729990515106646661045385956293637

lemma rel_primrec :
    Primrec (fun p => rel p.2.1 p.2.2 : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → SubFormula L μ n) := by
  letI : ∀ n, Primcodable { t : UTerm L μ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have h : Primrec (fun f => ⟨f.1, f.2.1, (fun i => UTerm.subtEquiv (f.2.2 i))⟩
    : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → (k : ℕ) × L.rel k × (Fin k → UTerm L μ)) :=
    encode_iff.mp (Primrec.encode.of_eq <| by
      rintro ⟨k, r, v⟩; simp[Encodable.encode_prod_val r, encode_finArrow']
      funext i; exact encode_ofEquiv subtEquiv _)
  have : Primrec (fun f => UFormula.rel f.2.1 (fun i => UTerm.subtEquiv (f.2.2 i))
      : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → UFormula L μ) :=
    UFormula.rel_primrec.comp h
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    rintro ⟨k, r, v⟩; simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

lemma nrel_primrec :
    Primrec (fun p => nrel p.2.1 p.2.2 : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → SubFormula L μ n) := by
  letI : ∀ n, Primcodable { t : UTerm L μ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have h : Primrec (fun f => ⟨f.1, f.2.1, (fun i => UTerm.subtEquiv (f.2.2 i))⟩
    : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → (k : ℕ) × L.rel k × (Fin k → UTerm L μ)) :=
    encode_iff.mp (Primrec.encode.of_eq <| by
      rintro ⟨k, r, v⟩; simp[Encodable.encode_prod_val r, encode_finArrow']
      funext i; exact encode_ofEquiv subtEquiv _)
  have : Primrec (fun f => UFormula.nrel f.2.1 (fun i => UTerm.subtEquiv (f.2.2 i))
      : (k : ℕ) × L.rel k × (Fin k → SubTerm L μ n) → UFormula L μ) :=
    UFormula.nrel_primrec.comp h
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    rintro ⟨k, r, v⟩; simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

def relL (r : (k : ℕ) × L.rel k) (l : List (SubTerm L μ n)) : Option (SubFormula L μ n) :=
  if h : l.length = r.1
    then some (rel r.2 (fun i => l.get (i.cast h.symm)))
    else none

def nrelL (r : (k : ℕ) × L.rel k) (l : List (SubTerm L μ n)) : Option (SubFormula L μ n) :=
  if h : l.length = r.1
    then some (nrel r.2 (fun i => l.get (i.cast h.symm)))
    else none

lemma relL_primrec : Primrec₂ (relL : (Σ k, L.rel k) → List (SubTerm L μ n) → Option (SubFormula L μ n)) := by
  letI : ∀ n, Primcodable { t : UTerm L μ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have : Primrec₂ (fun f v => UFormula.relL f (v.map (UTerm.subtEquiv ·))
      : (k : ℕ) × L.rel k → List (SubTerm L μ n) → Option (UFormula L μ)) :=
    UFormula.relL_primrec.comp₂ Primrec₂.left (to₂' <| list_map snd (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.right))
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    rintro ⟨⟨k, f⟩, l⟩; simp[relL, UFormula.relL]
    by_cases hl : l.length = k <;> simp[hl]
    { simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]
      funext i; congr }

lemma nrelL_primrec : Primrec₂ (nrelL : (Σ k, L.rel k) → List (SubTerm L μ n) → Option (SubFormula L μ n)) := by
  letI : ∀ n, Primcodable { t : UTerm L μ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
  have : Primrec₂ (fun f v => UFormula.nrelL f (v.map (UTerm.subtEquiv ·))
      : (k : ℕ) × L.rel k → List (SubTerm L μ n) → Option (UFormula L μ)) :=
    UFormula.nrelL_primrec.comp₂ Primrec₂.left (to₂' <| list_map snd (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.right))
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    rintro ⟨⟨k, f⟩, l⟩; simp[nrelL, UFormula.nrelL]
    by_cases hl : l.length = k <;> simp[hl]
    { simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]
      funext i; congr }

lemma and_primrec : Primrec₂ (· ⋏ · : SubFormula L μ n → SubFormula L μ n → SubFormula L μ n) := by
  letI : ∀ n , Primcodable { p : UFormula L μ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  have : Primrec₂ (fun p q => UFormula.and (subfEquiv p) (subfEquiv q)
      : SubFormula L μ n → SubFormula L μ n → UFormula L μ) :=
    UFormula.and_primrec.comp₂
      (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.left)
      (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.right)
  exact Primrec₂.encode_iff.mp <| (Primrec.encode.comp₂ this).of_eq <| by
    intro p q
    simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

lemma or_primrec : Primrec₂ (· ⋎ · : SubFormula L μ n → SubFormula L μ n → SubFormula L μ n) := by
  letI : ∀ n , Primcodable { p : UFormula L μ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  have : Primrec₂ (fun p q => UFormula.or (subfEquiv p) (subfEquiv q)
      : SubFormula L μ n → SubFormula L μ n → UFormula L μ) :=
    UFormula.or_primrec.comp₂
      (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.left)
      (subtype_val.comp₂ $ of_equiv.comp₂ Primrec₂.right)
  exact Primrec₂.encode_iff.mp <| (Primrec.encode.comp₂ this).of_eq <| by
    intro p q
    simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

lemma all_primrec : Primrec (∀' · : SubFormula L μ (n + 1) → SubFormula L μ n) := by
  letI : ∀ n , Primcodable { p : UFormula L μ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  have : Primrec (fun p => UFormula.all (subfEquiv p) : SubFormula L μ (n + 1) → UFormula L μ) :=
    UFormula.all_primrec.comp (subtype_val.comp $ of_equiv)
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    intro p; simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

lemma ex_primrec : Primrec (∃' · : SubFormula L μ (n + 1) → SubFormula L μ n) := by
  letI : ∀ n , Primcodable { p : UFormula L μ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  have : Primrec (fun p => UFormula.ex (subfEquiv p) : SubFormula L μ (n + 1) → UFormula L μ) :=
    UFormula.ex_primrec.comp (subtype_val.comp $ of_equiv)
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    intro p; simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq]

private lemma subfEquiv_neg_eq_neg_subfEquiv (p : SubFormula L μ n) :
    (subfEquiv (~p)).val = UFormula.neg (subfEquiv p).val := by
  induction p using rec' <;> simp[UFormula.neg, UTerm.ofSubTerm_eq_subtEquiv, UFormula.ofSubFormula_eq_subfEquiv, *]

lemma neg_primrec : Primrec (~· : SubFormula L μ n → SubFormula L μ n) := by
  letI : ∀ n , Primcodable { p : UFormula L μ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
  have : Primrec (fun p => UFormula.neg (subfEquiv p) : SubFormula L μ n → UFormula L μ) :=
    UFormula.neg_primrec.comp (subtype_val.comp $ of_equiv)
  exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
    intro p; simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq, subfEquiv_neg_eq_neg_subfEquiv]

lemma imply_primrec : Primrec₂ (· ⟶ · : SubFormula L μ n → SubFormula L μ n → SubFormula L μ n) :=
  or_primrec.comp₂ (neg_primrec.comp₂ Primrec₂.left) Primrec₂.right

lemma bv_subtEquiv (p : SubFormula L μ n) : (subfEquiv p).val.bv ≤ n := by
  induction p <;> simp

lemma subfEquiv_bind_eq_bind (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    (subfEquiv (Rew.bindl b e p)).val =
    UFormula.bind (fun x => if hx : x < n₁ then subtEquiv (b ⟨x, hx⟩) else default) (fun x => subtEquiv $ e x) (subfEquiv p) := by
  induction p using rec' generalizing n₂ μ₂ e <;>
    simp[SubTerm.subtEquiv_bind_eq_bind, bindq, Rew.rel, Rew.nrel, UFormula.bind,
      ofSubTerm_eq_subtEquiv, ofSubFormula_eq_subfEquiv, *]
  case hall _ k p ih =>
    simp[Rew.q_bind, Rew.bindl, ih, bindq_eq_bind]
    apply UFormula.bind_eq_bind_of_eq
    · intro x hx; simp[shiftb]
      cases' x with x <;> simp[Nat.succ_eq_add_one]
      have : x < k := Nat.succ_lt_succ_iff.mp (lt_of_lt_of_le hx (bv_subtEquiv p))
      simp[this, SubTerm.subtEquiv_bShift_eq_bShift]
    · intro x; exact SubTerm.subtEquiv_bShift_eq_bShift (e x)
  case hex _ k p ih =>
    simp[Rew.q_bind, Rew.bindl, ih, bindq_eq_bind]
    apply UFormula.bind_eq_bind_of_eq
    · intro x hx; simp[shiftb]
      cases' x with x <;> simp[Nat.succ_eq_add_one]
      have : x < k := Nat.succ_lt_succ_iff.mp (lt_of_lt_of_le hx (bv_subtEquiv p))
      simp[this, SubTerm.subtEquiv_bShift_eq_bShift]
    · intro x; exact SubTerm.subtEquiv_bShift_eq_bShift (e x)

variable {σ : Type*} {μ₁ : Type*} {μ₂ : Type*} [Primcodable μ₁] [Primcodable μ₂] [Primcodable σ]

lemma bind_primrec {b : σ → Fin n₁ → SubTerm L μ₂ n₂} {e : σ → μ₁ → SubTerm L μ₂ n₂} {p : σ → SubFormula L μ₁ n₁}
  (hb : Primrec b) (he : Primrec₂ e) (hp : Primrec p) : Primrec (fun x => Rew.bindl (b x) (e x) (p x)) := by
    letI : ∀ n, Primcodable { t : UTerm L μ₁ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
    letI : ∀ n, Primcodable { t : UTerm L μ₂ // t.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp UTerm.bv_primrec (Primrec.const n))
    letI : ∀ n , Primcodable { p : UFormula L μ₁ // p.bv ≤ n } := fun n => Primcodable.subtype (nat_le.comp bv_primrec (Primrec.const n))
    have : Primrec (fun z =>
        UFormula.bind (fun x => if hx : x < n₁ then subtEquiv (b z ⟨x, hx⟩) else default)
          (fun x => subtEquiv $ e z x) (subfEquiv (p z))
        : σ → UFormula L μ₂) :=
      UFormula.bind_primrec_param (SubTerm.brew_primrec hb)
        (subtype_val.comp₂ $ of_equiv.comp₂ $ he.comp₂ Primrec₂.left Primrec₂.right)
        (subtype_val.comp $ of_equiv.comp hp)
    exact encode_iff.mp <| (Primrec.encode.comp this).of_eq <| by
      intro x
      simp[Encodable.encode_ofEquiv subfEquiv, Encodable.Subtype.encode_eq, subfEquiv_bind_eq_bind]

lemma substs_primrec :
    Primrec₂ (fun v p => Rew.substsl v p : (Fin n → SubTerm L μ n') → SubFormula L μ n → SubFormula L μ n') := by
  have : Primrec₂ (fun v p => Rew.bindl v (&·) p : (Fin n → SubTerm L μ n') → SubFormula L μ n → SubFormula L μ n') :=
    to₂' <| bind_primrec fst (SubTerm.fvar_primrec.comp snd) snd
  exact this.of_eq <| by { intro v p; unfold Rew.substsl; rw[Rew.eq_bind (Rew.substs v)]; simp[Function.comp] }

lemma substs₁_primrec :
    Primrec₂ (fun t p => Rew.substsl ![t] p : SubTerm L μ n' → SubFormula L μ 1 → SubFormula L μ n') :=
  substs_primrec.comp₂ (Primrec₂.encode_iff.mp $ 
    (Primrec.encode.comp₂ (list_cons.comp₂ Primrec₂.left (Primrec₂.const []))).of_eq
    <| by intro x _; simp[encode_finArrow]) Primrec₂.right

lemma shift_primrec : Primrec (Rew.shiftl : SyntacticSubFormula L n → SyntacticSubFormula L n) := by
  unfold Rew.shiftl; rw[Rew.eq_bind Rew.shift]
  exact bind_primrec (const _) (SubTerm.fvar_primrec.comp $ succ.comp snd) Primrec.id

lemma free_primrec : Primrec (Rew.freel : SyntacticSubFormula L (n + 1) → SyntacticSubFormula L n) := by
  unfold Rew.freel; rw[Rew.eq_bind Rew.free]
  exact bind_primrec (const _) (SubTerm.fvar_primrec.comp $ succ.comp snd) Primrec.id

lemma emb_primrec : Primrec (Rew.embl : Sentence L → Formula L μ) := by
  unfold Rew.embl; rw[Rew.eq_bind Rew.emb]; simp[Function.comp]
  exact bind_primrec (const _)
    (Primrec₂.option_some_iff.mp $ (Primrec₂.const none).of_eq <| by rintro _ ⟨⟩) Primrec.id



end SubFormula

end FirstOrder

end LO