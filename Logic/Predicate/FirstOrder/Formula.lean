import Logic.Predicate.Term

namespace FirstOrder

variable (L : Language.{u})

inductive SubFormula (μ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : SubFormula μ n
  | falsum {n} : SubFormula μ n
  | rel    {n} : ∀ {arity}, L.rel arity → (Fin arity → SubTerm L μ n) → SubFormula μ n
  | nrel   {n} : ∀ {arity}, L.rel arity → (Fin arity → SubTerm L μ n) → SubFormula μ n
  | and    {n} : SubFormula μ n → SubFormula μ n → SubFormula μ n
  | or     {n} : SubFormula μ n → SubFormula μ n → SubFormula μ n
  | all    {n} : SubFormula μ (n + 1) → SubFormula μ n
  | ex     {n} : SubFormula μ (n + 1) → SubFormula μ n

variable (μ : Type v) (μ₁ : Type v₁) (μ₂ : Type v₂) (μ₃ : Type v₃)

abbrev Formula := SubFormula L μ 0

abbrev Sentence := Formula L Empty

abbrev SyntacticSubFormula (n : ℕ) := SubFormula L ℕ n

abbrev SyntacticFormula := SyntacticSubFormula L 0

variable {L μ μ₁ μ₂ μ₃}

namespace SubFormula
variable {n n₁ n₂ : ℕ}

def neg {n} : SubFormula L μ n → SubFormula L μ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and p q  => or (neg p) (neg q)
  | or p q   => and (neg p) (neg q)
  | all p    => ex (neg p)
  | ex p     => all (neg p)

lemma neg_neg (p : SubFormula L μ n) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : HasLogicSymbols (SubFormula L μ n) where
  neg := neg
  arrow := fun p q => or (neg p) q
  and := and
  or := or
  top := verum
  bot := falsum

instance : HasUniv (SubFormula L μ) := ⟨all⟩
instance : HasEx (SubFormula L μ) := ⟨ex⟩

@[simp] lemma neg_top : ~(⊤ : SubFormula L μ n) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : SubFormula L μ n) = ⊤ := rfl

@[simp] lemma neg_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : ~(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : ~(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (p q : SubFormula L μ n) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

@[simp] lemma neg_or (p q : SubFormula L μ n) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

@[simp] lemma neg_all (p : SubFormula L μ (n + 1)) : ~(∀' p) = ∃' ~p := rfl

@[simp] lemma neg_ex (p : SubFormula L μ (n + 1)) : ~(∃' p) = ∀' ~p := rfl

@[simp] lemma neg_neg' (p : SubFormula L μ n) : ~~p = p := neg_neg p

@[simp] lemma neg_inj (p q : SubFormula L μ n) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (~·) h
  · exact congr_arg _

lemma neg_eq (p : SubFormula L μ n) : ~p = neg p := rfl

lemma imp_eq (p q : SubFormula L μ n) : p ⟶ q = ~p ⋎ q := rfl

lemma iff_eq (p q : SubFormula L μ n) : p ⟷ q = (~p ⋎ q) ⋏ (~q ⋎ p) := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : SubFormula L μ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[HasAnd.and]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : SubFormula L μ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[HasOr.or]

@[simp] lemma all_inj (p q : SubFormula L μ (n + 1)) : ∀' p = ∀' q ↔ p = q :=
  by simp[HasUniv.univ]

@[simp] lemma ex_inj (p q : SubFormula L μ (n + 1)) : ∃' p = ∃' q ↔ p = q :=
  by simp[HasEx.ex]

variable (L)

abbrev rel! (k) (r : L.rel k) (v : Fin k → SubTerm L μ n) := rel r v

abbrev nrel! (k) (r : L.rel k) (v : Fin k → SubTerm L μ n) := nrel r v

variable {L}

def complexity : {n : ℕ} → SubFormula L μ n → ℕ
| _, ⊤        => 0
| _, ⊥        => 0
| _, rel _ _  => 0
| _, nrel _ _ => 0
| _, p ⋏ q    => max p.complexity q.complexity + 1
| _, p ⋎ q    => max p.complexity q.complexity + 1
| _, ∀' p     => p.complexity + 1
| _, ∃' p     => p.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : SubFormula L μ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : SubFormula L μ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (p q : SubFormula L μ n) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : SubFormula L μ n) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : SubFormula L μ n) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : SubFormula L μ n) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_all (p : SubFormula L μ (n + 1)) : complexity (∀' p) = p.complexity + 1 := rfl
@[simp] lemma complexity_all' (p : SubFormula L μ (n + 1)) : complexity (all p) = p.complexity + 1 := rfl

@[simp] lemma complexity_ex (p : SubFormula L μ (n + 1)) : complexity (∃' p) = p.complexity + 1 := rfl
@[simp] lemma complexity_ex' (p : SubFormula L μ (n + 1)) : complexity (ex p) = p.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : ∀ n, SubFormula L μ n → Sort _}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : SubFormula L μ n), C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : SubFormula L μ n), C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C n (∃' p)) :
    ∀ {n : ℕ} (p : SubFormula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q
  | _, or p q   => hor p q
  | _, all p    => hall p
  | _, ex p     => hex p

@[elab_as_elim]
def rec' {C : ∀ n, SubFormula L μ n → Sort _}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n l : ℕ} (r : L.rel l) (v : Fin l → SubTerm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : SubFormula L μ n), C n p → C n q → C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : SubFormula L μ n), C n p → C n q → C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C (n + 1) p → C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : SubFormula L μ (n + 1)), C (n + 1) p → C n (∃' p)) :
    ∀ {n : ℕ} (p : SubFormula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, or p q   => hor p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, all p    => hall p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
  | _, ex p     => hex p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : ∀ {n}, SubFormula L μ n → String
  | _, ⊤                         => "\\top"
  | _, ⊥                         => "\\bot"
  | _, rel (arity := 0) r _      => "{" ++ toString r ++ "}"
  | _, rel (arity := _ + 1) r v  => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, nrel (arity := 0) r _     => "\\lnot {" ++ toString r ++ "}"
  | _, nrel (arity := _ + 1) r v => "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, p ⋏ q                     => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | _, p ⋎ q                     => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | _, @all _ _ n p              => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr p
  | _, @ex _ _ n p               => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr p

instance : Repr (SubFormula L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (SubFormula L μ n) := ⟨toStr⟩

end SubFormula

namespace SubFormula
variable {n n₁ n₂ n₃ m m₁ m₂ m₃ : ℕ}

@[simp] lemma complexity_neg (p : SubFormula L μ n) : complexity (~p) = complexity p :=
by induction p using rec' <;> simp[*]

@[reducible]
def bind' : ∀ {n₁ n₂}, (bound : Fin n₁ → SubTerm L μ₂ n₂) → (free : μ₁ → SubTerm L μ₂ n₂) →
    SubFormula L μ₁ n₁ → SubFormula L μ₂ n₂
  | _, _, _,     _,    ⊤          => ⊤
  | _, _, _,     _,    ⊥          => ⊥
  | _, _, bound, free, (rel r v)  => rel r (SubTerm.bind bound free ∘ v)
  | _, _, bound, free, (nrel r v) => nrel r (SubTerm.bind bound free ∘ v)
  | _, _, bound, free, (p ⋏ q)    => bind' bound free p ⋏ bind' bound free q
  | _, _, bound, free, (p ⋎ q)    => bind' bound free p ⋎ bind' bound free q
  | _, _, bound, free, (∀' p)     => ∀' bind' (Fin.cases #0 $ SubTerm.bShift ∘ bound) (SubTerm.bShift ∘ free) p
  | _, _, bound, free, (∃' p)     => ∃' bind' (Fin.cases #0 $ SubTerm.bShift ∘ bound) (SubTerm.bShift ∘ free) p

lemma bind'_neg {n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p) :
    bind' bound free (~p) = ~bind' bound free p :=
  by induction p using rec' generalizing n₂ <;> simp[*, bind', ←neg_eq]

def bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ where
  toFun := bind' bound free
  map_top' := by simp[bind']
  map_bot' := by simp[bind']
  map_and' := by simp[bind']
  map_or'  := by simp[bind']
  map_neg' := by simp[bind'_neg]
  map_imp' := by simp[imp_eq, bind'_neg, ←neg_eq, bind']

abbrev rewrite (f : μ₁ → SubTerm L μ₂ n) : SubFormula L μ₁ n →L SubFormula L μ₂ n := bind SubTerm.bvar f

def map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ :=
  bind (fun n => #(bound n)) (fun m => &(free m))

abbrev map₀ (free : μ₁ → μ₂) : SubFormula L μ₁ n →L SubFormula L μ₂ n := map id free

def substs {n'} (v : Fin n → SubTerm L μ n') : SubFormula L μ n →L SubFormula L μ n' :=
  bind v SubTerm.fvar

notation "⟦→ " v "⟧" => substs v
notation "⟦↦ " t "⟧" => substs ![t]

def emb {o : Type w} [h : IsEmpty o] : SubFormula L o n →L SubFormula L μ n := map id h.elim'

section bind
variable (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)

lemma bind_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind bound free (rel r v) = rel r (fun i => (v i).bind bound free) := rfl

lemma bind_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind bound free (nrel r v) = nrel r (fun i => (v i).bind bound free) := rfl

@[simp] lemma bind_all (p : SubFormula L μ₁ (n₁ + 1)) :
    bind bound free (∀' p) = ∀' bind (#0 :> SubTerm.bShift ∘ bound) (SubTerm.bShift ∘ free) p := rfl

@[simp] lemma bind_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    bind bound free (∃' p) = ∃' bind (#0 :> SubTerm.bShift ∘ bound) (SubTerm.bShift ∘ free) p := rfl

@[simp] lemma complexity_bind (p : SubFormula L μ₁ n₁) : complexity (bind bound free p) = complexity p :=
  by induction p using rec' generalizing μ₂ n₂ <;> simp[*, bind_rel, bind_nrel]

@[simp] lemma bind_id (p) : @bind L μ μ n n SubTerm.bvar SubTerm.fvar p = p :=
  by induction p using rec' <;> simp[*, bind_rel, bind_nrel]

@[simp] lemma eq_bind_of (bound : Fin n → SubTerm L μ n) (free : μ → SubTerm L μ n)
    (hbound : ∀ x, bound x = #x) (hfree : ∀ x, free x = &x) (p : SubFormula L μ n) :
    bind bound free p = p := by
  have : bound = SubTerm.bvar := funext hbound
  have : free = SubTerm.fvar := funext hfree
  simp[*]

end bind

lemma bind_bind
  (bound₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (bound₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) (p : SubFormula L μ₁ n₁) :
    bind bound₂ free₂ (bind bound₁ free₁ p) = bind (fun n => (bound₁ n).bind bound₂ free₂) (fun m => (free₁ m).bind bound₂ free₂) p := by
  induction p using rec' generalizing n₂ n₃ <;> simp[*, SubTerm.bind_bind, bind_rel, bind_nrel] <;>
  { congr
    refine funext (Fin.cases (by simp) (by simp[SubTerm.bShift, SubTerm.map, SubTerm.bind_bind]))
    refine funext (by simp[SubTerm.bShift, SubTerm.map, SubTerm.bind_bind]) }

lemma bind_comp_bind
  (bound₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (bound₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) :
    (bind bound₂ free₂).comp (bind bound₁ free₁) = bind (fun n => (bound₁ n).bind bound₂ free₂) (fun m => (free₁ m).bind bound₂ free₂) :=
  by ext p; simp[bind_bind]

section map
variable (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)

lemma map_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map bound free (rel r v) = rel r (fun i => (v i).map bound free) := rfl

lemma map_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map bound free (nrel r v) = nrel r (fun i => (v i).map bound free) := rfl

@[simp] lemma map_all (p : SubFormula L μ₁ (n₁ + 1)) :
    map bound free (∀' p) = ∀' map (0 :> Fin.succ ∘ bound) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma map_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    map bound free (∃' p) = ∃' map (0 :> Fin.succ ∘ bound) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma map_univClosure (free : μ₁ → μ₂) (p : SubFormula L μ₁ n) :
    map id free (univClosure p) = univClosure (map id (free) p) := by
  induction n <;> simp[*]

@[simp] lemma complexity_map (p : SubFormula L μ₁ n₁) : complexity (map bound free p) = complexity p :=
  complexity_bind _ _ _

end map

lemma map_map
  (bound₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (bound₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (p : SubFormula L μ₁ n₁) :
    map bound₂ free₂ (map bound₁ free₁ p) = map (bound₂ ∘ bound₁) (free₂ ∘ free₁) p :=
  bind_bind _ _ _ _ _

@[simp] lemma map_id (p) : @map L μ μ n n id id p = p :=
  bind_id _

lemma map_inj : ∀ {n₁ n₂ μ₁ μ₂} {bound : Fin n₁ → Fin n₂} {free : μ₁ → μ₂},
    (hb : Function.Injective bound) → (hf : Function.Injective free) → Function.Injective $ map (L := L) bound free
  | _, _, _, _, _,     _,    _,  _,  ⊤,        p => by cases p using cases' <;> simp[map_rel, map_nrel]
  | _, _, _, _, _,     _,    _,  _,  ⊥,        p => by cases p using cases' <;> simp[map_rel, map_nrel]
  | _, _, _, _, _,     _,    hb, hf, rel r v,  p => by
    cases p using cases' <;> simp[map_rel, map_nrel]
    case hrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact SubTerm.map_inj hb hf (congr_fun h i)
  | _, _, _, _, _,     _,    hb, hf, nrel r v, p => by
    cases p using cases' <;> simp[map_rel, map_nrel]
    case hnrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact SubTerm.map_inj hb hf (congr_fun h i)
  | _, _, _, _, _,     _,    hb, hf, p ⋏ q,    r => by
    cases r using cases' <;> simp[map_rel, map_nrel]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | _, _, _, _, _,     _,    hb, hf, p ⋎ q,    r => by
    cases r using cases' <;> simp[map_rel, map_nrel]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | _, _, _, _, bound, free, hb, hf, ∀' p,     q => by
    cases q using cases' <;> simp[map_rel, map_nrel]
    intro h; exact map_inj (bound := 0 :> Fin.succ ∘ bound)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h
  | _, _, _, _, bound, free, hb, hf, ∃' p,     q => by
    cases q using cases' <;> simp[map_rel, map_nrel]
    intro h; exact map_inj (bound := 0 :> Fin.succ ∘ bound)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h

section substs
variable {n' : ℕ} (w : Fin n → SubTerm L μ n')

@[simp] lemma substs_rel_zero (w : Fin 0 → SubTerm L μ 0) (p : SubFormula L μ 0):
    substs w p = p := by simp[substs]

lemma substs_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    substs w (rel r v) = rel r (fun i => SubTerm.substs w (v i)) :=
  by simp[substs, SubTerm.substs, bind_rel]

@[simp] lemma substs_rel₀ (r : L.rel 0) :
    substs w (rel r ![]) = rel r ![] :=
  by simp[substs_rel]

@[simp] lemma substs_rel₁ (r : L.rel 1) (t : SubTerm L μ n) :
    substs w (rel r ![t]) = rel r ![SubTerm.substs w t] :=
  by simp[Matrix.constant_eq_singleton, substs_rel]

@[simp] lemma substs_rel₂ (r : L.rel 2) (t₁ t₂ : SubTerm L μ n) :
    substs w (rel r ![t₁, t₂]) = rel r ![SubTerm.substs w t₁, SubTerm.substs w t₂] :=
  by simp[substs_rel]; funext i; induction i using Fin.induction <;> simp

lemma substs_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    substs w (nrel r v) = nrel r (fun i => SubTerm.substs w (v i)) :=
  by simp[substs, SubTerm.substs, bind_nrel]

@[simp] lemma substs_nrel₀ (r : L.rel 0) :
    substs w (nrel r ![]) = nrel r ![] :=
  by simp[substs_nrel]

@[simp] lemma substs_nrel₁ (r : L.rel 1) (t : SubTerm L μ n) :
    substs w (nrel r ![t]) = nrel r ![SubTerm.substs w t] :=
  by simp[Matrix.constant_eq_singleton, substs_nrel]

@[simp] lemma substs_nrel₂ (r : L.rel 2) (t₁ t₂ : SubTerm L μ n) :
    substs w (nrel r ![t₁, t₂]) = nrel r ![SubTerm.substs w t₁, SubTerm.substs w t₂] :=
  by simp[substs_nrel]; funext i; induction i using Fin.induction <;> simp

lemma substs_all {n'} (w : Fin n → SyntacticSubTerm L n') (p : SyntacticSubFormula L (n + 1)) :
    substs w (∀' p) = ∀' (substs (#0 :> SubTerm.bShift ∘ w) p) := by
  simp[substs, bind_bind]

lemma substs_ex {n'} (w : Fin n → SyntacticSubTerm L n') (p : SyntacticSubFormula L (n + 1)) :
    substs w (∃' p) = ∃' (substs (#0 :> SubTerm.bShift ∘ w) p) := by
  simp[substs, bind_bind]

lemma substs_substs {n₁ n₂ n₃} (w : Fin n₂ → SubTerm L μ n₃) (v : Fin n₁ → SubTerm L μ n₂) (p : SubFormula L μ n₁) :
    ⟦→ w⟧ (⟦→ v⟧ p) = ⟦→ SubTerm.substs w ∘ v⟧ p := by simp[substs, bind_bind]; congr

@[simp] lemma complexity_substs {k} (w : Fin k → SyntacticSubTerm L n) (p : SyntacticSubFormula L k) :
  (⟦→ w⟧ p).complexity = p.complexity := by simp[substs]

end substs

section emb
variable (o : Type v) [empty : IsEmpty o]

lemma emb_rel {k} (r : L.rel k) (v : Fin k → SubTerm L o n) :
    emb (μ := μ) (rel r v) = rel r (fun i => (v i).emb) :=
  by simp[emb, map_rel, SubTerm.emb]

@[simp] lemma emb_rel₀ (r : L.rel 0) :
    emb (μ := μ) (n := n) (rel (μ := o) r ![]) = rel r ![] :=
  by simp[emb_rel]

@[simp] lemma emb_rel₁ (r : L.rel 1) (t : SubTerm L o n) :
    emb (μ := μ) (n := n) (rel r ![t]) = rel r ![t.emb] :=
  by simp[Matrix.constant_eq_singleton, emb_rel]

@[simp] lemma emb_rel₂ (r : L.rel 2) (t₁ t₂ : SubTerm L o n) :
    emb (μ := μ) (n := n) (rel r ![t₁, t₂]) = rel r ![t₁.emb, t₂.emb] :=
  by simp[emb_rel]; funext i; induction i using Fin.induction <;> simp

lemma emb_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L o n) :
    emb (μ := μ) (nrel r v) = nrel r (fun i => (v i).emb) :=
  by simp[emb, map_nrel, SubTerm.emb]

@[simp] lemma emb_nrel₀ (r : L.rel 0) :
    emb (μ := μ) (n := n) (nrel (μ := o) r ![]) = nrel r ![] :=
  by simp[emb_nrel]

@[simp] lemma emb_nrel₁ (r : L.rel 1) (t : SubTerm L o n) :
    emb (μ := μ) (n := n) (nrel r ![t]) = nrel r ![t.emb] :=
  by simp[Matrix.constant_eq_singleton, emb_nrel]

@[simp] lemma emb_nrel₂ (r : L.rel 2) (t₁ t₂ : SubTerm L o n) :
    emb (μ := μ) (n := n) (nrel r ![t₁, t₂]) = nrel r ![t₁.emb, t₂.emb] :=
  by simp[emb_nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma emb_all (p : SubFormula L o (n + 1)) :
    emb (μ := μ) (∀' p) = ∀' emb p :=
  by simp[emb]

@[simp] lemma emb_ex (p : SubFormula L o (n + 1)) :
    emb (μ := μ) (∃' p) = ∃' emb p :=
  by simp[emb]

@[simp] lemma emb_univClosure {o : Type v} [IsEmpty o] (p : SubFormula L o n) :
    emb (μ := μ) (univClosure p) = univClosure (emb p) := by
  simp[emb]

end emb

section Syntactic

def shift : SyntacticSubFormula L n →L SyntacticSubFormula L n :=
  map id Nat.succ

def free : SyntacticSubFormula L (n + 1) →L SyntacticSubFormula L n :=
  bind (SubTerm.bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticSubFormula L n →L SyntacticSubFormula L (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ SubTerm.fvar)

section shift

lemma shift_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (rel r v) = rel r (fun i => SubTerm.shift $ v i) := rfl

@[simp] lemma shift_rel₀ (r : L.rel 0) :
    shift (rel (n := n) r ![]) = rel r ![] := by simp[shift_rel]

@[simp] lemma shift_rel₁ (r : L.rel 1) (t : SyntacticSubTerm L n) :
    shift (rel (n := n) r ![t]) = rel r ![t.shift] := by
  simp[Matrix.constant_eq_singleton, shift_rel]

@[simp] lemma shift_rel₂ (r : L.rel 2) (t₁ t₂ : SyntacticSubTerm L n) :
    shift (rel (n := n) r ![t₁, t₂]) = rel r ![t₁.shift, t₂.shift] := by
  simp[shift_rel]; funext i; induction i using Fin.induction <;> simp

lemma shift_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (nrel r v) = nrel r (fun i => SubTerm.shift $ v i) := rfl

@[simp] lemma shift_nrel₀ (r : L.rel 0) :
    shift (nrel (n := n) r ![]) = nrel r ![] := by simp[shift_nrel]

@[simp] lemma shift_nrel₁ (r : L.rel 1) (t : SyntacticSubTerm L n) :
    shift (nrel (n := n) r ![t]) = nrel r ![t.shift] := by
  simp[Matrix.constant_eq_singleton, shift_nrel]

@[simp] lemma shift_nrel₂ (r : L.rel 2) (t₁ t₂ : SyntacticSubTerm L n) :
    shift (nrel (n := n) r ![t₁, t₂]) = nrel r ![t₁.shift, t₂.shift] := by
  simp[shift_nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma shift_all (p : SyntacticSubFormula L (n + 1)) :
    shift (∀' p) = ∀' shift p  := by simp[shift]

@[simp] lemma shift_ex (p : SyntacticSubFormula L (n + 1)) :
    shift (∃' p) = ∃' shift p  := by simp[shift]

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[shift, map_map, Function.comp]; exact map_id _)

def shiftEmb : SyntacticSubFormula L n ↪ SyntacticSubFormula L n where
  toFun := shift
  inj' := shift_Injective

lemma shiftEmb_eq_shift (p : SyntacticSubFormula L n) :
  shiftEmb p = shift p := rfl

lemma shift_substs (w : Fin k → SyntacticSubTerm L n) (p : SyntacticSubFormula L k) :
    shift (substs w p) = substs (SubTerm.shift ∘ w) (shift p) :=
  by simp[shift, substs, map, bind_bind]; congr

lemma shift_substs1 (t : SyntacticSubTerm L n) (p : SyntacticSubFormula L 1) :
    shift (substs ![t] p) = substs ![t.shift] (shift p) :=
  by simp[shift_substs, Function.comp, Matrix.constant_eq_singleton]

@[simp] lemma shift_emb {o : Type v} [h : IsEmpty o] (p : SubFormula L o n) :
    shift (emb p : SyntacticSubFormula L n) = emb p := by
  simp[shift, emb, map_map]; congr; funext x; exact h.elim x

@[simp] lemma complexity_shift (p : SyntacticSubFormula L n) :
    complexity (shift p) = complexity p :=
  by simp[shift]

end shift

section free

lemma free_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    free (rel r v) = rel r (fun i => SubTerm.free $ v i) := rfl

lemma free_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L (n + 1)) :
    free (nrel r v) = nrel r (fun i => SubTerm.free $ v i) := rfl

@[simp] lemma free_all (p : SyntacticSubFormula L (n + 1 + 1)) :
    free (∀' p) = ∀' free p  := by
  simp[free]; congr; exact funext (Fin.cases (by simp) (Fin.lastCases (by simp) (by simp; simp[Fin.succ_castSucc])))

@[simp] lemma free_ex (p : SyntacticSubFormula L (n + 1 + 1)) :
    free (∃' p) = ∃' free p  := by
  simp[free]; congr; exact funext (Fin.cases (by simp) (Fin.lastCases (by simp) (by simp; simp[Fin.succ_castSucc])))

@[simp] lemma complexity_free (p : SyntacticSubFormula L (n + 1)) :
    complexity (free p) = complexity p :=
  by simp[free]

end free

section fix

lemma fix_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    fix (rel r v) = rel r (fun i => SubTerm.fix $ v i) := rfl

lemma fix_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    fix (nrel r v) = nrel r (fun i => SubTerm.fix $ v i) := rfl

@[simp] lemma fix_all (p : SyntacticSubFormula L (n + 1)) :
    fix (∀' p) = ∀' fix p := by
  simp[fix]; congr
  · exact funext (Fin.cases (by simp) (by simp[Fin.succ_castSucc])) 
  · exact funext (Nat.rec (by simp) (by simp))

@[simp] lemma fix_ex (p : SyntacticSubFormula L (n + 1)) :
    fix (∃' p) = ∃' fix p := by
  simp[fix]; congr
  · exact funext (Fin.cases (by simp) (by simp[Fin.succ_castSucc])) 
  · exact funext (Nat.rec (by simp) (by simp))

end fix

@[simp] lemma free_fix (p : SyntacticSubFormula L n) : free (fix p) = p :=
  by simp[fix, free, bind_bind]; apply eq_bind_of <;> simp; intros x; cases x <;> simp

@[simp] lemma fix_free (p : SyntacticSubFormula L (n + 1)) : fix (free p) = p :=
  by
  simp[fix, free, bind_bind]; apply eq_bind_of <;> simp
  intros x; exact Fin.lastCases (by simp) (by simp) x

lemma rewrite_free_eq_substs (p : SyntacticSubFormula L 1) (t : SyntacticTerm L) :
    rewrite (t :>ₙ SubTerm.fvar) (free p) = ⟦↦ t⟧ p :=
  by simp[substs, free, bind_bind, Matrix.vecConsLast_vecEmpty, Matrix.constant_eq_singleton] 

lemma rewrite_shift_eq_self (p : SyntacticFormula L) (t : SyntacticTerm L) :
    rewrite (t :>ₙ SubTerm.fvar) (shift p) = p :=
  by simp[shift, map, bind_bind]

@[simp] lemma substs_shift_eq_free (p : SyntacticSubFormula L 1) : ⟦↦ &0⟧ (shift p) = free p :=
  by simp[substs, shift, free, map, bind_bind, Matrix.constant_eq_singleton, Matrix.vecConsLast_vecEmpty]

lemma free_substs_eq_substs_shift {n'} (w : Fin n' → SyntacticSubTerm L (n + 1)) (p : SyntacticSubFormula L n') :
    free (substs w p) = substs (fun i => (w i).free) (shift p) :=
  by simp[free, substs, shift, map, bind_bind, SubTerm.shift, SubTerm.map, SubTerm.free, SubTerm.bind_bind]

lemma substs_eq_subst1 (w : Fin (n + 1) → SyntacticTerm L) (p : SyntacticSubFormula L (n + 1)) :
    substs w p = ⟦↦ w (Fin.last n)⟧ (fix $ substs (SubTerm.shift ∘ w ∘ Fin.castSucc) $ free p) := by
  simp[substs, substs, free, fix, bind_bind]; congr
  funext x; cases x using Fin.lastCases <;> simp[shift, map, bind_bind, SubTerm.shift, SubTerm.map, SubTerm.bind_bind]

lemma free_substs {n'} (w : Fin n → SyntacticSubTerm L (n' + 1)) (p : SyntacticSubFormula L n) :
    free (substs w p) = substs (SubTerm.free ∘ w) (shift p) := by
  simp[free, substs, shift, map, bind_bind]; congr

variable (L)

structure Operator (ι : Type w) where
  operator : {μ : Type v} → {n : ℕ} → (ι → SubTerm L μ n) → SubFormula L μ n
  bind_operator : ∀ {μ₁ μ₂ n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (v : ι → SubTerm L μ₁ n₁),
    bind bound free (operator v) = operator (fun i => SubTerm.bind bound free (v i))

abbrev Finitary (n : ℕ) := Operator L (Fin n)

abbrev OperatorMatrix (ι : Type w) (I : ι → Type w') := Operator L ((i : ι ) × I i)

variable {L}

namespace Operator
variable {ι : Type w} {ι₁ : Type w₁} {ι₂ : Type w₂}

section

variable (o : Operator L ι)

lemma map_operator {μ₁ μ₂ : Type v} {n₁ n₂} (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)
  (v : ι → SubTerm L μ₁ n₁) :
    map bound free (o.operator v) = o.operator (fun i => SubTerm.map bound free (v i)) := o.bind_operator _ _ _

lemma substs_operator (w : Fin n → SubTerm L μ n) (v : ι → SubTerm L μ n) :
    substs w (o.operator v) = o.operator (fun i => SubTerm.substs w (v i)) := o.bind_operator _ _ _

lemma emb_operator {ν : Type v} [IsEmpty ν] (v : ι → SubTerm L ν n) :
    emb (μ := μ) (o.operator v) = o.operator (fun i => SubTerm.emb (v i)) := o.bind_operator _ _ _

lemma shift_operator (v : ι → SyntacticSubTerm L n) :
    shift (o.operator v) = o.operator (fun i => SubTerm.shift (v i)) := o.bind_operator _ _ _

lemma free_operator (v : ι → SyntacticSubTerm L (n + 1)) :
    free (o.operator v) = o.operator (fun i => SubTerm.free (v i)) := o.bind_operator _ _ _

lemma fix_operator (v : ι → SyntacticSubTerm L n) :
    fix (o.operator v) = o.operator (fun i => SubTerm.fix (v i)) := o.bind_operator _ _ _

end

section
variable (o : Finitary L 1)

@[simp] lemma substs_operator₁ (w : Fin n → SubTerm L μ n) (t : SubTerm L μ n) :
    substs w (o.operator ![t]) = o.operator ![SubTerm.substs w t] :=
  by simp[Matrix.constant_eq_singleton, substs_operator]

@[simp] lemma emb_operator₁ {ν : Type v} [IsEmpty ν] (t : SubTerm L ν n) :
    emb (μ := μ) (o.operator ![t]) = o.operator ![t.emb] :=
  by simp[Matrix.constant_eq_singleton, emb_operator]

@[simp] lemma shift_operator₁ (t : SyntacticSubTerm L n) :
    shift (o.operator ![t]) = o.operator ![t.shift] :=
  by simp[Matrix.constant_eq_singleton, shift_operator]

@[simp] lemma free_operator₁ (t : SyntacticSubTerm L (n + 1)) :
    free (o.operator ![t]) = o.operator ![t.free] :=
  by simp[Matrix.constant_eq_singleton, free_operator]

end

section
variable (o : Finitary L 2)

@[simp] lemma substs_operator₂ (w : Fin n → SubTerm L μ n) (t₁ t₂ : SubTerm L μ n) :
    substs w (o.operator ![t₁, t₂]) = o.operator ![SubTerm.substs w t₁, SubTerm.substs w t₂] :=
  by simp[substs_operator]; congr; funext i; induction i using Fin.induction <;> simp

@[simp] lemma emb_operator₂ {ν : Type v} [IsEmpty ν] (t₁ t₂ : SubTerm L ν n) :
    emb (μ := μ) (o.operator ![t₁, t₂]) = o.operator ![t₁.emb, t₂.emb] :=
  by simp[emb_operator]; congr; funext i; induction i using Fin.induction <;> simp

@[simp] lemma shift_operator₂ (t₁ t₂ : SyntacticSubTerm L n) :
    shift (o.operator ![t₁, t₂]) = o.operator ![t₁.shift, t₂.shift] :=
  by simp[shift_operator]; congr; funext i; induction i using Fin.induction <;> simp

@[simp] lemma free_operator₂ (t₁ t₂ : SyntacticSubTerm L (n + 1)) :
    free (o.operator ![t₁, t₂]) = o.operator ![t₁.free, t₂.free] :=
  by simp[free_operator]; congr; funext i; induction i using Fin.induction <;> simp

end

section OperatorMatrix
variable {ι : Type w} {I : ι → Type w'} (o : OperatorMatrix L ι I)

def operatorMatrix {μ : Type v} {n : ℕ} (v : (i : ι) → I i → SubTerm L μ n) : SubFormula L μ n :=
  o.operator (Sigma.uncurry v)

lemma bind_operatorMatrix {μ₁ μ₂ n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)
    (v : (i : ι) → I i → SubTerm L μ₁ n₁) :
    bind bound free (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.bind bound free (v i j)) :=
  by simp[operatorMatrix, o.bind_operator bound free (Sigma.uncurry v)]; congr

def mkMatrix (operatorMatrix : {μ : Type v} → {n : ℕ} → ((i : ι) → I i → SubTerm L μ n) → SubFormula L μ n)
  (bind_operatorMatrix : ∀ {μ₁ μ₂ n₁ n₂} (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)
    (v : (i : ι) → I i → SubTerm L μ₁ n₁),
    bind bound free (operatorMatrix v) = operatorMatrix fun i j => SubTerm.bind bound free (v i j)) :
    OperatorMatrix L ι I where
  operator := fun v => operatorMatrix (Sigma.curry v)
  bind_operator := fun bound free v => bind_operatorMatrix bound free (Sigma.curry v)

@[simp] lemma mkMatrix_operatorMatrix
  (operatorMatrix : {μ : Type v} → {n : ℕ} → ((i : ι) → I i → SubTerm L μ n) → SubFormula L μ n) {bind_operatorMatrix}
  (v : (i : ι) → I i → SubTerm L μ n) :
  (mkMatrix operatorMatix bind_operatorMatrix).operatorMatrix v = operatorMatix v := rfl

section

lemma map_operatorMatrix {μ₁ μ₂ : Type v} {n₁ n₂} (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)
  (v : (i : ι) → I i → SubTerm L μ₁ n₁) :
    map bound free (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.map bound free (v i j)) :=
  o.bind_operatorMatrix _ _ _

lemma substs_operatorMatrix (w : Fin n → SubTerm L μ n) (v : (i : ι) → I i → SubTerm L μ n) :
    substs w (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.substs w (v i j)) :=
  o.bind_operatorMatrix _ _ _

lemma emb_operatorMatrix {ν : Type v} [IsEmpty ν] (v : (i : ι) → I i → SubTerm L ν n) :
    emb (μ := μ) (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.emb (v i j)) :=
  o.bind_operatorMatrix _ _ _

lemma shift_operatorMatrix (v : (i : ι) → I i → SyntacticSubTerm L n) :
    shift (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.shift (v i j)) :=
  o.bind_operatorMatrix _ _ _

lemma free_operatorMatrix (v : (i : ι) → I i → SyntacticSubTerm L (n + 1)) :
    free (o.operatorMatrix v) = o.operatorMatrix (fun i j => SubTerm.free (v i j)) :=
  o.bind_operatorMatrix _ _ _

end

end OperatorMatrix

end Operator

@[elab_as_elim]
def formulaRec {C : SyntacticFormula L → Sort _}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hrel    : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (rel r v))
  (hnrel   : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (nrel r v))
  (hand    : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋎ q))
  (hall    : ∀ (p : SyntacticSubFormula L 1), C (free p) → C (∀' p))
  (hex     : ∀ (p : SyntacticSubFormula L 1), C (free p) → C (∃' p)) :
    ∀ (p : SyntacticFormula L), C p
  | ⊤        => hverum
  | ⊥        => hfalsum
  | rel r v  => hrel r v
  | nrel r v => hnrel r v
  | p ⋏ q    => hand p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | p ⋎ q    => hor p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | ∀' p     => hall p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (free p))
  | ∃' p     => hex p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (free p))
  termination_by formulaRec _ _ _ _ _ _ _ _ p => p.complexity

end Syntactic

def fvarList : {n : ℕ} → SubFormula L μ n → List μ
  | _, ⊤        => []
  | _, ⊥        => []
  | _, rel _ v  => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, nrel _ v => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, p ⋏ q    => p.fvarList ++ q.fvarList
  | _, p ⋎ q    => p.fvarList ++ q.fvarList
  | _, ∀' p     => p.fvarList
  | _, ∃' p     => p.fvarList

abbrev fvar? (p : SubFormula L μ n) (x : μ) : Prop := x ∈ p.fvarList

lemma bind_eq_of_funEqOn (bound : Fin n₁ → SubTerm L μ₂ n₂) (free₁ free₂ : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁)
  (h : Function.funEqOn (fvar? p) free₁ free₂) :
    bind bound free₁ p = bind bound free₂ p := by
  induction p using rec' generalizing n₂ <;> simp[*, bind_rel, bind_nrel] <;> simp[fvar?, fvarList] at h
  case hrel =>
    funext i
    exact SubTerm.bind_eq_of_funEqOn _ _ _ _ (h.of_subset (by simp[fvarList]; intro x hx; exact ⟨i, hx⟩))
  case hnrel =>
    funext i
    exact SubTerm.bind_eq_of_funEqOn _ _ _ _ (h.of_subset (by simp[fvarList]; intro x hx; exact ⟨i, hx⟩))
  case hand ihp ihq =>
    exact ⟨ihp _ _ _ (h.of_subset (fun x hx => Or.inl hx)), ihq _ _ _ (h.of_subset (fun x hx => Or.inr hx))⟩
  case hor ihp ihq =>
    exact ⟨ihp _ _ _ (h.of_subset (fun x hx => Or.inl hx)), ihq _ _ _ (h.of_subset (fun x hx => Or.inr hx))⟩
  case hall ih =>
    exact ih _ _ _ (by intro x hx; simp[h x hx])
  case hex ih =>
    exact ih _ _ _ (by intro x hx; simp[h x hx])

def upper (p : SyntacticSubFormula L n) : ℕ := Finset.sup p.fvarList.toFinset id + 1

example (n : ℕ) : ¬n < n := irrefl_of _ _

lemma not_fvar?_of_lt_upper (p : SyntacticSubFormula L n) (h : p.upper ≤ m) : ¬fvar? p m := by
  simp[upper, Nat.add_one_le_iff, fvar?] at h ⊢
  intro hm
  have : m ≤ Finset.sup p.fvarList.toFinset id :=
    Finset.le_sup (s := p.fvarList.toFinset) (b := m) (f := id) (by simpa using hm)
  exact irrefl_of _ _ $ lt_of_lt_of_le h this

@[simp] lemma not_fvar?_upper (p : SyntacticSubFormula L n) : ¬fvar? p p.upper :=
  not_fvar?_of_lt_upper p (by simp)

lemma bind_eq_of_funEqOn' {bound₁ bound₂ : Fin n → SubTerm L μ n} {free₁ free₂ : μ → SubTerm L μ n} (p : SubFormula L μ n)
  (hbound : bound₁ = bound₂)
  (hfree : Function.funEqOn (fvar? p) free₁ free₂) :
    bind bound₁ free₁ p = bind bound₂ free₂ p := by
  rw[hbound]; exact bind_eq_of_funEqOn _ _ _ _ hfree

lemma ne_of_ne_complexity {p q : SubFormula L μ n} (h : p.complexity ≠ q.complexity) : p ≠ q :=
  by rintro rfl; contradiction

@[simp] lemma ex_ne_subst (p : SubFormula L μ 1) (t) : ⟦↦ t⟧ p ≠ ∃' p := ne_of_ne_complexity (by simp[substs])

@[simp] lemma ne_or_left (p q : SubFormula L μ n) : p ≠ p ⋎ q := ne_of_ne_complexity (by simp)

@[simp] lemma ne_or_right (p q : SubFormula L μ n) : q ≠ p ⋎ q := ne_of_ne_complexity (by simp)

inductive Open : {n : ℕ} → SubFormula L μ n → Prop
  | verum                      : Open ⊤
  | falsum                     : Open ⊥
  | rel {k} (r : L.rel k) (v)  : Open (rel r v)
  | nrel {k} (r : L.rel k) (v) : Open (nrel r v)
  | and {p q : SubFormula L μ n}   : Open p → Open q → Open (p ⋏ q)
  | or {p q : SubFormula L μ n}    : Open p → Open q → Open (p ⋎ q)

attribute [simp] Open.verum Open.falsum Open.rel Open.nrel

end SubFormula

abbrev Theory (L : Language) := Set (Sentence L)

class SubTheory (T U : Theory L) where
  sub : T ⊆ U

namespace SubTheory

variable {T U T₁ T₂ T₃ : Theory L}

instance : SubTheory T T := ⟨by rfl⟩

def trans [SubTheory T₁ T₂] [SubTheory T₂ T₃] : SubTheory T₁ T₃ := ⟨subset_trans (sub (T := T₁) (U := T₂)) sub⟩

end SubTheory

namespace SubFormula

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [DecidableEq μ]

def hasDecEq : (p q : SubFormula L μ n) → Decidable (p = q)
  | ⊤,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊥,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | rel r v,  q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | nrel r v, q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | p ⋏ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | p ⋎ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | ∀' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hall p' => simp; exact hasDecEq p p'
  | ∃' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hex p' => simp; exact hasDecEq p p'

instance : DecidableEq (SubFormula L μ n) := hasDecEq


declare_syntax_cat subformula
syntax "⊤" : subformula
syntax "⊥" : subformula
syntax:45 subterm:45 " = " subterm:0 : subformula
syntax:45 subterm:45 " ≠ " subterm:0 : subformula
syntax:45 subterm:45 " < " subterm:0 : subformula
syntax:45 subterm:45 " ≮ " subterm:0 : subformula
syntax:45 "[" term "](" subterm,* ")" : subformula
syntax:max "¬" subformula:35 : subformula
syntax:32 subformula:32 " ∧ " subformula:33 : subformula
syntax:32 "⋀ " ident ", " subformula : subformula
syntax:30 subformula:30 " ∨ " subformula:31 : subformula
syntax:max "∀ " subformula:35 : subformula
syntax:max "∃ " subformula:35 : subformula
syntax:25 "∀* " subformula:24 : subformula

syntax subformula "⟦" subterm,* "⟧" : subformula
syntax:max "⇑" subformula:10 : subformula

syntax "(" subformula ")" : subformula
syntax:max "!" term:max : subformula
syntax "“" subformula "”" : term
 
macro_rules
  | `(“ ⊤ ”)                                       => `(⊤)
  | `(“ ⊥ ”)                                       => `(⊥)
  | `(“ ! $t:term ”)                               => `($t)
  | `(“ [ $d:term ]( $t:subterm,* ) ”)             => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(rel $d $v)
  | `(“ ¬ $p:subformula ”)                         => `(~“$p”)
  | `(“ $t:subterm = $u:subterm ”)                 => `(rel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm ≠ $u:subterm ”)                 => `(nrel Language.Eq.eq ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm < $u:subterm ”)                 => `(rel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $t:subterm ≮ $u:subterm ”)                 => `(nrel Language.Lt.lt ![ᵀ“$t”, ᵀ“$u”])
  | `(“ $p:subformula ∧ $q:subformula ”)           => `(“$p” ⋏ “$q”)
  | `(“ ⋀ $i, $p:subformula ”)                    => `(Matrix.conj fun $i => “$p”)
  | `(“ $p:subformula ∨ $q:subformula ”)           => `(“$p” ⋎ “$q”)
  | `(“ ∀ $p:subformula ”)                         => `(∀' “$p”)
  | `(“ ∃ $p:subformula ”)                         => `(∃' “$p”)
  | `(“ ∀* $p:subformula ”)                        => `(univClosure “$p”)
  | `(“ $p:subformula ⟦ $t:subterm,* ⟧ ”)            => do
    let v ← t.getElems.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(ᵀ“$a” :> $s))
    `(substs $v “$p”)
  | `(“ ⇑$p:subformula ”)                         => `(shift “$p”)

  | `(“ ( $x ) ”)                                  => `(“$x”)

#check (“ ¬ [Language.toRelational 0]() ” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#check (“ [Language.toRelational 1](&0) ” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#check (“ ¬ [Language.toRelational 1](&0, &1) ” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#check “ ¬(∀ ∀ (#0 + 1) * #1 < #0 + #1 ∨ 0 < 5) ”
#check “⋀ i, #i < #i + 9”

syntax:10 subformula:9 " → " subformula:10 : subformula
syntax:10 subformula:10 " ↔ " subformula:10 : subformula

macro_rules
  | `(“ $p:subformula → $q:subformula ”) => `(“$p” ⟶ “$q”)
  | `(“ $p:subformula ↔ $q:subformula ”) => `(“$p” ⟷ “$q”)

#reduce (“(∃ ⊤) ↔ !(∃' ⊤)” : Sentence Language.oring)

section delab
open Lean PrettyPrinter Delaborator SubExpr

notation "lang(=)" => Language.Eq.eq
notation "lang(<)" => Language.Lt.lt

@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(lang(=))

@[app_unexpander Language.Lt.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(lang(<))

@[app_unexpander SubFormula.rel]
def unexpandFunc : Unexpander
  | `($_ $c ![])                 => `(“ [$c]() ”)
  | `($_ $f ![ᵀ“ $t ”])          => `(“ [$f]($t) ”)
  | `($_ $f ![ᵀ“ $t ”, ᵀ“ $u ”]) => `(“ [$f]($t, $u) ”)
  | _                            => throw ()

@[app_unexpander HasAnd.and]
def unexpandAnd : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ∧ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ∧ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ∧ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasOr.or]
def unexpandOr : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ∨ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ∨ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ∨ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasNeg.neg]
def unexpandNeg : Unexpander
  | `($_ “$p:subformula”) => `(“ ¬$p ”)
  | _                     => throw ()

@[app_unexpander HasUniv.univ]
def unexpandUniv : Unexpander
  | `($_ “$p:subformula”) => `(“ ∀ $p ”)
  | _                     => throw ()

@[app_unexpander HasEx.ex]
def unexpandEx : Unexpander
  | `($_ “$p:subformula”) => `(“ ∃ $p ”)
  | _                     => throw ()

@[app_unexpander HasArrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p → $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p → !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t → $q) ”)
  | _                                     => throw ()

@[app_unexpander HasLogicSymbols.iff]
def unexpandIff : Unexpander
  | `($_ “$p:subformula” “$q:subformula”) => `(“ ($p ↔ $q) ”)
  | `($_ “$p:subformula” $u:term)         => `(“ ($p ↔ !$u) ”)
  | `($_ $t:term         “$q:subformula”) => `(“ (!$t ↔ $q) ”)
  | _                                     => throw ()

@[app_unexpander HasLogicSymbols.Hom.toFun]
def unexpandHomToFum : Unexpander
  | `($_ ⟦↦ ᵀ“$t:subterm”⟧                   “$p:subformula”) => `(“ ($p:subformula)⟦$t ⟧ ”)
  | `($_ ⟦↦ #$x⟧                             “$p:subformula”) => `(“ ($p:subformula)⟦#$x⟧ ”)
  | `($_ ⟦↦ &$x⟧                             “$p:subformula”) => `(“ ($p:subformula)⟦&$x⟧ ”)
  | `($_ ⟦↦ $t ⟧                             “$p:subformula”) => `(“ ($p:subformula)⟦ᵀ!$t⟧ ”)
  | `($_ ⟦→ ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦$t,  $u ⟧ ”)
  | `($_ ⟦→ ![ᵀ“$t:subterm”, #$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦$t,  #$y⟧ ”)
  | `($_ ⟦→ ![ᵀ“$t:subterm”, &$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦$t,  &$y⟧ ”)
  | `($_ ⟦→ ![ᵀ“$t:subterm”, $u           ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦$t,  ᵀ!$u⟧ ”)
  | `($_ ⟦→ ![#$x,           ᵀ“$u:subterm”]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦#$x, $u ⟧ ”)
  | `($_ ⟦→ ![#$x,           #$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦#$x, #$y⟧ ”)
  | `($_ ⟦→ ![#$x,           &$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦#$x, &$y⟧ ”)
  | `($_ ⟦→ ![#$x,           $u           ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦#$x, ᵀ!$u⟧ ”)
  | `($_ ⟦→ ![&$x,           ᵀ“$u:subterm”]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦&$x, $u ⟧ ”)
  | `($_ ⟦→ ![&$x,           #$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦&$x, #$y⟧ ”)
  | `($_ ⟦→ ![&$x,           &$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦&$x, &$y⟧ ”)
  | `($_ ⟦→ ![&$x,           $u           ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦&$x, ᵀ!$u⟧ ”)
  | `($_ ⟦→ ![$t,            ᵀ“$u:subterm”]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦ᵀ!$t, $u ⟧ ”)
  | `($_ ⟦→ ![$t,            #$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦ᵀ!$t, #$y⟧ ”)
  | `($_ ⟦→ ![$t,            &$y          ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦ᵀ!$t, &$y⟧ ”)
  | `($_ ⟦→ ![$t,            $u           ]⟧ “$p:subformula”) => `(“ ($p:subformula)⟦ᵀ!$t, ᵀ!$u⟧ ”)
  | _                                           => throw ()


@[app_unexpander Matrix.conj]
def unexpandMatrixConj : Unexpander
  | `($_ fun $i:ident => “$p:subformula”) => `(“ (⋀ $i, $p) ”)
  | _                                     => throw ()

@[app_unexpander SubFormula.shift]
def unexpandShift : Unexpander
  | `($_ “$p:subformula”) => `(“ ⇑ $p ”)
  | _                     => throw ()

@[app_unexpander SubFormula.rel]
def unexpandRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm = $u  ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm = #$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm = &$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm = ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        = $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        = #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        = &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        = ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        = $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        = #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        = &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        = ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       = $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       = #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       = &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       = ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm < $u  ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm < #$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm < &$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm < ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        < $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        < #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        < &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        < ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        < $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        < #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        < &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        < ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       < $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       < #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       < &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       < ᵀ!$u ”)

  | _                                             => throw ()

@[app_unexpander SubFormula.nrel]
def unexpandNRelArith : Unexpander
  | `($_ lang(=) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm ≠ $u  ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm ≠ #$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm ≠ &$y ”)
  | `($_ lang(=) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm ≠ ᵀ!$u ”)
  | `($_ lang(=) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        ≠ $u  ”)
  | `($_ lang(=) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≠ #$y ”)
  | `($_ lang(=) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≠ &$y ”)
  | `($_ lang(=) ![#$x:term,      $u           ]) => `(“ #$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        ≠ $u  ”)
  | `($_ lang(=) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≠ #$y ”)
  | `($_ lang(=) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≠ &$y ”)
  | `($_ lang(=) ![&$x:term,      $u           ]) => `(“ &$x        ≠ ᵀ!$u ”)
  | `($_ lang(=) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       ≠ $u  ”)
  | `($_ lang(=) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≠ #$y ”)
  | `($_ lang(=) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≠ &$y ”)
  | `($_ lang(=) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≠ ᵀ!$u ”)

  | `($_ lang(<) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm ≮ $u  ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm ≮ #$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm ≮ &$y ”)
  | `($_ lang(<) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm ≮ ᵀ!$u ”)
  | `($_ lang(<) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        ≮ $u  ”)
  | `($_ lang(<) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≮ #$y ”)
  | `($_ lang(<) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≮ &$y ”)
  | `($_ lang(<) ![#$x:term,      $u           ]) => `(“ #$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        ≮ $u  ”)
  | `($_ lang(<) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≮ #$y ”)
  | `($_ lang(<) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≮ &$y ”)
  | `($_ lang(<) ![&$x:term,      $u           ]) => `(“ &$x        ≮ ᵀ!$u ”)
  | `($_ lang(<) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       ≮ $u  ”)
  | `($_ lang(<) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≮ #$y ”)
  | `($_ lang(<) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≮ &$y ”)
  | `($_ lang(<) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≮ ᵀ!$u ”)

  | _                                             => throw ()

#check “ ¬∃ ∀ ((#0 + 1) * #1 < #0 + #1 ↔ 0 < &5) ”
#check (“0 < 0 → ∀ 0 < #0 → 0 ≮ 2” : Sentence Language.oring)
#check “¬⊤ ∨ (¬#0 < 5)⟦#3, 7⟧⟦2, #3⟧”
#check “⋀ i, #i < #i + 9”

end delab

end SubFormula

end FirstOrder