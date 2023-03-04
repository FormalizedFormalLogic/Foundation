import Logic.Predicate.Term

namespace FirstOrder

variable (L : Language.{u})

inductive SubFormula (μ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : SubFormula μ n
  | falsum {n} : SubFormula μ n
  | rel    {n} : ∀ {k}, L.rel k → (Fin k → SubTerm L μ n) → SubFormula μ n
  | nrel   {n} : ∀ {k}, L.rel k → (Fin k → SubTerm L μ n) → SubFormula μ n
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
  | _, ⊤                     => "\\top"
  | _, ⊥                     => "\\bot"
  | _, rel (k := 0) r _      => "{" ++ toString r ++ "}"
  | _, rel (k := _ + 1) r v  => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, nrel (k := 0) r _     => "\\lnot {" ++ toString r ++ "}"
  | _, nrel (k := _ + 1) r v => "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, p ⋏ q                 => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | _, p ⋎ q                 => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | _, @all _ _ n p          => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr p
  | _, @ex _ _ n p           => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr p

instance : Repr (SubFormula L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (SubFormula L μ n) := ⟨toStr⟩

end SubFormula

namespace SubFormula
variable {n n₁ n₂ n₃ m m₁ m₂ m₃ : ℕ}

@[simp] lemma complexity_neg (p : SubFormula L μ n) : complexity (~p) = complexity p :=
by induction p using rec' <;> simp[*]

@[reducible]
def bind' : ∀ {n₁ n₂}, (fixed : Fin n₁ → SubTerm L μ₂ n₂) → (free : μ₁ → SubTerm L μ₂ n₂) →
    SubFormula L μ₁ n₁ → SubFormula L μ₂ n₂
  | _, _, _,     _,    ⊤          => ⊤
  | _, _, _,     _,    ⊥          => ⊥
  | _, _, fixed, free, (rel r v)  => rel r (SubTerm.bind fixed free ∘ v)
  | _, _, fixed, free, (nrel r v) => nrel r (SubTerm.bind fixed free ∘ v)
  | _, _, fixed, free, (p ⋏ q)    => bind' fixed free p ⋏ bind' fixed free q
  | _, _, fixed, free, (p ⋎ q)    => bind' fixed free p ⋎ bind' fixed free q
  | _, _, fixed, free, (∀' p)     => ∀' bind' (Fin.cases #0 $ SubTerm.bShift ∘ fixed) (SubTerm.bShift ∘ free) p
  | _, _, fixed, free, (∃' p)     => ∃' bind' (Fin.cases #0 $ SubTerm.bShift ∘ fixed) (SubTerm.bShift ∘ free) p

lemma bind'_neg {n₁ n₂} (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p) :
    bind' fixed free (~p) = ~bind' fixed free p :=
  by induction p using rec' generalizing n₂ <;> simp[*, bind', ←neg_eq]

def bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ where
  toFun := bind' fixed free
  map_top' := by simp[bind']
  map_bot' := by simp[bind']
  map_and' := by simp[bind']
  map_or'  := by simp[bind']
  map_neg' := by simp[bind'_neg]
  map_imp' := by simp[imp_eq, bind'_neg, ←neg_eq, bind']

def map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ :=
  bind (fun n => #(fixed n)) (fun m => &(free m))

def subst (t : SubTerm L μ n) : SubFormula L μ (n + 1) →L SubFormula L μ n :=
  bind (SubTerm.fixedVar <: t) SubTerm.freeVar

section bind
variable (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂)

lemma bind_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind fixed free (rel r v) = rel r (fun i => (v i).bind fixed free) := rfl

lemma bind_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    bind fixed free (nrel r v) = nrel r (fun i => (v i).bind fixed free) := rfl

@[simp] lemma bind_all (p : SubFormula L μ₁ (n₁ + 1)) :
    bind fixed free (∀' p) = ∀' bind (#0 :> SubTerm.bShift ∘ fixed) (SubTerm.bShift ∘ free) p := rfl

@[simp] lemma bind_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    bind fixed free (∃' p) = ∃' bind (#0 :> SubTerm.bShift ∘ fixed) (SubTerm.bShift ∘ free) p := rfl

@[simp] lemma complexity_bind (p : SubFormula L μ₁ n₁) : complexity (bind fixed free p) = complexity p :=
  by induction p using rec' generalizing μ₂ n₂ <;> simp[*, bind_rel, bind_nrel]

@[simp] lemma bind_id (p) : @bind L μ μ n n SubTerm.fixedVar SubTerm.freeVar p = p :=
  by induction p using rec' <;> simp[*, bind_rel, bind_nrel]

@[simp] lemma eq_bind_of (fixed : Fin n → SubTerm L μ n) (free : μ → SubTerm L μ n)
    (hfixed : ∀ x, fixed x = #x) (hfree : ∀ x, free x = &x) (p : SubFormula L μ n) :
    bind fixed free p = p :=
  by
  have : fixed = SubTerm.fixedVar := funext hfixed
  have : free = SubTerm.freeVar := funext hfree
  simp[*]

end bind

lemma bind_bind
  (fixed₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (fixed₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) (p : SubFormula L μ₁ n₁) :
    bind fixed₂ free₂ (bind fixed₁ free₁ p) = bind (fun n => (fixed₁ n).bind fixed₂ free₂) (fun m => (free₁ m).bind fixed₂ free₂) p := by
  induction p using rec' generalizing n₂ n₃ <;> simp[*, SubTerm.bind_bind, bind_rel, bind_nrel] <;>
  { congr
    refine funext (Fin.cases (by simp) (by simp[SubTerm.bShift, SubTerm.map, SubTerm.bind_bind]))
    refine funext (by simp[SubTerm.bShift, SubTerm.map, SubTerm.bind_bind]) }

lemma bind_comp_bind
  (fixed₁ : Fin n₁ → SubTerm L μ₂ n₂) (free₁ : μ₁ → SubTerm L μ₂ n₂)
  (fixed₂ : Fin n₂ → SubTerm L μ₃ n₃) (free₂ : μ₂ → SubTerm L μ₃ n₃) :
    (bind fixed₂ free₂).comp (bind fixed₁ free₁) = bind (fun n => (fixed₁ n).bind fixed₂ free₂) (fun m => (free₁ m).bind fixed₂ free₂) :=
  by ext p; simp[bind_bind]

section map
variable (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂)

lemma map_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map fixed free (rel r v) = rel r (fun i => (v i).map fixed free) := rfl

lemma map_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ₁ n₁) :
    map fixed free (nrel r v) = nrel r (fun i => (v i).map fixed free) := rfl

@[simp] lemma map_all (p : SubFormula L μ₁ (n₁ + 1)) :
    map fixed free (∀' p) = ∀' map (0 :> Fin.succ ∘ fixed) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma map_ex (p : SubFormula L μ₁ (n₁ + 1)) :
    map fixed free (∃' p) = ∃' map (0 :> Fin.succ ∘ fixed) free p :=
  by simp[map]; congr; exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma complexity_map (p : SubFormula L μ₁ n₁) : complexity (map fixed free p) = complexity p :=
  complexity_bind _ _ _

end map

lemma map_map
  (fixed₁ : Fin n₁ → Fin n₂) (free₁ : μ₁ → μ₂)
  (fixed₂ : Fin n₂ → Fin n₃) (free₂ : μ₂ → μ₃) (p : SubFormula L μ₁ n₁) :
    map fixed₂ free₂ (map fixed₁ free₁ p) = map (fixed₂ ∘ fixed₁) (free₂ ∘ free₁) p :=
  bind_bind _ _ _ _ _

@[simp] lemma map_id (p) : @map L μ μ n n id id p = p :=
  bind_id _

lemma subst_rel {s : SubTerm L μ n} {k} (r : L.rel k) (v : Fin k → SubTerm L μ (n + 1)) :
    subst s (rel r v) = rel r (fun i => SubTerm.subst s (v i)) :=
  by simp[subst, SubTerm.subst, bind_rel]

lemma subst_nrel {s : SubTerm L μ n} {k} (r : L.rel k) (v : Fin k → SubTerm L μ (n + 1)) :
    subst s (nrel r v) = nrel r (fun i => SubTerm.subst s (v i)) :=
  by simp[subst, SubTerm.subst, bind_nrel]

@[simp] lemma subst_all {s : SubTerm L μ n} (p : SubFormula L μ (n + 1 + 1)) :
    subst s (∀' p) = ∀' subst s.bShift p := by
  simp[subst, SubTerm.subst]; congr
  funext i
  cases' i using Fin.cases with i <;> simp
  cases' i using Fin.lastCases with i <;> simp[Fin.succ_castSucc]

@[simp] lemma subst_ex {s : SubTerm L μ n} (p : SubFormula L μ (n + 1 + 1)) :
    subst s (∃' p) = ∃' subst s.bShift p := by
  simp[subst, SubTerm.subst]; congr
  funext i
  cases' i using Fin.cases with i <;> simp
  cases' i using Fin.lastCases with i <;> simp[Fin.succ_castSucc]

section Syntactic

def shift : SyntacticSubFormula L n →L SyntacticSubFormula L n :=
  map id Nat.succ

def free : SyntacticSubFormula L (n + 1) →L SyntacticSubFormula L n :=
  bind (SubTerm.fixedVar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticSubFormula L n →L SyntacticSubFormula L (n + 1) :=
  bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ SubTerm.freeVar)

lemma shift_rel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (rel r v) = rel r (fun i => SubTerm.shift $ v i) := rfl

lemma shift_nrel {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) :
    shift (nrel r v) = nrel r (fun i => SubTerm.shift $ v i) := rfl

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

lemma shift_subst (s : SyntacticSubTerm L n) (p : SyntacticSubFormula L (n + 1)) :
    shift (subst s p) = subst s.shift (shift p) :=
  by
  simp[shift, subst, map, bind_bind]; congr; funext x
  cases' x using Fin.lastCases <;> simp; rfl

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

@[simp] lemma free_fix (p : SyntacticSubFormula L n) : free (fix p) = p :=
  by simp[fix, free, bind_bind]; apply eq_bind_of <;> simp; intros x; cases x <;> simp

@[simp] lemma fix_free (p : SyntacticSubFormula L (n + 1)) : fix (free p) = p :=
  by
  simp[fix, free, bind_bind]; apply eq_bind_of <;> simp
  intros x; exact Fin.lastCases (by simp) (by simp) x

@[simp] lemma subst_shift_eq_free (p : SyntacticSubFormula L 1) : subst &0 (shift p) = free p :=
  by simp[subst, shift, free, map, bind_bind]

@[simp] lemma complexity_free (p : SyntacticSubFormula L (n + 1)) :
    complexity (free p) = complexity p :=
  by simp[free]

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

lemma ne_of_ne_complexity {p q : SubFormula L μ n} (h : p.complexity ≠ q.complexity) : p ≠ q :=
  by rintro rfl; contradiction

declare_syntax_cat subformula
syntax "⊤" : subformula
syntax "⊥" : subformula
syntax:45 subterm:45 "=" subterm:0 : subformula
syntax:45 subterm:45 "<" subterm:0 : subformula
syntax:45 subterm:45 "≤" subterm:0 : subformula
syntax:45 "prop" term:max : subformula
syntax:45 "rel¹" term "/[" subterm:0 "]" : subformula
syntax:45 "rel²" term "/[" subterm:0 "," subterm:0 "]" : subformula
syntax:45 "rel³" term "/[" subterm:0 "," subterm:0 "," subterm:0 "]" : subformula
syntax:33 "¬" subformula : subformula
syntax:32 subformula:32 "∧" subformula:33 : subformula
syntax:30 subformula:30 "∨" subformula:31 : subformula
syntax:20 "∀" subformula:20 : subformula
syntax:20 "∃" subformula:20 : subformula
syntax "(" subformula ")" : subformula
syntax:max "!" term:max : subformula
syntax "“" subformula "”" : term
 
macro_rules
  | `(“ ⊤ ”)                                          => `(⊤)
  | `(“ ⊥ ”)                                          => `(⊥)
  | `(“ ! $t:term ”)                                  => `($t)
  | `(“ prop $s:term ”)                               => `(rel $s ![])
  | `(“ rel¹ $s:term /[ $t:subterm ] ”)               => `(rel $s ![T“$t”])
  | `(“ rel² $s:term /[ $t₁:subterm, $t₂:subterm ] ”) => `(rel $s ![T“$t₁”, T“$t₂”])
  | `(“ rel³ $s:term /[ $t₁:subterm, $t₂:subterm, $t₃:subterm ] ”) => `(rel $s ![T“$t₁”, T“$t₂”, T“$t₃”])
  | `(“ ¬ $p:subformula ”)                            => `(~“$p”)
  | `(“ $t:subterm = $u:subterm ”)                    => `(rel Language.HasEq.eq ![T“$t”, T“$u”])
  | `(“ $t:subterm < $u:subterm ”)                    => `(rel Language.HasLt.lt ![T“$t”, T“$u”])
  | `(“ $t:subterm ≤ $u:subterm ”)                    =>
    `(rel Language.HasLt.lt ![T“$t”, T“$u”] ⋎ rel Language.HasEq.eq ![T“$t”, T“$u”])
  | `(“ $p:subformula ∧ $q:subformula ”)              => `(“$p” ⋏ “$q”)
  | `(“ $p:subformula ∨ $q:subformula ”)              => `(“$p” ⋎ “$q”)
  | `(“ ∀ $p:subformula ”)                            => `(∀' “$p”)
  | `(“ ∃ $p:subformula ”)                            => `(∃' “$p”)
  | `(“ ( $x ) ”)                                     => `(“$x”)

#reduce (“¬ prop (Language.toRelational 1)” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#reduce (“rel¹ Language.toRelational 1 /[&0]” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#reduce (“¬ rel² Language.toRelational 1 /[&0, &1]” : Formula (Language.relational (fun _ => ℕ)) ℕ)
#reduce (“¬ (∀ ∀ (#0 + 1) * #1 < #0 + #1)” : Sentence Language.oring)

syntax:10 subformula:10 "→" subformula:11 : subformula
syntax:10 subformula:10 "↔" subformula:11 : subformula

macro_rules
  | `(“ $p:subformula → $q:subformula ”) => `(“$p” ⟶ “$q”)
  | `(“ $p:subformula ↔ $q:subformula ”) => `(“$p” ⟷ “$q”)

#reduce (“(∃ ⊤) ↔ !(∃' ⊤)” : Sentence Language.oring)

end SubFormula

abbrev Theory (L : Language) (μ) := Set (Formula L μ)

abbrev CTheory (L : Language) := Set (Sentence L)

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

end SubFormula

end FirstOrder