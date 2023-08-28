import Logic.Predicate.FirstOrder.Basic.Term.Term

namespace FirstOrder

inductive SubFormula (L : Language.{u}) (μ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : SubFormula L μ n
  | falsum {n} : SubFormula L μ n
  | rel    {n} : {arity : ℕ} → L.rel arity → (Fin arity → SubTerm L μ n) → SubFormula L μ n
  | nrel   {n} : {arity : ℕ} → L.rel arity → (Fin arity → SubTerm L μ n) → SubFormula L μ n
  | and    {n} : SubFormula L μ n → SubFormula L μ n → SubFormula L μ n
  | or     {n} : SubFormula L μ n → SubFormula L μ n → SubFormula L μ n
  | all    {n} : SubFormula L μ (n + 1) → SubFormula L μ n
  | ex     {n} : SubFormula L μ (n + 1) → SubFormula L μ n

abbrev Formula (L : Language.{u}) (μ : Type v) := SubFormula L μ 0

abbrev Sentence (L : Language.{u}) := Formula L Empty

abbrev SubSentence (L : Language.{u}) (n : ℕ) := SubFormula L Empty n

abbrev SyntacticSubFormula (L : Language.{u}) (n : ℕ) := SubFormula L ℕ n

abbrev SyntacticFormula (L : Language.{u}) := SyntacticSubFormula L 0

namespace SubFormula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

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

section ToString

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
  | n, all p                     => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr p
  | n, ex p                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr p

instance : Repr (SubFormula L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (SubFormula L μ n) := ⟨toStr⟩

end ToString

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

lemma ball_eq (p q : SubFormula L μ (n + 1)) : (∀[p] q) = ∀' (p ⟶ q) := rfl

lemma bex_eq (p q : SubFormula L μ (n + 1)) : (∃[p] q) = ∃' (p ⋏ q) := rfl

@[simp] lemma neg_ball (p q : SubFormula L μ (n + 1)) : ~(∀[p] q) = ∃[p] ~q := by
  simp[HasLogicSymbols.ball, HasLogicSymbols.bex, imp_eq]

@[simp] lemma neg_bex (p q : SubFormula L μ (n + 1)) : ~(∃[p] q) = ∀[p] ~q := by
  simp[HasLogicSymbols.ball, HasLogicSymbols.bex, imp_eq]

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : SubFormula L μ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[HasAnd.and]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : SubFormula L μ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[HasOr.or]

@[simp] lemma all_inj (p q : SubFormula L μ (n + 1)) : ∀' p = ∀' q ↔ p = q :=
  by simp[HasUniv.univ]

@[simp] lemma ex_inj (p q : SubFormula L μ (n + 1)) : ∃' p = ∃' q ↔ p = q :=
  by simp[HasEx.ex]

abbrev rel! (L : Language.{u}) (k) (r : L.rel k) (v : Fin k → SubTerm L μ n) := rel r v

abbrev nrel! (L : Language.{u}) (k) (r : L.rel k) (v : Fin k → SubTerm L μ n) := nrel r v

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
def cases' {C : ∀ n, SubFormula L μ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → SubTerm L μ n), C n (nrel r v))
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
def rec' {C : ∀ n, SubFormula L μ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → SubTerm L μ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → SubTerm L μ n), C n (nrel r v))
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

@[simp] lemma complexity_neg (p : SubFormula L μ n) : complexity (~p) = complexity p :=
  by induction p using rec' <;> simp[*]

section Decidable

variable [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [DecidableEq μ]

def hasDecEq : {n : ℕ} → (p q : SubFormula L μ n) → Decidable (p = q)
  | _, ⊤,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, ⊥,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, rel r v,  q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, nrel r v, q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, p ⋏ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, p ⋎ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, ∀' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hall p' => simp; exact hasDecEq p p'
  | _, ∃' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hex p' => simp; exact hasDecEq p p'

instance : DecidableEq (SubFormula L μ n) := hasDecEq

end Decidable

end SubFormula

namespace Rew

open SubFormula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def loMap : ⦃n₁ n₂ : ℕ⦄ → Rew L μ₁ n₁ μ₂ n₂ → SubFormula L μ₁ n₁ → SubFormula L μ₂ n₂
  | _, _, _, ⊤        => ⊤
  | _, _, _, ⊥        => ⊥
  | _, _, ω, rel r v  => rel r (ω ∘ v)
  | _, _, ω, nrel r v => nrel r (ω ∘ v)
  | _, _, ω, p ⋏ q    => ω.loMap p ⋏ ω.loMap q
  | _, _, ω, p ⋎ q    => ω.loMap p ⋎ ω.loMap q
  | _, _, ω, ∀' p     => ∀' ω.q.loMap p
  | _, _, ω, ∃' p     => ∃' ω.q.loMap p

section

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma loMap_neg (p : SubFormula L μ₁ n₁) :
    ω.loMap (~p) = ~ω.loMap p :=
  by induction p using SubFormula.rec' generalizing n₂ <;> simp[*, loMap, ←SubFormula.neg_eq]

lemma ext_loMap' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) (p : SubFormula L μ₁ n₁) : ω₁.loMap p = ω₂.loMap p:= by simp[h]

lemma neg' (p : SubFormula L μ₁ n₁) : ω.loMap (~p) = ~ω.loMap p := loMap_neg ω p

lemma or' (p q : SubFormula L μ₁ n₁) : ω.loMap (p ⋎ q) = ω.loMap p ⋎ ω.loMap q := by rfl

def hom (ω : Rew L μ₁ n₁ μ₂ n₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ where
  map_top' := by rfl
  map_bot' := by rfl
  map_neg' := ω.loMap_neg
  map_and' := fun p q => by rfl
  map_or' := fun p q => by rfl
  map_imply' := fun p q => by simp[SubFormula.imp_eq, neg', or']

/-
instance : FunLike (Rew L μ₁ n₁ μ₂ n₂) (SubFormula L μ₁ n₁) (fun _ => SubFormula L μ₂ n₂) where
  coe := fun ω => loMap ω
  coe_injective' := fun ω₁ ω₂ h => ext_loMap ω₁ ω₂ (congr_fun h)

instance : CoeFun (Rew L μ₁ n₁ μ₂ n₂) (fun _ => SubFormula L μ₁ n₁ → SubFormula L μ₂ n₂) := FunLike.hasCoeToFun

scoped[FirstOrder] notation:max ω "ᵀ" => (ω : SubTerm _ _ _ → SubTerm _ _ _)

scoped[FirstOrder] notation:max ω "ᴾ" => (ω : SubFormula _ _ _ → SubFormula _ _ _)

lemma neg' (p : SubFormula L μ₁ n₁) : ω (~p) = ~ω p := loMap_neg ω p

lemma or' (p q : SubFormula L μ₁ n₁) : ω (p ⋎ q) = ω p ⋎ ω q := by rfl

instance : HasLogicSymbols.homClass (Rew L μ₁ n₁ μ₂ n₂) (SubFormula L μ₁ n₁) (SubFormula L μ₂ n₂) where
  map_top := fun ω => by rfl
  map_bot := fun ω => by rfl
  map_neg := loMap_neg
  map_and := fun ω p q => by rfl
  map_or := fun ω p q => by rfl
  map_imply := fun ω p q => by simp[SubFormula.imp_eq, neg', or']

-/

protected lemma rel {k} {r : L.rel k} {v : Fin k → SubTerm L μ₁ n₁} :
    ω.hom (rel r v) = rel r (fun i => ω (v i)) := by rfl

protected lemma nrel {k} {r : L.rel k} {v : Fin k → SubTerm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r (fun i => ω (v i)) := by rfl

lemma rel' {k} {r : L.rel k} {v : Fin k → SubTerm L μ₁ n₁} :
    ω.hom (rel r v) = rel r (ω ∘ v) := by rfl

lemma nrel' {k} {r : L.rel k} {v : Fin k → SubTerm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r (ω ∘ v) := by rfl

@[simp] lemma rel0 {r : L.rel 0} {v : Fin 0 → SubTerm L μ₁ n₁} :
    ω.hom (rel r v) = rel r ![] := by simp[ω.rel]

@[simp] lemma rel1 {r : L.rel 1} {t : SubTerm L μ₁ n₁} :
    ω.hom (rel r ![t]) = rel r ![ω t] := by simp[ω.rel, Matrix.constant_eq_singleton]

@[simp] lemma rel2 {r : L.rel 2} {t₁ t₂ : SubTerm L μ₁ n₁} :
    ω.hom (rel r ![t₁, t₂]) = rel r ![ω t₁, ω t₂] := by simp[ω.rel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma rel3 {r : L.rel 3} {t₁ t₂ t₃ : SubTerm L μ₁ n₁} :
    ω.hom (rel r ![t₁, t₂, t₃]) = rel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.rel]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[simp] lemma nrel0 {r : L.rel 0} {v : Fin 0 → SubTerm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r ![] := by simp[ω.nrel]

@[simp] lemma nrel1 {r : L.rel 1} {t : SubTerm L μ₁ n₁} :
    ω.hom (nrel r ![t]) = nrel r ![ω t] := by simp[ω.nrel, Matrix.constant_eq_singleton]

@[simp] lemma nrel2 {r : L.rel 2} {t₁ t₂ : SubTerm L μ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂]) = nrel r ![ω t₁, ω t₂] := by simp[ω.nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma nrel3 {r : L.rel 3} {t₁ t₂ t₃ : SubTerm L μ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂, t₃]) = nrel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.nrel]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[simp] protected lemma all {p : SubFormula L μ₁ (n₁ + 1)} :
    ω.hom (∀' p) = ∀' ω.q.hom p := by rfl

@[simp] protected lemma ex {p : SubFormula L μ₁ (n₁ + 1)} :
    ω.hom (∃' p) = ∃' ω.q.hom p := by rfl

@[simp] protected lemma ball {p q : SubFormula L μ₁ (n₁ + 1)} :
    ω.hom (∀[p] q) = ∀[ω.q.hom p] ω.q.hom q := by simp[ball_eq]

@[simp] protected lemma bex {p q : SubFormula L μ₁ (n₁ + 1)} :
    ω.hom (∃[p] q) = ∃[ω.q.hom p] ω.q.hom q := by simp[bex_eq]

@[simp] lemma complexity (p : SubFormula L μ₁ n₁) : (ω.hom p).complexity = p.complexity := by
  induction p using SubFormula.rec' generalizing n₂ <;> simp[Rew.rel, Rew.nrel, *]

lemma hom_ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) {p} : ω₁.hom p = ω₂.hom p := by simp[h]

end

@[simp] lemma hom_id_eq : (Rew.id.hom : SubFormula L μ n →L SubFormula L μ n) = HasLogicSymbols.Hom.id := by
  ext p; induction p using SubFormula.rec' <;> simp[Rew.rel, Rew.nrel, *]

abbrev bindl (b : Fin n₁ → SubTerm L μ₂ n₂) (e : μ₁ → SubTerm L μ₂ n₂) :
    SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ := (bind b e).hom

abbrev rewritel (f : μ₁ → SubTerm L μ₂ n) : SubFormula L μ₁ n →L SubFormula L μ₂ n := (rewrite f).hom

abbrev rewriteMapl (e : μ₁ → μ₂) : SubFormula L μ₁ n →L SubFormula L μ₂ n := (rewriteMap e).hom

abbrev mapl (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) : SubFormula L μ₁ n₁ →L SubFormula L μ₂ n₂ := (map b e).hom

abbrev map₀l (e : μ₁ → μ₂) : SubFormula L μ₁ n →L SubFormula L μ₂ n := mapl id e

abbrev substsl {n'} (v : Fin n → SubTerm L μ n') : SubFormula L μ n →L SubFormula L μ n' := (substs v).hom

abbrev embl {o : Type w} [IsEmpty o] : SubFormula L o n →L SubFormula L μ n := emb.hom

section Syntactic

abbrev shiftl : SyntacticSubFormula L n →L SyntacticSubFormula L n := shift.hom

abbrev freel : SyntacticSubFormula L (n + 1) →L SyntacticSubFormula L n := free.hom

abbrev fixl : SyntacticSubFormula L n →L SyntacticSubFormula L (n + 1) := fix.hom

end Syntactic

lemma hom_comp_eq (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) : (ω₂.comp ω₁).hom = ω₂.hom.comp ω₁.hom := by
  ext p; simp; induction p using SubFormula.rec' generalizing n₂ n₃ <;> simp[Rew.rel, Rew.nrel, comp_app, q_comp, *]

lemma hom_comp_app (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    (ω₂.comp ω₁).hom p = ω₂.hom (ω₁.hom p) := by simp[hom_comp_eq]

lemma mapl_inj : ∀ {n₁ n₂ μ₁ μ₂} {b : Fin n₁ → Fin n₂} {e : μ₁ → μ₂},
    (hb : Function.Injective b) → (hf : Function.Injective e) → Function.Injective $ mapl (L := L) b e
  | _, _, _, _, _, _, _,  _,  ⊤,        p => by cases p using cases' <;> simp[Rew.rel, Rew.nrel]
  | _, _, _, _, _, _, _,  _,  ⊥,        p => by cases p using cases' <;> simp[Rew.rel, Rew.nrel]
  | _, _, _, _, _, _, hb, hf, rel r v,  p => by
    cases p using cases' <;> simp[Rew.rel, Rew.nrel]
    case hrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)
  | _, _, _, _, _, _, hb, hf, nrel r v, p => by
    cases p using cases' <;> simp[Rew.rel, Rew.nrel]
    case hnrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)
  | _, _, _, _, _, _, hb, hf, p ⋏ q,    r => by
    cases r using cases' <;> simp[Rew.rel, Rew.nrel]
    intro hp hq; exact ⟨mapl_inj hb hf hp, mapl_inj hb hf hq⟩
  | _, _, _, _, _, _, hb, hf, p ⋎ q,    r => by
    cases r using cases' <;> simp[Rew.rel, Rew.nrel]
    intro hp hq; exact ⟨mapl_inj hb hf hp, mapl_inj hb hf hq⟩
  | _, _, _, _, b, e, hb, hf, ∀' p,     q => by
    cases q using cases' <;> simp[Rew.rel, Rew.nrel, q_map]
    intro h; exact mapl_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h
  | _, _, _, _, b, e, hb, hf, ∃' p,     q => by
    cases q using cases' <;> simp[Rew.rel, Rew.nrel, q_map]
    intro h; exact mapl_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h

lemma embl_Injective {o} [e : IsEmpty o] : Function.Injective (embl : SubFormula L o n → SubFormula L μ n) :=
  by simp[embl, emb]; exact mapl_inj Function.injective_id (fun x => IsEmpty.elim e x)

lemma shiftl_Injective : Function.Injective (shiftl : SyntacticSubFormula L n → SyntacticSubFormula L n) :=
  by simp[shiftl, shift]; exact mapl_inj Function.injective_id Nat.succ_injective

@[simp] lemma hom_fix_free (p : SyntacticSubFormula L (n + 1)) :
    fixl (freel p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_free_fix (p : SyntacticSubFormula L n) :
    freel (fixl p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_substs_mbar_zero_comp_shift_eq_free (p : SyntacticSubFormula L 1) :
    substsl ![&0] (Rew.shiftl p) = freel p := by simp[←hom_comp_app, substs_mbar_zero_comp_shift_eq_free]

end Rew

namespace SubFormula

variable {L : Language.{u}} {μ : Type v} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def shiftEmb : SyntacticSubFormula L n ↪ SyntacticSubFormula L n where
  toFun := Rew.shiftl
  inj' := Rew.shiftl_Injective

lemma shiftEmb_eq_shift (p : SyntacticSubFormula L n) :
  shiftEmb p = Rew.shiftl p := rfl

def qr : ∀ {n}, SubFormula L μ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, p ⋏ q    => max p.qr q.qr
  | _, p ⋎ q    => max p.qr q.qr
  | _, ∀' p     => p.qr + 1
  | _, ∃' p     => p.qr + 1

@[simp] lemma qr_top : (⊤ : SubFormula L μ n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : SubFormula L μ n).qr = 0 := rfl

@[simp] lemma qr_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : (rel r v).qr = 0 := rfl

@[simp] lemma qr_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : (nrel r v).qr = 0 := rfl

@[simp] lemma qr_and (p q : SubFormula L μ n) : (p ⋏ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : SubFormula L μ n) : (p ⋎ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_all (p : SubFormula L μ (n + 1)) : (∀' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : SubFormula L μ (n + 1)) : (∃' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_neg (p : SubFormula L μ n) : (~p).qr = p.qr := by
  induction' p using rec' <;> simp[*]

@[simp] lemma qr_imply (p q : SubFormula L μ n) : (p ⟶ q).qr = max p.qr q.qr :=
  by simp[imp_eq]

@[simp] lemma qr_iff (p q : SubFormula L μ n) : (p ⟷ q).qr = max p.qr q.qr :=
  by simp[iff_eq, total_of]

def qfree (p : SubFormula L μ n) : Prop := p.qr = 0

@[simp] lemma qfree_top : (⊤ : SubFormula L μ n).qfree := rfl

@[simp] lemma qfree_bot : (⊥ : SubFormula L μ n).qfree := rfl

@[simp] lemma qfree_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : (rel r v).qfree := rfl

@[simp] lemma qfree_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) : (nrel r v).qfree := rfl

@[simp] lemma qfree_and {p q : SubFormula L μ n} : (p ⋏ q).qfree ↔ p.qfree ∧ q.qfree := by simp[qfree]

@[simp] lemma qfree_or {p q : SubFormula L μ n} : (p ⋎ q).qfree ↔ p.qfree ∧ q.qfree := by simp[qfree]

@[simp] lemma not_qfree_all {p : SubFormula L μ (n + 1)} : ¬(∀' p).qfree := by simp[qfree]

@[simp] lemma not_qfree_ex {p : SubFormula L μ (n + 1)} : ¬(∃' p).qfree := by simp[qfree]

@[simp] lemma qfree_neg {p : SubFormula L μ n} : (~p).qfree ↔ p.qfree := by
  simp[qfree]

@[simp] lemma qfree_imply {p q : SubFormula L μ n} : (p ⟶ q).qfree ↔ p.qfree ∧ q.qfree :=
  by simp[qfree]

@[simp] lemma qfree_iff {p q : SubFormula L μ n} : (p ⟷ q).qfree ↔ p.qfree ∧ q.qfree :=
  by simp[qfree]

structure Abbrev (L : Language.{u}) (n : ℕ) where
  sentence : SubSentence L n

structure Operator (L : Language.{u}) (ι : Type w) where
  operator : {μ : Type v} → {n : ℕ} → (ι → SubTerm L μ n) → SubFormula L μ n
  rew_operator : ∀ {μ₁ μ₂ n₁ n₂} (ω : Rew L μ₁ n₁ μ₂ n₂) (v : ι → SubTerm L μ₁ n₁), ω.hom (operator v) = operator (fun i => ω (v i))

abbrev Finitary (L : Language.{u}) (n : ℕ) := Operator L (Fin n)

abbrev OperatorMatrix (ι : Type w) (I : ι → Type w') := Operator L ((i : ι ) × I i)

namespace Abbrev

def toOperator (a : Abbrev L n) : Finitary L n where
  operator := fun v => Rew.substsl v (Rew.embl a.sentence)
  rew_operator := fun ω v => by
    simp[Empty.eq_elim, ←Rew.hom_comp_app]; exact Rew.ext_loMap' (by ext x <;> simp[Rew.comp_app]; { contradiction }) _

end Abbrev

@[elab_as_elim]
def formulaRec {C : SyntacticFormula L → Sort _}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hrel    : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (rel r v))
  (hnrel   : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (nrel r v))
  (hand    : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋎ q))
  (hall    : ∀ (p : SyntacticSubFormula L 1), C (Rew.freel p) → C (∀' p))
  (hex     : ∀ (p : SyntacticSubFormula L 1), C (Rew.freel p) → C (∃' p)) :
    ∀ (p : SyntacticFormula L), C p
  | ⊤        => hverum
  | ⊥        => hfalsum
  | rel r v  => hrel r v
  | nrel r v => hnrel r v
  | p ⋏ q    => hand p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | p ⋎ q    => hor p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | ∀' p     => hall p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.freel p))
  | ∃' p     => hex p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.freel p))
  termination_by formulaRec _ _ _ _ _ _ _ _ p => p.complexity

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

lemma rew_eq_of_funEqOn {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} {p}
  (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : Function.funEqOn (fvar? p) (ω₁ ∘ SubTerm.fvar) (ω₂ ∘ SubTerm.fvar)) :
    ω₁.hom p = ω₂.hom p := by
  induction p using rec' generalizing n₂ <;> simp[*, Rew.rel, Rew.nrel] <;> simp[fvar?, fvarList] at hf
  case hrel =>
    funext i
    exact SubTerm.rew_eq_of_funEqOn _ _ _ hb (hf.of_subset (by simp[fvarList]; intro x hx; exact ⟨i, hx⟩))
  case hnrel =>
    funext i
    exact SubTerm.rew_eq_of_funEqOn _ _ _ hb (hf.of_subset (by simp[fvarList]; intro x hx; exact ⟨i, hx⟩))
  case hand ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hor ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hall ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb]) (fun x hx => by simp; exact congr_arg _ (hf x hx))
  case hex ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb]) (fun x hx => by simp; exact congr_arg _ (hf x hx))

lemma rew_eq_of_funEqOn₀ {ω₁ ω₂ : Rew L μ₁ 0 μ₂ n₂} {p} (hf : Function.funEqOn (fvar? p) (ω₁ ∘ SubTerm.fvar) (ω₂ ∘ SubTerm.fvar)) : ω₁.hom p = ω₂.hom p :=
  rew_eq_of_funEqOn (fun x => Fin.elim0 x) hf

def upper (p : SyntacticSubFormula L n) : ℕ := Finset.sup p.fvarList.toFinset id + 1

lemma not_fvar?_of_lt_upper (p : SyntacticSubFormula L n) (h : p.upper ≤ m) : ¬fvar? p m := by
  simp[upper, Nat.add_one_le_iff, fvar?] at h ⊢
  intro hm
  have : m ≤ Finset.sup p.fvarList.toFinset id :=
    Finset.le_sup (s := p.fvarList.toFinset) (b := m) (f := id) (by simpa using hm)
  exact irrefl_of _ _ $ lt_of_lt_of_le h this

@[simp] lemma not_fvar?_upper (p : SyntacticSubFormula L n) : ¬fvar? p p.upper :=
  not_fvar?_of_lt_upper p (by simp)

lemma ne_of_ne_complexity {p q : SubFormula L μ n} (h : p.complexity ≠ q.complexity) : p ≠ q :=
  by rintro rfl; contradiction

@[simp] lemma ex_ne_subst (p : SubFormula L μ 1) (t) : [→ t].hom p ≠ ∃' p := ne_of_ne_complexity (by simp)

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

namespace SubFormula

variable {L : Language.{u}} {L₁ : Language.{u₁}} {{L₂ : Language.{u₂}}} {L₃ : Language.{u₃}} {μ : Type v} {Φ : L₁ →ᵥ L₂}

def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, SubFormula L₁ μ n → SubFormula L₂ μ n
  | _, ⊤        => ⊤ 
  | _, ⊥        => ⊥ 
  | _, rel r v  => rel (Φ.rel r) (SubTerm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (SubTerm.lMap Φ ∘ v)
  | _, p ⋏ q    => lMapAux Φ p ⋏ lMapAux Φ q
  | _, p ⋎ q    => lMapAux Φ p ⋎ lMapAux Φ q
  | _, ∀' p     => ∀' lMapAux Φ p
  | _, ∃' p     => ∃' lMapAux Φ p

lemma lMapAux_neg {n} (p : SubFormula L₁ μ n) :
    (~p).lMapAux Φ = ~p.lMapAux Φ :=
  by induction p using SubFormula.rec' <;> simp[*, lMapAux, ←SubFormula.neg_eq]

def lMap (Φ : L₁ →ᵥ L₂) {n} : SubFormula L₁ μ n →L SubFormula L₂ μ n where
  toTr := lMapAux Φ
  map_top' := by simp[lMapAux]
  map_bot' := by simp[lMapAux]
  map_and' := by simp[lMapAux]
  map_or'  := by simp[lMapAux]
  map_neg' := by simp[lMapAux_neg]
  map_imply' := by simp[SubFormula.imp_eq, lMapAux_neg, ←SubFormula.neg_eq, lMapAux]

lemma lMap_rel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

lemma lMap_nrel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_all (p : SubFormula L₁ μ (n + 1)) :
    lMap Φ (∀' p) = ∀' lMap Φ p := rfl

@[simp] lemma lMap_ex (p : SubFormula L₁ μ (n + 1)) :
    lMap Φ (∃' p) = ∃' lMap Φ p := rfl

lemma lMap_bind (b : Fin n₁ → SubTerm L₁ μ₂ n₂) (e : μ₁ → SubTerm L₁ μ₂ n₂) (p) :
    lMap Φ (Rew.bindl b e p) = Rew.bindl (SubTerm.lMap Φ ∘ b) (SubTerm.lMap Φ ∘ e) (lMap Φ p) := by
  induction p using rec' generalizing μ₂ n₂ <;>
  simp[*, Rew.rel, Rew.nrel, lMap_rel, lMap_nrel, SubTerm.lMap_bind, Rew.q_bind, Matrix.comp_vecCons', SubTerm.lMap_bShift, Function.comp]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) (p) :
    lMap Φ (Rew.mapl b e p) = Rew.mapl b e (lMap Φ p) := lMap_bind _ _ _

lemma lMap_substs (w : Fin k → SubTerm L₁ μ n) (p : SubFormula L₁ μ k) :
    lMap Φ (Rew.substsl w p) = Rew.substsl (SubTerm.lMap Φ ∘ w) (lMap Φ p) := lMap_bind _ _ _

lemma lMap_shift (p : SyntacticSubFormula L₁ n) : lMap Φ (Rew.shiftl p) = Rew.shiftl (lMap Φ p) := lMap_bind _ _ _

lemma lMap_free (p : SyntacticSubFormula L₁ (n + 1)) : lMap Φ (Rew.freel p) = Rew.freel (lMap Φ p) := by
  simp[Rew.freel, Rew.free, lMap_bind, Function.comp, Matrix.comp_vecConsLast]
  
lemma lMap_fix (p : SyntacticSubFormula L₁ n) : lMap Φ (Rew.fixl p) = Rew.fixl (lMap Φ p) :=
  by simp[Rew.fixl, Rew.fix, lMap_bind, Function.comp, Rew.bindl]; congr; { funext x; cases x <;> simp }

lemma lMap_emb {o : Type w} [IsEmpty o] (p : SubFormula L₁ o n) :
    (lMap Φ (Rew.embl p) : SubFormula L₂ μ n) = Rew.embl (lMap Φ p) := lMap_bind _ _ _

variable [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

noncomputable def langFun : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.bunionᵢ Finset.univ (fun i => (v i).lang)
  | _, nrel _ v => Finset.bunionᵢ Finset.univ (fun i => (v i).lang)
  | _, p ⋏ q    => langFun p ∪ langFun q 
  | _, p ⋎ q    => langFun p ∪ langFun q 
  | _, ∀' p     => langFun p 
  | _, ∃' p     => langFun p 

noncomputable def langRel : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, p ⋏ q    => langRel p ∪ langRel q 
  | _, p ⋎ q    => langRel p ∪ langRel q 
  | _, ∀' p     => langRel p 
  | _, ∃' p     => langRel p

lemma langFun_rel_ss {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) (i) :
    (v i).lang ⊆ (rel r v).langFun :=
  by intros x; simp[langFun]; intros h; exact ⟨i, h⟩

end SubFormula

abbrev Theory (L : Language.{u}) := Set (Sentence L)

abbrev SyntacticTheory (L : Language.{u}) := Set (SyntacticFormula L)

class SubTheory (T U : Theory L) where
  sub : T ⊆ U

namespace SubTheory

variable {T U T₁ T₂ T₃ : Theory L}

instance : SubTheory T T := ⟨by rfl⟩

def trans [SubTheory T₁ T₂] [SubTheory T₂ T₃] : SubTheory T₁ T₃ := ⟨subset_trans (sub (T := T₁) (U := T₂)) sub⟩

end SubTheory

def Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := SubFormula.lMap Φ '' T

end FirstOrder