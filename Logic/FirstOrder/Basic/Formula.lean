import Logic.FirstOrder.Basic.Term

namespace LO

namespace FirstOrder

inductive Subformula (L : Language.{u}) (μ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : Subformula L μ n
  | falsum {n} : Subformula L μ n
  | rel    {n} : {arity : ℕ} → L.rel arity → (Fin arity → Subterm L μ n) → Subformula L μ n
  | nrel   {n} : {arity : ℕ} → L.rel arity → (Fin arity → Subterm L μ n) → Subformula L μ n
  | and    {n} : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | or     {n} : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | all    {n} : Subformula L μ (n + 1) → Subformula L μ n
  | ex     {n} : Subformula L μ (n + 1) → Subformula L μ n

abbrev Formula (L : Language.{u}) (μ : Type v) := Subformula L μ 0

abbrev Sentence (L : Language.{u}) := Formula L Empty

abbrev Subsentence (L : Language.{u}) (n : ℕ) := Subformula L Empty n

abbrev SyntacticSubformula (L : Language.{u}) (n : ℕ) := Subformula L ℕ n

abbrev SyntacticFormula (L : Language.{u}) := SyntacticSubformula L 0

namespace Subformula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def neg {n} : Subformula L μ n → Subformula L μ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and p q  => or (neg p) (neg q)
  | or p q   => and (neg p) (neg q)
  | all p    => ex (neg p)
  | ex p     => all (neg p)

lemma neg_neg (p : Subformula L μ n) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : LogicSymbol (Subformula L μ n) where
  tilde := neg
  arrow := fun p q => or (neg p) q
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : UnivQuantifier (Subformula L μ) := ⟨all⟩

instance : ExQuantifier (Subformula L μ) := ⟨ex⟩

section ToString

variable [∀ k, ToString (L.func k)] [∀ k, ToString (L.rel k)] [ToString μ]

def toStr : ∀ {n}, Subformula L μ n → String
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

instance : Repr (Subformula L μ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Subformula L μ n) := ⟨toStr⟩

end ToString

@[simp] lemma neg_top : ~(⊤ : Subformula L μ n) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : Subformula L μ n) = ⊤ := rfl

@[simp] lemma neg_rel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : ~(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : ~(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (p q : Subformula L μ n) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

@[simp] lemma neg_or (p q : Subformula L μ n) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

@[simp] lemma neg_all (p : Subformula L μ (n + 1)) : ~(∀' p) = ∃' ~p := rfl

@[simp] lemma neg_ex (p : Subformula L μ (n + 1)) : ~(∃' p) = ∀' ~p := rfl

@[simp] lemma neg_neg' (p : Subformula L μ n) : ~~p = p := neg_neg p

@[simp] lemma neg_inj (p q : Subformula L μ n) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (~·) h
  · exact congr_arg _

lemma neg_eq (p : Subformula L μ n) : ~p = neg p := rfl

lemma imp_eq (p q : Subformula L μ n) : p ⟶ q = ~p ⋎ q := rfl

lemma iff_eq (p q : Subformula L μ n) : p ⟷ q = (~p ⋎ q) ⋏ (~q ⋎ p) := rfl

lemma ball_eq (p q : Subformula L μ (n + 1)) : (∀[p] q) = ∀' (p ⟶ q) := rfl

lemma bex_eq (p q : Subformula L μ (n + 1)) : (∃[p] q) = ∃' (p ⋏ q) := rfl

@[simp] lemma neg_ball (p q : Subformula L μ (n + 1)) : ~(∀[p] q) = ∃[p] ~q := by
  simp[LogicSymbol.ball, LogicSymbol.bex, imp_eq]

@[simp] lemma neg_bex (p q : Subformula L μ (n + 1)) : ~(∃[p] q) = ∀[p] ~q := by
  simp[LogicSymbol.ball, LogicSymbol.bex, imp_eq]

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Subformula L μ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Subformula L μ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Vee.vee]

@[simp] lemma all_inj (p q : Subformula L μ (n + 1)) : ∀' p = ∀' q ↔ p = q :=
  by simp[UnivQuantifier.univ]

@[simp] lemma ex_inj (p q : Subformula L μ (n + 1)) : ∃' p = ∃' q ↔ p = q :=
  by simp[ExQuantifier.ex]

abbrev rel! (L : Language.{u}) (k) (r : L.rel k) (v : Fin k → Subterm L μ n) := rel r v

abbrev nrel! (L : Language.{u}) (k) (r : L.rel k) (v : Fin k → Subterm L μ n) := nrel r v

def complexity : {n : ℕ} → Subformula L μ n → ℕ
| _, ⊤        => 0
| _, ⊥        => 0
| _, rel _ _  => 0
| _, nrel _ _ => 0
| _, p ⋏ q    => max p.complexity q.complexity + 1
| _, p ⋎ q    => max p.complexity q.complexity + 1
| _, ∀' p     => p.complexity + 1
| _, ∃' p     => p.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Subformula L μ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Subformula L μ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (p q : Subformula L μ n) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : Subformula L μ n) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Subformula L μ n) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : Subformula L μ n) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_all (p : Subformula L μ (n + 1)) : complexity (∀' p) = p.complexity + 1 := rfl
@[simp] lemma complexity_all' (p : Subformula L μ (n + 1)) : complexity (all p) = p.complexity + 1 := rfl

@[simp] lemma complexity_ex (p : Subformula L μ (n + 1)) : complexity (∃' p) = p.complexity + 1 := rfl
@[simp] lemma complexity_ex' (p : Subformula L μ (n + 1)) : complexity (ex p) = p.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : ∀ n, Subformula L μ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → Subterm L μ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → Subterm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : Subformula L μ n), C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : Subformula L μ n), C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : Subformula L μ (n + 1)), C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : Subformula L μ (n + 1)), C n (∃' p)) :
    ∀ {n : ℕ} (p : Subformula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q
  | _, or p q   => hor p q
  | _, all p    => hall p
  | _, ex p     => hex p

@[elab_as_elim]
def rec' {C : ∀ n, Subformula L μ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → Subterm L μ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.rel k) (v : Fin k → Subterm L μ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (p q : Subformula L μ n), C n p → C n q → C n (p ⋏ q))
  (hor     : ∀ {n : ℕ} (p q : Subformula L μ n), C n p → C n q → C n (p ⋎ q))
  (hall    : ∀ {n : ℕ} (p : Subformula L μ (n + 1)), C (n + 1) p → C n (∀' p))
  (hex     : ∀ {n : ℕ} (p : Subformula L μ (n + 1)), C (n + 1) p → C n (∃' p)) :
    ∀ {n : ℕ} (p : Subformula L μ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, or p q   => hor p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, all p    => hall p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
  | _, ex p     => hex p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)

@[simp] lemma complexity_neg (p : Subformula L μ n) : complexity (~p) = complexity p :=
  by induction p using rec' <;> simp[*]

section Decidable

variable [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [DecidableEq μ]

def hasDecEq : {n : ℕ} → (p q : Subformula L μ n) → Decidable (p = q)
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

instance : DecidableEq (Subformula L μ n) := hasDecEq

end Decidable

end Subformula

namespace Rew

open Subformula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def loMap : ⦃n₁ n₂ : ℕ⦄ → Rew L μ₁ n₁ μ₂ n₂ → Subformula L μ₁ n₁ → Subformula L μ₂ n₂
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

lemma loMap_neg (p : Subformula L μ₁ n₁) :
    ω.loMap (~p) = ~ω.loMap p :=
  by induction p using Subformula.rec' generalizing n₂ <;> simp[*, loMap, ←Subformula.neg_eq]

lemma ext_loMap' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) (p : Subformula L μ₁ n₁) : ω₁.loMap p = ω₂.loMap p:= by simp[h]

lemma neg' (p : Subformula L μ₁ n₁) : ω.loMap (~p) = ~ω.loMap p := loMap_neg ω p

lemma or' (p q : Subformula L μ₁ n₁) : ω.loMap (p ⋎ q) = ω.loMap p ⋎ ω.loMap q := by rfl

def hom (ω : Rew L μ₁ n₁ μ₂ n₂) : Subformula L μ₁ n₁ →L Subformula L μ₂ n₂ where
  map_top' := by rfl
  map_bot' := by rfl
  map_neg' := ω.loMap_neg
  map_and' := fun p q => by rfl
  map_or' := fun p q => by rfl
  map_imply' := fun p q => by simp[Subformula.imp_eq, neg', or']

/-
instance : FunLike (Rew L μ₁ n₁ μ₂ n₂) (Subformula L μ₁ n₁) (fun _ => Subformula L μ₂ n₂) where
  coe := fun ω => loMap ω
  coe_injective' := fun ω₁ ω₂ h => ext_loMap ω₁ ω₂ (congr_fun h)

instance : CoeFun (Rew L μ₁ n₁ μ₂ n₂) (fun _ => Subformula L μ₁ n₁ → Subformula L μ₂ n₂) := FunLike.hasCoeToFun

scoped[FirstOrder] notation:max ω "ᵀ" => (ω : Subterm _ _ _ → Subterm _ _ _)

scoped[FirstOrder] notation:max ω "ᴾ" => (ω : Subformula _ _ _ → Subformula _ _ _)

lemma neg' (p : Subformula L μ₁ n₁) : ω (~p) = ~ω p := loMap_neg ω p

lemma or' (p q : Subformula L μ₁ n₁) : ω (p ⋎ q) = ω p ⋎ ω q := by rfl

instance : LogicSymbol.homClass (Rew L μ₁ n₁ μ₂ n₂) (Subformula L μ₁ n₁) (Subformula L μ₂ n₂) where
  map_top := fun ω => by rfl
  map_bot := fun ω => by rfl
  map_neg := loMap_neg
  map_and := fun ω p q => by rfl
  map_or := fun ω p q => by rfl
  map_imply := fun ω p q => by simp[Subformula.imp_eq, neg', or']

-/

lemma hom_eq_loMap : ω.hom = ω.loMap := rfl

protected lemma rel {k} {r : L.rel k} {v : Fin k → Subterm L μ₁ n₁} :
    ω.hom (rel r v) = rel r (fun i => ω (v i)) := rfl

protected lemma nrel {k} {r : L.rel k} {v : Fin k → Subterm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r (fun i => ω (v i)) := by rfl

lemma rel' {k} {r : L.rel k} {v : Fin k → Subterm L μ₁ n₁} :
    ω.hom (rel r v) = rel r (ω ∘ v) := by rfl

lemma nrel' {k} {r : L.rel k} {v : Fin k → Subterm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r (ω ∘ v) := by rfl

@[simp] lemma rel0 {r : L.rel 0} {v : Fin 0 → Subterm L μ₁ n₁} :
    ω.hom (rel r v) = rel r ![] := by simp[ω.rel, Matrix.empty_eq]

@[simp] lemma rel1 {r : L.rel 1} {t : Subterm L μ₁ n₁} :
    ω.hom (rel r ![t]) = rel r ![ω t] := by simp[ω.rel, Matrix.constant_eq_singleton]

@[simp] lemma rel2 {r : L.rel 2} {t₁ t₂ : Subterm L μ₁ n₁} :
    ω.hom (rel r ![t₁, t₂]) = rel r ![ω t₁, ω t₂] := by simp[ω.rel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma rel3 {r : L.rel 3} {t₁ t₂ t₃ : Subterm L μ₁ n₁} :
    ω.hom (rel r ![t₁, t₂, t₃]) = rel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.rel]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[simp] lemma nrel0 {r : L.rel 0} {v : Fin 0 → Subterm L μ₁ n₁} :
    ω.hom (nrel r v) = nrel r ![] := by simp[ω.nrel, Matrix.empty_eq]

@[simp] lemma nrel1 {r : L.rel 1} {t : Subterm L μ₁ n₁} :
    ω.hom (nrel r ![t]) = nrel r ![ω t] := by simp[ω.nrel, Matrix.constant_eq_singleton]

@[simp] lemma nrel2 {r : L.rel 2} {t₁ t₂ : Subterm L μ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂]) = nrel r ![ω t₁, ω t₂] := by simp[ω.nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma nrel3 {r : L.rel 3} {t₁ t₂ t₃ : Subterm L μ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂, t₃]) = nrel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.nrel]; funext i; induction' i using Fin.induction with i <;> simp; induction' i using Fin.induction with i <;> simp

@[simp] protected lemma all {p : Subformula L μ₁ (n₁ + 1)} :
    ω.hom (∀' p) = ∀' ω.q.hom p := by rfl

@[simp] protected lemma ex {p : Subformula L μ₁ (n₁ + 1)} :
    ω.hom (∃' p) = ∃' ω.q.hom p := by rfl

@[simp] protected lemma ball {p q : Subformula L μ₁ (n₁ + 1)} :
    ω.hom (∀[p] q) = ∀[ω.q.hom p] ω.q.hom q := by simp[ball_eq]

@[simp] protected lemma bex {p q : Subformula L μ₁ (n₁ + 1)} :
    ω.hom (∃[p] q) = ∃[ω.q.hom p] ω.q.hom q := by simp[bex_eq]

attribute [irreducible] hom

@[simp] lemma complexity (p : Subformula L μ₁ n₁) : (ω.hom p).complexity = p.complexity := by
  induction p using Subformula.rec' generalizing n₂ <;> simp[*, Rew.rel, Rew.nrel]

lemma hom_ext' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) {p} : ω₁.hom p = ω₂.hom p := by simp[h]

end

@[simp] lemma hom_id_eq : (Rew.id.hom : Subformula L μ n →L Subformula L μ n) = LogicSymbol.Hom.id := by
  ext p; induction p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel, *]

lemma hom_comp_eq (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) : (ω₂.comp ω₁).hom = ω₂.hom.comp ω₁.hom := by
  ext p; simp; induction p using Subformula.rec' generalizing n₂ n₃ <;> simp[Rew.rel, Rew.nrel, comp_app, q_comp, *]

lemma hom_comp_app (ω₂ : Rew L μ₂ n₂ μ₃ n₃) (ω₁ : Rew L μ₁ n₁ μ₂ n₂) (p : Subformula L μ₁ n₁) :
    (ω₂.comp ω₁).hom p = ω₂.hom (ω₁.hom p) := by simp[hom_comp_eq]

lemma mapl_inj : ∀ {n₁ n₂ μ₁ μ₂} {b : Fin n₁ → Fin n₂} {e : μ₁ → μ₂},
    (hb : Function.Injective b) → (hf : Function.Injective e) → Function.Injective $ (map (L := L) b e).hom
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

lemma emb.hom_Injective {o} [e : IsEmpty o] : Function.Injective (emb.hom : Subformula L o n → Subformula L μ n) :=
  by simp[emb]; exact mapl_inj Function.injective_id (fun x => IsEmpty.elim e x)

lemma shift.hom_Injective : Function.Injective (shift.hom : SyntacticSubformula L n → SyntacticSubformula L n) :=
  by simp[shift]; exact mapl_inj Function.injective_id Nat.succ_injective

@[simp] lemma hom_fix_free (p : SyntacticSubformula L (n + 1)) :
    fix.hom (free.hom p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_free_fix (p : SyntacticSubformula L n) :
    free.hom (fix.hom p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_substs_mbar_zero_comp_shift_eq_free (p : SyntacticSubformula L 1) :
    (substs ![&0]).hom (Rew.shift.hom p) = free.hom p := by simp[←hom_comp_app, substs_mbar_zero_comp_shift_eq_free]

@[simp] protected lemma emb_univClosure {o} [e : IsEmpty o] {σ : Subformula L o n} :
    (emb.hom (univClosure σ) : Subformula L μ 0) = univClosure (emb.hom σ) := by induction n <;> simp[*]

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

@[simp] lemma eq_top_iff {p : Subformula L μ₁ n₁} : ω.hom p = ⊤ ↔ p = ⊤ := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_bot_iff {p : Subformula L μ₁ n₁} : ω.hom p = ⊥ ↔ p = ⊥ := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_rel_iff {p : Subformula L μ₁ n₁} {k} {r : L.rel k} {v} :
    ω.hom p = Subformula.rel r v ↔ ∃ v', ω ∘ v' = v ∧ p = Subformula.rel r v' := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]
  case hrel k' r' v =>
    by_cases hk : k' = k <;> simp[hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp[hr, Function.funext_iff]

lemma eq_nrel_iff {p : Subformula L μ₁ n₁} {k} {r : L.rel k} {v} :
    ω.hom p = Subformula.nrel r v ↔ ∃ v', ω ∘ v' = v ∧ p = Subformula.nrel r v' := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]
  case hnrel k' r' v =>
    by_cases hk : k' = k <;> simp[hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp[hr, Function.funext_iff]

@[simp] lemma eq_and_iff {p : Subformula L μ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⋏ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⋏ p₂ := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_or_iff {p : Subformula L μ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⋎ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⋎ p₂ := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_all_iff {p : Subformula L μ₁ n₁} {q} :
    ω.hom p = ∀' q ↔ ∃ p', ω.q.hom p' = q ∧ p = ∀' p' := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_ex_iff {p : Subformula L μ₁ n₁} {q} :
    ω.hom p = ∃' q ↔ ∃ p', ω.q.hom p' = q ∧ p = ∃' p' := by
  cases p using Subformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_neg_iff {p : Subformula L μ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⟶ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⟶ p₂ := by
  simp[imp_eq]; constructor
  · rintro ⟨p₁, hp₁, q₂, rfl, rfl⟩; exact ⟨~p₁, by simp[hp₁]⟩
  · rintro ⟨p₁, rfl, p₂, rfl, rfl⟩; exact ⟨~p₁, by simp, p₂, by simp⟩

lemma eq_ball_iff {p : Subformula L μ₁ n₁} {q₁ q₂} :
    (ω.hom p = ∀[q₁] q₂) ↔ ∃ p₁ p₂, ω.q.hom p₁ = q₁ ∧ ω.q.hom p₂ = q₂ ∧ p = ∀[p₁] p₂ := by
  simp[LogicSymbol.ball, eq_all_iff]; constructor
  · rintro ⟨p', ⟨p₁, rfl, p₂, rfl, rfl⟩, rfl⟩; exact ⟨p₁, rfl, p₂, rfl, rfl⟩
  · rintro ⟨p₁, rfl, p₂, rfl, rfl⟩; simp; exact ⟨p₁, rfl, p₂, rfl, rfl⟩

end Rew

scoped syntax (name := substsHomNotation) term:max "/[" term,* "]" : term

scoped macro_rules (kind := substsHomNotation)
  | `($p:term /[$terms:term,*]) => `((Rew.substs ![$terms,*]).hom $p)

namespace Subformula

variable {L : Language.{u}} {μ : Type v} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def shiftEmb : SyntacticSubformula L n ↪ SyntacticSubformula L n where
  toFun := Rew.shift.hom
  inj' := Rew.shift.hom_Injective

lemma shiftEmb_eq_shift (p : SyntacticSubformula L n) :
  shiftEmb p = Rew.shift.hom p := rfl

def qr : ∀ {n}, Subformula L μ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, p ⋏ q    => max p.qr q.qr
  | _, p ⋎ q    => max p.qr q.qr
  | _, ∀' p     => p.qr + 1
  | _, ∃' p     => p.qr + 1

@[simp] lemma qr_top : (⊤ : Subformula L μ n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : Subformula L μ n).qr = 0 := rfl

@[simp] lemma qr_rel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : (rel r v).qr = 0 := rfl

@[simp] lemma qr_nrel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : (nrel r v).qr = 0 := rfl

@[simp] lemma qr_and (p q : Subformula L μ n) : (p ⋏ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : Subformula L μ n) : (p ⋎ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_all (p : Subformula L μ (n + 1)) : (∀' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : Subformula L μ (n + 1)) : (∃' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_neg (p : Subformula L μ n) : (~p).qr = p.qr := by
  induction' p using rec' <;> simp[*]

@[simp] lemma qr_imply (p q : Subformula L μ n) : (p ⟶ q).qr = max p.qr q.qr :=
  by simp[imp_eq]

@[simp] lemma qr_iff (p q : Subformula L μ n) : (p ⟷ q).qr = max p.qr q.qr :=
  by simp[iff_eq, total_of]

def qfree (p : Subformula L μ n) : Prop := p.qr = 0

@[simp] lemma qfree_top : (⊤ : Subformula L μ n).qfree := rfl

@[simp] lemma qfree_bot : (⊥ : Subformula L μ n).qfree := rfl

@[simp] lemma qfree_rel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : (rel r v).qfree := rfl

@[simp] lemma qfree_nrel {k} (r : L.rel k) (v : Fin k → Subterm L μ n) : (nrel r v).qfree := rfl

@[simp] lemma qfree_and {p q : Subformula L μ n} : (p ⋏ q).qfree ↔ p.qfree ∧ q.qfree := by simp[qfree]

@[simp] lemma qfree_or {p q : Subformula L μ n} : (p ⋎ q).qfree ↔ p.qfree ∧ q.qfree := by simp[qfree]

@[simp] lemma not_qfree_all {p : Subformula L μ (n + 1)} : ¬(∀' p).qfree := by simp[qfree]

@[simp] lemma not_qfree_ex {p : Subformula L μ (n + 1)} : ¬(∃' p).qfree := by simp[qfree]

@[simp] lemma qfree_neg {p : Subformula L μ n} : (~p).qfree ↔ p.qfree := by
  simp[qfree]

@[simp] lemma qfree_imply {p q : Subformula L μ n} : (p ⟶ q).qfree ↔ p.qfree ∧ q.qfree :=
  by simp[qfree]

@[simp] lemma qfree_iff {p q : Subformula L μ n} : (p ⟷ q).qfree ↔ p.qfree ∧ q.qfree :=
  by simp[qfree]

structure Operator (L : Language.{u}) (n : ℕ) where
  sentence : Subsentence L n

abbrev Const (L : Language.{u}) := Operator L 0

namespace Operator

def operator {arity : ℕ} (o : Operator L arity) (v : Fin arity → Subterm L μ n) : Subformula L μ n :=
  (Rew.substs v).hom (Rew.emb.hom o.sentence)

def const (c : Const L) : Subformula L μ n := c.operator ![]

instance : Coe (Const L) (Subformula L μ n) := ⟨Operator.const⟩

def comp (o : Operator L k) (w : Fin k → Subterm.Operator L l) : Operator L l :=
  ⟨o.operator (fun x => (w x).term)⟩

lemma operator_comp (o : Operator L k) (w : Fin k → Subterm.Operator L l) (v : Fin l → Subterm L μ n) :
  (o.comp w).operator v = o.operator (fun x => (w x).operator v) := by
    simp[operator, comp, ←Rew.hom_comp_app]; congr 2
    ext <;> simp[Rew.comp_app]
    · congr
    · contradiction

def and {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋏ o₂.sentence⟩

def or {k} (o₁ o₂ : Operator L k) : Operator L k := ⟨o₁.sentence ⋎ o₂.sentence⟩

@[simp] lemma operator_and (o₁ o₂ : Operator L k) (v : Fin k → Subterm L μ n) :
  (o₁.and o₂).operator v = o₁.operator v ⋏ o₂.operator v := by simp[operator, and]

@[simp] lemma operator_or (o₁ o₂ : Operator L k) (v : Fin k → Subterm L μ n) :
  (o₁.or o₂).operator v = o₁.operator v ⋎ o₂.operator v := by simp[operator, or]

protected class Eq (L : Language) where
  eq : Subformula.Operator L 2

protected class LT (L : Language) where
  lt : Subformula.Operator L 2

protected class LE (L : Language) where
  le : Subformula.Operator L 2

protected class Mem (L : Language) where
  mem : Subformula.Operator L 2

instance [Language.Eq L] : Operator.Eq L := ⟨⟨Subformula.rel Language.Eq.eq Subterm.bvar⟩⟩

instance [Language.LT L] : Operator.LT L := ⟨⟨Subformula.rel Language.LT.lt Subterm.bvar⟩⟩

instance [Operator.Eq L] [Operator.LT L] : Operator.LE L := ⟨Eq.eq.or LT.lt⟩

lemma Eq.sentence_eq [L.Eq] : (@Operator.Eq.eq L _).sentence = Subformula.rel Language.Eq.eq Subterm.bvar := rfl

lemma LT.sentence_eq [L.LT] : (@Operator.LT.lt L _).sentence = Subformula.rel Language.LT.lt Subterm.bvar := rfl

lemma LE.def_of_Eq_of_LT [Operator.Eq L] [Operator.LT L] :
    (@Operator.LE.le L _) = Eq.eq.or LT.lt := rfl

end Operator

@[elab_as_elim]
def formulaRec {C : SyntacticFormula L → Sort _}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hrel    : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (rel r v))
  (hnrel   : ∀ {l : ℕ} (r : L.rel l) (v : Fin l → SyntacticTerm L), C (nrel r v))
  (hand    : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋎ q))
  (hall    : ∀ (p : SyntacticSubformula L 1), C (Rew.free.hom p) → C (∀' p))
  (hex     : ∀ (p : SyntacticSubformula L 1), C (Rew.free.hom p) → C (∃' p)) :
    ∀ (p : SyntacticFormula L), C p
  | ⊤        => hverum
  | ⊥        => hfalsum
  | rel r v  => hrel r v
  | nrel r v => hnrel r v
  | p ⋏ q    => hand p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | p ⋎ q    => hor p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p) (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | ∀' p     => hall p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.free.hom p))
  | ∃' p     => hex p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.free.hom p))
  termination_by formulaRec _ _ _ _ _ _ _ _ p => p.complexity

def fvarList : {n : ℕ} → Subformula L μ n → List μ
  | _, ⊤        => []
  | _, ⊥        => []
  | _, rel _ v  => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, nrel _ v => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, p ⋏ q    => p.fvarList ++ q.fvarList
  | _, p ⋎ q    => p.fvarList ++ q.fvarList
  | _, ∀' p     => p.fvarList
  | _, ∃' p     => p.fvarList

abbrev fvar? (p : Subformula L μ n) (x : μ) : Prop := x ∈ p.fvarList

@[simp] lemma fvarList_top : fvarList (⊤ : Subformula L μ n) = [] := rfl

@[simp] lemma fvarList_bot : fvarList (⊥ : Subformula L μ n) = [] := rfl

@[simp] lemma fvarList_all (p : Subformula L μ (n + 1)) : fvarList (∀' p) = fvarList p := rfl

@[simp] lemma fvarList_ex (p : Subformula L μ (n + 1)) : fvarList (∃' p) = fvarList p := rfl

@[simp] lemma fvarList_neg (p : Subformula L μ n) : fvarList (~p) = fvarList p := by
  induction p using rec' <;> simp[*, fvarList, ←neg_eq]

@[simp] lemma fvarList_sentence {o : Type w} [IsEmpty o] (p : Subformula L o n) : fvarList p = [] := by
  induction p using rec' <;> simp[*, fvarList, ←neg_eq]

@[simp] lemma fvarList_emb {o : Type w} [IsEmpty o] (p : Subformula L o n) : fvarList (Rew.emb.hom p : Subformula L μ n) = [] := by
  induction p using rec' <;> simp[*, Rew.rel, Rew.nrel, fvarList, ←neg_eq]

lemma rew_eq_of_funEqOn {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} {p}
  (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : Function.funEqOn (fvar? p) (ω₁ ∘ Subterm.fvar) (ω₂ ∘ Subterm.fvar)) :
    ω₁.hom p = ω₂.hom p := by
  induction p using rec' generalizing n₂ <;> simp[*, Rew.rel, Rew.nrel] <;> simp[fvar?, fvarList] at hf
  case hrel =>
    funext i
    exact Subterm.rew_eq_of_funEqOn _ _ _ hb (hf.of_subset (by intro x hx; exact ⟨i, hx⟩))
  case hnrel =>
    funext i
    exact Subterm.rew_eq_of_funEqOn _ _ _ hb (hf.of_subset (by intro x hx; exact ⟨i, hx⟩))
  case hand ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hor ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hall ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb]) (fun x hx => by simp; exact congr_arg _ (hf x hx))
  case hex ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb]) (fun x hx => by simp; exact congr_arg _ (hf x hx))

lemma rew_eq_of_funEqOn₀ {ω₁ ω₂ : Rew L μ₁ 0 μ₂ n₂} {p} (hf : Function.funEqOn (fvar? p) (ω₁ ∘ Subterm.fvar) (ω₂ ∘ Subterm.fvar)) : ω₁.hom p = ω₂.hom p :=
  rew_eq_of_funEqOn (fun x => Fin.elim0 x) hf

def upper (p : SyntacticSubformula L n) : ℕ := Finset.sup p.fvarList.toFinset id + 1

lemma not_fvar?_of_lt_upper (p : SyntacticSubformula L n) (h : p.upper ≤ m) : ¬fvar? p m := by
  simp[upper, Nat.add_one_le_iff, fvar?] at h ⊢
  intro hm
  have : m ≤ Finset.sup p.fvarList.toFinset id :=
    Finset.le_sup (s := p.fvarList.toFinset) (b := m) (f := id) (by simpa using hm)
  exact irrefl_of _ _ $ lt_of_lt_of_le h this

@[simp] lemma not_fvar?_upper (p : SyntacticSubformula L n) : ¬fvar? p p.upper :=
  not_fvar?_of_lt_upper p (by simp)

lemma ne_of_ne_complexity {p q : Subformula L μ n} (h : p.complexity ≠ q.complexity) : p ≠ q :=
  by rintro rfl; contradiction

@[simp] lemma ex_ne_subst (p : Subformula L μ 1) (t) : [→ t].hom p ≠ ∃' p := ne_of_ne_complexity (by simp)

@[simp] lemma ne_or_left (p q : Subformula L μ n) : p ≠ p ⋎ q := ne_of_ne_complexity (by simp)

@[simp] lemma ne_or_right (p q : Subformula L μ n) : q ≠ p ⋎ q := ne_of_ne_complexity (by simp)

inductive Open : {n : ℕ} → Subformula L μ n → Prop
  | verum                      : Open ⊤
  | falsum                     : Open ⊥
  | rel {k} (r : L.rel k) (v)  : Open (rel r v)
  | nrel {k} (r : L.rel k) (v) : Open (nrel r v)
  | and {p q : Subformula L μ n}   : Open p → Open q → Open (p ⋏ q)
  | or {p q : Subformula L μ n}    : Open p → Open q → Open (p ⋎ q)

attribute [simp] Open.verum Open.falsum Open.rel Open.nrel

variable {L : Language.{u}} {L₁ : Language.{u₁}} {{L₂ : Language.{u₂}}} {L₃ : Language.{u₃}} {μ : Type v} {Φ : L₁ →ᵥ L₂}

def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, Subformula L₁ μ n → Subformula L₂ μ n
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | _, rel r v  => rel (Φ.rel r) (Subterm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (Subterm.lMap Φ ∘ v)
  | _, p ⋏ q    => lMapAux Φ p ⋏ lMapAux Φ q
  | _, p ⋎ q    => lMapAux Φ p ⋎ lMapAux Φ q
  | _, ∀' p     => ∀' lMapAux Φ p
  | _, ∃' p     => ∃' lMapAux Φ p

lemma lMapAux_neg {n} (p : Subformula L₁ μ n) :
    (~p).lMapAux Φ = ~p.lMapAux Φ :=
  by induction p using Subformula.rec' <;> simp[*, lMapAux, ←Subformula.neg_eq]

def lMap (Φ : L₁ →ᵥ L₂) {n} : Subformula L₁ μ n →L Subformula L₂ μ n where
  toTr := lMapAux Φ
  map_top' := by simp[lMapAux]
  map_bot' := by simp[lMapAux]
  map_and' := by simp[lMapAux]
  map_or'  := by simp[lMapAux]
  map_neg' := by simp[lMapAux_neg]
  map_imply' := by simp[Subformula.imp_eq, lMapAux_neg, ←Subformula.neg_eq, lMapAux]

lemma lMap_rel {k} (r : L₁.rel k) (v : Fin k → Subterm L₁ μ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

lemma lMap_nrel {k} (r : L₁.rel k) (v : Fin k → Subterm L₁ μ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_all (p : Subformula L₁ μ (n + 1)) :
    lMap Φ (∀' p) = ∀' lMap Φ p := rfl

@[simp] lemma lMap_ex (p : Subformula L₁ μ (n + 1)) :
    lMap Φ (∃' p) = ∃' lMap Φ p := rfl

lemma lMap_bind (b : Fin n₁ → Subterm L₁ μ₂ n₂) (e : μ₁ → Subterm L₁ μ₂ n₂) (p) :
    lMap Φ ((Rew.bind b e).hom p) = (Rew.bind (Subterm.lMap Φ ∘ b) (Subterm.lMap Φ ∘ e)).hom (lMap Φ p) := by
  induction p using rec' generalizing μ₂ n₂ <;>
  simp[*, Rew.rel, Rew.nrel, lMap_rel, lMap_nrel, Subterm.lMap_bind, Rew.q_bind, Matrix.comp_vecCons', Subterm.lMap_bShift, Function.comp]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : μ₁ → μ₂) (p) :
    lMap Φ ((Rew.map b e).hom p) = (Rew.map b e).hom (lMap Φ p) := lMap_bind _ _ _

lemma lMap_rewrite (f : μ → Subterm L₁ μ n) (p : Subformula L₁ μ n) :
    lMap Φ ((Rew.rewrite f).hom p) = (Rew.rewrite (Subterm.lMap Φ ∘ f)).hom (lMap Φ p) :=
  by simp[Rew.rewrite, lMap_bind, Function.comp]

lemma lMap_substs (w : Fin k → Subterm L₁ μ n) (p : Subformula L₁ μ k) :
    lMap Φ ((Rew.substs w).hom p) = (Rew.substs (Subterm.lMap Φ ∘ w)).hom (lMap Φ p) := lMap_bind _ _ _

lemma lMap_shift (p : SyntacticSubformula L₁ n) : lMap Φ (Rew.shift.hom p) = Rew.shift.hom (lMap Φ p) := lMap_bind _ _ _

lemma lMap_free (p : SyntacticSubformula L₁ (n + 1)) : lMap Φ (Rew.free.hom p) = Rew.free.hom (lMap Φ p) := by
  simp[Rew.free, lMap_bind, Function.comp, Matrix.comp_vecConsLast]

lemma lMap_fix (p : SyntacticSubformula L₁ n) : lMap Φ (Rew.fix.hom p) = Rew.fix.hom (lMap Φ p) :=
  by simp[Rew.fix, lMap_bind, Function.comp]; congr; { funext x; cases x <;> simp }

lemma lMap_emb {o : Type w} [IsEmpty o] (p : Subformula L₁ o n) :
    (lMap Φ (Rew.emb.hom p) : Subformula L₂ μ n) = Rew.emb.hom (lMap Φ p) := lMap_bind _ _ _

end Subformula

namespace Rew

open Subformula

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {μ μ' : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂} {μ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma hom_operator (o : Operator L k) (v : Fin k → Subterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator (fun i => ω (v i)) := by
  simp[Operator.operator, ←Rew.hom_comp_app]; congr 2
  ext <;> simp[Rew.comp_app]; contradiction

lemma hom_operator' (o : Operator L k) (v : Fin k → Subterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator (ω ∘ v) := ω.hom_operator o v

@[simp] lemma hom_finitary0 (o : Operator L 0) (v : Fin 0 → Subterm L μ₁ n₁) :
    ω.hom (o.operator v) = o.operator ![] := by simp[ω.hom_operator', Matrix.empty_eq]

@[simp] lemma hom_finitary1 (o : Operator L 1) (t : Subterm L μ₁ n₁) :
    ω.hom (o.operator ![t]) = o.operator ![ω t] := by simp[ω.hom_operator']

@[simp] lemma hom_finitary2 (o : Operator L 2) (t₁ t₂ : Subterm L μ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp[ω.hom_operator']

@[simp] lemma hom_finitary3 (o : Operator L 3) (t₁ t₂ t₃ : Subterm L μ₁ n₁) :
    ω.hom (o.operator ![t₁, t₂, t₃]) = o.operator ![ω t₁, ω t₂, ω t₃] := by simp[ω.hom_operator']

@[simp] lemma hom_const (o : Const L) : ω.hom (Operator.const c) = Operator.const c := by
  simp[Operator.const, ω.hom_operator']

end Rew

abbrev Theory (L : Language.{u}) := Set (Sentence L)

abbrev SyntacticTheory (L : Language.{u}) := Set (SyntacticFormula L)

def Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Subformula.lMap Φ '' T

end FirstOrder

end LO
