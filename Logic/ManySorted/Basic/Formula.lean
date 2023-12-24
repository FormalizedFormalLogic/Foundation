import Logic.ManySorted.Basic.Term

namespace LO

namespace ManySorted

inductive Semiformula {S : Type w} [DecidableEq S] (L : Language.{w, u} S) (μ : S → Type v) : (S → ℕ) → Type _
  | verum  {n}                  : Semiformula L μ n
  | falsum {n}                  : Semiformula L μ n
  | rel    {n} {arity : S → ℕ} : L.Rel arity → ((s : S) → (i : Fin (arity s)) → Semiterm s L μ n) → Semiformula L μ n
  | nrel   {n} {arity : S → ℕ} : L.Rel arity → ((s : S) → (i : Fin (arity s)) → Semiterm s L μ n) → Semiformula L μ n
  | and    {n}                  : Semiformula L μ n → Semiformula L μ n → Semiformula L μ n
  | or     {n}                  : Semiformula L μ n → Semiformula L μ n → Semiformula L μ n
  | call   {n : S → ℕ} (s : S) : Semiformula L μ (Nat.indexedSucc s n) → Semiformula L μ (Nat.indexedSucc s n) → Semiformula L μ n
  | cex    {n : S → ℕ} (s : S) : Semiformula L μ (Nat.indexedSucc s n) → Semiformula L μ (Nat.indexedSucc s n) → Semiformula L μ n

variable {S : Type w} [DecidableEq S]

abbrev Formula (L : Language.{w, u} S) (μ : S → Type v) := Semiformula L μ 0

abbrev Sentence (L : Language.{w, u} S) := Formula L (fun _ => Empty)

abbrev Semisentence (L : Language.{w, u} S) (n : ℕ) := Semiformula L (fun _ => Empty) n

abbrev SyntacticSemiformula (L : Language.{w, u} S) (n : ℕ) := Semiformula L (fun _ => ℕ) n

abbrev SyntacticFormula (L : Language.{w, u} S) := SyntacticSemiformula L 0

namespace Semiformula
variable
  {L : Language.{w, u} S} {L₁ : Language.{w, u₁} S} {L₂ : Language.{w, u₂} S} {L₃ : Language.{w, u₃} S}
  {μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂} {μ₃ : S → Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : S → ℕ}

def neg {n} : Semiformula L μ n → Semiformula L μ n
  | verum      => falsum
  | falsum     => verum
  | rel r v    => nrel r v
  | nrel r v   => rel r v
  | and p q    => or (neg p) (neg q)
  | or p q     => and (neg p) (neg q)
  | call s q p => cex s q (neg p)
  | cex s q p  => call s q (neg p)

lemma neg_neg (p : Semiformula L μ n) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : LogicSymbol (Semiformula L μ n) where
  tilde := neg
  arrow := fun p q => or (neg p) q
  wedge := and
  vee := or
  top := verum
  bot := falsum

scoped[LO.ManySorted] notation:64 "∀[" q " ∷" s "] " p:64 => Semiformula.call s q p

scoped[LO.ManySorted] notation:64 "∃[" q " ∷" s "] " p:64 => Semiformula.cex s q p

def all (s : S) (p : Semiformula L μ (Nat.indexedSucc s n)) : Semiformula L μ n := ∀[⊤ ∷s] p

def ex (s : S) (p : Semiformula L μ (Nat.indexedSucc s n)) : Semiformula L μ n := ∃[⊤ ∷s] p

scoped[LO.ManySorted] notation:64 "∀[∷" s "] " p:64 => Semiformula.all s p

scoped[LO.ManySorted] notation:64 "∃[∷" s "] " p:64 => Semiformula.ex s p

@[simp] lemma neg_top : ~(⊤ : Semiformula L μ n) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : Semiformula L μ n) = ⊤ := rfl

@[simp] lemma neg_rel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → (i : Fin (k s)) → Semiterm s L μ n) : ~(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → (i : Fin (k s)) → Semiterm s L μ n) : ~(nrel r v) = rel r v := rfl

lemma neg_and (p q : Semiformula L μ n) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

lemma neg_or (p q : Semiformula L μ n) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

lemma neg_call (s : S) (q p : Semiformula L μ (Nat.indexedSucc s n)) : ~(∀[q ∷s] p) = ∃[q ∷s] ~p := rfl

lemma neg_cex (q p : Semiformula L μ (Nat.indexedSucc s n)) : ~(∃[q ∷s] p) = ∀[q ∷s] ~p := rfl

lemma neg_all (s : S) (p : Semiformula L μ (Nat.indexedSucc s n)) : ~(∀[∷s] p) = ∃[∷s] ~p := rfl

lemma neg_ex (s : S) (p : Semiformula L μ (Nat.indexedSucc s n)) : ~(∃[∷s] p) = ∀[∷s] ~p := rfl

lemma neg_neg' (p : Semiformula L μ n) : ~~p = p := neg_neg p

@[simp] lemma neg_inj (p q : Semiformula L μ n) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa[neg_neg'] using congr_arg (~·) h
  · exact congr_arg _

lemma neg_eq (p : Semiformula L μ n) : ~p = neg p := rfl

lemma imp_eq (p q : Semiformula L μ n) : p ⟶ q = ~p ⋎ q := rfl

lemma iff_eq (p q : Semiformula L μ n) : p ⟷ q = (~p ⋎ q) ⋏ (~q ⋎ p) := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Semiformula L μ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Semiformula L μ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Vee.vee]

@[simp] lemma call_inj (p₁ q₁ p₂ q₂ : Semiformula L μ (Nat.indexedSucc s n)) : ∀[q₁ ∷s] p₁ = ∀[q₂ ∷s] p₂ ↔ q₁ = q₂ ∧ p₁ = p₂ :=
  by simp

@[simp] lemma cex_inj  (p₁ q₁ p₂ q₂ : Semiformula L μ (Nat.indexedSucc s n)) : ∃[q₁ ∷s] p₁ = ∃[q₂ ∷s] p₂ ↔ q₁ = q₂ ∧ p₁ = p₂ :=
  by simp

@[simp] lemma all_inj (p₁ p₂ : Semiformula L μ (Nat.indexedSucc s n)) : ∀[∷s] p₁ = ∀[∷s] p₂ ↔ p₁ = p₂ := by simp[Semiformula.all]

@[simp] lemma ex_inj (p₁ p₂ : Semiformula L μ (Nat.indexedSucc s n)) : ∃[∷s] p₁ = ∃[∷s] p₂ ↔ p₁ = p₂ := by simp[Semiformula.ex]

def complexity : {n : S → ℕ} → Semiformula L μ n → ℕ
| _, ⊤         => 0
| _, ⊥         => 0
| _, rel _ _   => 0
| _, nrel _ _  => 0
| _, p ⋏ q     => max p.complexity q.complexity + 1
| _, p ⋎ q     => max p.complexity q.complexity + 1
| _, ∀[q ∷_] p => max q.complexity p.complexity + 1
| _, ∃[q ∷_] p => max q.complexity p.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformula L μ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L μ n) = 0 := rfl

@[simp] lemma complexity_rel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → Fin (k s) → Semiterm s L μ n) :
    complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → Fin (k s) → Semiterm s L μ n) :
    complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (p q : Semiformula L μ n) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : Semiformula L μ n) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Semiformula L μ n) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : Semiformula L μ n) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_call (q p : Semiformula L μ (Nat.indexedSucc s n)) :
    complexity (∀[q ∷s] p) = max q.complexity p.complexity + 1 := rfl

@[simp] lemma complexity_cex (q p : Semiformula L μ (Nat.indexedSucc s n)) :
    complexity (∃[q ∷s] p) = max q.complexity p.complexity + 1 := rfl

@[simp] lemma complexity_all (p : Semiformula L μ (Nat.indexedSucc s n)) :
    complexity (∀[∷s] p) = p.complexity + 1 := by simp[all]

@[simp] lemma complexity_ex (p : Semiformula L μ (Nat.indexedSucc s n)) :
    complexity (∃[∷s] p) = p.complexity + 1 := by simp[ex]

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L μ n → Sort*}
  (hverum  : ∀ {n : S → ℕ}, C n ⊤)
  (hfalsum : ∀ {n : S → ℕ}, C n ⊥)
  (hrel    : ∀ {n : S → ℕ} {arity : S → ℕ} (r : L.Rel arity) (v : (s : S) → (i : Fin (arity s)) → Semiterm s L μ n), C n (rel r v))
  (hnrel   : ∀ {n : S → ℕ} {arity : S → ℕ} (r : L.Rel arity) (v : (s : S) → (i : Fin (arity s)) → Semiterm s L μ n), C n (nrel r v))
  (hand    : ∀ {n : S → ℕ} (p q : Semiformula L μ n), C n (p ⋏ q))
  (hor     : ∀ {n : S → ℕ} (p q : Semiformula L μ n), C n (p ⋎ q))
  (hall    : ∀ {n : S → ℕ} {s : S} (q p : Semiformula L μ (Nat.indexedSucc s n)), C n (∀[q ∷s] p))
  (hex     : ∀ {n : S → ℕ} {s : S} (q p : Semiformula L μ (Nat.indexedSucc s n)), C n (∃[q ∷s] p)) :
    ∀ {n : S → ℕ} (p : Semiformula L μ n), C n p
  | _, verum      => hverum
  | _, falsum     => hfalsum
  | _, rel r v    => hrel r v
  | _, nrel r v   => hnrel r v
  | _, and p q    => hand p q
  | _, or p q     => hor p q
  | _, call _ q p => hall q p
  | _, cex _ q p  => hex q p

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L μ n → Sort*}
  (hverum  : ∀ {n : S → ℕ}, C n ⊤)
  (hfalsum : ∀ {n : S → ℕ}, C n ⊥)
  (hrel    : ∀ {n : S → ℕ} {arity : S → ℕ} (r : L.Rel arity) (v : (s : S) → (i : Fin (arity s)) → Semiterm s L μ n), C n (rel r v))
  (hnrel   : ∀ {n : S → ℕ} {arity : S → ℕ} (r : L.Rel arity) (v : (s : S) → (i : Fin (arity s)) → Semiterm s L μ n), C n (nrel r v))
  (hand    : ∀ {n : S → ℕ} (p q : Semiformula L μ n), C n p → C n q → C n (p ⋏ q))
  (hor     : ∀ {n : S → ℕ} (p q : Semiformula L μ n), C n p → C n q → C n (p ⋎ q))
  (hall    : ∀ {n : S → ℕ} {s} (q p : Semiformula L μ (Nat.indexedSucc s n)),
    C (Nat.indexedSucc s n) q → C (Nat.indexedSucc s n) p → C n (∀[q ∷s] p))
  (hex     : ∀ {n : S → ℕ} {s} (q p : Semiformula L μ (Nat.indexedSucc s n)),
    C (Nat.indexedSucc s n) q → C (Nat.indexedSucc s n) p → C n (∃[q ∷s] p)) :
    ∀ {n : S → ℕ} (p : Semiformula L μ n), C n p
  | _, verum      => hverum
  | _, falsum     => hfalsum
  | _, rel r v    => hrel r v
  | _, nrel r v   => hnrel r v
  | _, and p q    =>
    hand p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, or p q     =>
    hor p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p) (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, call _ q p =>
    hall q p (rec' hverum hfalsum hrel hnrel hand hor hall hex q) (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
  | _, cex _ q p  =>
    hex q p (rec' hverum hfalsum hrel hnrel hand hor hall hex q) (rec' hverum hfalsum hrel hnrel hand hor hall hex p)

@[simp] lemma complexity_neg (p : Semiformula L μ n) : complexity (~p) = complexity p :=
  by induction p using rec' <;> simp[neg_and, neg_or, neg_call, neg_cex, *]

section Decidable

variable [(s : S) → (k : S → ℕ) → DecidableEq (L.Func s k)] [(k : S → ℕ) → DecidableEq (L.Rel k)]
  [(s : S) → DecidableEq (μ s)]
  [Fintype S]

def hasDecEq : {n : S → ℕ} → (p q : Semiformula L μ n) → Decidable (p = q)
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
          | isTrue h  => by
            simp[h]
            exact Fintype.decideEqPi v v₂
              <| fun s => Matrix.decVec _ _ (fun i => decEq (v s i) (v₂ s i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, nrel r v, q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by
            simp[h]
            exact Fintype.decideEqPi v v₂
              <| fun s => Matrix.decVec _ _ (fun i => decEq (v s i) (v₂ s i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, p ⋏ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[*])
        | isFalse hp => isFalse (by simp[*])
  | _, p ⋎ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[*])
        | isFalse hp => isFalse (by simp[*])
  | _, ∀[q ∷s] p, r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hall s' q' p' =>
        by_cases hs : s = s'
        · rcases hs with rfl
          exact match hasDecEq p p' with
          | isTrue hp =>
            match hasDecEq q q' with
            | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
            | isFalse hq => isFalse (by simp[*])
          | isFalse hp => isFalse (by simp[*])
        · exact isFalse (by simp[hs])
  | _, ∃[q ∷s] p, r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hex s' q' p' =>
        by_cases hs : s = s'
        · rcases hs with rfl
          exact match hasDecEq p p' with
          | isTrue hp =>
            match hasDecEq q q' with
            | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
            | isFalse hq => isFalse (by simp[*])
          | isFalse hp => isFalse (by simp[*])
        · exact isFalse (by simp[hs])

instance : DecidableEq (Semiformula L μ n) := hasDecEq

end Decidable

end Semiformula

namespace Rew

open Semiformula

variable
  {L : Language.{w, u} S}
  {μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂} {μ₃ : S → Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : S → ℕ}

def loMap : ⦃n₁ n₂ : S → ℕ⦄ → Rew L μ₁ n₁ μ₂ n₂ → Semiformula L μ₁ n₁ → Semiformula L μ₂ n₂
  | _, _, _, ⊤         => ⊤
  | _, _, _, ⊥         => ⊥
  | _, _, ω, rel r v   => rel r (fun s i => ω.trm (v s i))
  | _, _, ω, nrel r v  => nrel r (fun s i => ω.trm (v s i))
  | _, _, ω, p ⋏ q     => ω.loMap p ⋏ ω.loMap q
  | _, _, ω, p ⋎ q     => ω.loMap p ⋎ ω.loMap q
  | _, _, ω, ∀[q ∷s] p => ∀[(ω.q s).loMap q ∷s] ((ω.q s).loMap p)
  | _, _, ω, ∃[q ∷s] p => ∃[(ω.q s).loMap q ∷s] ((ω.q s).loMap p)

section

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma loMap_neg (p : Semiformula L μ₁ n₁) :
    ω.loMap (~p) = ~ω.loMap p :=
  by induction p using Semiformula.rec' generalizing n₂ <;> simp[neg_and, neg_or, neg_call, neg_cex, loMap, ←Semiformula.neg_eq, *]

lemma ext_loMap' {ω₁ ω₂ : Rew L μ₁ n₁ μ₂ n₂} (h : ω₁ = ω₂) (p : Semiformula L μ₁ n₁) : ω₁.loMap p = ω₂.loMap p:= by simp[h]

lemma neg' (p : Semiformula L μ₁ n₁) : ω.loMap (~p) = ~ω.loMap p := loMap_neg ω p

lemma or' (p q : Semiformula L μ₁ n₁) : ω.loMap (p ⋎ q) = ω.loMap p ⋎ ω.loMap q := rfl

def hom (ω : Rew L μ₁ n₁ μ₂ n₂) : Semiformula L μ₁ n₁ →L Semiformula L μ₂ n₂ where
  map_top' := rfl
  map_bot' := rfl
  map_neg' := ω.loMap_neg
  map_and' := fun p q => rfl
  map_or' := fun p q => rfl
  map_imply' := fun p q => by simp[Semiformula.imp_eq, neg', or']

lemma hom_eq_loMap : ω.hom = ω.loMap := rfl

protected lemma rel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → (i : Fin (k s)) → Semiterm s L μ₁ n₁) :
    ω.hom (rel r v) = rel r (fun s i => ω.trm (v s i)) := rfl

protected lemma nrel {k : S → ℕ} (r : L.Rel k) (v : (s : S) → (i : Fin (k s)) → Semiterm s L μ₁ n₁) :
    ω.hom (nrel r v) = nrel r (fun s i => ω.trm (v s i)) := rfl

@[simp] protected lemma call (s : S) (q p : Semiformula L μ₁ (Nat.indexedSucc s n₁)) :
    ω.hom (∀[q ∷s] p) = ∀[(ω.q s).hom q ∷s] (ω.q s).hom p := rfl

@[simp] protected lemma cex (s : S) (q p : Semiformula L μ₁ (Nat.indexedSucc s n₁)) :
    ω.hom (∃[q ∷s] p) = ∃[(ω.q s).hom q ∷s] (ω.q s).hom p := rfl

@[simp] protected lemma all (s : S) (p : Semiformula L μ₁ (Nat.indexedSucc s n₁)) :
    ω.hom (∀[∷s] p) = ∀[∷s] (ω.q s).hom p := rfl

@[simp] protected lemma ex (s : S) (p : Semiformula L μ₁ (Nat.indexedSucc s n₁)) :
    ω.hom (∃[∷s] p) = ∃[∷s] (ω.q s).hom p := rfl

end

end Rew

end ManySorted

end LO
