import Foundation.Logic.Predicate.Term
import Foundation.Logic.Predicate.Quantifier

/-!
# Formulas of first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformula L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/

namespace LO

namespace FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  | verum  {n} : Semiformula L ξ n
  | falsum {n} : Semiformula L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | nrel   {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | and    {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | or     {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | all    {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  | ex     {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Sentence (L : Language) := Formula L Empty

abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

abbrev SyntacticSemiformula (L : Language) (n : ℕ) := Semiformula L ℕ n

abbrev SyntacticFormula (L : Language) := SyntacticSemiformula L 0

namespace Semiformula

variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and φ ψ  => or (neg φ) (neg ψ)
  | or φ ψ   => and (neg φ) (neg ψ)
  | all φ    => ex (neg φ)
  | ex φ     => all (neg φ)

lemma neg_neg (φ : Semiformula L ξ n) : neg (neg φ) = φ :=
  by induction φ <;> simp[*, neg]

instance : LogicalConnective (Semiformula L ξ n) where
  tilde := neg
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl
  neg := neg_neg

instance : Quantifier (Semiformula L ξ) where
  univ := all
  ex := ex

section ToString

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

def toStr {n} : Semiformula L ξ n → String
  | ⊤                         => "\\top"
  | ⊥                         => "\\bot"
  | rel (arity := 0) r _      => "{" ++ toString r ++ "}"
  | rel (arity := _ + 1) r v  => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | nrel (arity := 0) r _     => "\\lnot {" ++ toString r ++ "}"
  | nrel (arity := _ + 1) r v => "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | φ ⋏ ψ                     => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ                     => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | all φ                     => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | ex φ                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ

instance : Repr (Semiformula L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiformula L ξ n) := ⟨toStr⟩

end ToString

@[simp] lemma neg_top : ∼(⊤ : Semiformula L ξ n) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : Semiformula L ξ n) = ⊤ := rfl

@[simp] lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (φ ψ : Semiformula L ξ n) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl

@[simp] lemma neg_or (φ ψ : Semiformula L ξ n) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

@[simp] lemma neg_all (φ : Semiformula L ξ (n + 1)) : ∼(∀' φ) = ∃' ∼φ := rfl

@[simp] lemma neg_ex (φ : Semiformula L ξ (n + 1)) : ∼(∃' φ) = ∀' ∼φ := rfl

@[simp] lemma neg_neg' (φ : Semiformula L ξ n) : ∼∼φ = φ := neg_neg φ

@[simp] lemma neg_inj (φ ψ : Semiformula L ξ n) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _

@[simp] lemma neg_univClosure (φ : Semiformula L ξ n) : ∼(∀* φ) = ∃* ∼φ := by
  induction n <;> simp [univClosure, exClosure, *]

@[simp] lemma neg_exClosure (φ : Semiformula L ξ n) : ∼(∃* φ) = ∀* ∼φ := by
  induction n <;> simp [univClosure, exClosure, *]

lemma neg_eq (φ : Semiformula L ξ n) : ∼φ = neg φ := rfl

lemma imp_eq (φ ψ : Semiformula L ξ n) : φ ➝ ψ = ∼φ ⋎ ψ := rfl

lemma iff_eq (φ ψ : Semiformula L ξ n) : φ ⭤ ψ = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := rfl

lemma ball_eq (φ ψ : Semiformula L ξ (n + 1)) : (∀[φ] ψ) = ∀' (φ ➝ ψ) := rfl

lemma bex_eq (φ ψ : Semiformula L ξ (n + 1)) : (∃[φ] ψ) = ∃' (φ ⋏ ψ) := rfl

@[simp] lemma neg_ball (φ ψ : Semiformula L ξ (n + 1)) : ∼(∀[φ] ψ) = ∃[φ] ∼ψ := by
  simp [ball, bex, imp_eq]

@[simp] lemma neg_bex (φ ψ : Semiformula L ξ (n + 1)) : ∼(∃[φ] ψ) = ∀[φ] ∼ψ := by
  simp [ball, bex, imp_eq]

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp [Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp[Vee.vee]

@[simp] lemma all_inj (φ ψ : Semiformula L ξ (n + 1)) : ∀' φ = ∀' ψ ↔ φ = ψ :=
  by simp[UnivQuantifier.univ]

@[simp] lemma ex_inj (φ ψ : Semiformula L ξ (n + 1)) : ∃' φ = ∃' ψ ↔ φ = ψ :=
  by simp[ExQuantifier.ex]

@[simp] lemma univClosure_inj (φ ψ : Semiformula L ξ n) : ∀* φ = ∀* ψ ↔ φ = ψ := by
  induction n <;> simp [*, univClosure_succ]

@[simp] lemma exClosure_inj (φ ψ : Semiformula L ξ n) : ∃* φ = ∃* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exClosure_succ]

@[simp] lemma univItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∀^[k] φ = ∀^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, univItr_succ]

@[simp] lemma exItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∃^[k] φ = ∃^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exItr_succ]

@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L ξ n} :
    φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_eq]

abbrev rel! (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := rel r v

abbrev nrel! (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := nrel r v

def complexity {n : ℕ} : Semiformula L ξ n → ℕ
| ⊤        => 0
| ⊥        => 0
| rel _ _  => 0
| nrel _ _ => 0
| φ ⋏ ψ    => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ    => max φ.complexity ψ.complexity + 1
| ∀' φ     => φ.complexity + 1
| ∃' φ     => φ.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (φ ψ : Semiformula L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Semiformula L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Semiformula L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Semiformula L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_all (φ : Semiformula L ξ (n + 1)) : complexity (∀' φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl

@[simp] lemma complexity_ex (φ : Semiformula L ξ (n + 1)) : complexity (∃' φ) = φ.complexity + 1 := rfl
@[simp] lemma complexity_ex' (φ : Semiformula L ξ (n + 1)) : complexity (ex φ) = φ.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋏ ψ))
  (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋎ ψ))
  (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∀' φ))
  (hex     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ  => hand φ ψ
  | _, or φ ψ   => hor φ ψ
  | _, all φ    => hall φ
  | _, ex φ     => hex φ

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hverum  : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
  (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
  (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∀' φ))
  (hex     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ  => hand φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ) (rec' hverum hfalsum hrel hnrel hand hor hall hex ψ)
  | _, or φ ψ   => hor φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ) (rec' hverum hfalsum hrel hnrel hand hor hall hex ψ)
  | _, all φ    => hall φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)
  | _, ex φ     => hex φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)

@[simp] lemma complexity_neg (φ : Semiformula L ξ n) : complexity (∼φ) = complexity φ :=
  by induction φ using rec' <;> simp[*]

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [DecidableEq ξ]

def hasDecEq : {n : ℕ} → (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
  | _, ⊤,        ψ => by cases ψ using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, ⊥,        ψ => by cases ψ using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, rel r v,  ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, nrel r v, ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, φ ⋏ ψ,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, φ ⋎ ψ,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, ∀' φ,     ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      case hall φ' => simp; exact hasDecEq φ φ'
  | _, ∃' φ,     ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      case hex φ' => simp; exact hasDecEq φ φ'

instance : DecidableEq (Semiformula L ξ n) := hasDecEq

end Decidable

/-! Quantifier Rank -/

section qr

def qr : ∀ {n}, Semiformula L ξ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, φ ⋏ ψ    => max φ.qr ψ.qr
  | _, φ ⋎ ψ    => max φ.qr ψ.qr
  | _, ∀' φ     => φ.qr + 1
  | _, ∃' φ     => φ.qr + 1

@[simp] lemma qr_top : (⊤ : Semiformula L ξ n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : Semiformula L ξ n).qr = 0 := rfl

@[simp] lemma qr_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).qr = 0 := rfl

@[simp] lemma qr_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).qr = 0 := rfl

@[simp] lemma qr_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).qr = max φ.qr ψ.qr := rfl

@[simp] lemma qr_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).qr = max φ.qr ψ.qr := rfl

@[simp] lemma qr_all (φ : Semiformula L ξ (n + 1)) : (∀' φ).qr = φ.qr + 1 := rfl

@[simp] lemma qr_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ).qr = φ.qr + 1 := rfl

@[simp] lemma qr_neg (φ : Semiformula L ξ n) : (∼φ).qr = φ.qr := by
  induction' φ using rec' <;> simp[*]

@[simp] lemma qr_imply (φ ψ : Semiformula L ξ n) : (φ ➝ ψ).qr = max φ.qr ψ.qr :=
  by simp[imp_eq]

@[simp] lemma qr_iff (φ ψ : Semiformula L ξ n) : (φ ⭤ ψ).qr = max φ.qr ψ.qr :=
  by simp[iff_eq, total_of]

end qr

/-! Open (Semi-)Formula -/

section Open

def Open (φ : Semiformula L ξ n) : Prop := φ.qr = 0

@[simp] lemma open_top : (⊤ : Semiformula L ξ n).Open := rfl

@[simp] lemma open_bot : (⊥ : Semiformula L ξ n).Open := rfl

@[simp] lemma open_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).Open := rfl

@[simp] lemma open_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).Open := rfl

@[simp] lemma open_and {φ ψ : Semiformula L ξ n} : (φ ⋏ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp[Open]

@[simp] lemma open_or {φ ψ : Semiformula L ξ n} : (φ ⋎ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp[Open]

@[simp] lemma not_open_all {φ : Semiformula L ξ (n + 1)} : ¬(∀' φ).Open := by simp[Open]

@[simp] lemma not_open_ex {φ : Semiformula L ξ (n + 1)} : ¬(∃' φ).Open := by simp[Open]

@[simp] lemma open_neg {φ : Semiformula L ξ n} : (∼φ).Open ↔ φ.Open := by
  simp[Open]

@[simp] lemma open_imply {φ ψ : Semiformula L ξ n} : (φ ➝ ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp[Open]

@[simp] lemma open_iff {φ ψ : Semiformula L ξ n} : (φ ⭤ ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp[Open]

end Open

/-! Free Variables -/

section FreeVariables

variable [DecidableEq ξ]

def freeVariables : {n : ℕ} → Semiformula L ξ n → Finset ξ
  | _, rel _ v  => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, φ ⋏ ψ    => freeVariables φ ∪ freeVariables ψ
  | _, φ ⋎ ψ    => freeVariables φ ∪ freeVariables ψ
  | _, ∀' φ     => freeVariables φ
  | _, ∃' φ     => freeVariables φ

lemma freeVariables_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

lemma freeVariables_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

@[simp] lemma freeVariables_verum : (⊤ : Semiformula L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_falsum : (⊥ : Semiformula L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

@[simp] lemma freeVariables_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

@[simp] lemma freeVariables_all (φ : Semiformula L ξ (n + 1)) : (∀' φ).freeVariables = φ.freeVariables := rfl

@[simp] lemma freeVariables_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ).freeVariables = φ.freeVariables := rfl

@[simp] lemma freeVariables_not (φ : Semiformula L ξ n) : (∼φ).freeVariables = φ.freeVariables := by
  induction φ using rec' <;> simp [*, freeVariables_rel, freeVariables_nrel]

@[simp] lemma freeVariables_imp (φ ψ : Semiformula L ξ n) : (φ ➝ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := by simp [imp_eq]

@[simp] lemma freeVariables_univClosure (φ : Semiformula L ξ n) : (∀* φ).freeVariables = φ.freeVariables := by
  induction n <;> simp [univClosure, *]

@[simp] lemma freeVariables_sentence {ο : Type*} [IsEmpty ο] (φ : Semiformula L ο n) : φ.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x

abbrev FVar? (φ : Semiformula L ξ n) (x : ξ) : Prop := x ∈ φ.freeVariables

@[simp] lemma fvar?_rel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_rel]

@[simp] lemma fvar?_nrel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_nrel]

@[simp] lemma fvar?_top (x) : ¬(⊤ : Semiformula L ξ n).FVar? x := by simp [FVar?]

@[simp] lemma fvar?_falsum (x) : ¬(⊥ : Semiformula L ξ n).FVar? x := by simp [FVar?]

@[simp] lemma fvar?_and (x) (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_or (x) (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_all (x) (φ : Semiformula L ξ (n + 1)) : (∀' φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_ex (x) (φ : Semiformula L ξ (n + 1)) : (∃' φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

@[simp] lemma fvar?_univClosure (x) (φ : Semiformula L ξ n) : (∀* φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

def fvSup (φ : SyntacticSemiformula L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ

lemma lt_fvSup_of_fvar? {φ : SyntacticSemiformula L n} : φ.FVar? m → m < φ.fvSup := by
  unfold fvSup FVar?
  intro hm
  have : ∃ s : ℕ, φ.freeVariables.max = s := Finset.max_of_mem hm
  rcases this with ⟨s, hs⟩
  have : m ≤ s := by
    have : (m : WithBot ℕ) ≤ ↑s := by simpa [hs] using Finset.le_max hm
    exact WithBot.coe_le_coe.mp this
  simpa [hs, WithBot.recBotCoe] using Nat.lt_add_one_of_le this

lemma not_fvar?_of_lt_fvSup (φ : SyntacticSemiformula L n) (h : φ.fvSup ≤ m) : ¬φ.FVar? m :=
  fun hm ↦ (lt_self_iff_false _).mp (lt_of_le_of_lt h <| lt_fvSup_of_fvar? hm)

@[simp] lemma not_fvar?_fvSup (φ : SyntacticSemiformula L n) : ¬φ.FVar? φ.fvSup :=
  not_fvar?_of_lt_fvSup φ (by simp)

end FreeVariables

section

variable {α : Type*} [LinearOrder  α]

lemma List.maximam?_some_of_not_nil {l : List α} (h : l ≠ []) : l.max?.isSome := by
  cases l
  case nil => simp at h
  case cons l => simp [List.max?_cons]

lemma List.maximam?_eq_some {l : List α} {a} (h : l.max? = some a) : ∀ x ∈ l, x ≤ a :=
  List.max?_le_iff (by simp) h (x := a) |>.mp (by rfl)

end

lemma ne_of_ne_complexity {φ ψ : Semiformula L ξ n} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction

@[simp] lemma ne_or_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋎ ψ := ne_of_ne_complexity (by simp)

@[simp] lemma ne_or_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋎ ψ := ne_of_ne_complexity (by simp)

variable {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language} {ξ : Type*} {Φ : L₁ →ᵥ L₂}

def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, Semiformula L₁ ξ n → Semiformula L₂ ξ n
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | _, rel r v  => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, φ ⋏ ψ    => lMapAux Φ φ ⋏ lMapAux Φ ψ
  | _, φ ⋎ ψ    => lMapAux Φ φ ⋎ lMapAux Φ ψ
  | _, ∀' φ     => ∀' lMapAux Φ φ
  | _, ∃' φ     => ∃' lMapAux Φ φ

lemma lMapAux_neg {n} (φ : Semiformula L₁ ξ n) :
    (∼φ).lMapAux Φ = ∼φ.lMapAux Φ :=
  by induction φ using Semiformula.rec' <;> simp[*, lMapAux, ←Semiformula.neg_eq]

def lMap (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n →ˡᶜ Semiformula L₂ ξ n where
  toTr := lMapAux Φ
  map_top' := by simp[lMapAux]
  map_bot' := by simp[lMapAux]
  map_and' := by simp[lMapAux]
  map_or'  := by simp[lMapAux]
  map_neg' := by simp[lMapAux_neg]
  map_imply' := by simp[Semiformula.imp_eq, lMapAux_neg, ←Semiformula.neg_eq, lMapAux]

lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_rel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) ![] := by simp[lMap_rel, Matrix.empty_eq]

@[simp] lemma lMap_rel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t]) = rel (Φ.rel r) ![t.lMap Φ] := by simp[lMap_rel, Matrix.constant_eq_singleton]

@[simp] lemma lMap_rel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t₁, t₂]) = rel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  simp[lMap_rel]; funext i; induction i using Fin.induction <;> simp

lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_nrel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) ![] := by simp[lMap_nrel, Matrix.empty_eq]

@[simp] lemma lMap_nrel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t]) = nrel (Φ.rel r) ![t.lMap Φ] := by simp[lMap_nrel, Matrix.constant_eq_singleton]

@[simp] lemma lMap_nrel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t₁, t₂]) = nrel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  simp[lMap_nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma lMap_all (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀' φ) = ∀' lMap Φ φ := rfl

@[simp] lemma lMap_ex (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃' φ) = ∃' lMap Φ φ := rfl

@[simp] lemma lMap_ball (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀[φ] ψ) = ∀[lMap Φ φ] lMap Φ ψ := by simp [ball]

@[simp] lemma lMap_bex (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃[φ] ψ) = ∃[lMap Φ φ] lMap Φ ψ := by simp [bex]

@[simp] lemma lMap_univClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∀* φ) = ∀* lMap Φ φ := by induction n <;> simp [*, univClosure_succ]

@[simp] lemma lMap_exClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∃* φ) = ∃* lMap Φ φ := by induction n <;> simp [*, exClosure_succ]

@[simp] lemma lMap_univItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∀^[k] φ) = ∀^[k] lMap Φ φ := by induction k <;> simp [*, univItr_succ]; rfl

@[simp] lemma lMap_exItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∃^[k] φ) = ∃^[k] lMap Φ φ := by induction k <;> simp [*, exItr_succ]; rfl

@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (φ : Semiformula L₁ ξ n) :
    (Semiformula.lMap Φ φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' <;> try simp [lMap_rel, lMap_nrel, freeVariables_rel, freeVariables_nrel, *]

end Semiformula

abbrev Theory (L : Language) := Set (SyntacticFormula L)

abbrev ClosedTheory (L : Language) := Set (Sentence L)

instance : Collection (SyntacticFormula L) (Theory L) := inferInstance

instance : Collection (Sentence L) (ClosedTheory L) := inferInstance

def Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T

namespace Theory

variable (T U : Theory L)

instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩

lemma add_def : T + U = T ∪ U := rfl

end Theory

end FirstOrder

end LO
