import Logic.ManySorted.Basic.Term

namespace LO

namespace ManySorted

inductive Subformula {S : Type w} [DecidableEq S] (L : Language.{w, u} S) (μ : S → Type v) : (S → ℕ) → Type _
  | verum  {n}                  : Subformula L μ n
  | falsum {n}                  : Subformula L μ n
  | rel    {n} {arity} {aug}    : L.Rel aug → ((i : Fin arity) → Subterm (aug i) L μ n) → Subformula L μ n
  | nrel   {n} {arity} {aug}    : L.Rel aug → ((i : Fin arity) → Subterm (aug i) L μ n) → Subformula L μ n
  | and    {n}                  : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | or     {n}                  : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | call   {n : S → ℕ} (s : S) : Subformula L μ (Nat.indexedSucc s n) → Subformula L μ (Nat.indexedSucc s n) → Subformula L μ n
  | cex    {n : S → ℕ} (s : S) : Subformula L μ (Nat.indexedSucc s n) → Subformula L μ (Nat.indexedSucc s n) → Subformula L μ n

variable {S : Type w} [DecidableEq S]

abbrev Formula (L : Language.{w, u} S) (μ : S → Type v) := Subformula L μ 0

abbrev Sentence (L : Language.{w, u} S) := Formula L (fun _ => Empty)

abbrev Subsentence (L : Language.{w, u} S) (n : ℕ) := Subformula L (fun _ => Empty) n

abbrev SyntacticSubformula (L : Language.{w, u} S) (n : ℕ) := Subformula L (fun _ => ℕ) n

abbrev SyntacticFormula (L : Language.{w, u} S) := SyntacticSubformula L 0

namespace Subformula
variable
  {L : Language.{w, u} S} {L₁ : Language.{w, u₁} S} {L₂ : Language.{w, u₂} S} {L₃ : Language.{w, u₃} S}
  {μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂} {μ₃ : S → Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : S → ℕ}

def neg {n} : Subformula L μ n → Subformula L μ n
  | verum      => falsum
  | falsum     => verum
  | rel r v    => nrel r v
  | nrel r v   => rel r v
  | and p q    => or (neg p) (neg q)
  | or p q     => and (neg p) (neg q)
  | call s q p => cex s (neg q) (neg p)
  | cex s q p  => call s (neg q) (neg p)

lemma neg_neg (p : Subformula L μ n) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : LogicSymbol (Subformula L μ n) where
  tilde := neg
  arrow := fun p q => or (neg p) q
  wedge := and
  vee := or
  top := verum
  bot := falsum

scoped notation:max "∀[" q " ∷" s "]" p:64 => Subformula.call s q p

scoped notation:max "∃[" q " ∷" s "]" p:64 => Subformula.cex s q p

@[simp] lemma neg_top : ~(⊤ : Subformula L μ n) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : Subformula L μ n) = ⊤ := rfl

@[simp] lemma neg_rel {a} (r : L.Rel a) (v : (i : Fin k) → Subterm (a i) L μ n) : ~(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {a} (r : L.Rel a) (v : (i : Fin k) → Subterm (a i) L μ n) : ~(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (p q : Subformula L μ n) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

@[simp] lemma neg_or (p q : Subformula L μ n) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

@[simp] lemma neg_all (s : S) (q p : Subformula L μ (Nat.indexedSucc s n)) : ~(∀[q ∷s] p) = ∃[~q ∷s] ~p := rfl

@[simp] lemma neg_ex (q p : Subformula L μ (Nat.indexedSucc s n)) : ~(∃[q ∷s] p) = ∀[~q ∷s] ~p := rfl

@[simp] lemma neg_neg' (p : Subformula L μ n) : ~~p = p := neg_neg p

@[simp] lemma neg_inj (p q : Subformula L μ n) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (~·) h
  · exact congr_arg _

lemma neg_eq (p : Subformula L μ n) : ~p = neg p := rfl

lemma imp_eq (p q : Subformula L μ n) : p ⟶ q = ~p ⋎ q := rfl

lemma iff_eq (p q : Subformula L μ n) : p ⟷ q = (~p ⋎ q) ⋏ (~q ⋎ p) := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Subformula L μ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Subformula L μ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Vee.vee]

@[simp] lemma all_inj (p₁ q₁ p₂ q₂ : Subformula L μ (Nat.indexedSucc s n)) : ∀[q₁ ∷s] p₁ = ∀[q₂ ∷ s] p₂ ↔ q₁ = q₂ ∧ p₁ = p₂ :=
  by simp

@[simp] lemma ex_inj  (p₁ q₁ p₂ q₂ : Subformula L μ (Nat.indexedSucc s n)) : ∃[q₁ ∷s] p₁ = ∃[q₂ ∷ s] p₂ ↔ q₁ = q₂ ∧ p₁ = p₂ :=
  by simp

end Subformula

namespace Rew

open Subformula

variable
  {L : Language.{w, u} S}
  {μ : S → Type v} {μ₁ : S → Type v₁} {μ₂ : S → Type v₂} {μ₃ : S → Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : S → ℕ}

/-
def loMap : ⦃n₁ n₂ : S → ℕ⦄ → Rew L μ₁ n₁ μ₂ n₂ → Subformula L μ₁ n₁ → Subformula L μ₂ n₂
  | _, _, _, ⊤        => ⊤
  | _, _, _, ⊥        => ⊥
  | _, _, ω, rel r v  => rel r (fun i => ω.trm (v i))
  | _, _, ω, nrel r v => nrel r (fun i => ω.trm (v i))
  | _, _, ω, p ⋏ q    => ω.loMap p ⋏ ω.loMap q
  | _, _, ω, p ⋎ q    => ω.loMap p ⋎ ω.loMap q
  | _, _, ω, ∀[q ∷s] p     => Subformula.call s (ω.q.loMap $ by {  }) (ω.q.loMap $ by {  })
  | _, _, ω, ∃[q ∷s] p     => ∃[ω.q.loMap q ∷s] ω.q.loMap p
-/

end Rew

end ManySorted

end LO
