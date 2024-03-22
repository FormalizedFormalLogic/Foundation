import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Order.Le
import Logic.FirstOrder.Class.Init

namespace LO.FirstOrder

namespace Rew

variable {μ : Type*}

lemma hom_eq_id_of_eq_on_fvar_list (ω : Rew L μ n μ n) (hb : ∀ x, ω (#x) = #x) (hf : ∀ x ∈ p.fvarList, ω (&x) = &x) :
    ω.hom p = p := by
  suffices ω.hom p = Rew.id.hom p by
    simpa using this
  apply Semiformula.rew_eq_of_funEqOn
  · simpa using hb
  · intro x hx; simp [hf x hx]

end Rew

variable {L : Language} {ξ : Type*} [DecidableEq ξ]

namespace Semiformula

def Equivalent (T : Theory L) (p q : Semiformula L ξ n) : Prop := T ⊨ ∀ᶠ* ∀* (p ⟷ q)

variable {T : Theory L} {p q r : Semiformula L ξ n}

namespace Equivalent

notation p:80 " ↔[" T "] " q:80 => Equivalent T p q

@[refl] protected lemma refl : p ↔[T] p := by simp [Equivalent, consequence_iff, models_iff]

@[symm] protected lemma symm : p ↔[T] q → q ↔[T] p := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall]
  intro h M x _ hT ε e
  exact Iff.symm <| h M x hT ε e

@[trans] protected lemma trans : p ↔[T] q → q ↔[T] r → p ↔[T] r := by
  simp only [Equivalent, consequence_iff, models_iff, Semiformula.val_fvUnivClosure, Semiformula.eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq]
  intro hp hq M x _ hT ε e
  exact Iff.trans (hp M hT ε e) (hq M hT ε e)

lemma of_subtheory (H : T ≾ T') (h : p ↔[T] q) : p ↔[T'] q := LO.Sound.sound <| H.sub <| LO.Complete.complete h

lemma rew [DecidableEq ξ'] (h : p ↔[T] q) (ω : Rew L ξ n ξ' n') : (ω.hom p) ↔[T] (ω.hom q) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall, eval_rew,
    Function.comp] at h ⊢
  intro M x _ hT ε e; exact h M x hT _ _

lemma not {p₁ p₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) : (~p₁) ↔[T] (~p₂) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop_neg_eq] at hp ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e]

lemma and {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (p₁ ⋏ q₁) ↔[T] (p₂ ⋏ q₂) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall,
    LogicalConnective.HomClass.map_and, LogicalConnective.Prop_and_eq] at hp hq ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e, hq M x hT ε e]

lemma or {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (p₁ ⋎ q₁) ↔[T] (p₂ ⋎ q₂) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop_or_eq] at hp hq ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e, hq M x hT ε e]

lemma imp {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) :
    (p₁ ⟶ q₁) ↔[T] (p₂ ⟶ q₂) := or (not hp) hq

lemma all {p₁ p₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) : (∀' p₁) ↔[T] (∀' p₂) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall, eval_all] at hp ⊢
  intro M x _ hT ε e
  apply forall_congr'; intro a
  exact hp M x hT ε (a :> e)

lemma ex {p₁ p₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) : (∃' p₁) ↔[T] (∃' p₂) := by
  simp only [Equivalent, consequence_iff, models_iff, val_fvUnivClosure, eval_univClosure,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop_iff_eq, Nonempty.forall, eval_ex] at hp ⊢
  intro M x _ hT ε e
  apply exists_congr; intro a
  exact hp M x hT ε (a :> e)

lemma ball {p₁ p₂ q₁ q₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (∀[p₁] q₁) ↔[T] (∀[p₂] q₂) :=
  all (imp hp hq)

lemma bex {p₁ p₂ q₁ q₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (∃[p₁] q₁) ↔[T] (∃[p₂] q₂) :=
  ex (and hp hq)

lemma all_and_all (p q : Semiformula L ξ (n + 1)) :
    ((∀' p) ⋏ (∀' q)) ↔[T] (∀' ∀' ((Rew.substs (#1 :> (#·.succ.succ))).hom p ⋏ (Rew.substs (#0 :> (#·.succ.succ))).hom q)) := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']
  intro M x _ _ ε e
  constructor
  · rintro ⟨hp, hq⟩ a b; exact ⟨hp a, hq b⟩
  · rintro h; exact ⟨fun a ↦ (h a x).1, fun b ↦ (h x b).2⟩

lemma all_or_all (p q : Semiformula L ξ (n + 1)) :
    ((∀' p) ⋎ (∀' q)) ↔[T] (∀' ∀' ((Rew.substs (#1 :> (#·.succ.succ))).hom p ⋎ (Rew.substs (#0 :> (#·.succ.succ))).hom q)) := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']
  intro M x _ _ ε e
  constructor
  · rintro (hp | hq) a b
    · exact Or.inl (hp a)
    · exact Or.inr (hq b)
  · rintro h; by_contra A
    simp [not_or, not_forall] at A
    rcases A with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rcases h a b with (H | H) <;> contradiction

lemma ex_and_ex (p q : Semiformula L ξ (n + 1)) :
    ((∃' p) ⋏ (∃' q)) ↔[T] (∃' ∃' ((Rew.substs (#1 :> (#·.succ.succ))).hom p ⋏ (Rew.substs (#0 :> (#·.succ.succ))).hom q)) := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']

lemma ex_or_ex (p q : Semiformula L ξ (n + 1)) :
    ((∃' p) ⋎ (∃' q)) ↔[T] (∃' ∃' ((Rew.substs (#1 :> (#·.succ.succ))).hom p ⋎ (Rew.substs (#0 :> (#·.succ.succ))).hom q)) := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']
  intro M x _ _ ε e
  constructor
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨a, x, Or.inl ha⟩
    · exact ⟨x, b, Or.inr hb⟩
  · rintro ⟨a, b, (h | h)⟩
    · exact Or.inl ⟨a, h⟩
    · exact Or.inr ⟨b, h⟩

lemma dummy_quantifier_all (p : Semiformula L ξ n) :
    (∀' Rew.bShift.hom p) ↔[T] p := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']

lemma dummy_quantifier_ex (p : Semiformula L ξ n) :
    (∃' Rew.bShift.hom p) ↔[T] p := by
  simp [Equivalent, consequence_iff, models_iff, eval_substs, Matrix.comp_vecCons']

end Equivalent

end Semiformula

def RewClosure (C : Semiformula L ξ n → Prop) : Semiformula L ξ n → Prop := fun p ↦ ∃ p₀, C p₀ ∧ ∃ ω : Rew L ξ n ξ n, p = ω.hom p₀

def EqvClosure (T : Theory L) (C : Semiformula L ξ n → Prop) : Semiformula L ξ n → Prop := fun p ↦ ∃ p₀, C p₀ ∧ p₀ ↔[T] p

section eqvClosure

variable {T : Theory L} {C : Semiformula L ξ n → Prop}

lemma mem_equivalent_closure_of_equivalent {p q : Semiformula L ξ n} (h : p ↔[T] q) :
    EqvClosure T C p → EqvClosure T C q := by
  rintro ⟨p₀, hp₀, h₀⟩; exact ⟨p₀, hp₀, h₀.trans h⟩

lemma subset_equivalent_closure {p} : C p → EqvClosure T C p := by
  intro hp; exact ⟨p, hp, by rfl⟩

@[simp] lemma eqv_eqv : EqvClosure T (EqvClosure T C) = EqvClosure T C := by
  ext p; simp [EqvClosure]; constructor
  · rintro ⟨q, ⟨r, hr, hrq⟩, hqp⟩
    exact ⟨r, hr, hrq.trans hqp⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, ⟨q, hq, by rfl⟩, hqp⟩

end eqvClosure

abbrev UnitSemiformula (L : Language) (n : ℕ) := Semiformula L Unit n

namespace Rew

def unify : Rew L ξ n Unit n := Rew.rewriteMap (fun _ ↦ ())

@[simp] lemma unify_bvar (x : Fin n) : unify (#x : Semiterm L ξ n) = #x := rfl

@[simp] lemma unify_fvar (x : ξ) : unify (&x : Semiterm L ξ n) = &() := rfl

@[simp] lemma q_unify : (unify : Rew L ξ n Unit n).q = unify := by ext x; { cases x using Fin.cases <;> simp }; { simp }

end Rew

@[ext] structure Class (L : Language) (ξ : Type*) where
  Domain : {n : ℕ} → Semiformula L ξ n → Prop
  rew_closed : ∀ {n n'}, ∀ ω : Rew L ξ n ξ n', ∀ p, Domain p → Domain (ω.hom p)

namespace Class

variable {c : Class L ξ}

/-
lemma shift_closed {p : SyntacticFormula L} (hp : p ∈ c.Domain) : Rew.shift.hom p ∈ c.Domain := by
  have : (Rew.hom (Rew.rewrite (&·.succ))) p ∈ c.Domain := c.rew_closed p hp (&·.succ)
  have : @Rew.shift L 0 = Rew.rewrite (&·.succ) := by ext <;> simp
  rw [this]; assumption
-/

protected def eqvClosure (c : Class L ξ) (T : Theory L) : Class L ξ where
  Domain := fun {n} ↦ EqvClosure T c.Domain
  rew_closed := by
    rintro n n' ω p ⟨p', hp', H⟩
    exact ⟨ω.hom p', c.rew_closed ω p' hp', H.rew ω⟩

lemma domain_eqvClosure {T : Theory L} {n} {p q : Semiformula L ξ n} (hp : (c.eqvClosure T).Domain p) (h : p ↔[T] q) :
    (c.eqvClosure T).Domain q := by
  rcases hp with ⟨p', hp', H⟩
  exact ⟨p', hp', H.trans h⟩

instance : LE (Class L ξ) := ⟨fun c c' ↦ ∀ {n} {p : Semiformula L ξ n}, c.Domain p → c'.Domain p⟩

namespace LE

variable {c c' : Class L ξ}

@[refl] protected lemma refl : c ≤ c := id

@[trans] protected lemma trans {c₁ c₂ c₃ : Class L ξ} : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃ :=
  fun h₁ h₂ _ _ hp ↦ h₂ (h₁ hp)

end LE

lemma le_eqvClosure (c : Class L ξ) (T : Theory L) : c ≤ c.eqvClosure T := by intro _ p hp; exact subset_equivalent_closure hp

lemma eqvClosure_monotone {c c' : Class L ξ} (h : c ≤ c') (T : Theory L) : c.eqvClosure T ≤ c'.eqvClosure T := by
  rintro _ p ⟨p', hp, H⟩; exact ⟨p', h hp, H⟩

lemma le_of_subtheory (c : Class L ξ) {T T' : Theory L} (h : T ≾ T') : c.eqvClosure T ≤ c.eqvClosure T' := by
  rintro _ p ⟨p', hp', H⟩; exact ⟨p', hp', H.of_subtheory h⟩

class Atom (c : Class L ξ) : Prop where
  verum : ∀ n, c.Domain (⊤ : Semiformula L ξ n)
  falsum : ∀ n, c.Domain (⊥ : Semiformula L ξ n)
  rel : ∀ {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), c.Domain (Semiformula.rel r v)
  nrel : ∀ {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), c.Domain (Semiformula.nrel r v)

class Not (c : Class L ξ) : Prop where
  not {n} {p : Semiformula L ξ n} : c.Domain p → c.Domain (~p)

class And (c : Class L ξ) : Prop where
  and {n} {p q : Semiformula L ξ n} : c.Domain p → c.Domain q → c.Domain (p ⋏ q)

class Or (c : Class L ξ) : Prop where
  or {n} {p q : Semiformula L ξ n} : c.Domain p → c.Domain q → c.Domain (p ⋎ q)

class BAll (c : Class L ξ) [L.LT] : Prop where
  ball {n} {p : Semiformula L ξ (n + 1)} {t} : c.Domain p → t.Positive → c.Domain (∀[“#0 < !!t”] p)

class BEx (c : Class L ξ) [L.LT] : Prop where
  bex {n} {p : Semiformula L ξ (n + 1)} {t} : c.Domain p → t.Positive → c.Domain (∃[“#0 < !!t”] p)

class All (c : Class L ξ) [L.LT] : Prop where
  all {n} {p : Semiformula L ξ (n + 1)} : c.Domain p → c.Domain (∀' p)

class Ex (c : Class L ξ) [L.LT] : Prop where
  ex {n} {p : Semiformula L ξ (n + 1)} : c.Domain p → c.Domain (∃' p)

section Atom

variable [c.Atom] [Nonempty (Term L ξ)]

attribute [simp] Atom.verum Atom.falsum Atom.rel Atom.nrel

@[simp] lemma mem_eq [L.Eq] (t u : Semiterm L ξ n) : c.Domain “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_not_eq [L.Eq] (t u : Semiterm L ξ n) : c.Domain “!!t ≠ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_lt [L.LT] (t u : Semiterm L ξ n) : c.Domain “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

@[simp] lemma mem_not_lt [L.LT] (t u : Semiterm L ξ n) : c.Domain “!!t ≮ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

def of_le (c c' : Class L ξ) [c.Atom] (h : c ≤ c') : c'.Atom where
  verum := fun n ↦ h (Atom.verum n)
  falsum := fun n ↦ h (Atom.falsum n)
  rel := fun r v ↦ h (Atom.rel r v)
  nrel := fun r v ↦ h (Atom.nrel r v)

instance eqvClosure_atom : (c.eqvClosure T).Atom := of_le c _ (le_eqvClosure c T)

end Atom

section Not

variable [c.Not]

instance eqvClosure_not : (c.eqvClosure T).Not := ⟨by rintro _ p ⟨p', hp', H⟩; exact ⟨~p', Not.not hp', H.not⟩⟩

end Not

section And

variable [c.And]

instance eqvClosure_and : (c.eqvClosure T).And := ⟨by rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋏ q', And.and hp' hq', Hp.and Hq⟩⟩

end And

section Or

variable [c.Or]

instance eqvClosure_or : (c.eqvClosure T).Or := ⟨by rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋎ q', Or.or hp' hq', Hp.or Hq⟩⟩

variable [c.Not]

lemma mem_imply {p q : Semiformula L ξ n} (hp : c.Domain p) (hq : c.Domain q) : c.Domain (p ⟶ q) := by
  simp [Semiformula.imp_eq]; exact Or.or (Not.not hp) hq

variable [c.And]

lemma mem_iff {p q : Semiformula L ξ n} (hp : c.Domain p) (hq : c.Domain q) : c.Domain (p ⟷ q) := by
  simp [LO.LogicalConnective.iff]; exact And.and (mem_imply hp hq) (mem_imply hq hp)

end Or

section BAll

variable [L.LT] [c.BAll]

instance eqvClosure_ball : (c.eqvClosure T).BAll :=
  ⟨by rintro n p t ⟨p', hp', H⟩ ht; exact ⟨∀[“#0 < !!t”] p', BAll.ball hp' ht, Semiformula.Equivalent.ball (by rfl) H⟩⟩

end BAll

section BEx

variable [L.LT] [c.BEx]

instance eqvClosure_bex : (c.eqvClosure T).BEx :=
  ⟨by rintro n p t ⟨p', hp', H⟩ ht; exact ⟨∃[“#0 < !!t”] p', BEx.bex hp' ht, Semiformula.Equivalent.bex (by rfl) H⟩⟩

end BEx

section

variable [c.Atom] [c.And] [c.Or] [Nonempty (Term L ξ)]

@[simp] lemma mem_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.Domain “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply Or.or <;> simp

@[simp] lemma mem_not_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.Domain “¬!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply And.and <;> simp

end

end Class

def openClass (L : Language) (ξ : Type*) : Class L ξ where
  Domain := Semiformula.Open
  rew_closed := by simp

instance : (openClass L ξ).Atom where
  verum := fun _ ↦ Semiformula.open_top
  falsum := fun _ ↦ Semiformula.open_bot
  rel := fun r v ↦ Semiformula.open_rel r v
  nrel := fun r v ↦ Semiformula.open_nrel r v

instance : (openClass T ξ).Not := ⟨Semiformula.open_neg.mpr⟩

instance : (openClass T ξ).And := ⟨fun hp hq ↦ Semiformula.open_and.mpr ⟨hp, hq⟩⟩

instance : (openClass T ξ).Or := ⟨fun hp hq ↦ Semiformula.open_or.mpr ⟨hp, hq⟩⟩

section

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

attribute [aesop 1 (rule_sets := [FormulaClass]) norm]
  Class.mem_imply
  Class.mem_iff

attribute [aesop 2 (rule_sets := [FormulaClass]) norm]
  Class.BAll.ball
  Class.BEx.bex

attribute [aesop 3 (rule_sets := [FormulaClass]) norm]
  Class.And.and
  Class.Or.or
  Class.rew_closed
  Class.Not.not
  Class.All.all
  Class.Ex.ex

macro "formula_class" : attr =>
  `(attr|aesop 0 (rule_sets := [$(Lean.mkIdent `FormulaClass):ident]) safe)

macro "formula_class" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `FormulaClass):ident]))

macro "formula_class?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `FormulaClass):ident]))

example : (openClass ℒₒᵣ ℕ).Domain (“¬0 < 6 → &6 + #5 ≠ 0” : Semiformula ℒₒᵣ ℕ 8) := by { formula_class }

end

end LO.FirstOrder
