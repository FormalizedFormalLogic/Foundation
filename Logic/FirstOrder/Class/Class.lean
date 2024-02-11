import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Order.Le
import Logic.FirstOrder.Class.Init

namespace LO.FirstOrder

namespace Rew

variable {μ : Type*}

lemma hom_eq_id_of_eq_on_fvar_list (ω : Rew L μ n μ n) (hb : ∀ x, ω (#x) = #x) (hf : ∀ x ∈ p.fvarList, ω (&x) = &x) :
    ω.hom p = p := by
  suffices : ω.hom p = Rew.id.hom p
  · simpa using this
  apply Semiformula.rew_eq_of_funEqOn
  · simpa using hb
  · intro x hx; simp [hf x hx]

@[simp] lemma rewriteMap_fvEnumInv_fvEnum [DecidableEq ξ] [Inhabited ξ] (q : Semiformula L ξ n) :
    (Rew.rewriteMap (q.fvEnumInv ∘ q.fvEnum)).hom q = q :=
  hom_eq_id_of_eq_on_fvar_list _ (by simp) (fun x hx ↦ by simp [Semiformula.fvEnumInv_fvEnum hx])

lemma rewrite_eq_rewriteMap (f : ξ₁ → ξ₂) :
    (Rew.rewrite fun x ↦ &(f x) : Rew L ξ₁ n ξ₂ n) = Rew.rewriteMap f := rfl

end Rew

variable {L : Language} {ξ : Type*} [DecidableEq ξ]

namespace Semiformula

def Equivalent (T : Theory L) (p q : Semiformula L ξ n) : Prop := T ⊨ ∀ᶠ* ∀* (p ⟷ q)

variable {T : Theory L} {p q r : Semiformula L ξ n}

namespace Equivalent

notation p:80 " ↔[" T "] " q:80 => Equivalent T p q

@[refl] protected lemma refl : p ↔[T] p := by simp [Equivalent, consequence_iff, models_iff]

@[symm] protected lemma symm : p ↔[T] q → q ↔[T] p := by
  simp [Equivalent, consequence_iff, models_iff]
  intro h M x _ hT ε e
  exact Iff.symm <| h M x hT ε e

@[trans] protected lemma trans : p ↔[T] q → q ↔[T] r → p ↔[T] r := by
  simp [Equivalent, consequence_iff, models_iff]
  intro hp hq M x _ hT ε e
  exact Iff.trans (hp M x hT ε e) (hq M x hT ε e)

lemma of_subtheory (H : T ≾ T') (h : p ↔[T] q) : p ↔[T'] q := LO.Sound.sound <| H.sub <| LO.Complete.complete h

lemma rew [DecidableEq ξ'] (h : p ↔[T] q) (ω : Rew L ξ n ξ' n') : (ω.hom p) ↔[T] (ω.hom q) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at h ⊢
  intro M x _ hT ε e; exact h M x hT _ _

lemma not {p₁ p₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) : (~p₁) ↔[T] (~p₂) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at hp ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e]

lemma and {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (p₁ ⋏ q₁) ↔[T] (p₂ ⋏ q₂) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at hp hq ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e, hq M x hT ε e]

lemma or {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) : (p₁ ⋎ q₁) ↔[T] (p₂ ⋎ q₂) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at hp hq ⊢
  intro M x _ hT ε e; rw [hp M x hT ε e, hq M x hT ε e]

lemma imp {p₁ p₂ q₁ q₂ : Semiformula L ξ n} (hp : p₁ ↔[T] p₂) (hq : q₁ ↔[T] q₂) :
    (p₁ ⟶ q₁) ↔[T] (p₂ ⟶ q₂) := or (not hp) hq

lemma all {p₁ p₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) : (∀' p₁) ↔[T] (∀' p₂) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at hp ⊢
  intro M x _ hT ε e
  apply forall_congr'; intro a
  exact hp M x hT ε (a :> e)

lemma ex {p₁ p₂ : Semiformula L ξ (n + 1)} (hp : p₁ ↔[T] p₂) : (∃' p₁) ↔[T] (∃' p₂) := by
  simp [Equivalent, consequence_iff, models_iff, eval_rew, Function.comp] at hp ⊢
  intro M x _ hT ε e
  apply exists_congr; intro a
  exact hp M x hT ε (a :> e)

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

section EqvClosure

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

end EqvClosure

@[ext] structure Class (L : Language) where
  Domain : {n : ℕ} → SyntacticSemiformula L n → Prop
  rew_closed : ∀{n n'} (ω : Rew L ℕ n ℕ n'), ∀ p, Domain p → Domain (ω.hom p)

namespace Class

variable {c : Class L}

protected def eqvClosure (c : Class L) (T : Theory L) : Class L where
  Domain := EqvClosure T c.Domain
  rew_closed := by
    rintro _ _ ω p ⟨p', hp', H⟩;
    exact ⟨ω.hom p', c.rew_closed ω p' hp', H.rew ω⟩

def Mem (c : Class L) (p : Semiformula L ξ n) : Prop :=
    ∃ f : ℕ → Semiterm L ξ n, ∃ p₀, c.Domain p₀ ∧ p = (Rew.rewrite f).hom p₀

lemma mem_eqv_closure_Domain {p q : SyntacticSemiformula L n} (H : p ↔[T] q) : c.Domain p → (c.eqvClosure T).Domain q :=
  fun hp ↦ ⟨p, hp, H⟩

@[simp] lemma eqv_eqv : (c.eqvClosure T).eqvClosure T = c.eqvClosure T := by
  ext; simp [Class.eqvClosure]

lemma mem_eqv_closure_of_equiv_of_nonempty (hξ : Nonempty ξ) {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.Mem p → (c.eqvClosure T).Mem q := by
  haveI : Inhabited ξ := Classical.inhabited_of_nonempty hξ
  rintro ⟨f, p, hp, rfl⟩
  let q₀ : SyntacticSemiformula L n := (Rew.rewriteMap q.fvEnum).hom q
  have hq : q = (Rew.rewriteMap q.fvEnumInv).hom q₀ := by simp [←Rew.hom_comp_app]
  have hp' : Domain c (((Rew.rewriteMap q.fvEnum).comp (Rew.rewrite f)).hom p) :=
    c.rew_closed ((Rew.rewriteMap q.fvEnum).comp (Rew.rewrite f)) p hp
  have : Domain (c.eqvClosure T) q₀ :=
    mem_eqv_closure_Domain (by simp [Rew.hom_comp_app]; exact H.rew _) hp'
  exact ⟨_, q₀,this, hq⟩

lemma mem_eqv_closure_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.Mem p → (c.eqvClosure T).Mem q := by
  by_cases hξ : Nonempty ξ
  · exact mem_eqv_closure_of_equiv_of_nonempty hξ H
  · haveI hξ : IsEmpty ξ := not_nonempty_iff.mp hξ
    rintro ⟨f, p, hp, rfl⟩
    let q₀ : SyntacticSemiformula L n := (Rew.rewriteMap hξ.elim).hom q
    have hq : q = (Rew.rewrite (fun _ ↦ f 0)).hom q₀ := by
      simp [←Rew.hom_comp_app]
      symm; exact Rew.hom_eq_id_of_eq_on_fvar_list _ (fun x ↦ by simp [Rew.comp_app]) (fun x ↦ by simp)
    have hp' : Domain c (((Rew.rewriteMap hξ.elim).comp (Rew.rewrite f)).hom p) :=
    c.rew_closed ((Rew.rewriteMap hξ.elim).comp (Rew.rewrite f)) p hp
    have : Domain (c.eqvClosure T) q₀ :=
      mem_eqv_closure_Domain (by simp [Rew.hom_comp_app]; exact H.rew _) hp'
    exact ⟨_, q₀,this, hq⟩

lemma mem_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : (c.eqvClosure T).Mem p → (c.eqvClosure T).Mem q := by
  intro h; simpa using mem_eqv_closure_of_equiv H h

lemma mem_iff_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : (c.eqvClosure T).Mem p ↔ (c.eqvClosure T).Mem q :=
  ⟨mem_of_equiv H, mem_of_equiv H.symm⟩

lemma mem_of_domain {p : SyntacticSemiformula L n} (h : c.Domain p) : c.Mem p := ⟨(&·), _, h, by simp⟩

lemma mem_rew {p₁ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) : c.Mem p₁ → c.Mem (ω.hom p₁) := by
  rintro ⟨f, p, hp, rfl⟩; simp [Mem]
  let p' : SyntacticSemiformula L n₂ := (Rew.bind (fun x ↦ &↑x) (fun x ↦ &(x + n₁))).hom p
  exact ⟨fun x ↦ if hx : x < n₁ then ω #⟨x, hx⟩ else ω (f (x - n₁)), p', c.rew_closed _ _ hp,
    by simp [←Rew.hom_comp_app]; congr 2; ext <;> simp [Rew.comp_app]⟩

lemma cast {p q : Semiformula L ξ n} (hp : c.Mem p) (e : p = q) : c.Mem q := e ▸ hp

instance : LE (Class L) := ⟨fun c c' ↦ ∀ {n} {p : SyntacticSemiformula L n}, c.Domain p → c'.Domain p⟩

namespace LE

variable {c c' : Class L}

@[refl] protected lemma refl : c ≤ c := id

@[trans] protected lemma trans {c₁ c₂ c₃ : Class L} : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃ := fun h₁ h₂ _ _ hp ↦ h₂ (h₁ hp)

lemma Mem (H : c ≤ c') {p : Semiformula L ξ n} (hp : c.Mem p) : c'.Mem p := by
  rcases hp with ⟨f, p, hp, rfl⟩
  exact ⟨f, p, H hp, rfl⟩

end LE

lemma le_eqvClosure (c : Class L) (T : Theory L) : c ≤ c.eqvClosure T := by intro _ p hp; exact subset_equivalent_closure hp

lemma le_of_subtheory (c : Class L) {T T' : Theory L} (h : T ≾ T') : c.eqvClosure T ≤ c.eqvClosure T' := by
  rintro _ p ⟨p', hp', H⟩; exact ⟨p', hp', H.of_subtheory h⟩

class Atom (c : Class L) : Prop where
  verum : ∀ n, c.Domain (⊤ : SyntacticSemiformula L n)
  falsum : ∀ n, c.Domain (⊥ : SyntacticSemiformula L n)
  rel : ∀ {n k} (r : L.Rel k) (v : Fin k → SyntacticSemiterm L n), c.Domain (Semiformula.rel r v)
  nrel : ∀ {n k} (r : L.Rel k) (v : Fin k → SyntacticSemiterm L n), c.Domain (Semiformula.nrel r v)

class Not (c : Class L) : Prop where
  not {n} {p : SyntacticSemiformula L n} : c.Domain p → c.Domain (~p)

class And (c : Class L) : Prop where
  and {n} {p q : SyntacticSemiformula L n} : c.Domain p → c.Domain q → c.Domain (p ⋏ q)

class Or (c : Class L) : Prop where
  or {n} {p q : SyntacticSemiformula L n} : c.Domain p → c.Domain q → c.Domain (p ⋎ q)

class BAll (c : Class L) [L.LT] : Prop where
  ball {n} {p : SyntacticSemiformula L (n + 1)} : c.Domain p → c.Domain (∀[“#0 < &0”] p)

class BEx (c : Class L) [L.LT] : Prop where
  bex {n} {p : SyntacticSemiformula L (n + 1)} : c.Domain p → c.Domain (∃[“#0 < &0”] p)

section Atom

variable [c.Atom] [Nonempty (Term L ξ)]

@[simp] lemma mem_verum : c.Mem (⊤ : Semiformula L ξ n) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  simpa using mem_rew (Rew.bind ![] (fun _ ↦ t) : Rew L ℕ 0 ξ n) (mem_of_domain (Atom.verum _))

@[simp] lemma mem_falsum : c.Mem (⊥ : Semiformula L ξ n) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  simpa using mem_rew (Rew.bind ![] (fun _ ↦ t) : Rew L ℕ 0 ξ n) (mem_of_domain (Atom.falsum _))

@[simp] lemma mem_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : c.Mem (Semiformula.rel r v) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  have : c.Mem (Semiformula.rel (n := n) r (&↑·)) := (mem_of_domain (Atom.rel r (& ·)))
  simpa [Rew.rel] using c.mem_rew (Rew.rewrite (fun x ↦ if hx : x < k then v ⟨x, hx⟩ else t) : Rew L ℕ n ξ n) this


@[simp] lemma mem_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : c.Mem (Semiformula.nrel r v) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  have : Mem c (Semiformula.nrel (n := n) r (&↑·)) := (mem_of_domain (Atom.nrel r (& ·)))
  simpa [Rew.nrel] using mem_rew (Rew.rewrite (fun x ↦ if hx : x < k then v ⟨x, hx⟩ else t) : Rew L ℕ n ξ n) this

@[simp] lemma mem_eq [L.Eq] (t u : Semiterm L ξ n) : c.Mem “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_not_eq [L.Eq] (t u : Semiterm L ξ n) : c.Mem “!!t ≠ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_lt [L.LT] (t u : Semiterm L ξ n) : c.Mem “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

@[simp] lemma mem_not_lt [L.LT] (t u : Semiterm L ξ n) : c.Mem “!!t ≮ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

def of_le (c c' : Class L) [c.Atom] (h : c ≤ c') : c'.Atom where
  verum := fun n ↦ h (Atom.verum n)
  falsum := fun n ↦ h (Atom.falsum n)
  rel := fun r v ↦ h (Atom.rel r v)
  nrel := fun r v ↦ h (Atom.nrel r v)

instance : (c.eqvClosure T).Atom := of_le c _ (le_eqvClosure c T)

end Atom

section Not

variable [c.Not]

lemma mem_not {p : Semiformula L ξ n} (hp : c.Mem p) : c.Mem (~p) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  simpa using mem_rew (Rew.rewrite f) (mem_of_domain (Not.not hp))

instance : (c.eqvClosure T).Not := ⟨by rintro _ p ⟨p', hp', H⟩; exact ⟨~p', Not.not hp', H.not⟩⟩

end Not

section And

variable [c.And]

lemma mem_and {p q : Semiformula L ξ n} (hp : c.Mem p) (hq : c.Mem q) : c.Mem (p ⋏ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : c.Domain ((Rew.rewriteMap (Nat.bit false)).hom p) := c.rew_closed (Rew.rewriteMap (Nat.bit false)) _ hp
  have hq' : c.Domain ((Rew.rewriteMap (Nat.bit true)).hom q) := c.rew_closed (Rew.rewriteMap (Nat.bit true)) _ hq
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.rewrite fg) <| c.mem_of_domain (And.and hp' hq')) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

instance : (c.eqvClosure T).And := ⟨by rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋏ q', And.and hp' hq', Hp.and Hq⟩⟩

end And

section Or

variable [c.Or]

lemma mem_or {p q : Semiformula L ξ n} (hp : c.Mem p) (hq : c.Mem q) : c.Mem (p ⋎ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : c.Domain ((Rew.rewriteMap (Nat.bit false)).hom p) := c.rew_closed _ _ hp
  have hq' : c.Domain ((Rew.rewriteMap (Nat.bit true)).hom q) := c.rew_closed _ _ hq
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.rewrite fg) <| c.mem_of_domain (Or.or hp' hq')) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

instance : (c.eqvClosure T).Or := ⟨by rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋎ q', Or.or hp' hq', Hp.or Hq⟩⟩

variable [c.Not]

lemma mem_imply {p q : Semiformula L ξ n} (hp : c.Mem p) (hq : c.Mem q) : c.Mem (p ⟶ q) := by
  simp [Semiformula.imp_eq]; exact mem_or (mem_not hp) hq

variable [c.And]

lemma mem_iff {p q : Semiformula L ξ n} (hp : c.Mem p) (hq : c.Mem q) : c.Mem (p ⟷ q) := by
  simp [LO.LogicSymbol.iff]; exact mem_and (mem_imply hp hq) (mem_imply hq hp)

end Or

section BAll

variable [L.LT] [c.BAll]

lemma mem_ball_aux (hξ : Nonempty ξ) {p : Semiformula L ξ (n + 1)} (hp : c.Mem p) {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    c.Mem (∀[“#0 < !!t”] p) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
  haveI : Inhabited ξ := Classical.inhabited_of_nonempty hξ
  generalize hp' : (Rew.rewrite f).hom p = p'
  have : c.Mem (∀[“#0 < &0”] (Rew.rewrite (fun x ↦ &(p'.fvEnum x + 1))).hom p') :=
    mem_of_domain <| BAll.ball (by simp [←hp', ←Rew.hom_comp_app]; exact c.rew_closed _ _ hp)
  have : c.Mem (∀[“#0 < !!(Rew.bShift t)”] (Rew.rewriteMap $ p'.fvEnumInv ∘ p'.fvEnum).hom p') := by
    simpa [-Rew.rewriteMap_fvEnumInv_fvEnum, Rew.rewriteMap, Function.comp,
        ←Rew.hom_comp_app, Rew.rewrite_comp_rewrite, Function.comp] using
      mem_rew (Rew.rewrite (t :>ₙ fun x ↦ &(p'.fvEnumInv x))) this
  simpa using this

lemma mem_ball {p : Semiformula L ξ (n + 1)} (hp : c.Mem p) {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    c.Mem (∀[“#0 < !!t”] p) := by
  by_cases hξ : Nonempty ξ
  · exact mem_ball_aux hξ hp ht
  haveI : IsEmpty ξ := not_nonempty_iff.mp hξ
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
  generalize hp' : (Rew.rewrite f).hom p = p'
  have : c.Mem (∀[“#0 < &0”] Rew.emb.hom p') :=
    mem_of_domain <| BAll.ball (by simp [←hp', ←Rew.hom_comp_app]; exact c.rew_closed _ _ hp)
  simpa [←Rew.hom_comp_app, Rew.rewrite_comp_rewrite, Function.comp] using
    mem_rew (Rew.rewrite (fun _ ↦ t)) this

end BAll

section BEx

variable [L.LT] [c.BEx]

lemma mem_bex_aux (hξ : Nonempty ξ) {p : Semiformula L ξ (n + 1)} (hp : c.Mem p) {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    c.Mem (∃[“#0 < !!t”] p) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
  haveI : Inhabited ξ := Classical.inhabited_of_nonempty hξ
  generalize hp' : (Rew.rewrite f).hom p = p'
  have : c.Mem (∃[“#0 < &0”] (Rew.rewrite (fun x ↦ &(p'.fvEnum x + 1))).hom p') :=
    mem_of_domain <| BEx.bex (by simp [←hp', ←Rew.hom_comp_app]; exact c.rew_closed _ _ hp)
  have : c.Mem (∃[“#0 < !!(Rew.bShift t)”] (Rew.rewriteMap $ p'.fvEnumInv ∘ p'.fvEnum).hom p') := by
    simpa [-Rew.rewriteMap_fvEnumInv_fvEnum, Rew.rewriteMap, Function.comp,
        ←Rew.hom_comp_app, Rew.rewrite_comp_rewrite, Function.comp] using
      mem_rew (Rew.rewrite (t :>ₙ fun x ↦ &(p'.fvEnumInv x))) this
  simpa using this

lemma mem_bex {p : Semiformula L ξ (n + 1)} (hp : c.Mem p) {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    c.Mem (∃[“#0 < !!t”] p) := by
  by_cases hξ : Nonempty ξ
  · exact mem_bex_aux hξ hp ht
  haveI : IsEmpty ξ := not_nonempty_iff.mp hξ
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
  generalize hp' : (Rew.rewrite f).hom p = p'
  have : c.Mem (∃[“#0 < &0”] Rew.emb.hom p') :=
    mem_of_domain <| BEx.bex (by simp [←hp', ←Rew.hom_comp_app]; exact c.rew_closed _ _ hp)
  simpa [←Rew.hom_comp_app, Rew.rewrite_comp_rewrite, Function.comp] using
    mem_rew (Rew.rewrite (fun _ ↦ t)) this

end BEx

section

variable [c.Atom] [c.And] [c.Or] [Nonempty (Term L ξ)]

@[simp] lemma mem_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.Mem “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply mem_or <;> simp

@[simp] lemma mem_not_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.Mem “¬!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply mem_and <;> simp

end

end Class

def openClass (L : Language) : Class L where
  Domain := Semiformula.Open
  rew_closed := by simp

instance : (openClass L).Atom where
  verum := fun _ ↦ Semiformula.open_top
  falsum := fun _ ↦ Semiformula.open_bot
  rel := fun r v ↦ Semiformula.open_rel r v
  nrel := fun r v ↦ Semiformula.open_nrel r v

instance : (openClass T).Not := ⟨Semiformula.open_neg.mpr⟩

instance : (openClass T).And := ⟨fun hp hq ↦ Semiformula.open_and.mpr ⟨hp, hq⟩⟩

instance : (openClass T).Or := ⟨fun hp hq ↦ Semiformula.open_or.mpr ⟨hp, hq⟩⟩

section

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

attribute [aesop 1 (rule_sets [FormulaClass]) norm]
  Class.mem_imply
  Class.mem_iff
  Class.mem_ball
  Class.mem_bex

attribute [aesop 2 (rule_sets [FormulaClass]) norm]
  Class.mem_and
  Class.mem_or
  Class.mem_rew
  Class.mem_not

macro "formula_class" : attr =>
  `(attr|aesop 4 (rule_sets [$(Lean.mkIdent `FormulaClass):ident]) safe)

macro "formula_class" (config)? : tactic =>
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `FormulaClass):ident]))

macro "formula_class?" (config)? : tactic =>
  `(tactic| aesop? (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `FormulaClass):ident]))

example : (openClass ℒₒᵣ).Mem (“¬0 < 6 → &6 + #5 ≠ 0” : Semiformula ℒₒᵣ ℕ 8) := by { formula_class }

end

end LO.FirstOrder
