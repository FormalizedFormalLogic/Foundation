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

def rewClosure (s : Set (Semiformula L ξ n)) : Set (Semiformula L ξ n) := { p | ∃ p₀ ∈ s, ∃ ω : Rew L ξ n ξ n, p = ω.hom p₀ }

def eqvClosure (T : Theory L) (s : Set (Semiformula L ξ n)) : Set (Semiformula L ξ n) := { p | ∃ p₀ ∈ s, p₀ ↔[T] p }

section eqvClosure

variable {T : Theory L} {s : Set (Semiformula L ξ n)}

lemma mem_equivalent_closure_of_equivalent {p q : Semiformula L ξ n} (h : p ↔[T] q) :
    p ∈ eqvClosure T s → q ∈ eqvClosure T s := by
  rintro ⟨p₀, hp₀, h₀⟩; exact ⟨p₀, hp₀, h₀.trans h⟩

lemma subset_equivalent_closure : s ⊆ eqvClosure T s := by
  intro p hp; exact ⟨p, hp, by rfl⟩

@[simp] lemma eqv_eqv : eqvClosure T (eqvClosure T s) = eqvClosure T s := by
  ext p; simp [eqvClosure]; constructor
  · rintro ⟨q, ⟨r, hr, hrq⟩, hqp⟩
    exact ⟨r, hr, hrq.trans hqp⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, ⟨q, hq, by rfl⟩, hqp⟩

end eqvClosure

@[ext] structure Class (L : Language) where
  domain : Set (SyntacticFormula L)
  rewrite_closed : ∀ p ∈ domain, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ domain
  --equivalent_closed : ∀ p q : SyntacticFormula L, p ↔[T] q → p ∈ domain → q ∈ domain

namespace Class

variable {c : Class L}

protected def eqvClosure (c : Class L) (T : Theory L) : Class L where
  domain := eqvClosure T c.domain
  rewrite_closed := by rintro p ⟨p', hp', H⟩ f; exact ⟨(Rew.rewrite f).hom p', c.rewrite_closed p' hp' f, H.rew _⟩

def mem (c : Class L) (p : Semiformula L ξ n) : Prop :=
    ∃ v : ℕ → Semiterm L ξ n, ∃ p₀ ∈ c.domain, p = (Rew.bind ![] v).hom p₀

lemma mem_eqv_closure_domain (H : p ↔[T] q) : p ∈ c.domain → q ∈ (c.eqvClosure T).domain :=
  fun hp ↦ ⟨p, hp, H⟩

@[simp] lemma eqv_eqv : (c.eqvClosure T).eqvClosure T = c.eqvClosure T := by
  ext; simp [Class.eqvClosure]

lemma mem_eqv_closure_of_equiv_of_nonempty (hξ : Nonempty ξ) {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.mem p → (c.eqvClosure T).mem q := by
  haveI : Inhabited ξ := Classical.inhabited_of_nonempty hξ
  rintro ⟨v, p, hp, rfl⟩
  generalize hω : ((Rew.bind (fun x ↦ &x.val) (fun x ↦ &(x + n))).comp (Rew.rewriteMap q.fvEnum) : Rew L ξ n ℕ 0) = ω
  let q₀ : SyntacticFormula L := ω.hom q
  have hq : q = (Rew.bind ![] (fun x ↦ if hx : x < n then #⟨x, hx⟩ else &(q.fvEnumInv (x - n)))).hom q₀ := by
    simp [←hω, ←Rew.hom_comp_app]
    symm; apply Rew.hom_eq_id_of_eq_on_fvar_list
    · simp [Rew.comp_app]
    · intro x hx
      simp [Rew.comp_app, Semiformula.fvEnumInv_fvEnum hx]
  have hp' : (Rew.hom (Rew.rewrite fun x ↦ ω (v x))) p ∈ c.domain := c.rewrite_closed p hp (fun x ↦ ω (v x))
  have : q₀ ∈ (c.eqvClosure T).domain := mem_eqv_closure_domain (by
    simp [Semiformula.Equivalent, consequence_iff, models_iff, Semiformula.eval_rew, Function.comp, Matrix.empty_eq] at H ⊢
    intro M x _ hT ε
    have : Semiformula.Val! M (fun x ↦ Semiterm.val! M (fun x ↦ (ω #x).val! M ![] ε) (fun x ↦ (ω &x).val! M ![] ε) (v x)) p ↔
        (Semiformula.Eval! M (fun x ↦ (ω #x).val! M ![] ε) fun x ↦ (ω &x).val! M ![] ε) q :=
      H M x hT (fun x ↦ (ω &x).val! M ![] ε) (fun x ↦ (ω #x).val! M ![] ε)
    simp[←this]
    apply iff_of_eq; congr
    funext x; simp [Semiterm.val_rew ω (v x), Function.comp]) hp'
  exact ⟨_, q₀, this, hq⟩

lemma mem_eqv_closure_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.mem p → (c.eqvClosure T).mem q := by
  by_cases hξ : Nonempty ξ
  · exact mem_eqv_closure_of_equiv_of_nonempty hξ H
  · haveI hξ : IsEmpty ξ := not_nonempty_iff.mp hξ
    rintro ⟨v, p, hp, rfl⟩
    generalize hω : (Rew.bind (fun x ↦ &x.val) hξ.elim : Rew L ξ n ℕ 0) = ω
    let q₀ : SyntacticFormula L := ω.hom q
    have hq : q = (Rew.bind ![] fun x ↦ if hx : x < n then #⟨x, hx⟩ else v 0).hom q₀ := by
      simp [←hω, ←Rew.hom_comp_app]
      symm; apply Rew.hom_eq_id_of_eq_on_fvar_list
      · simp [Rew.comp_app]
      · intro x _; exact hξ.elim' x
    have hp' : (Rew.hom (Rew.rewrite fun x ↦ ω (v x))) p ∈ c.domain := c.rewrite_closed p hp (fun x ↦ ω (v x))
    have : q₀ ∈ (c.eqvClosure T).domain := mem_eqv_closure_domain (by
      simp [Semiformula.Equivalent, consequence_iff, models_iff, Semiformula.eval_rew, Function.comp, Matrix.empty_eq, hξ.eq_elim] at H ⊢
      intro M x _ hT ε
      have := H M x hT (fun x ↦ (ω #x).val! M ![] ε)
      simp[←this]
      apply iff_of_eq; congr
      funext x; simp [Semiterm.val_rew ω (v x), Function.comp, hξ.eq_elim]) hp'
    exact ⟨_, q₀, this, hq⟩

lemma mem_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : (c.eqvClosure T).mem p → (c.eqvClosure T).mem q := by
  intro h; simpa using mem_eqv_closure_of_equiv H h

lemma mem_iff_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : (c.eqvClosure T).mem p ↔ (c.eqvClosure T).mem q :=
  ⟨mem_of_equiv H, mem_of_equiv H.symm⟩

lemma mem_of_mem_domain {p : SyntacticFormula L} (h : p ∈ c.domain) : c.mem p := ⟨(&·), _, h, by simp⟩

lemma mem_rew {p₁ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) : c.mem p₁ → c.mem (ω.hom p₁) := by
  rintro ⟨v, p, hp, rfl⟩
  exact ⟨fun x ↦ (ω.comp (Rew.bind ![] v)) (&x), _, hp, by simp [←Rew.hom_comp_app]; congr; ext x <;> simp; { exact x.elim0 }⟩

lemma cast {p q : Semiformula L ξ n} (hp : c.mem p) (e : p = q) : c.mem q := e ▸ hp

instance : LE (Class L) := ⟨fun c c' ↦ c.domain ⊆ c'.domain⟩

namespace LE

variable {c c' : Class L}

@[refl] protected lemma refl : c ≤ c := Set.Subset.rfl

@[trans] protected lemma trans {c₁ c₂ c₃ : Class L} : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃ := Set.Subset.trans

lemma mem (H : c ≤ c') {p : Semiformula L ξ n} (hp : c.mem p) : c'.mem p := by
  rcases hp with ⟨f, p, hp, rfl⟩
  exact ⟨f, p, H hp, rfl⟩

end LE

lemma le_eqvClosure (c : Class L) (T : Theory L) : c ≤ c.eqvClosure T := by intro p hp; exact subset_equivalent_closure hp

lemma le_of_subtheory (c : Class L) {T T' : Theory L} (h : T ≾ T') : c.eqvClosure T ≤ c.eqvClosure T' := by
  rintro p ⟨p', hp', H⟩; exact ⟨p', hp', H.of_subtheory h⟩

class Atom (c : Class L) : Prop where
  verum : ⊤ ∈ c.domain
  falsum : ⊥ ∈ c.domain
  rel : ∀ {k} (r : L.Rel k) (v), Semiformula.rel r v ∈ c.domain
  nrel : ∀ {k} (r : L.Rel k) (v), Semiformula.nrel r v ∈ c.domain

class Not (c : Class L) : Prop where
  not {p : SyntacticFormula L} : p ∈ c.domain → ~p ∈ c.domain

class And (c : Class L) : Prop where
  and {p q : SyntacticFormula L} : p ∈ c.domain → q ∈ c.domain → p ⋏ q ∈ c.domain

class Or (c : Class L) : Prop where
  or {p q : SyntacticFormula L} : p ∈ c.domain → q ∈ c.domain → p ⋎ q ∈ c.domain

section Atom

variable [c.Atom] [Nonempty (Term L ξ)]

@[simp] lemma mem_verum : c.mem (⊤ : Semiformula L ξ n) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  simpa using mem_rew (Rew.bind ![] (fun _ ↦ t) : Rew L ℕ 0 ξ n) (mem_of_mem_domain Atom.verum)

@[simp] lemma mem_falsum : c.mem (⊥ : Semiformula L ξ n) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  simpa using mem_rew (Rew.bind ![] (fun _ ↦ t) : Rew L ℕ 0 ξ n) (mem_of_mem_domain Atom.falsum)

@[simp] lemma mem_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : c.mem (Semiformula.rel r v) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  have : mem c (Semiformula.rel r (&↑·)) := (mem_of_mem_domain (Atom.rel r (& ·)))
  simpa [Rew.rel] using mem_rew (Rew.bind ![] (fun x ↦ if hx : x < k then v ⟨x, hx⟩ else t) : Rew L ℕ 0 ξ n) this

@[simp] lemma mem_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : c.mem (Semiformula.nrel r v) := by
  let t : Semiterm L ξ n := Rew.substs ![] Classical.ofNonempty
  have : mem c (Semiformula.nrel r (&↑·)) := (mem_of_mem_domain (Atom.nrel r (& ·)))
  simpa [Rew.nrel] using mem_rew (Rew.bind ![] (fun x ↦ if hx : x < k then v ⟨x, hx⟩ else t) : Rew L ℕ 0 ξ n) this

@[simp] lemma mem_eq [L.Eq] (t u : Semiterm L ξ n) : c.mem “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_not_eq [L.Eq] (t u : Semiterm L ξ n) : c.mem “!!t ≠ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.Eq.eq]

@[simp] lemma mem_lt [L.LT] (t u : Semiterm L ξ n) : c.mem “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

@[simp] lemma mem_not_lt [L.LT] (t u : Semiterm L ξ n) : c.mem “!!t ≮ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel, Semiformula.Operator.LT.lt]

def of_le (c c' : Class L) [c.Atom] (h : c ≤ c') : c'.Atom where
  verum := h Atom.verum
  falsum := h Atom.falsum
  rel := fun r v ↦ h (Atom.rel r v)
  nrel := fun r v ↦ h (Atom.nrel r v)

instance : (c.eqvClosure T).Atom := of_le c _ (le_eqvClosure c T)

end Atom

section Not

variable [c.Not]

lemma mem_not {p : Semiformula L ξ n} (hp : c.mem p) : c.mem (~p) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  simpa using mem_rew (Rew.bind ![] f) (mem_of_mem_domain (Not.not hp))

instance : (c.eqvClosure T).Not := ⟨by rintro p ⟨p', hp', H⟩; exact ⟨~p', Not.not hp', H.not⟩⟩

end Not

section And

variable [c.And]

lemma mem_and {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⋏ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : (Rew.rewriteMap (Nat.bit false)).hom p ∈ c.domain := c.rewrite_closed _ hp _
  have hq' : (Rew.rewriteMap (Nat.bit true)).hom q ∈ c.domain := c.rewrite_closed _ hq _
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.bind ![] fg) <| c.mem_of_mem_domain (And.and hp' hq')) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

instance : (c.eqvClosure T).And := ⟨by rintro p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋏ q', And.and hp' hq', Hp.and Hq⟩⟩

end And

section Or

variable [c.Or]

lemma mem_or {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⋎ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : (Rew.rewriteMap (Nat.bit false)).hom p ∈ c.domain := c.rewrite_closed _ hp _
  have hq' : (Rew.rewriteMap (Nat.bit true)).hom q ∈ c.domain := c.rewrite_closed _ hq _
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.bind ![] fg) <| c.mem_of_mem_domain (Or.or hp' hq')) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

instance : (c.eqvClosure T).Or := ⟨by rintro p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩; exact ⟨p' ⋎ q', Or.or hp' hq', Hp.or Hq⟩⟩

variable [c.Not]

lemma mem_imply {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⟶ q) := by
  simp [Semiformula.imp_eq]; exact mem_or (mem_not hp) hq

variable [c.And]

lemma mem_iff {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⟷ q) := by
  simp [LO.LogicSymbol.iff]; exact mem_and (mem_imply hp hq) (mem_imply hq hp)

end Or

section

variable [c.Atom] [c.And] [c.Or] [Nonempty (Term L ξ)]

@[simp] lemma mem_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.mem “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply mem_or <;> simp

@[simp] lemma mem_not_le [L.Eq] [L.LT] (t u : Semiterm L ξ n) : c.mem “¬!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Rew.rel,
    Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.eq, Semiformula.Operator.LT.lt]
  apply mem_and <;> simp

end

end Class

def openClass (L : Language) : Class L where
  domain := Semiformula.Open
  rewrite_closed := by intro p hp f; simpa [Set.mem_def] using hp

instance : (openClass L).Atom where
  verum := Semiformula.open_top
  falsum := Semiformula.open_bot
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

example : (openClass ℒₒᵣ).mem (“¬0 < 6 → &6 + #5 ≠ 0” : Semiformula ℒₒᵣ ℕ 8) := by { formula_class }

end

end LO.FirstOrder
