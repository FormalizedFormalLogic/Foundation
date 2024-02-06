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

end Equivalent

end Semiformula

def rewClosure (s : Set (Semiformula L ξ n)) : Set (Semiformula L ξ n) := { p | ∃ p₀ ∈ s, ∃ ω : Rew L ξ n ξ n, p = ω.hom p₀ }

def equivalentClosure (T : Theory L) (s : Set (Semiformula L ξ n)) : Set (Semiformula L ξ n) := { p | ∃ p₀ ∈ s, p₀ ↔[T] p }

section equivalentClosure

variable {T : Theory L} {s : Set (Semiformula L ξ n)}

lemma mem_equivalent_closure_of_equivalent {p q : Semiformula L ξ n} (h : p ↔[T] q) :
    p ∈ equivalentClosure T s → q ∈ equivalentClosure T s := by
  rintro ⟨p₀, hp₀, h₀⟩; exact ⟨p₀, hp₀, h₀.trans h⟩

lemma subset_equivalent_closure : s ⊆ equivalentClosure T s := by
  intro p hp; exact ⟨p, hp, by rfl⟩

end equivalentClosure

structure Class (T : Theory L) where
  domain : Set (SyntacticFormula L)
  rewrite_closed : ∀ p ∈ domain, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ domain
  equivalent_closed : ∀ p q : SyntacticFormula L, p ↔[T] q → p ∈ domain → q ∈ domain

namespace Class

variable {T : Theory L} {c : Class T}

def mem (c : Class T) (p : Semiformula L ξ n) : Prop :=
    ∃ v : ℕ → Semiterm L ξ n, ∃ p₀ ∈ c.domain, p = (Rew.bind ![] v).hom p₀

lemma mem_of_equiv_of_nonempty (hξ : Nonempty ξ) {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.mem p → c.mem q := by
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
  have : q₀ ∈ c.domain := c.equivalent_closed _ _ (by
    simp [Semiformula.Equivalent, consequence_iff, models_iff, Semiformula.eval_rew, Function.comp, Matrix.empty_eq] at H ⊢
    intro M x _ hT ε
    have : Semiformula.Val! M (fun x ↦ Semiterm.val! M (fun x ↦ (ω #x).val! M ![] ε) (fun x ↦ (ω &x).val! M ![] ε) (v x)) p ↔
        (Semiformula.Eval! M (fun x ↦ (ω #x).val! M ![] ε) fun x ↦ (ω &x).val! M ![] ε) q :=
      H M x hT (fun x ↦ (ω &x).val! M ![] ε) (fun x ↦ (ω #x).val! M ![] ε)
    simp[←this]
    apply iff_of_eq; congr
    funext x; simp [Semiterm.val_rew ω (v x), Function.comp]) hp'
  exact ⟨_, q₀, this, hq⟩

lemma mem_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.mem p → c.mem q := by
  by_cases hξ : Nonempty ξ
  · exact mem_of_equiv_of_nonempty hξ H
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
    have : q₀ ∈ c.domain := c.equivalent_closed _ _ (by
      simp [Semiformula.Equivalent, consequence_iff, models_iff, Semiformula.eval_rew, Function.comp, Matrix.empty_eq, hξ.eq_elim] at H ⊢
      intro M x _ hT ε
      have := H M x hT (fun x ↦ (ω #x).val! M ![] ε)
      simp[←this]
      apply iff_of_eq; congr
      funext x; simp [Semiterm.val_rew ω (v x), Function.comp, hξ.eq_elim]) hp'
    exact ⟨_, q₀, this, hq⟩

lemma mem_iff_of_equiv {p q : Semiformula L ξ n} (H : p ↔[T] q) : c.mem p ↔ c.mem q :=
  ⟨mem_of_equiv H, mem_of_equiv H.symm⟩

lemma mem_of_mem_domain {p : SyntacticFormula L} (h : p ∈ c.domain) : c.mem p := ⟨(&·), _, h, by simp⟩

lemma mem_rew {p₁ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) : c.mem p₁ → c.mem (ω.hom p₁) := by
  rintro ⟨v, p, hp, rfl⟩
  exact ⟨fun x ↦ (ω.comp (Rew.bind ![] v)) (&x), _, hp, by simp [←Rew.hom_comp_app]; congr; ext x <;> simp; { exact x.elim0 }⟩

lemma cast {p q : Semiformula L ξ n} (hp : c.mem p) (e : p = q) : c.mem q := e ▸ hp

class Atom (c : Class T) : Prop where
  verum : ⊤ ∈ c.domain
  falsum : ⊥ ∈ c.domain
  rel : ∀ {k} (r : L.Rel k) (v), Semiformula.rel r v ∈ c.domain
  nrel : ∀ {k} (r : L.Rel k) (v), Semiformula.nrel r v ∈ c.domain

class Not (c : Class T) : Prop where
  not {p : SyntacticFormula L} : p ∈ c.domain → ∃ r ∈ c.domain, r ↔[T] (~p)

class And (c : Class T) : Prop where
  and {p q : SyntacticFormula L} : p ∈ c.domain → q ∈ c.domain → ∃ r ∈ c.domain, r ↔[T] (p ⋏ q)

class Or (c : Class T) : Prop where
  or {p q : SyntacticFormula L} : p ∈ c.domain → q ∈ c.domain → ∃ r ∈ c.domain, r ↔[T] (p ⋎ q)

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

end Atom

section Not

variable [c.Not]

lemma mem_not {p : Semiformula L ξ n} (hp : c.mem p) : c.mem (~p) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases Not.not hp with ⟨q, hq, H⟩
  simpa using mem_rew (Rew.bind ![] f) (mem_of_equiv H (mem_of_mem_domain hq))

end Not

section And

variable [c.And]

lemma mem_and {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⋏ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : (Rew.rewriteMap (Nat.bit false)).hom p ∈ c.domain := c.rewrite_closed _ hp _
  have hq' : (Rew.rewriteMap (Nat.bit true)).hom q ∈ c.domain := c.rewrite_closed _ hq _
  rcases And.and hp' hq' with ⟨r, hr, H⟩
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.bind ![] fg) <| mem_of_equiv H <| c.mem_of_mem_domain hr) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

end And

section Or

variable [c.Or]

lemma mem_or {p q : Semiformula L ξ n} (hp : c.mem p) (hq : c.mem q) : c.mem (p ⋎ q) := by
  rcases hp with ⟨f, p, hp, rfl⟩
  rcases hq with ⟨g, q, hq, rfl⟩
  have hp' : (Rew.rewriteMap (Nat.bit false)).hom p ∈ c.domain := c.rewrite_closed _ hp _
  have hq' : (Rew.rewriteMap (Nat.bit true)).hom q ∈ c.domain := c.rewrite_closed _ hq _
  rcases Or.or hp' hq' with ⟨r, hr, H⟩
  let fg : ℕ → Semiterm L ξ n :=
    fun x ↦ Nat.bitCasesOn (C := fun _ ↦ Semiterm L ξ n) x (fun b x ↦ b.casesOn (f x) (g x))
  refine cast (mem_rew (Rew.bind ![] fg) <| mem_of_equiv H <| c.mem_of_mem_domain hr) ?_
  simp [←Rew.hom_comp_app]; constructor
  · congr; ext <;> simp [Rew.comp_app]
  · congr; ext <;> simp [Rew.comp_app]

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

def generatedFromRewriteClosedSet (T : Theory L) (s : Set (SyntacticFormula L))
    (H : ∀ p ∈ s, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ s) : Class T where
  domain := equivalentClosure T s
  rewrite_closed := by
    rintro p ⟨p₀, hs₀, hp⟩ f
    exact ⟨(Rew.rewrite f).hom p₀, H p₀ hs₀ f, hp.rew (Rew.rewrite f)⟩
  equivalent_closed := by
    intro p q H hp; exact mem_equivalent_closure_of_equivalent H hp

lemma generated_not {s : Set (SyntacticFormula L)} {H : ∀ p ∈ s, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ s}
    (h : ∀ p ∈ s, ∃ r ∈ s, r ↔[T] (~p)) : (generatedFromRewriteClosedSet T s H).Not := ⟨by
  rintro p ⟨p₀, hp₀, Hp⟩
  exact ⟨~p₀, h _ hp₀, Hp.not⟩⟩

lemma generated_and {s : Set (SyntacticFormula L)} {H : ∀ p ∈ s, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ s}
    (h : ∀ p ∈ s, ∀ q ∈ s, ∃ r ∈ s, r ↔[T] (p ⋏ q)) : (generatedFromRewriteClosedSet T s H).And := ⟨by
  rintro p q ⟨p₀, hp₀, Hp⟩ ⟨q₀, hq₀, Hq⟩
  exact ⟨p₀ ⋏ q₀, h _ hp₀ _ hq₀, Hp.and Hq⟩⟩

lemma generated_or {s : Set (SyntacticFormula L)} {H : ∀ p ∈ s, ∀ f : ℕ → Term L ℕ, (Rew.rewrite f).hom p ∈ s}
    (h : ∀ p ∈ s, ∀ q ∈ s, ∃ r ∈ s, r ↔[T] (p ⋎ q)) : (generatedFromRewriteClosedSet T s H).Or := ⟨by
  rintro p q ⟨p₀, hp₀, Hp⟩ ⟨q₀, hq₀, Hq⟩
  exact ⟨p₀ ⋎ q₀, h _ hp₀ _ hq₀, Hp.or Hq⟩⟩

end Class

def openClass {L : Language} (T : Theory L) : Class T :=
  Class.generatedFromRewriteClosedSet T Semiformula.Open (by intro p hp f; simpa [Set.mem_def] using hp)

instance : (openClass T).Atom where
  verum := subset_equivalent_closure Semiformula.open_top
  falsum := subset_equivalent_closure Semiformula.open_bot
  rel := fun r v ↦ subset_equivalent_closure (Semiformula.open_rel r v)
  nrel := fun r v ↦ subset_equivalent_closure (Semiformula.open_nrel r v)

instance : (openClass T).Not :=
  Class.generated_not (by intro p (hp : p.Open); exact ⟨~p, Semiformula.open_neg.mpr hp, by rfl⟩)

instance : (openClass T).And :=
  Class.generated_and (by intro p (hp : p.Open) q (hq : q.Open); exact ⟨p ⋏ q, Semiformula.open_and.mpr ⟨hp, hq⟩, by rfl⟩)

instance : (openClass T).Or :=
  Class.generated_or (by intro p (hp : p.Open) q (hq : q.Open); exact ⟨p ⋎ q, Semiformula.open_or.mpr ⟨hp, hq⟩, by rfl⟩)

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

example : (openClass T).mem (“¬0 < 6 → &6 + #5 ≠ 0” : Semiformula ℒₒᵣ ℕ 8) := by formula_class

end

end LO.FirstOrder
