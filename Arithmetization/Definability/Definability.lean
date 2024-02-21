import Arithmetization.Lemmata
import Arithmetization.Definability.Init
import Arithmetization.Definability.BoundedTheory

namespace LO.FirstOrder

def Defined {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.PVal! M v p

def DefinedWithParam {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semiformula L M k) : Prop :=
  ∀ v, R v ↔ Semiformula.Eval! M v id p

namespace Defined

variable [Structure L M]

lemma pval {k} {R : (Fin k → M) → Prop} {p : Semisentence L k} (h : Defined R p) (v) :
    Semiformula.PVal! M v p ↔ R v := (h v).symm

end Defined

namespace DefinedWithParam

variable [Structure L M]

lemma eval {k} {R : (Fin k → M) → Prop} {p : Semiformula L M k} (h : DefinedWithParam R p) (v) :
    Semiformula.Eval! M v id p ↔ R v := (h v).symm

end DefinedWithParam

namespace Arith

section definability

variable {T : Theory ℒₒᵣ}
variable {M : Type} [DecidableEq M] [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

namespace Definability

namespace FormulaHierarchy

-- abbrev of_zero (p : FormulaHierarchy Γ 0 ℒₒᵣ μ k) : FormulaHierarchy b' s ℒₒᵣ μ k :=
--   ⟨p, p.prop.of_zero⟩

variable (Γ : Polarity) (s : ℕ) (L : Language) [L.LT] (μ : Type*) (n)

end FormulaHierarchy

namespace BSemisentence

def eq : BSemisentence T Γ s 2 := ⟨“#0 = #1”, by simp⟩

def lt : BSemisentence T Γ s 2 := ⟨“#0 < #1”, by simp⟩

def le : BSemisentence T Γ s 2 := ⟨“#0 ≤ #1”, by simp⟩

end BSemisentence

end Definability

namespace Model

open Definability

variable (T Γ s)

abbrev DefinedPred (P : M → Prop) (p : BSemisentence T Γ s 1) : Prop :=
  Defined (λ v ↦ P (v 0)) p.val

abbrev DefinedRel (R : M → M → Prop) (p : BSemisentence T Γ s 2) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1)) p.val

abbrev DefinedRel₃ (R : M → M → M → Prop) (p : BSemisentence T Γ s 3) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2)) p.val

abbrev DefinedRel₄ (R : M → M → M → M → Prop) (p : BSemisentence T Γ s 4) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) p.val

notation Γ "ᴴ(" s ")[" T "]-Predicate" => DefinedPred T Γ s

notation Γ "ᴴ(" s ")[" T "]-Relation" => DefinedRel T Γ s

notation Γ "ᴴ(" s ")[" T "]-Relation₃" => DefinedRel₃ T Γ s

notation Γ "ᴴ(" s ")[" T "]-Relation₄" => DefinedRel₄ T Γ s

abbrev DefinedFunction {k} (f : (Fin k → M) → M) (p : BSemisentence T Γ s (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) p.val

abbrev DefinedFunction₁ (f : M → M) (p : BSemisentence T Γ s 2) : Prop :=
  DefinedFunction T Γ s (fun v => f (v 0)) p

abbrev DefinedFunction₂ (f : M → M → M) (p : BSemisentence T Γ s 3) : Prop :=
  DefinedFunction T Γ s (fun v => f (v 0) (v 1)) p

abbrev DefinedFunction₃ (f : M → M → M → M) (p : BSemisentence T Γ s 4) : Prop :=
  DefinedFunction T Γ s (fun v => f (v 0) (v 1) (v 2)) p

notation Γ "ᴴ(" s ")[" T "]-Function₁" => DefinedFunction₁ T Γ s

notation Γ "ᴴ(" s ")[" T "]-Function₂" => DefinedFunction₂ T Γ s

notation Γ "ᴴ(" s ")[" T "]-Function₃" => DefinedFunction₃ T Γ s

def DefinedRel.eq : DefinedRel T Γ s ((· = ·) : M → M → Prop) BSemisentence.eq := by intro v; simp [BSemisentence.eq]

def DefinedRel.lt : DefinedRel T Γ s ((· < ·) : M → M → Prop) BSemisentence.lt := by intro v; simp [BSemisentence.lt]

def DefinedRel.le [𝐏𝐀⁻.Mod M] :
    DefinedRel T Γ s ((· ≤ ·) : M → M → Prop) BSemisentence.le := by intro v; simp [BSemisentence.le]

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ p : BSemiformula T Γ s M k, DefinedWithParam P p.val

abbrev DefinablePred (P : M → Prop) : Prop := Definable T Γ s (k := 1) (fun v ↦ P (v 0))

abbrev DefinableRel (P : M → M → Prop) : Prop := Definable T Γ s (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := Definable T Γ s (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop := Definable T Γ s (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev DefinableFunction (f : (Fin k → M) → M) : Prop := Definable T Γ s (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev DefinableFunction₁ (f : M → M) : Prop := DefinableFunction T Γ s (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : M → M → M) : Prop := DefinableFunction T Γ s (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := DefinableFunction T Γ s (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

variable {T Γ s}

lemma defined_to_with_param {k} {P : (Fin k → M) → Prop} (p : BSemisentence T Γ s k) (hP : Defined P p.val) :
    Definable T Γ s P := ⟨⟨Rew.emb.hom p.val, HClassIn.rew p.property _⟩, by intro; simp [hP.pval]⟩

lemma defined_to_with_param₀ {k} {P : (Fin k → M) → Prop} (p : BSemisentence T Γ' 0 k) (hP : Defined P p.val) :
    Definable T Γ s P := ⟨⟨Rew.emb.hom p.val, HClassIn.rew (HClassIn.zero_le _ Γ s p.property) _⟩, by intro; simp [hP.pval]⟩

namespace Definable

lemma of_iff {p : (Fin k → M) → Prop} (q) (h : ∀ x, p x ↔ q x) (H : Definable T Γ s q) : Definable T Γ s p := by
  rwa [show p = q from by funext v; simp [h]]

lemma finmap {P : (Fin k → M) → Prop} (h : Definable T Γ s P) (f : Fin k → Fin n) :
    Definable T Γ s fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨p, h⟩
  exact ⟨⟨(Rew.substs (fun i ↦ #(f i))).hom p, HClassIn.rew p.property _⟩, by intro v; simp [h.eval]⟩

end Definable

namespace DefinableFunction

lemma of_eq {f : (Fin k → M) → M} (g) (h : ∀ v, f v = g v) (H : DefinableFunction T Γ s f) : DefinableFunction T Γ s g := by
  rwa [show g = f from by funext v; simp [h]]

lemma finmap {f : (Fin k → M) → M} (hf : DefinableFunction T Γ s f) (e : Fin k → Fin n) :
    DefinableFunction T Γ s fun v ↦ f (fun i ↦ v (e i)) := by
  have := Definable.finmap (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff _ (by intro x; simp)

lemma rel {f : (Fin k → M) → M} (h : DefinableFunction T Γ s f) :
  Definable T Γ s (fun v ↦ v 0 = f (v ·.succ)) := h

end DefinableFunction

instance DefinableFunction₁.graph {f : M → M} [h : DefinableFunction₁ T Γ s f] :
  DefinableRel T Γ s (Function.Graph f) := h

instance DefinableFunction₂.graph {f : M → M → M} [h : DefinableFunction₂ T Γ s f] :
  DefinableRel₃ T Γ s (Function.Graph₂ f) := h

instance DefinableFunction₃.graph {f : M → M → M → M} [h : DefinableFunction₃ T Γ s f] :
  DefinableRel₄ T Γ s (Function.Graph₃ f) := h

namespace DefinableRel

instance eq : DefinableRel T Γ s ((· = ·) : M → M → Prop) := ⟨⟨“#0 = #1”, by simp⟩, by intro; simp⟩

instance lt : DefinableRel T Γ s ((· < ·) : M → M → Prop) := ⟨⟨“#0 < #1”, by simp⟩, by intro; simp⟩

instance le [𝐏𝐀⁻.Mod M] : DefinableRel T Γ s ((· ≤ ·) : M → M → Prop) := ⟨⟨“#0 ≤ #1”, by simp⟩, by intro; simp⟩

end DefinableRel

namespace DefinableFunction₂

instance add : DefinableFunction₂ T Γ s ((· + ·) : M → M → M) where
  definable := ⟨⟨“#0 = #1 + #2”, by simp⟩, by intro _; simp⟩

instance mul : DefinableFunction₂ T Γ s ((· * ·) : M → M → M) where
  definable := ⟨⟨“#0 = #1 * #2”, by simp⟩, by intro _; simp⟩

end DefinableFunction₂

/--/

variable (Γ s)

class PolyBounded (f : (Fin k → M) → M) : Prop where
  bounded : ∃ t : Semiterm ℒₒᵣ M k, ∀ v : Fin k → M, f v ≤ t.val! M v id

abbrev PolyBounded₁ (f : M → M) : Prop := PolyBounded (k := 1) (fun v => f (v 0))

abbrev PolyBounded₂ (f : M → M → M) : Prop := PolyBounded (k := 2) (fun v => f (v 0) (v 1))

abbrev PolyBounded₃ (f : M → M → M → M) : Prop := PolyBounded (k := 3) (fun v => f (v 0) (v 1) (v 2))

variable {Γ s}

namespace PolyBounded

@[simp] lemma var {k} (i : Fin k) : PolyBounded (fun v : Fin k → M ↦ v i) := ⟨#i, by intro _; simp⟩

@[simp] lemma const {k} (c : M) : PolyBounded (fun _ : Fin k → M ↦ c) := ⟨&c, by intro _; simp⟩

@[simp] lemma val_id' (t : Semiterm ℒₒᵣ M n) (e : Fin n → Fin k) :
    PolyBounded fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t :=
  ⟨Rew.substs (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs]⟩

@[simp] lemma val_id (t : Semiterm ℒₒᵣ M k) : PolyBounded fun v : Fin k → M => Semiterm.val! M v id t :=
  ⟨t, by intro _; simp⟩

lemma finmap {f : (Fin k → M) → M} (hf : PolyBounded f) (e : Fin k → Fin n) :
    PolyBounded fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.substs (fun x ↦ #(e x)) t, by intro; simp [Semiterm.val_substs, ht]⟩

lemma comp {k} {f : (Fin l → M) → M} {g : Fin l → (Fin k → M) → M} (hf : PolyBounded f) (hg : ∀ i, PolyBounded (g i)) :
    PolyBounded (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.substs tg tf, by
      intro v; simp [Semiterm.val_substs]
      exact le_trans (htf (g · v)) (Model.polynomial_mono tf (fun i ↦ htg i v) (by simp))⟩

end PolyBounded

lemma PolyBounded₁.comp {f : M → M} {k} {g : (Fin k → M) → M} (hf : PolyBounded₁ f) (hg : PolyBounded g) :
    PolyBounded (fun v ↦ f (g v)) := PolyBounded.comp hf (l := 1) (fun _ ↦ hg)

lemma PolyBounded₂.comp {f : M → M → M} {k} {g₁ g₂ : (Fin k → M) → M} (hf : PolyBounded₂ f) (hg₁ : PolyBounded g₁) (hg₂ : PolyBounded g₂) :
    PolyBounded (fun v ↦ f (g₁ v) (g₂ v)) := PolyBounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma PolyBounded₃.comp {f : M → M → M → M} {k} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : PolyBounded₃ f) (hg₁ : PolyBounded g₁) (hg₂ : PolyBounded g₂) (hg₃ : PolyBounded g₃) :
    PolyBounded (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := PolyBounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases' i using Fin.cases with i <;> simp [*]
        cases' i using Fin.cases with i <;> simp [*])

namespace PolyBounded₂

instance add : PolyBounded₂ ((· + ·) : M → M → M) where
  bounded := ⟨ᵀ“#0 + #1”, by intro _; simp⟩

instance mul : PolyBounded₂ ((· * ·) : M → M → M) where
  bounded := ⟨ᵀ“#0 * #1”, by intro _; simp⟩

instance hAdd : PolyBounded₂ (HAdd.hAdd : M → M → M) where
  bounded := ⟨ᵀ“#0 + #1”, by intro _; simp⟩

instance hMul : PolyBounded₂ (HMul.hMul : M → M → M) where
  bounded := ⟨ᵀ“#0 * #1”, by intro _; simp⟩

end PolyBounded₂

variable (Γ s)

def Semipolynomial {k} (f : (Fin k → M) → M) := PolyBounded f ∧ DefinableFunction Γ s f

abbrev Semipolynomial₁ (f : M → M) : Prop := Semipolynomial Γ s (k := 1) (fun v => f (v 0))

abbrev Semipolynomial₂ (f : M → M → M) : Prop := Semipolynomial Γ s (k := 2) (fun v => f (v 0) (v 1))

abbrev Semipolynomial₃ (f : M → M → M → M) : Prop := Semipolynomial Γ s (k := 3) (fun v => f (v 0) (v 1) (v 2))

variable {Γ s}

lemma Semipolynomial.bounded {f : (Fin k → M) → M} (h : Semipolynomial Γ s f) : PolyBounded f := h.1

lemma Semipolynomial₁.bounded {f : M → M} (h : Semipolynomial₁ Γ s f) : PolyBounded₁ f := h.1

lemma Semipolynomial₂.bounded {f : M → M → M} (h : Semipolynomial₂ Γ s f) : PolyBounded₂ f := h.1

lemma Semipolynomial₃.bounded {f : M → M → M → M} (h : Semipolynomial₃ Γ s f) : PolyBounded₃ f := h.1

lemma Semipolynomial.definable {f : (Fin k → M) → M} (h : Semipolynomial Γ s f) : DefinableFunction Γ s f := h.2

lemma Semipolynomial₁.definable {f : M → M} (h : Semipolynomial₁ Γ s f) : DefinableFunction₁ Γ s f := h.2

lemma Semipolynomial₂.definable {f : M → M → M} (h : Semipolynomial₂ Γ s f) : DefinableFunction₂ Γ s f := h.2

lemma Semipolynomial₃.definable {f : M → M → M → M} (h : Semipolynomial₃ Γ s f) : DefinableFunction₃ Γ s f := h.2

namespace Semipolynomial

lemma of_polybounded_of_definable (f : (Fin k → M) → M) [hb : PolyBounded f] [hf : DefinableFunction Γ s f] :
    Semipolynomial Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : M → M) [hb : PolyBounded₁ f] [hf : DefinableFunction₁ Γ s f] :
    Semipolynomial₁ Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : M → M → M) [hb : PolyBounded₂ f] [hf : DefinableFunction₂ Γ s f] :
    Semipolynomial₂ Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : M → M → M → M) [hb : PolyBounded₃ f] [hf : DefinableFunction₃ Γ s f] :
    Semipolynomial₃ Γ s f := ⟨hb, hf⟩

lemma finmap {f : (Fin k → M) → M} (hf : Semipolynomial Γ s f) (e : Fin k → Fin n) :
    Semipolynomial Γ s fun v ↦ f (fun i ↦ v (e i)) := ⟨hf.bounded.finmap e, hf.definable.finmap e⟩

end Semipolynomial

namespace Definable

lemma of_zero {P : (Fin k → M) → Prop} (h : Definable Γ 0 P) : Definable b' s P := by
  rcases h with ⟨⟨p, hp⟩⟩
  exact ⟨⟨p.of_zero, by simp [hp]⟩⟩

lemma const {P : Prop} : Definable Γ s (fun _ : Fin k → M ↦ P) := by
  by_cases hP : P
  · exact ⟨⟨⊤, by simp⟩, by intro; simp[hP]⟩
  · exact ⟨⟨⊥, by simp⟩, by intro; simp[hP]⟩

lemma and {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable Γ s P₁) (h₂ : Definable Γ s P₂) :
    Definable Γ s (fun v ↦ P₁ v ∧ P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⋏ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma or {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable Γ s P₁) (h₂ : Definable Γ s P₂) :
    Definable Γ s (fun v ↦ P₁ v ∨ P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⋎ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma not {P : (Fin k → M) → Prop} (h : Definable Γ.alt s P) :
    Definable Γ s (fun v ↦ ¬P v) := by
  rcases h with ⟨p, h⟩; exact ⟨⟨~p.val, by simp⟩, by intro x; simp [h.eval]⟩

lemma imp {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable Γ.alt s P₁) (h₂ : Definable Γ s P₂) :
    Definable Γ s (fun v ↦ P₁ v → P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⟶ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma iff {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable Γ s P₁) (h₁' : Definable Γ.alt s P₁) (h₂ : Definable Γ s P₂) (h₂' : Definable Γ.alt s P₂) :
    Definable Γ s (fun v ↦ P₁ v ↔ P₂ v) := by
  simp [iff_iff_implies_and_implies]
  apply and <;>  apply imp <;> simp [*]

lemma iff₀ {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable Γ 0 P₁) (h₂ : Definable Γ 0 P₂) :
    Definable Γ 0 (fun v ↦ P₁ v ↔ P₂ v) := iff h₁ h₁.of_zero h₂ h₂.of_zero

lemma ball_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial Γ s f) (h : Definable Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Γ s (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∀[#0 < #1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma bex_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial Γ s f) (h : Definable Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Γ s (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∃[#0 < #1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma ball_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial Γ s f) (h : Definable Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Γ s (fun v ↦ ∀ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∀[#0 < #1 + 1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma bex_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial Γ s f) (h : Definable Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Γ s (fun v ↦ ∃ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∃[#0 < #1 + 1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma all {P : (Fin k → M) → M → Prop} (h : Definable Π (s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Π (s + 1) (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨⟨∀' p, by simp⟩, by intro v; simp [hp.eval]⟩

lemma ex {P : (Fin k → M) → M → Prop} (h : Definable Σ (s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable Σ (s + 1) (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨⟨∃' p, by simp⟩, by intro v; simp [hp.eval]⟩

@[simp] lemma val_id' (t : Semiterm ℒₒᵣ M n) (e : Fin n → Fin k) :
    DefinableFunction Γ s fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t :=
  ⟨⟨“#0 = !!(Rew.substs (fun x ↦ #(e x).succ) t)”, by simp⟩, by intro v; simp [Semiterm.val_substs]⟩

@[simp] lemma val_id (t : Semiterm ℒₒᵣ M k) :
    DefinableFunction Γ s fun v : Fin k → M => Semiterm.val! M v id t :=
  ⟨⟨“#0 = !!(Rew.bShift t)”, by simp⟩, by intro v; simp [Semiterm.val_bShift']⟩

end Definable

namespace DefinableFunction

@[simp] lemma const {k} (c : M) : DefinableFunction Γ s (fun _ : Fin k → M ↦ c) :=
  ⟨⟨“#0 = &c”, by simp⟩, by intro v; simp⟩

@[simp] lemma var {k} (i : Fin k) : DefinableFunction Γ s (fun v : Fin k → M ↦ v i) :=
  ⟨⟨“#0 = !!#i.succ”, by simp⟩, by intro _; simp⟩

end DefinableFunction

namespace Semipolynomial

lemma of_iff {g : (Fin k → M) → M} (f) (h : ∀ v, f v = g v) (H : Semipolynomial Γ s f) : Semipolynomial Γ s g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

@[simp] lemma var {k} (i : Fin k) : Semipolynomial Γ s (fun v : Fin k → M ↦ v i) := ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : M) : Semipolynomial Γ s (fun _ : Fin k → M ↦ c) := ⟨by simp, by simp⟩

@[simp] lemma val_id' (t : Semiterm ℒₒᵣ M n) (e : Fin n → Fin k) :
    Semipolynomial Γ s fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t := ⟨by simp, by simp⟩

@[simp] lemma val_id (t : Semiterm ℒₒᵣ M k) : Semipolynomial Γ s fun v : Fin k → M => Semiterm.val! M v id t := ⟨by simp, by simp⟩

end Semipolynomial

namespace Definable

lemma comp₁ {k} {P : M → Prop} {f : (Fin k → M) → M} [hP : DefinablePred Γ s P] (hf : Semipolynomial Γ s f) :
    Definable Γ s (fun v ↦ P (f v)) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : Definable Γ s (fun v ↦ ∃ z ≤ Semiterm.val! M v id bf, z = f v ∧ P z) :=
    bex_le (by simp) (and hf.definable $ by rcases hP with ⟨p, hp⟩; exact ⟨⟨p /[#0], by simp⟩, by intro _; simp [hp.eval]⟩)
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f v, hbf v, rfl, h⟩
    · rintro ⟨_, _, rfl, h⟩; exact h)

lemma comp₂ {k} {R : M → M → Prop} {f₁ f₂ : (Fin k → M) → M}
    [hR : DefinableRel Γ s R] (hf₁ : Semipolynomial Γ s f₁) (hf₂ : Semipolynomial Γ s f₂) :
    Definable Γ s (fun v ↦ R (f₁ v) (f₂ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  have : Definable Γ s (fun v ↦
      ∃ z₁ ≤ Semiterm.val! M v id bf₁, ∃ z₂ ≤ Semiterm.val! M v id bf₂, z₁ = f₁ v ∧ z₂ = f₂ v ∧ R z₁ z₂) :=
    bex_le (Semipolynomial.val_id _) <| bex_le (Semipolynomial.val_id' _ _)
      <| and (hf₁.definable.rel.finmap _)
        <| and (by simpa using hf₂.definable.rel.finmap (0 :> (·.succ.succ)))
          <| by simpa using hR.finmap (n := k + 2) ![1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, rfl, rfl, h⟩; exact h)

lemma comp₃ {k} {R : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hR : DefinableRel₃ Γ s R] (hf₁ : Semipolynomial Γ s f₁) (hf₂ : Semipolynomial Γ s f₂) (hf₃ : Semipolynomial Γ s f₃) :
    Definable Γ s (fun v ↦ R (f₁ v) (f₂ v) (f₃ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  have : Definable Γ s (fun v ↦
      ∃ z₁ ≤ Semiterm.val! M v id bf₁, ∃ z₂ ≤ Semiterm.val! M v id bf₂, ∃ z₃ ≤ Semiterm.val! M v id bf₃,
        z₁ = f₁ v ∧ z₂ = f₂ v ∧ z₃ = f₃ v ∧ R z₁ z₂ z₃) :=
    bex_le (Semipolynomial.val_id _) <| bex_le (Semipolynomial.val_id' _ _)
      <| bex_le (Semipolynomial.val_id' _ _)
        <| and (by simpa using hf₁.definable.rel.finmap (n := k + 3) (2 :> (·.succ.succ.succ)))
          <| and (by simpa using hf₂.definable.rel.finmap (n := k + 3) (1 :> (·.succ.succ.succ)))
            <| and (by simpa using hf₃.definable.rel.finmap (n := k + 3) (0 :> (·.succ.succ.succ)))
              <| by simpa using hR.finmap (n := k + 3) ![2, 1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, f₃ v, hbf₃ v, rfl, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, _, _, rfl, rfl, rfl, h⟩; exact h)

lemma comp₄ {k} {R : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hR : DefinableRel₄ Γ s R] (hf₁ : Semipolynomial Γ s f₁) (hf₂ : Semipolynomial Γ s f₂) (hf₃ : Semipolynomial Γ s f₃) (hf₄ : Semipolynomial Γ s f₄) :
    Definable Γ s (fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  rcases hf₄.bounded with ⟨bf₄, hbf₄⟩
  have : Definable Γ s (fun v ↦
      ∃ z₁ ≤ Semiterm.val! M v id bf₁, ∃ z₂ ≤ Semiterm.val! M v id bf₂, ∃ z₃ ≤ Semiterm.val! M v id bf₃, ∃ z₄ ≤ Semiterm.val! M v id bf₄,
        z₁ = f₁ v ∧ z₂ = f₂ v ∧ z₃ = f₃ v ∧ z₄ = f₄ v ∧ R z₁ z₂ z₃ z₄) :=
    bex_le (Semipolynomial.val_id _) <| bex_le (Semipolynomial.val_id' _ _) <| bex_le (Semipolynomial.val_id' _ _) <| bex_le (Semipolynomial.val_id' _ _)
        <| and (by simpa using hf₁.definable.rel.finmap (n := k + 4) (3 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₂.definable.rel.finmap (n := k + 4) (2 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₃.definable.rel.finmap (n := k + 4) (1 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₄.definable.rel.finmap (n := k + 4) (0 :> (·.succ.succ.succ.succ)))
        <| by simpa using hR.finmap (n := k + 4) ![3, 2, 1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, f₃ v, hbf₃ v, f₄ v, hbf₄ v, rfl, rfl, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, h⟩; exact h)

end Definable

lemma DefinableFunction₁.comp {k} {f : M → M} {g : (Fin k → M) → M}
    (hf : DefinableFunction₁ Γ s f) (hg : Semipolynomial Γ s g) :
    DefinableFunction Γ s (fun v ↦ f (g v)) := by
  have := Definable.comp₂ (k := k + 1) (R := Function.Graph f) (Semipolynomial.var 0) (hg.finmap Fin.succ)
  simpa using this

lemma DefinableFunction₂.comp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : DefinableFunction₂ Γ s f) (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) :
    DefinableFunction Γ s (fun v ↦ f (g₁ v) (g₂ v)) := by
  have := Definable.comp₃ (k := k + 1) (R := Function.Graph₂ f) (Semipolynomial.var 0) (hg₁.finmap Fin.succ) (hg₂.finmap Fin.succ)
  simpa using this

lemma DefinableFunction₃.comp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : DefinableFunction₃ Γ s f) (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) (hg₃ : Semipolynomial Γ s g₃)  :
    DefinableFunction Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := by
  have := Definable.comp₄ (k := k + 1) (R := Function.Graph₃ f) (Semipolynomial.var 0) (hg₁.finmap Fin.succ) (hg₂.finmap Fin.succ) (hg₃.finmap Fin.succ)
  simpa using this

lemma Semipolynomial₁.comp {k} {f : M → M} {g : (Fin k → M) → M} (hf : Semipolynomial₁ Γ s f) (hg : Semipolynomial Γ s g) :
    Semipolynomial Γ s (fun v ↦ f (g v)) := ⟨hf.bounded.comp hg.bounded, hf.definable.comp hg⟩

lemma Semipolynomial₂.comp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : Semipolynomial₂ Γ s f) (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) :
    Semipolynomial Γ s (fun v ↦ f (g₁ v) (g₂ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded, hf.definable.comp hg₁ hg₂⟩

lemma Semipolynomial₃.comp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : Semipolynomial₃ Γ s f) (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) (hg₃ : Semipolynomial Γ s g₃) :
    Semipolynomial Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded hg₃.bounded, hf.definable.comp hg₁ hg₂ hg₃⟩

lemma Semipolynomial.comp₁ {k} {f : M → M} {g : (Fin k → M) → M}
    [hfb : PolyBounded₁ f] [hfd : DefinableFunction₁ Γ s f] (hg : Semipolynomial Γ s g) :
    Semipolynomial Γ s (fun v ↦ f (g v)) := Semipolynomial₁.comp ⟨hfb, hfd⟩ hg

lemma Semipolynomial.comp₂ {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    [hfb : PolyBounded₂ f] [hfd : DefinableFunction₂ Γ s f] (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) :
    Semipolynomial Γ s (fun v ↦ f (g₁ v) (g₂ v)) := Semipolynomial₂.comp ⟨hfb, hfd⟩ hg₁ hg₂

lemma Semipolynomial.comp₃ {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    [hfb : PolyBounded₃ f] [hfd : DefinableFunction₃ Γ s f] (hg₁ : Semipolynomial Γ s g₁) (hg₂ : Semipolynomial Γ s g₂) (hg₃ : Semipolynomial Γ s g₃) :
    Semipolynomial Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Semipolynomial₃.comp ⟨hfb, hfd⟩ hg₁ hg₂ hg₃

section

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

open Definable

attribute [aesop (rule_sets [Definability]) norm]
  sq
  pow_three
  pow_four
  Definable.const

attribute [aesop 1 (rule_sets [Definability]) safe]
  Semipolynomial.comp₁
  Semipolynomial.comp₂
  Semipolynomial.comp₃
  Definable.comp₁
  Definable.comp₂
  Definable.comp₃
  Definable.comp₄
  Definable.const

attribute [aesop 4 (rule_sets [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.iff₀
  Definable.ball_lt
  Definable.ball_le
  Definable.bex_lt
  Definable.bex_le

attribute [aesop 8 (rule_sets [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.ex

macro "definability" : attr =>
  `(attr|aesop 4 (rule_sets [$(Lean.mkIdent `Definability):ident]) safe)

macro "definability" (config)? : tactic =>
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `Definability):ident]))

macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `Definability):ident]))

example (c : M) : Semipolynomial₂ Σ 0 (fun x y : M ↦ c + 2 * x^2) := by definability

example {ex : M → M} [h : ∀ Γ s, DefinableFunction₁ Γ s ex] (c : M) :
  DefinableRel Σ 0 (fun x y : M ↦ ∃ z < x + c * y, ex x = z ∧ ex (x + 1) = 2 * z) := by
    simp [Function.Graph.iff_left ex]
    definability

end

end Model

end definability

end Arith


end LO.FirstOrder
