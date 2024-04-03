import Arithmetization.Vorspiel.Lemmata
import Arithmetization.Definability.Init
import Arithmetization.Vorspiel.Graph
import Logic.FirstOrder.Arith.StrictHierarchy
import Aesop

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

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]
variable {L : Language} [L.ORing] [Structure L M] [Structure.ORing L M] [Structure.Monotone L M]

namespace Definability

abbrev HSemiformula (Γ : Polarity) (s : ℕ) (L : Language) [L.LT] (μ : Type*) (n) :=
  { p : Semiformula L μ n // Hierarchy Γ s p }

structure DeltaSemiformula (L : Language) [L.LT] (T : Theory L) (ν : ℕ) (ξ : Type*) [DecidableEq ξ] (n) :=
  sigma : HSemiformula Σ ν L ξ n
  pi : HSemiformula Π ν L ξ n
  equiv : T ⊨ ∀ᶠ* ∀* (sigma.val ⟷ pi.val)

abbrev HSemisentence (Γ : Polarity) (s : ℕ) (L : Language) [L.LT] (n) := HSemiformula Γ s L Empty n

variable (L)

def HSemiformula.extd (p : HSemiformula Γ m ℒₒᵣ ξ n) : HSemiformula Γ m L ξ n :=
  ⟨Semiformula.lMap Language.oringEmb p, Hierarchy.oringEmb p.prop⟩

variable {L}

@[simp] lemma HSemiformula.pval_extd_iff {p : HSemisentence Γ m ℒₒᵣ n} :
    Semiformula.PVal! M e (p.extd L).val ↔ Semiformula.PVal! M e p.val := by
  simp [HSemiformula.extd]

lemma HSemiformula.extd_val (p : HSemiformula Γ m ℒₒᵣ ξ n) :
    (p.extd L).val = Semiformula.lMap Language.oringEmb p := rfl

scoped[LO.FirstOrder.Arith] notation "Δ₀-Sentence " n => Definability.HSemisentence Σ 0 ℒₒᵣ n

scoped[LO.FirstOrder.Arith] notation "Δ₀(exp)-Sentence " n => Definability.HSemisentence Σ 0 ℒₒᵣ(exp) n

namespace HSemiformula

abbrev of_zero (p : HSemiformula Γ 0 L μ k) : HSemiformula b' s L μ k := ⟨p, p.prop.of_zero⟩

variable (Γ : Polarity) (s : ℕ) (L : Language) [L.LT] (μ : Type*) (n)

@[simp] lemma hierarchy (p : HSemiformula Γ s L μ n) : Hierarchy Γ s p.val := p.prop

@[simp] lemma hierarchy_zero {Γ b' s} (p : HSemiformula Γ 0 L μ n) : Hierarchy b' s p.val :=
  Hierarchy.of_zero p.hierarchy

end HSemiformula

namespace HSemisentence

def eq : HSemisentence Γ s L 2 := ⟨“#0 = #1”, by simp⟩

def lt : HSemisentence Γ s L 2 := ⟨“#0 < #1”, by simp⟩

def le : HSemisentence Γ s L 2 := ⟨“#0 ≤ #1”, by simp⟩

end HSemisentence

end Definability

namespace Model

open Definability

variable (L) (Γ : Polarity) (s : ℕ)

abbrev DefinedPred (P : M → Prop) (p : HSemisentence Γ s L 1) : Prop :=
  Defined (λ v ↦ P (v 0)) p.val

abbrev DefinedRel (R : M → M → Prop) (p : HSemisentence Γ s L 2) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1)) p.val

abbrev DefinedRel₃ (R : M → M → M → Prop) (p : HSemisentence Γ s L 3) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2)) p.val

abbrev DefinedRel₄ (R : M → M → M → M → Prop) (p : HSemisentence Γ s L 4) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) p.val

abbrev DefinedFunction {k} (f : (Fin k → M) → M) (p : HSemisentence Γ s L (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) p.val

abbrev DefinedFunction₁ (f : M → M) (p : HSemisentence Γ s L 2) : Prop :=
  DefinedFunction L Γ s (fun v => f (v 0)) p

abbrev DefinedFunction₂ (f : M → M → M) (p : HSemisentence Γ s L 3) : Prop :=
  DefinedFunction L Γ s (fun v => f (v 0) (v 1)) p

abbrev DefinedFunction₃ (f : M → M → M → M) (p : HSemisentence Γ s L 4) : Prop :=
  DefinedFunction L Γ s (fun v => f (v 0) (v 1) (v 2)) p

notation Γ "(" s ")-Predicate " P " via " p => DefinedPred ℒₒᵣ Γ s P p

notation "Δ₀-Predicate " P " via " p => DefinedPred ℒₒᵣ Σ 0 P p

notation Γ "(" s ")-Relation " P " via " p => DefinedRel ℒₒᵣ Γ s P p

notation "Δ₀-Relation " P " via " p => DefinedRel ℒₒᵣ Σ 0 P p

notation Γ "(" s ")-Relation₃ " P " via " p => DefinedRel₃ ℒₒᵣ Γ s P p

notation "Δ₀-Relation₃ " P " via " p => DefinedRel₃ ℒₒᵣ Σ 0 P p

notation Γ "(" s ")-Relation₄ " P " via " p => DefinedRel₄ ℒₒᵣ Γ s P p

notation "Δ₀-Relation₄ " P " via " p => DefinedRel₄ ℒₒᵣ Σ 0 P p

notation Γ "(" s ")-Function₁ " f " via " p => DefinedFunction₁ ℒₒᵣ Γ s f p

notation "Δ₀-Function₁ " f " via " p => DefinedFunction₁ ℒₒᵣ Σ 0 f p

notation Γ "(" s ")-Function₂ " f " via " p => DefinedFunction₂ ℒₒᵣ Γ s f p

notation "Δ₀-Function₂ " f " via " p => DefinedFunction₂ ℒₒᵣ Σ 0 f p

notation Γ "(" s ")-Function₃ " f " via " p => DefinedFunction₃ ℒₒᵣ Γ s f p

notation "Δ₀-Function₃ " f " via " p => DefinedFunction₃ ℒₒᵣ Σ 0 f p

def DefinedRel.eq : Γ(s)-Relation ((· = ·) : M → M → Prop) via HSemisentence.eq := by intro v; simp [HSemisentence.eq]

def DefinedRel.lt : Γ(s)-Relation ((· < ·) : M → M → Prop) via HSemisentence.lt := by intro v; simp [HSemisentence.lt]

def DefinedRel.le : Γ(s)-Relation ((· ≤ ·) : M → M → Prop) via HSemisentence.le := by intro v; simp [HSemisentence.le]

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ p : HSemiformula Γ s L M k, DefinedWithParam P p.val

instance Definable.of_sigma_zero {k} (P : (Fin k → M) → Prop) [h : Definable L Σ 0 P] (Γ ν) : Definable L Γ ν P :=
  ⟨by rcases h with ⟨p, hp⟩; exact ⟨⟨p, Hierarchy.of_zero p.prop⟩, hp⟩⟩

abbrev DefinablePred (P : M → Prop) : Prop := Definable L Γ s (k := 1) (fun v ↦ P (v 0))

abbrev DefinableRel (P : M → M → Prop) : Prop := Definable L Γ s (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := Definable L Γ s (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop := Definable L Γ s (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev DefinableFunction (f : (Fin k → M) → M) : Prop := Definable L Γ s (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev DefinableFunction₁ (f : M → M) : Prop := DefinableFunction L Γ s (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : M → M → M) : Prop := DefinableFunction L Γ s (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := DefinableFunction L Γ s (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

notation Γ "(" s ")-Predicate " P => DefinablePred ℒₒᵣ Γ s P

notation Γ "(" s ")-Relation " P => DefinableRel ℒₒᵣ Γ s P

notation Γ "(" s ")-Relation₃ " P => DefinableRel₃ ℒₒᵣ Γ s P

notation Γ "(" s ")-Relation₄ " P => DefinableRel₄ ℒₒᵣ Γ s P

notation Γ "(" s ")-Function₁ " f => DefinableFunction₁ ℒₒᵣ Γ s f

notation Γ "(" s ")-Function₂ " f => DefinableFunction₂ ℒₒᵣ Γ s f

notation Γ "(" s ")-Function₃ " f => DefinableFunction₃ ℒₒᵣ Γ s f

variable {L Γ s}

lemma defined_to_with_param {k} {P : (Fin k → M) → Prop} (p : HSemisentence Γ s L k) (hP : Defined P p.val) :
    Definable L Γ s P := ⟨⟨Rew.emb.hom p.val, by simp⟩, by intro; simp [hP.pval]⟩

lemma defined_to_with_param₀ {k} {P : (Fin k → M) → Prop} (p : HSemisentence b' 0 L k) (hP : Defined P p.val) :
    Definable L Γ s P := ⟨⟨Rew.emb.hom p.val, by simp⟩, by intro; simp [hP.pval]⟩

instance {k} (P : (Fin k → M) → Prop) [d : Definable ℒₒᵣ Γ s P] : Definable L Γ s P := by
  rcases d with ⟨p, hp⟩
  exact ⟨⟨Semiformula.lMap Language.oringEmb p.val, Hierarchy.oringEmb p.prop⟩, by simp; intro v; simpa using hp v⟩

lemma defined_to_with_param_oRing₀ {k} {P : (Fin k → M) → Prop} (p : HSemisentence Γ' 0 ℒₒᵣ k) (hP : Defined P p.val) :
    Definable L Γ s P :=
  ⟨⟨Rew.emb.hom (Semiformula.lMap Language.oringEmb p.val),
      by simp; apply Hierarchy.oringEmb (Hierarchy.of_zero p.prop)⟩,
      by intro; simp [hP.pval]⟩

namespace Definable

lemma of_iff {p : (Fin k → M) → Prop} (q) (h : ∀ x, p x ↔ q x) (H : Definable L Γ s q) : Definable L Γ s p := by
  rwa [show p = q from by funext v; simp [h]]

lemma finmap {P : (Fin k → M) → Prop} (h : Definable L Γ s P) (f : Fin k → Fin n) :
    Definable L Γ s fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨p, h⟩
  exact ⟨⟨(Rew.substs (fun i ↦ #(f i))).hom p, by simp⟩, by intro v; simp [h.eval]⟩

end Definable

namespace DefinableFunction

lemma of_eq {f : (Fin k → M) → M} (g) (h : ∀ v, f v = g v) (H : DefinableFunction L Γ s f) : DefinableFunction L Γ s g := by
  rwa [show g = f from by funext v; simp [h]]

lemma finmap {f : (Fin k → M) → M} (hf : DefinableFunction L Γ s f) (e : Fin k → Fin n) :
    DefinableFunction L Γ s fun v ↦ f (fun i ↦ v (e i)) := by
  have := Definable.finmap (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff _ (by intro x; simp)

lemma rel {f : (Fin k → M) → M} (h : DefinableFunction L Γ s f) :
  Definable L Γ s (fun v ↦ v 0 = f (v ·.succ)) := h

end DefinableFunction

instance DefinableFunction₁.graph {f : M → M} [h : DefinableFunction₁ L Γ s f] :
  DefinableRel L Γ s (Function.Graph f) := h

instance DefinableFunction₂.graph {f : M → M → M} [h : DefinableFunction₂ L Γ s f] :
  DefinableRel₃ L Γ s (Function.Graph₂ f) := h

instance DefinableFunction₃.graph {f : M → M → M → M} [h : DefinableFunction₃ L Γ s f] :
  DefinableRel₄ L Γ s (Function.Graph₃ f) := h

namespace DefinableRel

instance eq : DefinableRel L Γ s ((· = ·) : M → M → Prop) := ⟨⟨“#0 = #1”, by simp⟩, by intro; simp⟩

instance lt : DefinableRel L Γ s ((· < ·) : M → M → Prop) := ⟨⟨“#0 < #1”, by simp⟩, by intro; simp⟩

instance le : DefinableRel L Γ s ((· ≤ ·) : M → M → Prop) := ⟨⟨“#0 ≤ #1”, by simp⟩, by intro; simp⟩

end DefinableRel

namespace DefinableFunction₂

instance add : DefinableFunction₂ L Γ s ((· + ·) : M → M → M) where
  definable := ⟨⟨“#0 = #1 + #2”, by simp⟩, by intro _; simp⟩

instance mul : DefinableFunction₂ L Γ s ((· * ·) : M → M → M) where
  definable := ⟨⟨“#0 = #1 * #2”, by simp⟩, by intro _; simp⟩

end DefinableFunction₂

variable (L Γ s)

class Bounded (f : (Fin k → M) → M) : Prop where
  bounded : ∃ t : Semiterm L M k, ∀ v : Fin k → M, f v ≤ t.val! M v id

abbrev Bounded₁ (f : M → M) : Prop := Bounded L (k := 1) (fun v => f (v 0))

abbrev Bounded₂ (f : M → M → M) : Prop := Bounded L (k := 2) (fun v => f (v 0) (v 1))

abbrev Bounded₃ (f : M → M → M → M) : Prop := Bounded L (k := 3) (fun v => f (v 0) (v 1) (v 2))

instance (f : (Fin k → M) → M) [h : Bounded ℒₒᵣ f] : Bounded L f := by
  rcases h with ⟨t, ht⟩
  exact ⟨Semiterm.lMap Language.oringEmb t, by simpa⟩

variable {L Γ s}

namespace Bounded

@[simp] lemma var {k} (i : Fin k) : Bounded L fun v : Fin k → M ↦ v i := ⟨#i, by intro _; simp⟩

@[simp] lemma const {k} (c : M) : Bounded L (fun _ : Fin k → M ↦ c) := ⟨&c, by intro _; simp⟩

@[simp] lemma val_id' (t : Semiterm L M n) (e : Fin n → Fin k) :
    Bounded L fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t :=
  ⟨Rew.substs (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs]⟩

@[simp] lemma val_id (t : Semiterm L M k) : Bounded L fun v : Fin k → M => Semiterm.val! M v id t :=
  ⟨t, by intro _; simp⟩

lemma finmap {f : (Fin k → M) → M} (hf : Bounded L f) (e : Fin k → Fin n) :
    Bounded L fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.substs (fun x ↦ #(e x)) t, by intro; simp [Semiterm.val_substs, ht]⟩

lemma comp {k} {f : (Fin l → M) → M} {g : Fin l → (Fin k → M) → M} (hf : Bounded L f) (hg : ∀ i, Bounded L (g i)) :
    Bounded L (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.substs tg tf, by
      intro v; simp [Semiterm.val_substs]
      exact le_trans (htf (g · v)) (Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by simp))⟩

end Bounded

lemma Bounded₁.comp {f : M → M} {k} {g : (Fin k → M) → M} (hf : Bounded₁ L f) (hg : Bounded L g) :
    Bounded L (fun v ↦ f (g v)) := Bounded.comp hf (l := 1) (fun _ ↦ hg)

lemma Bounded₂.comp {f : M → M → M} {k} {g₁ g₂ : (Fin k → M) → M}
    (hf : Bounded₂ L f) (hg₁ : Bounded L g₁) (hg₂ : Bounded L g₂) :
    Bounded L (fun v ↦ f (g₁ v) (g₂ v)) := Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma Bounded₃.comp {f : M → M → M → M} {k} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : Bounded₃ L f) (hg₁ : Bounded L g₁) (hg₂ : Bounded L g₂) (hg₃ : Bounded L g₃) :
    Bounded L (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Bounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases' i using Fin.cases with i <;> simp [*]
        cases' i using Fin.cases with i <;> simp [*])

namespace Bounded₂

instance add : Bounded₂ L ((· + ·) : M → M → M) where
  bounded := ⟨ᵀ“#0 + #1”, by intro _; simp⟩

instance mul : Bounded₂ L ((· * ·) : M → M → M) where
  bounded := ⟨ᵀ“#0 * #1”, by intro _; simp⟩

instance hAdd : Bounded₂ L (HAdd.hAdd : M → M → M) where
  bounded := ⟨ᵀ“#0 + #1”, by intro _; simp⟩

instance hMul : Bounded₂ L (HMul.hMul : M → M → M) where
  bounded := ⟨ᵀ“#0 * #1”, by intro _; simp⟩

end Bounded₂

variable (L Γ s)

def Semipolynomial {k} (f : (Fin k → M) → M) := Bounded L f ∧ DefinableFunction L Γ s f

abbrev Semipolynomial₁ (f : M → M) : Prop := Semipolynomial L Γ s (k := 1) (fun v => f (v 0))

abbrev Semipolynomial₂ (f : M → M → M) : Prop := Semipolynomial L Γ s (k := 2) (fun v => f (v 0) (v 1))

abbrev Semipolynomial₃ (f : M → M → M → M) : Prop := Semipolynomial L Γ s (k := 3) (fun v => f (v 0) (v 1) (v 2))

variable {L Γ s}

lemma Semipolynomial.bounded {f : (Fin k → M) → M} (h : Semipolynomial L Γ s f) : Bounded L f := h.1

lemma Semipolynomial₁.bounded {f : M → M} (h : Semipolynomial₁ L Γ s f) : Bounded₁ L f := h.1

lemma Semipolynomial₂.bounded {f : M → M → M} (h : Semipolynomial₂ L Γ s f) : Bounded₂ L f := h.1

lemma Semipolynomial₃.bounded {f : M → M → M → M} (h : Semipolynomial₃ L Γ s f) : Bounded₃ L f := h.1

lemma Semipolynomial.definable {f : (Fin k → M) → M} (h : Semipolynomial L Γ s f) : DefinableFunction L Γ s f := h.2

lemma Semipolynomial₁.definable {f : M → M} (h : Semipolynomial₁ L Γ s f) : DefinableFunction₁ L Γ s f := h.2

lemma Semipolynomial₂.definable {f : M → M → M} (h : Semipolynomial₂ L Γ s f) : DefinableFunction₂ L Γ s f := h.2

lemma Semipolynomial₃.definable {f : M → M → M → M} (h : Semipolynomial₃ L Γ s f) : DefinableFunction₃ L Γ s f := h.2

namespace Semipolynomial

lemma of_polybounded_of_definable (f : (Fin k → M) → M) [hb : Bounded L f] [hf : DefinableFunction L Γ s f] :
    Semipolynomial L Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : M → M) [hb : Bounded₁ L f] [hf : DefinableFunction₁ L Γ s f] :
    Semipolynomial₁ L Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : M → M → M) [hb : Bounded₂ L f] [hf : DefinableFunction₂ L Γ s f] :
    Semipolynomial₂ L Γ s f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : M → M → M → M) [hb : Bounded₃ L f] [hf : DefinableFunction₃ L Γ s f] :
    Semipolynomial₃ L Γ s f := ⟨hb, hf⟩

lemma finmap {f : (Fin k → M) → M} (hf : Semipolynomial L Γ s f) (e : Fin k → Fin n) :
    Semipolynomial L Γ s fun v ↦ f (fun i ↦ v (e i)) := ⟨hf.bounded.finmap e, hf.definable.finmap e⟩

end Semipolynomial

namespace Definable

lemma of_zero {P : (Fin k → M) → Prop} (h : Definable L Γ 0 P) : Definable L b' s P := by
  rcases h with ⟨⟨p, hp⟩⟩
  exact ⟨⟨p.of_zero, by simp [hp]⟩⟩

lemma const {P : Prop} : Definable L Γ s (fun _ : Fin k → M ↦ P) := by
  by_cases hP : P
  · exact ⟨⟨⊤, by simp⟩, by intro; simp[hP]⟩
  · exact ⟨⟨⊥, by simp⟩, by intro; simp[hP]⟩

lemma and {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ s P₁) (h₂ : Definable L Γ s P₂) :
    Definable L Γ s (fun v ↦ P₁ v ∧ P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⋏ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma or {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ s P₁) (h₂ : Definable L Γ s P₂) :
    Definable L Γ s (fun v ↦ P₁ v ∨ P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⋎ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma not {P : (Fin k → M) → Prop} (h : Definable L Γ.alt s P) :
    Definable L Γ s (fun v ↦ ¬P v) := by
  rcases h with ⟨p, h⟩; exact ⟨⟨~p.val, by simp⟩, by intro x; simp [h.eval]⟩

lemma imp {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ.alt s P₁) (h₂ : Definable L Γ s P₂) :
    Definable L Γ s (fun v ↦ P₁ v → P₂ v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨⟨p₁ ⟶ p₂, by simp⟩, by intro x; simp [h₁, h₂, h₁.eval, h₂.eval]⟩

lemma imp₁ {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ.alt (s + 1) P₁) (h₂ : Definable L Γ (s + 1) P₂) :
    Definable L Γ (s + 1) (fun v ↦ P₁ v → P₂ v) := imp h₁ h₂

lemma iff {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ s P₁) (h₁' : Definable L Γ.alt s P₁) (h₂ : Definable L Γ s P₂) (h₂' : Definable L Γ.alt s P₂) :
    Definable L Γ s (fun v ↦ P₁ v ↔ P₂ v) := by
  simp [iff_iff_implies_and_implies]
  apply and <;>  apply imp <;> simp [*]

lemma iff₀ {P₁ P₂ : (Fin k → M) → Prop} (h₁ : Definable L Γ 0 P₁) (h₂ : Definable L Γ 0 P₂) :
    Definable L Γ 0 (fun v ↦ P₁ v ↔ P₂ v) := iff h₁ h₁.of_zero h₂ h₂.of_zero

lemma ball_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial L Γ s f) (h : Definable L Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ s (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∀[#0 < #1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma bex_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial L Γ s f) (h : Definable L Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ s (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∃[#0 < #1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma ball_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial L Γ s f) (h : Definable L Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ s (fun v ↦ ∀ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∀[#0 < #1 + 1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma bex_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial L Γ s f) (h : Definable L Γ s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ s (fun v ↦ ∃ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∃[#0 < #1 + 1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, ←le_iff_lt_succ]
        constructor
        · intro h; exact ⟨f v, hbf v, rfl, h⟩
        · rintro ⟨_, _, rfl, h⟩; exact h⟩

lemma all {P : (Fin k → M) → M → Prop} (h : Definable L Π (s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Π (s + 1) (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨⟨∀' p, by simp⟩, by intro v; simp [hp.eval]⟩

lemma ex {P : (Fin k → M) → M → Prop} (h : Definable L Σ (s + 1) (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Σ (s + 1) (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨⟨∃' p, by simp⟩, by intro v; simp [hp.eval]⟩

@[simp] lemma val_id' (t : Semiterm L M n) (e : Fin n → Fin k) :
    DefinableFunction L Γ s fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t :=
  ⟨⟨“#0 = !!(Rew.substs (fun x ↦ #(e x).succ) t)”, by simp⟩, by intro v; simp [Semiterm.val_substs]⟩

@[simp] lemma val_id (t : Semiterm L M k) :
    DefinableFunction L Γ s fun v : Fin k → M => Semiterm.val! M v id t :=
  ⟨⟨“#0 = !!(Rew.bShift t)”, by simp⟩, by intro v; simp [Semiterm.val_bShift']⟩

end Definable

namespace DefinableFunction

@[simp] lemma const {k} (c : M) : DefinableFunction L Γ s (fun _ : Fin k → M ↦ c) :=
  ⟨⟨“#0 = &c”, by simp⟩, by intro v; simp⟩

@[simp] lemma var {k} (i : Fin k) : DefinableFunction L Γ s (fun v : Fin k → M ↦ v i) :=
  ⟨⟨“#0 = !!#i.succ”, by simp⟩, by intro _; simp⟩

end DefinableFunction

namespace Semipolynomial

lemma of_iff {g : (Fin k → M) → M} (f) (h : ∀ v, f v = g v) (H : Semipolynomial L Γ s f) : Semipolynomial L Γ s g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

@[simp] lemma var {k} (i : Fin k) : Semipolynomial L Γ s (fun v : Fin k → M ↦ v i) := ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : M) : Semipolynomial L Γ s (fun _ : Fin k → M ↦ c) := ⟨by simp, by simp⟩

@[simp] lemma val_id' (t : Semiterm L M n) (e : Fin n → Fin k) :
    Semipolynomial L Γ s fun v : Fin k → M => Semiterm.val! M (fun x ↦ v (e x)) id t := ⟨by simp, by simp⟩

@[simp] lemma val_id (t : Semiterm L M k) : Semipolynomial L Γ s fun v : Fin k → M => Semiterm.val! M v id t := ⟨by simp, by simp⟩

end Semipolynomial

namespace Definable

lemma comp₁ {k} {P : M → Prop} {f : (Fin k → M) → M} [hP : DefinablePred L Γ s P] (hf : Semipolynomial L Γ s f) :
    Definable L Γ s (fun v ↦ P (f v)) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : Definable L Γ s (fun v ↦ ∃ z ≤ Semiterm.val! M v id bf, z = f v ∧ P z) :=
    bex_le (by simp) (and hf.definable $ by rcases hP with ⟨p, hp⟩; exact ⟨⟨p /[#0], by simp⟩, by intro _; simp [hp.eval]⟩)
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f v, hbf v, rfl, h⟩
    · rintro ⟨_, _, rfl, h⟩; exact h)

lemma comp₂ {k} {R : M → M → Prop} {f₁ f₂ : (Fin k → M) → M}
    [hR : DefinableRel L Γ s R] (hf₁ : Semipolynomial L Γ s f₁) (hf₂ : Semipolynomial L Γ s f₂) :
    Definable L Γ s (fun v ↦ R (f₁ v) (f₂ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  have : Definable L Γ s (fun v ↦
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
    [hR : DefinableRel₃ L Γ s R] (hf₁ : Semipolynomial L Γ s f₁) (hf₂ : Semipolynomial L Γ s f₂) (hf₃ : Semipolynomial L Γ s f₃) :
    Definable L Γ s (fun v ↦ R (f₁ v) (f₂ v) (f₃ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  have : Definable L Γ s (fun v ↦
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
    [hR : DefinableRel₄ L Γ s R] (hf₁ : Semipolynomial L Γ s f₁) (hf₂ : Semipolynomial L Γ s f₂) (hf₃ : Semipolynomial L Γ s f₃) (hf₄ : Semipolynomial L Γ s f₄) :
    Definable L Γ s (fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  rcases hf₄.bounded with ⟨bf₄, hbf₄⟩
  have : Definable L Γ s (fun v ↦
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
    (hf : DefinableFunction₁ L Γ s f) (hg : Semipolynomial L Γ s g) :
    DefinableFunction L Γ s (fun v ↦ f (g v)) := by
  have := Definable.comp₂ (k := k + 1) (R := Function.Graph f) (Semipolynomial.var 0) (hg.finmap Fin.succ)
  simpa using this

lemma DefinableFunction₂.comp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : DefinableFunction₂ L Γ s f) (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) :
    DefinableFunction L Γ s (fun v ↦ f (g₁ v) (g₂ v)) := by
  have := Definable.comp₃ (k := k + 1) (R := Function.Graph₂ f) (Semipolynomial.var 0) (hg₁.finmap Fin.succ) (hg₂.finmap Fin.succ)
  simpa using this

lemma DefinableFunction₃.comp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : DefinableFunction₃ L Γ s f) (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) (hg₃ : Semipolynomial L Γ s g₃)  :
    DefinableFunction L Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := by
  have := Definable.comp₄ (k := k + 1) (R := Function.Graph₃ f) (Semipolynomial.var 0) (hg₁.finmap Fin.succ) (hg₂.finmap Fin.succ) (hg₃.finmap Fin.succ)
  simpa using this

lemma Semipolynomial₁.comp {k} {f : M → M} {g : (Fin k → M) → M} (hf : Semipolynomial₁ L Γ s f) (hg : Semipolynomial L Γ s g) :
    Semipolynomial L Γ s (fun v ↦ f (g v)) := ⟨hf.bounded.comp hg.bounded, hf.definable.comp hg⟩

lemma Semipolynomial₂.comp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : Semipolynomial₂ L Γ s f) (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) :
    Semipolynomial L Γ s (fun v ↦ f (g₁ v) (g₂ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded, hf.definable.comp hg₁ hg₂⟩

lemma Semipolynomial₃.comp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : Semipolynomial₃ L Γ s f) (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) (hg₃ : Semipolynomial L Γ s g₃) :
    Semipolynomial L Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded hg₃.bounded, hf.definable.comp hg₁ hg₂ hg₃⟩

lemma Semipolynomial.comp₁ {k} {f : M → M} {g : (Fin k → M) → M}
    [hfb : Bounded₁ L f] [hfd : DefinableFunction₁ L Γ s f] (hg : Semipolynomial L Γ s g) :
    Semipolynomial L Γ s (fun v ↦ f (g v)) := Semipolynomial₁.comp ⟨hfb, hfd⟩ hg

lemma Semipolynomial.comp₂ {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    [hfb : Bounded₂ L f] [hfd : DefinableFunction₂ L Γ s f] (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) :
    Semipolynomial L Γ s (fun v ↦ f (g₁ v) (g₂ v)) := Semipolynomial₂.comp ⟨hfb, hfd⟩ hg₁ hg₂

lemma Semipolynomial.comp₃ {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    [hfb : Bounded₃ L f] [hfd : DefinableFunction₃ L Γ s f] (hg₁ : Semipolynomial L Γ s g₁) (hg₂ : Semipolynomial L Γ s g₂) (hg₃ : Semipolynomial L Γ s g₃) :
    Semipolynomial L Γ s (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Semipolynomial₃.comp ⟨hfb, hfd⟩ hg₁ hg₂ hg₃

section

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

open Definable

attribute [aesop (rule_sets := [Definability]) norm]
  sq
  pow_three
  pow_four
  Definable.const

attribute [aesop 1 (rule_sets := [Definability]) safe]
  Semipolynomial.comp₁
  Semipolynomial.comp₂
  Semipolynomial.comp₃
  Definable.comp₁
  Definable.comp₂
  Definable.comp₃
  Definable.comp₄
  Definable.const

attribute [aesop 4 (rule_sets := [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.iff₀
  Definable.ball_lt
  Definable.ball_le
  Definable.bex_lt
  Definable.bex_le

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.ex

macro "definability" : attr =>
  `(attr|aesop 4 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)

macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

example (c : M) : Semipolynomial₂ L Σ 0 (fun x y : M ↦ c + 2 * x^2) := by definability

example {ex : M → M} [h : ∀ Γ s, DefinableFunction₁ L Γ s ex] (c : M) :
  DefinableRel L Σ 0 (fun x y : M ↦ ∃ z < x + c * y, ex x = z ∧ ex (x + 1) = 2 * z) := by
    simp [Function.Graph.iff_left ex]
    definability

end

end Model

end definability

end Arith


end LO.FirstOrder
