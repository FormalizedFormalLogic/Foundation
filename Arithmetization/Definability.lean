import Logic.FirstOrder.Arith.PAminus
import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

def Defined {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.PVal! M v p

namespace Defined

variable [Structure L M]

lemma pval {k} {R : (Fin k → M) → Prop} {p : Semisentence L k} (h : Defined R p) (v) :
    Semiformula.PVal! M v p ↔ R v := (h v).symm

end Defined

namespace Arith

section definability

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

abbrev FormulaHierarchy (b : VType) (s : ℕ) (L : Language) [L.LT] (μ : Type*) (n) :=
  { p : Semiformula L μ  n // Hierarchy b s p }

abbrev SentenceHierarchy (b : VType) (s : ℕ) (L : Language) [L.LT] (n) := FormulaHierarchy b s L Empty n

abbrev SigmaSentence (s : ℕ) (L : Language) [L.LT] (n) := SentenceHierarchy Σ s L n

abbrev PiSentence (s : ℕ) (L : Language) [L.LT] (n) := SentenceHierarchy Π s L n

notation "Σᴬ[" s "]" => SigmaSentence s ℒₒᵣ

notation "Πᴬ[" s "]" => PiSentence s ℒₒᵣ

namespace FormulaHierarchy

abbrev of_zero (p : FormulaHierarchy b 0 ℒₒᵣ μ k) : FormulaHierarchy b' s ℒₒᵣ μ k :=
  ⟨p, p.prop.of_zero⟩

variable (b : VType) (s : ℕ) (L : Language) [L.LT] (μ : Type*) (n)

@[simp] lemma hierarchy (p : FormulaHierarchy b s L μ n) : Hierarchy b s p.val := p.prop

@[simp] lemma hierarchy_zero (p : FormulaHierarchy b 0 L μ n) : Hierarchy b' s p.val :=
  Hierarchy.of_zero p.hierarchy

end FormulaHierarchy

protected abbrev Defined (b s) {k} (R : (Fin k → M) → Prop) (p : SentenceHierarchy b s ℒₒᵣ k) : Prop :=
  Defined R p.val

abbrev DefinedPred (b : VType) (s : ℕ) (P : M → Prop) (p : SentenceHierarchy b s ℒₒᵣ 1) : Prop :=
  Arith.Defined b s (λ v ↦ P (v 0)) p

abbrev DefinedRel (b : VType) (s : ℕ) (R : M → M → Prop) (p : SentenceHierarchy b s ℒₒᵣ 2) : Prop :=
  Arith.Defined b s (λ v ↦ R (v 0) (v 1)) p

abbrev DefinedRel₃ (b : VType) (s : ℕ) (R : M → M → M → Prop) (p : SentenceHierarchy b s ℒₒᵣ 3) : Prop :=
  Arith.Defined b s (λ v ↦ R (v 0) (v 1) (v 2)) p

abbrev DefinedRel₄ (b : VType) (s : ℕ) (R : M → M → M → M → Prop) (p : SentenceHierarchy b s ℒₒᵣ 4) : Prop :=
  Arith.Defined b s (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) p

abbrev SigmaDefinedPred (s : ℕ) (P : M → Prop) (p : Σᴬ[s] 1) : Prop := DefinedPred Σ s P p

notation "Σᴬ[" s "]-Predicate" => SigmaDefinedPred s

abbrev SigmaDefinedRel (s : ℕ) (R : M → M → Prop) (p : Σᴬ[s] 2) : Prop := DefinedRel Σ s R p

notation "Σᴬ[" s "]-Relation" => SigmaDefinedRel s

abbrev SigmaDefinedRel₃ (s : ℕ) (R : M → M → M → Prop) (p : Σᴬ[s] 3) : Prop := DefinedRel₃ Σ s R p

notation "Σᴬ[" s "]-Relation₃" => SigmaDefinedRel₃ s

abbrev PiDefinedPred (s : ℕ) (t : Set M) (p : Πᴬ[s] 1) : Prop := DefinedPred Π s t p

notation "Πᴬ[" s "]-Predicate" => PiDefinedPred s

abbrev PiDefinedRel (s : ℕ) (R : M → M → Prop) (p : Πᴬ[s] 2) : Prop := DefinedRel Π s R p

notation "Πᴬ[" s "]-Relation" => PiDefinedRel s

abbrev DefinedFunction (b : VType) (s : ℕ) {k} (f : (Fin k → M) → M) (p : SentenceHierarchy b s ℒₒᵣ (k + 1)) : Prop :=
  Arith.Defined b s (fun v => v 0 = f (v ·.succ)) p

abbrev DefinedFunction₁ (b : VType) (s : ℕ) (f : M → M) (p : SentenceHierarchy b s ℒₒᵣ 2) : Prop :=
  DefinedFunction b s (fun v => f (v 0)) p

abbrev DefinedFunction₂ (b : VType) (s : ℕ) (f : M → M → M) (p : SentenceHierarchy b s ℒₒᵣ 3) : Prop :=
  DefinedFunction b s (fun v => f (v 0) (v 1)) p

abbrev SigmaDefinedFunction₁ (s : ℕ) (f : M → M) (p : Σᴬ[s] 2) : Prop := DefinedFunction₁ Σ s f p

notation "Σᴬ[" s "]-Function₁" => SigmaDefinedFunction₁ s

abbrev PiDefinedFunction₁ (s : ℕ) (f : M → M) (p : Πᴬ[s] 2) : Prop := DefinedFunction₁ Π s f p

notation "Πᴬ[" s "]-Function₁" => PiDefinedFunction₁ s

abbrev SigmaDefinedFunction₂ (s : ℕ) (f : M → M → M) (p : Σᴬ[s] 3) : Prop := DefinedFunction₂ Σ s f p

notation "Σᴬ[" s "]-Function₂" => SigmaDefinedFunction₂ s

abbrev PiDefinedFunction₂ (s : ℕ) (f : M → M → M) (p : Πᴬ[s] 3) : Prop := DefinedFunction₂ Π s f p

notation "Πᴬ[" s "]-Function₂" => PiDefinedFunction₂ s

def eqdef : SentenceHierarchy b s ℒₒᵣ 2 := ⟨“#0 = #1”, by simp⟩

def ltdef : SentenceHierarchy b s ℒₒᵣ 2 := ⟨“#0 < #1”, by simp⟩

def ledef : SentenceHierarchy b s ℒₒᵣ 2 := ⟨“#0 ≤ #1”, by simp⟩

def DefinedRel.eq : DefinedRel b s ((· = ·) : M → M → Prop) eqdef := by intro v; simp [eqdef]

def DefinedRel.lt : DefinedRel b s ((· < ·) : M → M → Prop) ltdef := by intro v; simp [ltdef]

def DefinedRel.le : DefinedRel b s ((· ≤ ·) : M → M → Prop) ledef := by intro v; simp [ledef]

def IsPolynomialWithParam {k} (f : (Fin k → M) → M) : Prop :=
  ∃ l, ∃ w, ∃ t : Semiterm ℒₒᵣ (Fin l) k, ∀ v, f v = Semiterm.val! M v w t

namespace IsPolynomialWithParam

@[simp] def const {k} (c : M) : IsPolynomialWithParam (fun _ : Fin k → M ↦ c) := ⟨1, ![c], &0, by simp⟩

@[simp] def var {k} (i : Fin k) : IsPolynomialWithParam (fun v : Fin k → M ↦ v i) := ⟨0, ![], #i, by simp⟩

@[aesop safe apply] def add {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    IsPolynomialWithParam (fun v ↦ f v + g v) := by
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg,
    ᵀ“!!(Rew.rewriteMap (Fin.castLE (by simp)) tf) + !!(Rew.rewriteMap (Fin.natAdd _) tg)”, by
      intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg]⟩

@[aesop safe apply] def mul {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    IsPolynomialWithParam (fun v ↦ f v * g v) := by
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg,
    ᵀ“!!(Rew.rewriteMap (Fin.castLE (by simp)) tf) * !!(Rew.rewriteMap (Fin.natAdd _) tg)”, by
      intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg]⟩

end IsPolynomialWithParam

variable (b : VType) (s : ℕ)

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  intro : ∃ p : SentenceHierarchy b s ℒₒᵣ k, Arith.Defined b s P p

abbrev DefinablePred (P : M → Prop) : Prop := Definable (k := 1) b s (fun v ↦ P (v 0))

abbrev DefinableRel (P : M → M → Prop) : Prop := Definable (k := 2) b s (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := Definable (k := 3) b s (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableFunction {k} (f : (Fin k → M) → M) : Prop := Definable b s (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev DefinableFunction₁ (f : M → M) : Prop := DefinableFunction b s (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : M → M → M) : Prop := DefinableFunction b s (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := DefinableFunction b s (k := 3) (fun v ↦ f (v 0) (v 1) (v 3))

def DefinableWithParam {k} (P : (Fin k → M) → Prop) : Prop :=
  ∃ l, ∃ w, ∃ p : FormulaHierarchy b s ℒₒᵣ (Fin l) k, ∀ v, P v ↔ Semiformula.Eval! M v w p.val

abbrev DefinablePredWithParam (P : M → Prop) : Prop := DefinableWithParam b s (k := 1) (fun v ↦ P (v 0))

variable {b : VType} {s : ℕ}

def Defined.definable {k} {P : (Fin k → M) → Prop} {p : SentenceHierarchy b s ℒₒᵣ k} (h : Arith.Defined b s P p) : Definable b s P := ⟨p, h⟩

def Definable.of_zero {k} {P : (Fin k → M) → Prop} (h : Definable b' 0 P) : Definable b s P := by
  rcases h with ⟨p, h⟩
  exact ⟨p.of_zero, by intro x; simpa using h x⟩

instance Definable.eq : DefinableRel b s ((· = ·) : M → M → Prop) := DefinedRel.eq.definable

instance Definable.lt : DefinableRel b s ((· < ·) : M → M → Prop) := DefinedRel.lt.definable

instance Definable.le : DefinableRel b s ((· ≤ ·) : M → M → Prop) := DefinedRel.le.definable

@[aesop safe apply] lemma DefinablePredWithParam.comp {P : M → Prop} (hP : DefinablePredWithParam b s P)
    {k} {f : (Fin k → M) → M} (hf : IsPolynomialWithParam f) :
    DefinableWithParam b s (fun v ↦ P (f v)) := by
  rcases hP with ⟨lp, wp, p, hp⟩
  rcases hf with ⟨lf, wf, t, hf⟩
  let p' : Semiformula ℒₒᵣ (Fin (lp + lf)) 1 := (Rew.rewriteMap (Fin.castLE (by simp))).hom p.val
  let t' : Semiterm ℒₒᵣ (Fin (lp + lf)) k := Rew.rewriteMap (Fin.natAdd _) t
  exact ⟨lp + lf, Matrix.vecAppend rfl wp wf, ⟨p' /[t'], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, ←hp]⟩

@[aesop safe apply] lemma DefinablePred.comp_definable_with_param {P : M → Prop} [hP : DefinablePred b s P]
    {k} {f : (Fin k → M) → M} (hf : IsPolynomialWithParam f) :
    DefinableWithParam b s (fun v ↦ P (f v)) := by
  rcases hP with ⟨p, hp⟩
  rcases hf with ⟨lf, wf, tf, hf⟩
  exact ⟨lf, wf, ⟨p.val .[tf], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hp.pval]⟩

@[aesop safe apply] lemma DefinableRel.comp_definable_with_param {R : M → M → Prop} [hR : DefinableRel b s R]
    {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ R (f v) (g v)) := by
  rcases hR with ⟨p, hp⟩
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg, ⟨p.val .[Rew.rewriteMap (Fin.castLE (by simp)) tf, Rew.rewriteMap (Fin.natAdd _) tg], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hp.pval, ←hf, ←hg]⟩

@[aesop safe apply] lemma DefinableRel₃.comp_definable_with_param {R : M → M → M → Prop} [hR : DefinableRel₃ b s R]
    {k} {f g h : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) (hh : IsPolynomialWithParam h) :
    DefinableWithParam b s (fun v ↦ R (f v) (g v) (h v)) := by
  rcases hR with ⟨p, hp⟩
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  rcases hh with ⟨lh, wh, th, hh⟩
  exact ⟨lf + lg + lh, Matrix.vecAppend rfl (Matrix.vecAppend rfl wf wg) wh,
    let tf' : Semiterm ℒₒᵣ (Fin (lf + lg)) k := Rew.rewriteMap (Fin.castLE (by simp)) tf
    let tg' : Semiterm ℒₒᵣ (Fin (lf + lg)) k := Rew.rewriteMap (Fin.natAdd _) tg
    ⟨p.val .[Rew.rewriteMap (Fin.castLE (by simp)) tf', Rew.rewriteMap (Fin.castLE (by simp)) tg', Rew.rewriteMap (Fin.natAdd _) th], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hp.pval, ←hf, ←hg, ←hh]⟩

@[aesop safe apply] lemma DefinableFunction₁.comp_definable_with_param_right {F : M → M} [hP : DefinableFunction₁ b s F]
    {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ f v = F (g v)) := by
  rcases hP with ⟨p, hp⟩
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg, ⟨p.val .[Rew.rewriteMap (Fin.castLE (by simp)) tf, Rew.rewriteMap (Fin.natAdd _) tg], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg, hp.pval]⟩

@[aesop safe apply] lemma DefinableFunction₁.comp_definable_with_param_left {F : M → M} [hP : DefinableFunction₁ b s F]
    {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ F (g v) = f v) :=
  cast (by congr; funext v; simp [eq_comm]) <| DefinableFunction₁.comp_definable_with_param_right (b := b) (s := s) (F := F) hf hg

@[aesop safe apply] lemma DefinableFunction₂.comp_definable_with_param_right {F : M → M→ M} [hP : DefinableFunction₂ b s F]
    {k} {f g h : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) (hh : IsPolynomialWithParam h) :
    DefinableWithParam b s (fun v ↦ f v = F (g v) (h v)) := by
  rcases hP with ⟨p, hp⟩
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  rcases hh with ⟨lh, wh, th, hh⟩
  exact ⟨lf + lg + lh, Matrix.vecAppend rfl (Matrix.vecAppend rfl wf wg) wh,
    let tf' : Semiterm ℒₒᵣ (Fin (lf + lg)) k := Rew.rewriteMap (Fin.castLE (by simp)) tf
    let tg' : Semiterm ℒₒᵣ (Fin (lf + lg)) k := Rew.rewriteMap (Fin.natAdd _) tg
    ⟨p.val .[Rew.rewriteMap (Fin.castLE (by simp)) tf', Rew.rewriteMap (Fin.castLE (by simp)) tg', Rew.rewriteMap (Fin.natAdd _) th], by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hp.pval, ←hf, ←hg, ←hh]⟩

@[aesop safe apply] lemma DefinableFunction₂.comp_definable_with_param_left {F : M → M → M} [hP : DefinableFunction₂ b s F]
    {k} {f g h : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) (hh : IsPolynomialWithParam h) :
    DefinableWithParam b s (fun v ↦ F (g v) (h v) = f v) :=
  cast (by congr; funext v; simp [eq_comm]) <| DefinableFunction₂.comp_definable_with_param_right (b := b) (s := s) (F := F) hf hg hh

lemma DefinablePredWithParam.of_iff {p : M → Prop} (q) (h : ∀ x, p x ↔ q x) (H : DefinablePredWithParam b s q) : DefinablePredWithParam b s p := by
  rwa [show p = q from by funext v; simp [h]]

namespace DefinableWithParam

lemma of_iff {p : (Fin k → M) → Prop} (q) (h : ∀ v, p v ↔ q v) (H : DefinableWithParam b s q) : DefinableWithParam b s p := by
  rwa [show p = q from by funext v; simp [h]]

@[simp] lemma const (p : Prop) : DefinableWithParam b s (fun _ : (Fin k → M) ↦ p) := by
  by_cases hp : p
  · exact ⟨0, ![], ⟨⊤, by simp⟩, by intro x; simp [hp]⟩
  · exact ⟨0, ![], ⟨⊥, by simp⟩, by intro x; simp [hp]⟩

@[aesop safe apply] lemma eq {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ f v = g v) := Definable.eq.comp_definable_with_param hf hg

/-

  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg,
    ⟨“!!(Rew.rewriteMap (Fin.castLE (by simp)) tf) = !!(Rew.rewriteMap (Fin.natAdd _) tg)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg]⟩

@[aesop safe apply] lemma lt {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ f v < g v) := by
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg,
    ⟨“!!(Rew.rewriteMap (Fin.castLE (by simp)) tf) < !!(Rew.rewriteMap (Fin.natAdd _) tg)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg]⟩

@[aesop safe apply] lemma le {k} {f g : (Fin k → M) → M} (hf : IsPolynomialWithParam f) (hg : IsPolynomialWithParam g) :
    DefinableWithParam b s (fun v ↦ f v ≤ g v) := by
  rcases hf with ⟨lf, wf, tf, hf⟩
  rcases hg with ⟨lg, wg, tg, hg⟩
  exact ⟨lf + lg, Matrix.vecAppend rfl wf wg,
    ⟨“!!(Rew.rewriteMap (Fin.castLE (by simp)) tf) ≤ !!(Rew.rewriteMap (Fin.natAdd _) tg)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Function.comp, Matrix.vecAppend_eq_ite, hf, hg]⟩

@[simp] lemma verum : DefinableWithParam b s (fun _ : (Fin k → M) ↦ True) := ⟨0, ![], ⟨⊤, by simp⟩, by intro x; simp⟩

@[simp] lemma falsum : DefinableWithParam b s (fun _ : (Fin k → M) ↦ False) := ⟨0, ![], ⟨⊥, by simp⟩, by intro x; simp⟩

-/

@[aesop safe apply] lemma and {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b s P₁) (h₂ : DefinableWithParam b s P₂) :
    DefinableWithParam b s (fun v ↦ P₁ v ∧ P₂ v) := by
  rcases h₁ with ⟨l₁, w₁, p₁, h₁⟩; rcases h₂ with ⟨l₂, w₂, p₂, h₂⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨(Rew.rewriteMap (Fin.castLE (by simp))).hom p₁.val ⋏ (Rew.rewriteMap (Fin.natAdd l₁)).hom p₂.val, by simp⟩,
    by intro x; simp [h₁, h₂, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite]⟩

@[aesop safe apply] lemma or {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b s P₁) (h₂ : DefinableWithParam b s P₂) :
    DefinableWithParam b s (fun v ↦ P₁ v ∨ P₂ v) := by
  rcases h₁ with ⟨l₁, w₁, p₁, h₁⟩; rcases h₂ with ⟨l₂, w₂, p₂, h₂⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨(Rew.rewriteMap (Fin.castLE (by simp))).hom p₁.val ⋎ (Rew.rewriteMap (Fin.natAdd l₁)).hom p₂.val, by simp⟩,
    by intro x; simp [h₁, h₂, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite]⟩

lemma not {P : (Fin k → M) → Prop} (h : DefinableWithParam b.alt s P) :
    DefinableWithParam b s (fun v ↦ ¬P v) := by
  rcases h with ⟨l, w, p, h⟩; exact ⟨l, w, ⟨~p.val, by simp⟩, by intro x; simp [h]⟩

@[aesop safe apply] lemma ball_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : IsPolynomialWithParam f) (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf with ⟨l₁, w₁, t, ht⟩
  rcases h with ⟨l₂, w₂, p, hp⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨“∀[#0 < !!(Rew.bShift <| Rew.rewriteMap (Fin.castLE (by simp)) t)] !((Rew.rewriteMap (Fin.natAdd l₁)).hom p.val)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite, ←ht, ←hp]⟩

@[aesop safe apply] lemma ball_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : IsPolynomialWithParam f) (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ ∀ x ≤ f v, P v x) := by
  rcases hf with ⟨l₁, w₁, t, ht⟩
  rcases h with ⟨l₂, w₂, p, hp⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨“∀[#0 < !!(Rew.bShift <| Rew.rewriteMap (Fin.castLE (by simp)) t) + 1] !((Rew.rewriteMap (Fin.natAdd l₁)).hom p.val)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite, ←ht, ←hp, Model.le_iff_lt_succ]⟩

@[aesop safe apply] lemma bex_lt {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : IsPolynomialWithParam f) (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf with ⟨l₁, w₁, t, ht⟩
  rcases h with ⟨l₂, w₂, p, hp⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨“∃[#0 < !!(Rew.bShift <| Rew.rewriteMap (Fin.castLE (by simp)) t)] !((Rew.rewriteMap (Fin.natAdd l₁)).hom p.val)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite, ←ht, ←hp]⟩

@[aesop safe apply] lemma bex_le {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : IsPolynomialWithParam f) (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ ∃ x ≤ f v, P v x) := by
  rcases hf with ⟨l₁, w₁, t, ht⟩
  rcases h with ⟨l₂, w₂, p, hp⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
    ⟨“∃[#0 < !!(Rew.bShift <| Rew.rewriteMap (Fin.castLE (by simp)) t) + 1] !((Rew.rewriteMap (Fin.natAdd l₁)).hom p.val)”, by simp⟩,
    by intro v; simp [Semiterm.val_rew, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite, ←ht, ←hp, Model.le_iff_lt_succ]⟩

lemma imp {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b.alt s P₁) (h₂ : DefinableWithParam b s P₂) :
    DefinableWithParam b s (fun v ↦ P₁ v → P₂ v) := by
  rcases h₁ with ⟨l₁, w₁, p₁, h₁⟩; rcases h₂ with ⟨l₂, w₂, p₂, h₂⟩
  exact ⟨l₁ + l₂, Matrix.vecAppend rfl w₁ w₂,
      ⟨(Rew.rewriteMap (Fin.castLE (by simp))).hom p₁.val ⟶ (Rew.rewriteMap (Fin.natAdd l₁)).hom p₂.val, by simp⟩, by
      intro x; simp [h₁, h₂, Semiformula.eval_rew, Function.comp, Matrix.vecAppend_eq_ite]⟩

@[aesop safe apply] lemma of_sigma_zero {P : (Fin k → M) → Prop} : DefinableWithParam Σ 0 P → DefinableWithParam b s P := by
  rintro ⟨l, w, p, h⟩; exact ⟨l, w, ⟨p.val, p.prop.of_zero⟩, by simpa using h⟩

lemma zero_alt {P : (Fin k → M) → Prop} : DefinableWithParam b 0 P → DefinableWithParam b' s P := by
  rintro ⟨l, w, p, h⟩; exact ⟨l, w, ⟨p.val, Hierarchy.of_zero p.prop⟩, by simpa using h⟩

@[aesop safe apply] lemma imp₀' {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b 0 P₁) (h₂ : DefinableWithParam b s P₂) :
    DefinableWithParam b s (fun v ↦ P₁ v → P₂ v) := h₁.zero_alt.imp h₂

@[aesop safe apply] lemma imp₀ {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b 0 P₁) (h₂ : DefinableWithParam b 0 P₂) :
    DefinableWithParam b 0 (fun v ↦ P₁ v → P₂ v) := h₁.zero_alt.imp h₂

@[aesop safe apply] lemma not₀ {P : (Fin k → M) → Prop} (h : DefinableWithParam b 0 P) :
    DefinableWithParam b 0 (fun v ↦ ¬P v) := h.zero_alt.not

@[aesop safe apply] lemma iff₀ {P₁ P₂ : (Fin k → M) → Prop} (h₁ : DefinableWithParam b 0 P₁) (h₂ : DefinableWithParam b 0 P₂) :
    DefinableWithParam b 0 (fun v ↦ P₁ v ↔ P₂ v) := by
  simp [iff_iff_implies_and_implies]; aesop

example : DefinablePredWithParam Σ 0 (fun x : M ↦ x < 0 + x → ∃ z < x, z = 6) := by aesop

end DefinableWithParam


variable {f : M → M}

section

variable {M : Type} [LE M] [Structure ℒₒᵣ M]

class PolyBounded {k} (f : (Fin k → M) → M) : Prop where
  intro : ∃ t : Polynomial k, ∀ v : Fin k → M, f v ≤ t.bVal! M v

abbrev PolyBounded₁ (f : M → M) : Prop :=
  PolyBounded (k := 1) (fun v => f (Matrix.vecHead v))

abbrev PolyBounded₂ (f : M → M → M) : Prop :=
  PolyBounded (k := 2) (fun v => f (v 0) (v 1))

end

namespace DefinableWithParam

@[aesop safe apply] lemma elim_function₁ {f : M → M} [hf : PolyBounded₁ f] [DefinableFunction₁ b s f]
    {t : (Fin k → M) → M} (ht : IsPolynomialWithParam t)
    {P : (Fin k → M) → M → Prop} (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ P v (f (t v))) := by
  rcases hf with ⟨u, hu⟩
  have : DefinableWithParam b s (fun v : Fin k → M ↦ ∃ z ≤ u.bVal! M ![t v], z = f (t v) ∧  P v z) := by
    apply bex_le
    · rcases ht with ⟨lt, wt, tt, ht⟩
      exact ⟨lt, wt, Rew.embSubsts ![tt] u, by intro v; simp [Semiterm.val_embSubsts, ←ht]⟩
    · apply and
      · apply DefinableFunction₁.comp_definable_with_param_right (by simp)
          (by rcases ht with ⟨lt, wt, tt, ht⟩
              exact ⟨lt, wt, Rew.bShift tt, by
                intro v; rw [show v = v 0 :> (v ·.succ) from by funext x; cases x using Fin.cases <;> simp]; simp [Semiterm.val_bShift, ←ht]⟩)
      · exact h
  exact this.of_iff _ (by
    intro v
    constructor
    · intro h; exact ⟨f (t v), by simp [h]; exact hu ![t v]⟩
    · rintro ⟨z, _, rfl, hz⟩; exact hz)

@[aesop safe apply] lemma elim_function₂ {f : M → M → M} [hf : PolyBounded₂ f] [DefinableFunction₂ b s f]
    {t₁ : (Fin k → M) → M} (ht₁ : IsPolynomialWithParam t₁)
    {t₂ : (Fin k → M) → M} (ht₂ : IsPolynomialWithParam t₂)
    {P : (Fin k → M) → M → Prop} (h : DefinableWithParam b s (fun w ↦ P (w ·.succ) (w 0))) :
    DefinableWithParam b s (fun v ↦ P v (f (t₁ v) (t₂ v))) := by
  rcases hf with ⟨u, hu⟩
  have : DefinableWithParam b s (fun v : Fin k → M ↦ ∃ z ≤ u.bVal! M ![t₁ v, t₂ v], z = f (t₁ v) (t₂ v) ∧ P v z) := by
    apply bex_le
    · rcases ht₁ with ⟨lt₁, wt₁, tt₁, ht₁⟩
      rcases ht₂ with ⟨lt₂, wt₂, tt₂, ht₂⟩
      exact ⟨lt₁ + lt₂, Matrix.vecAppend rfl wt₁ wt₂,
        Rew.embSubsts ![Rew.rewriteMap (Fin.castLE (by simp)) tt₁, Rew.rewriteMap (Fin.natAdd lt₁) tt₂] u,
          by intro v; simp [Semiterm.val_rewriteMap, Matrix.vecAppend_eq_ite, Semiterm.val_embSubsts, ←ht₁, ←ht₂]⟩
    · apply and
      · apply DefinableFunction₂.comp_definable_with_param_right (by simp)
          (by rcases ht₁ with ⟨lt, wt, tt, ht⟩
              exact ⟨lt, wt, Rew.bShift tt, by
                intro v; rw [show v = v 0 :> (v ·.succ) from by funext x; cases x using Fin.cases <;> simp]; simp [Semiterm.val_bShift, ←ht]⟩)
          (by rcases ht₂ with ⟨lt, wt, tt, ht⟩
              exact ⟨lt, wt, Rew.bShift tt, by
                intro v; rw [show v = v 0 :> (v ·.succ) from by funext x; cases x using Fin.cases <;> simp]; simp [Semiterm.val_bShift, ←ht]⟩)
      · exact h
  exact this.of_iff _ (by
    intro v
    constructor
    · intro h; exact ⟨f (t₁ v) (t₂ v), by simp [h]; exact hu ![t₁ v, t₂ v]⟩
    · rintro ⟨z, _, rfl, hz⟩; exact hz)

end DefinableWithParam

end definability
end Arith


end LO.FirstOrder
