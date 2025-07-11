import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
import Foundation.FirstOrder.Arithmetic.BoundedQuantifier
import Foundation.Vorspiel.Graph

namespace LO.FirstOrder.Arithmetic

end Arithmetic

def Defined {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm V v φ

def DefinedWithParam {k} (R : (Fin k → V) → Prop) [Structure L V] (φ : Semiformula L V k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm V v id φ

lemma Defined.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ : Semisentence L k} (h : Defined R φ) (v) :
    Semiformula.Evalbm V v φ ↔ R v := (h v).symm

lemma DefinedWithParam.iff [Structure L V] {k} {R : (Fin k → V) → Prop} {φ : Semiformula L V k} (h : DefinedWithParam R φ) (v) :
    Semiformula.Evalm V v id φ ↔ R v := (h v).symm

namespace Arithmetic.HierarchySymbol

variable (ξ : Type*) (n : ℕ)

open PeanoMinus

variable {V : Type*} [ORingStruc V]

def Defined (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semisentence k → Prop
  | 𝚺-[_], φ => FirstOrder.Defined R φ.val
  | 𝚷-[_], φ => FirstOrder.Defined R φ.val
  | 𝚫-[_], φ => φ.ProperOn V ∧ FirstOrder.Defined R φ.val

def DefinedWithParam (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol} → ℌ.Semiformula V k → Prop
  | 𝚺-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | 𝚷-[_], φ => FirstOrder.DefinedWithParam R φ.val
  | 𝚫-[_], φ => φ.ProperWithParamOn V ∧ FirstOrder.DefinedWithParam R φ.val

variable {ℌ : HierarchySymbol} {Γ : SigmaPiDelta}

section

variable (ℌ)

class Lightface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semisentence k, Defined P φ

class Boldface {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semiformula V k, DefinedWithParam P φ

abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) : Prop :=
  Defined (λ v ↦ P (v 0)) φ

abbrev DefinedRel (R : V → V → Prop) (φ : ℌ.Semisentence 2) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1)) φ

abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : ℌ.Semisentence 3) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2)) φ

abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : ℌ.Semisentence 4) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

variable {ℌ}

abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) φ

variable (ℌ)

abbrev DefinedFunction₀ (c : V) (φ : ℌ.Semisentence 1) : Prop :=
  DefinedFunction (fun _ => c) φ

abbrev DefinedFunction₁ (f : V → V) (φ : ℌ.Semisentence 2) : Prop :=
  DefinedFunction (fun v => f (v 0)) φ

abbrev DefinedFunction₂ (f : V → V → V) (φ : ℌ.Semisentence 3) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1)) φ

abbrev DefinedFunction₃ (f : V → V → V → V) (φ : ℌ.Semisentence 4) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2)) φ

abbrev DefinedFunction₄ (f : V → V → V → V → V) (φ : ℌ.Semisentence 5) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₅ (f : V → V → V → V → V → V) (φ : ℌ.Semisentence 6) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

abbrev BoldfacePred (P : V → Prop) : Prop := ℌ.Boldface (k := 1) (fun v ↦ P (v 0))

abbrev BoldfaceRel (P : V → V → Prop) : Prop := ℌ.Boldface (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev BoldfaceRel₃ (P : V → V → V → Prop) : Prop := ℌ.Boldface (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev BoldfaceRel₄ (P : V → V → V → V → Prop) : Prop := ℌ.Boldface (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev BoldfaceRel₅ (P : V → V → V → V → V → Prop) : Prop := ℌ.Boldface (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

abbrev BoldfaceRel₆ (P : V → V → V → V → V → V → Prop) : Prop := ℌ.Boldface (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

abbrev BoldfaceFunction (f : (Fin k → V) → V) : Prop := ℌ.Boldface (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev BoldfaceFunction₀ (c : V) : Prop := ℌ.BoldfaceFunction (k := 0) (fun _ ↦ c)

abbrev BoldfaceFunction₁ (f : V → V) : Prop := ℌ.BoldfaceFunction (k := 1) (fun v ↦ f (v 0))

abbrev BoldfaceFunction₂ (f : V → V → V) : Prop := ℌ.BoldfaceFunction (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev BoldfaceFunction₃ (f : V → V → V → V) : Prop := ℌ.BoldfaceFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

abbrev BoldfaceFunction₄ (f : V → V → V → V → V) : Prop := ℌ.BoldfaceFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

abbrev BoldfaceFunction₅ (f : V → V → V → V → V → V) : Prop := ℌ.BoldfaceFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {ℌ}

notation Γ "-Predicate " P " via " φ => DefinedPred Γ P φ

notation Γ "-Relation " P " via " φ => DefinedRel Γ P φ

notation Γ "-Relation₃ " P " via " φ => DefinedRel₃ Γ P φ

notation Γ "-Relation₄ " P " via " φ => DefinedRel₄ Γ P φ

notation Γ "-Function₀ " c " via " φ => DefinedFunction₀ Γ c φ

notation Γ "-Function₁ " f " via " φ => DefinedFunction₁ Γ f φ

notation Γ "-Function₂ " f " via " φ => DefinedFunction₂ Γ f φ

notation Γ "-Function₃ " f " via " φ => DefinedFunction₃ Γ f φ

notation Γ "-Function₄ " f " via " φ => DefinedFunction₄ Γ f φ

notation Γ "-Function₅ " f " via " φ => DefinedFunction₅ Γ f φ

notation Γ "-Predicate " P => BoldfacePred Γ P

notation Γ "-Relation " P => BoldfaceRel Γ P

notation Γ "-Relation₃ " P => BoldfaceRel₃ Γ P

notation Γ "-Relation₄ " P => BoldfaceRel₄ Γ P

notation Γ "-Relation₅ " P => BoldfaceRel₅ Γ P

notation Γ "-Function₁ " f => BoldfaceFunction₁ Γ f

notation Γ "-Function₂ " f => BoldfaceFunction₂ Γ f

notation Γ "-Function₃ " f => BoldfaceFunction₃ Γ f

notation Γ "-Function₄ " f => BoldfaceFunction₄ Γ f



notation Γ "-Predicate[" V "] " P " via " φ => DefinedPred (V := V) Γ P φ

notation Γ "-Relation[" V "] " P " via " φ => DefinedRel (V := V) Γ P φ

notation Γ "-Relation₃[" V "] " P " via " φ => DefinedRel₃ (V := V) Γ P φ

notation Γ "-Relation₄[" V "] " P " via " φ => DefinedRel₄ (V := V) Γ P φ

notation Γ "-Function₀[" V "] " c " via " φ => DefinedFunction₀ (V := V) Γ c φ

notation Γ "-Function₁[" V "] " f " via " φ => DefinedFunction₁ (V := V) Γ f φ

notation Γ "-Function₂[" V "] " f " via " φ => DefinedFunction₂ (V := V) Γ f φ

notation Γ "-Function₃[" V "] " f " via " φ => DefinedFunction₃ (V := V) Γ f φ

notation Γ "-Function₄[" V "] " f " via " φ => DefinedFunction₄ (V := V) Γ f φ

notation Γ "-Function₅[" V "] " f " via " φ => DefinedFunction₅ (V := V) Γ f φ

notation Γ "-Predicate[" V "] " P => BoldfacePred (V := V) Γ P

notation Γ "-Relation[" V "] " P => BoldfaceRel (V := V) Γ P

notation Γ "-Relation₃[" V "] " P => BoldfaceRel₃ (V := V) Γ P

notation Γ "-Relation₄[" V "] " P => BoldfaceRel₄ (V := V) Γ P

notation Γ "-Relation₅[" V "] " P => BoldfaceRel₅ (V := V) Γ P

notation Γ "-Function₁[" V "] " f => BoldfaceFunction₁ (V := V) Γ f

notation Γ "-Function₂[" V "] " f => BoldfaceFunction₂ (V := V) Γ f

notation Γ "-Function₃[" V "] " f => BoldfaceFunction₃ (V := V) Γ f

notation Γ "-Function₄[" V "] " f => BoldfaceFunction₄ (V := V) Γ f

end

section

variable {k} {P Q : (Fin k → V) → Prop}

namespace Defined

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) : FirstOrder.Defined R φ.val :=
  match ℌ with
  | 𝚺-[_] => h
  | 𝚷-[_] => h
  | 𝚫-[_] => h.2

lemma proper {R : (Fin k → V) → Prop} {m} {φ : 𝚫-[m].Semisentence k} (h : Defined R φ) : φ.ProperOn V := h.1

lemma of_zero {R : (Fin k → V) → Prop} {φ : 𝚺₀.Semisentence k} (h : Defined R φ) : Defined R (φ.ofZero ℌ) :=
  match ℌ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simp, by intro _; simp [h.iff]⟩

lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) : Defined R φ.emb :=
  match ℌ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x) {φ : ℌ.Semisentence k} (H : Defined Q φ) : Defined P φ := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable (φ : ℌ.Semisentence k) (hP : Defined P φ) : ℌ.Boldface P := ⟨φ.rew Rew.emb, by
  match ℌ with
  | 𝚺-[_] => intro; simp [hP.iff]
  | 𝚷-[_] => intro; simp [hP.iff]
  | 𝚫-[_] => exact ⟨
    fun v ↦ by rcases φ; simpa [HierarchySymbol.Semiformula.rew] using hP.proper.rew Rew.emb v,
    by intro; simp [hP.df.iff]⟩⟩

lemma to_definable₀ {φ : 𝚺₀.Semisentence k} (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable (φ.ofZero ℌ) hP.of_zero

lemma to_definable_oRing (φ : ℌ.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable φ.emb hP.emb

lemma to_definable_oRing₀ (φ : 𝚺₀.Semisentence k) (hP : Defined P φ) :
    ℌ.Boldface P := Defined.to_definable₀ hP.emb

end Defined

namespace DefinedFunction

lemma of_eq {f g : (Fin k → V) → V} (h : ∀ x, f x = g x)
    {φ : ℌ.Semisentence (k + 1)} (H : DefinedFunction f φ) : DefinedFunction g φ :=
  Defined.of_iff (by intro; simp [h]) H

lemma graph_delta {f : (Fin k → V) → V} {φ : 𝚺-[m].Semisentence (k + 1)}
    (h : DefinedFunction f φ) : DefinedFunction f φ.graphDelta :=
  ⟨by
      cases' m with m
      case zero => simp [HierarchySymbol.Semiformula.graphDelta]
      case succ =>
        simp only [Semiformula.graphDelta]
        intro e
        simp [Empty.eq_elim, h.df.iff]; tauto,
   by intro v; simp [h.df.iff]⟩

end DefinedFunction

namespace DefinedWithParam

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) : FirstOrder.DefinedWithParam R φ.val :=
  match ℌ with
  | 𝚺-[_] => h
  | 𝚷-[_] => h
  | 𝚫-[_] => h.2

lemma proper {R : (Fin k → V) → Prop} {m} {φ : 𝚫-[m].Semiformula V k} (h : DefinedWithParam R φ) : φ.ProperWithParamOn V := h.1

lemma of_zero {R : (Fin k → V) → Prop} {Γ'} {φ : Γ'-[0].Semiformula V k}
    (h : DefinedWithParam R φ) {Γ} : DefinedWithParam R (φ.ofZero Γ) :=
  match Γ with
  | 𝚺-[m] => by intro _; simp [h.df.iff]
  | 𝚷-[m] => by intro _; simp [h.df.iff]
  | 𝚫-[m] => ⟨by simp , by intro _; simp [h.df.iff]⟩

lemma of_deltaOne {R : (Fin k → V) → Prop} {Γ m} {φ : 𝚫₁.Semiformula V k}
    (h : DefinedWithParam R φ) : DefinedWithParam R (φ.ofDeltaOne Γ m) :=
  match Γ with
  | 𝚺 => by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]
  | 𝚷 => by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, h.proper.iff']
  | 𝚫 => ⟨by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma, h.proper.iff'],
    by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩

lemma emb {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : DefinedWithParam R φ) : DefinedWithParam R φ.emb :=
  match ℌ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x)
    {φ : ℌ.Semiformula V k} (H : DefinedWithParam Q φ) : DefinedWithParam P φ := by
  rwa [show P = Q from by funext v; simp [h]]

lemma transition {P Q : (Fin k → V) → Prop} (hP : DefinedWithParam P φ) (hQ : DefinedWithParam Q φ) :
    ∀ x, P x → Q x := fun x ↦ by simp [hP.df x, hQ.df x]

lemma to_definable {φ : ℌ.Semiformula V k} (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ, h⟩

lemma to_definable₀ {φ : Γ'-[0].Semiformula V k}
    (h : DefinedWithParam P φ) : ℌ.Boldface P := ⟨φ.ofZero ℌ, h.of_zero⟩

lemma to_definable_deltaOne {φ : 𝚫₁.Semiformula V k} {Γ m}
    (h : DefinedWithParam P φ) : Γ-[m + 1].Boldface P := ⟨φ.ofDeltaOne Γ m, h.of_deltaOne⟩

lemma retraction {φ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (f : Fin k → Fin l) :
    DefinedWithParam (fun v ↦ P fun i ↦ v (f i)) (φ.rew <| Rew.substs fun x ↦ #(f x)) :=
  match ℌ with
  | 𝚺-[_] => by intro; simp [hp.df.iff]
  | 𝚷-[_] => by intro; simp [hp.df.iff]
  | 𝚫-[_] => ⟨hp.proper.rew _, by intro; simp [hp.df.iff]⟩

@[simp] lemma verum : DefinedWithParam (fun _ ↦ True) (⊤ : ℌ.Semiformula V k) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp
  | 𝚷-[m] => by intro v; simp
  | 𝚫-[m] => ⟨by simp, by intro v; simp⟩

@[simp] lemma falsum : DefinedWithParam (fun _ ↦ False) (⊥ : ℌ.Semiformula V k) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp
  | 𝚷-[m] => by intro v; simp
  | 𝚫-[m] => ⟨by simp, by intro v; simp⟩

lemma and {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∧ Q x) (φ ⋏ ψ) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚷-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚫-[m] => ⟨hp.proper.and hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma or {φ ψ : ℌ.Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ∨ Q x) (φ ⋎ ψ) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚷-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚫-[m] => ⟨hp.proper.or hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma negSigma {φ : 𝚺-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negSigma := by intro v; simp [hp.iff]

lemma negPi {φ : 𝚷-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) φ.negPi := by intro v; simp [hp.iff]

lemma not {φ : 𝚫-[m].Semiformula V k} (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun x ↦ ¬P x) (∼φ) := ⟨hp.proper.neg, by intro v; simp [hp.proper.eval_neg, hp.df.iff]⟩

lemma imp {φ ψ : 𝚫-[m].Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x → Q x) (φ ➝ ψ) := (hp.not.or hq).of_iff (by intro x; simp [imp_iff_not_or])

lemma biconditional {φ ψ : 𝚫-[m].Semiformula V k} (hp : DefinedWithParam P φ) (hq : DefinedWithParam Q ψ) :
    DefinedWithParam (fun x ↦ P x ↔ Q x) (φ ⭤ ψ) := ((hp.imp hq).and (hq.imp hp)).of_iff <| by intro v; simp [iff_iff_implies_and_implies]

lemma ball {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) (t : Semiterm ℒₒᵣ V k) :
    DefinedWithParam (fun v ↦ ∀ x < t.valm V v id, P (x :> v)) (HierarchySymbol.Semiformula.ball t φ) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp [hp.df.iff]
  | 𝚷-[m] => by intro v; simp [hp.df.iff]
  | 𝚫-[m] => ⟨hp.proper.ball, by intro v; simp [hp.df.iff]⟩

lemma bex {P : (Fin (k + 1) → V) → Prop} {φ : ℌ.Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) (t : Semiterm ℒₒᵣ V k) :
    DefinedWithParam (fun v ↦ ∃ x < t.valm V v id, P (x :> v)) (HierarchySymbol.Semiformula.bex t φ) :=
  match ℌ with
  | 𝚺-[m] => by intro v; simp [hp.df.iff]
  | 𝚷-[m] => by intro v; simp [hp.df.iff]
  | 𝚫-[m] => ⟨hp.proper.bex, by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin (k + 1) → V) → Prop} {φ : 𝚺-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun v ↦ ∃ x, P (x :> v)) φ.ex := by intro _; simp [hp.df.iff]

lemma all {P : (Fin (k + 1) → V) → Prop} {φ : 𝚷-[m + 1].Semiformula V (k + 1)}
    (hp : DefinedWithParam P φ) :
    DefinedWithParam (fun v ↦ ∀ x, P (x :> v)) φ.all := by intro _; simp [hp.df.iff]

lemma conj₂ (Γ : List (ℌ.Semiformula V k)) {R : (φ : ℌ.Semiformula V k) → (Fin k → V) → Prop} (hR : ∀ φ ∈ Γ, DefinedWithParam (R φ) φ) :
    DefinedWithParam (fun x ↦ ∀ φ ∈ Γ, R φ x) (⋀Γ) :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simpa using hR _ (by simp)
  | φ :: ψ :: Γ => by simpa using (hR φ (by simp)).and (conj₂ (ψ :: Γ) (R := R) (fun ψ hψ ↦ hR ψ (by simp [hψ])))

lemma disj₂ (Γ : List (ℌ.Semiformula V k)) {R : (φ : ℌ.Semiformula V k) → (Fin k → V) → Prop} (hR : ∀ φ ∈ Γ, DefinedWithParam (R φ) φ) :
    DefinedWithParam (fun x ↦ ∃ φ ∈ Γ, R φ x) (⋁Γ) :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simpa using hR _ (by simp)
  | φ :: ψ :: Γ => by simpa using (hR φ (by simp)).or (disj₂ (ψ :: Γ) (R := R) (fun ψ hψ ↦ hR ψ (by simp [hψ])))

open Classical in
lemma fconj {s : Finset ι} {R : ι → (Fin k → V) → Prop} {φ : ι → ℌ.Semiformula V k} (hR : ∀ i ∈ s, DefinedWithParam (R i) (φ i)) :
    DefinedWithParam (fun x ↦ ∀ i ∈ s, R i x) (⩕ i ∈ s, φ i) := by
  suffices DefinedWithParam (fun x ↦ ∀ i ∈ s, R i x) (s.toList.map φ).conj₂ by simpa [Finset.conj', Finset.conj]
  have : DefinedWithParam (fun x ↦ ∀ i ∈ s, ∀ j ∈ s, φ i = φ j → R j x) (s.toList.map φ).conj₂ := by
    simpa using conj₂ (s.toList.map φ) (R := fun ψ v ↦ ∀ i ∈ s, ψ = φ i → R i v) (by
      suffices ∀ a ∈ s, DefinedWithParam (fun v => ∀ i ∈ s, φ a = φ i → R i v) (φ a) by simpa
      intro i hi
      exact (hR i hi).of_iff fun v ↦
        ⟨fun h ↦ h i hi rfl, fun h j hj e ↦
          (hR i hi).transition (show DefinedWithParam (R j) (φ i) from by simpa [e] using hR j hj) v h⟩)
  exact this.of_iff fun x ↦ ⟨fun h i hi j hj e ↦ h j hj, fun h i hi ↦ h i hi i hi rfl⟩

open Classical in
lemma fdisj {s : Finset ι} {R : ι → (Fin k → V) → Prop} {φ : ι → ℌ.Semiformula V k} (hR : ∀ i ∈ s, DefinedWithParam (R i) (φ i)) :
    DefinedWithParam (fun x ↦ ∃ i ∈ s, R i x) (⩖ i ∈ s, φ i) := by
  suffices DefinedWithParam (fun x ↦ ∃ i ∈ s, R i x) (s.toList.map φ).disj₂ by simpa [Finset.disj', Finset.disj]
  have : DefinedWithParam (fun x ↦ ∃ i ∈ s, ∀ j ∈ s, φ i = φ j → R j x) (s.toList.map φ).disj₂ := by
    simpa using disj₂ (s.toList.map φ) (R := fun ψ v ↦ ∀ i ∈ s, ψ = φ i → R i v) (by
      suffices ∀ a ∈ s, DefinedWithParam (fun v => ∀ i ∈ s, φ a = φ i → R i v) (φ a) by simpa
      intro i hi
      exact (hR i hi).of_iff fun v ↦
        ⟨fun h ↦ h i hi rfl, fun h j hj e ↦
          (hR i hi).transition (show DefinedWithParam (R j) (φ i) from by simpa [e] using hR j hj) v h⟩)
  exact this.of_iff fun x ↦
    ⟨fun ⟨i, hi, h⟩ ↦
      ⟨i, hi, fun j hj e ↦ (hR i hi).transition (show DefinedWithParam (R j) (φ i) from by simpa [e] using hR j hj) x h⟩,
      fun ⟨i, hi, h⟩ ↦ ⟨i, hi, h i hi rfl⟩⟩

end DefinedWithParam

namespace BoldfaceRel

@[simp] instance eq : ℌ.BoldfaceRel (Eq : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1” (by simp)) (by intro _; simp)

@[simp] instance lt : ℌ.BoldfaceRel (LT.lt : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 < #1” (by simp)) (by intro _; simp)

@[simp] instance le [V ⊧ₘ* 𝐏𝐀⁻] : ℌ.BoldfaceRel (LE.le : V → V → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 ≤ #1” (by simp)) (by intro _; simp)

end BoldfaceRel

namespace BoldfaceFunction₂

@[simp] instance add : ℌ.BoldfaceFunction₂ ((· + ·) : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance mul : ℌ.BoldfaceFunction₂ ((· * ·) : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

@[simp] instance hAdd : ℌ.BoldfaceFunction₂ (HAdd.hAdd : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance hMul : ℌ.BoldfaceFunction₂ (HMul.hMul : V → V → V) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

end BoldfaceFunction₂

namespace Boldface

lemma mkPolarity {P : (Fin k → V) → Prop} {Γ : Polarity}
    (φ : Semiformula ℒₒᵣ V k) (hp : Hierarchy Γ m φ) (hP : ∀ v, P v ↔ Semiformula.Evalm V v id φ) : Γ-[m].Boldface P :=
  match Γ with
  | 𝚺 => ⟨.mkSigma φ hp, by intro v; simp [hP]⟩
  | 𝚷 => ⟨.mkPi φ hp, by intro v; simp [hP]⟩

lemma of_iff (H : ℌ.Boldface Q) (h : ∀ x, P x ↔ Q x) : ℌ.Boldface P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma of_oRing (h : ℌ.Boldface P) : ℌ.Boldface P := by
  rcases h with ⟨φ, hP⟩; exact ⟨φ.emb, hP.emb⟩

lemma of_delta (h : 𝚫-[m].Boldface P) : Γ-[m].Boldface P := by
  rcases h with ⟨φ, h⟩
  match Γ with
  | 𝚺 => exact ⟨φ.sigma, by intro v; simp [HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | 𝚷 => exact ⟨φ.pi, by intro v; simp [←h.proper v, HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | 𝚫 => exact ⟨φ, h⟩

instance [𝚫-[m].Boldface P] (Γ) : Γ-[m].Boldface P := of_delta inferInstance

lemma of_sigma_of_pi (hσ : 𝚺-[m].Boldface P) (hπ : 𝚷-[m].Boldface P) : Γ-[m].Boldface P :=
  match Γ with
  | 𝚺 => hσ
  | 𝚷 => hπ
  | 𝚫 => by
    rcases hσ with ⟨φ, hp⟩; rcases hπ with ⟨ψ, hq⟩
    exact ⟨.mkDelta φ ψ, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩

lemma of_zero (h : Γ'-[0].Boldface P) : ℌ.Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable₀

lemma of_deltaOne (h : 𝚫₁.Boldface P) {Γ m} : Γ-[m + 1].Boldface P := by
  rcases h with ⟨⟨φ, hp⟩⟩; exact hp.to_definable_deltaOne

instance [𝚺₀.Boldface P] (ℌ : HierarchySymbol) : ℌ.Boldface P := Boldface.of_zero (Γ' := 𝚺) (ℌ := ℌ) inferInstance

lemma retraction (h : ℌ.Boldface P) {n} (f : Fin k → Fin n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.rew (Rew.substs (fun i ↦ #(f i))),
  match ℌ with
  | 𝚺-[_] => by intro; simp [h.df.iff]
  | 𝚷-[_] => by intro; simp [h.df.iff]
  | 𝚫-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

lemma retractiont (h : ℌ.Boldface P) (f : Fin k → Semiterm ℒₒᵣ V n) :
    ℌ.Boldface fun v ↦ P (fun i ↦ Semiterm.valm V v id (f i)) := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.rew (Rew.substs f),
  match ℌ with
  | 𝚺-[_] => by intro; simp [h.df.iff]
  | 𝚷-[_] => by intro; simp [h.df.iff]
  | 𝚫-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

@[simp] lemma const {P : Prop} : ℌ.Boldface (fun _ : Fin k → V ↦ P) := of_zero (by
  by_cases hP : P
  · exact ⟨.mkSigma ⊤ (by simp), by intro; simp [hP]⟩
  · exact ⟨.mkSigma ⊥ (by simp), by intro; simp [hP]⟩)

lemma and (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) :
    ℌ.Boldface (fun v ↦ P v ∧ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋏ p₂, h₁.and h₂⟩

lemma fconj {P : ι → (Fin k → V) → Prop} (s : Finset ι)
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∀ i ∈ s, P i v := by
    have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
    rcases Classical.axiomOfChoice this with ⟨φ, H⟩
    exact ⟨⟨_, DefinedWithParam.fconj fun i _ ↦ H i⟩⟩

lemma fdisj {P : ι → (Fin k → V) → Prop} (s : Finset ι)
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∃ i ∈ s, P i v := by
    have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
    rcases Classical.axiomOfChoice this with ⟨φ, H⟩
    exact ⟨⟨_, DefinedWithParam.fdisj fun i _ ↦ H i⟩⟩

lemma fintype_all [Fintype ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∀ i, P i v := by
  simpa using fconj Finset.univ h

lemma fintype_ex [Fintype ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Boldface fun w : Fin k → V ↦ P i w) :
    ℌ.Boldface fun v : Fin k → V ↦ ∃ i, P i v := by
  simpa using fdisj Finset.univ h

lemma or (h₁ : ℌ.Boldface P) (h₂ : ℌ.Boldface Q) :
    ℌ.Boldface (fun v ↦ P v ∨ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋎ p₂, h₁.or h₂⟩

lemma not (h : Γ.alt-[m].Boldface P) :
    Γ-[m].Boldface (fun v ↦ ¬P v) := by
  match Γ with
  | 𝚺 => rcases h with ⟨φ, h⟩; exact ⟨φ.negPi, h.negPi⟩
  | 𝚷 => rcases h with ⟨φ, h⟩; exact ⟨φ.negSigma, h.negSigma⟩
  | 𝚫 => rcases h with ⟨φ, h⟩; exact ⟨φ.negDelta, h.not⟩

lemma imp (h₁ : Γ.alt-[m].Boldface P) (h₂ : Γ-[m].Boldface Q) :
    Γ-[m].Boldface (fun v ↦ P v → Q v) := by
  match Γ with
  | 𝚺 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negPi.or p₂, (h₁.negPi.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚷 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negSigma.or p₂, (h₁.negSigma.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚫 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩; exact ⟨p₁ ➝ p₂, h₁.imp h₂⟩

lemma biconditional (h₁ : 𝚫-[m].Boldface P) (h₂ : 𝚫-[m].Boldface Q) {Γ} :
    Γ-[m].Boldface (fun v ↦ P v ↔ Q v) :=
  .of_delta (by rcases h₁ with ⟨φ, hp⟩; rcases h₂ with ⟨ψ, hq⟩; exact ⟨φ ⭤ ψ, hp.biconditional hq⟩)

lemma all {P : (Fin k → V) → V → Prop} (h : 𝚷-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    𝚷-[s + 1].Boldface (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkPi (∀' φ.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin k → V) → V → Prop} (h : 𝚺-[s + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    𝚺-[s + 1].Boldface (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨φ, hp⟩
  exact ⟨.mkSigma (∃' φ.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma equal' (i j : Fin k) : ℌ.Boldface fun v : Fin k → V ↦ v i = v j := by
  simpa using retraction BoldfaceRel.eq ![i, j]

lemma of_sigma {f : (Fin k → V) → V} (h : 𝚺-[m].BoldfaceFunction f) {Γ} : Γ-[m].BoldfaceFunction f := by
  cases' m with m
  · exact of_zero h
  apply of_sigma_of_pi
  · exact h
  · have : 𝚷-[m + 1].Boldface fun v ↦ ∀ y, y = f (v ·.succ) → v 0 = y := all <| imp
      (by simpa using retraction h (0 :> (·.succ.succ)))
      (by simpa using equal' 1 0)
    exact of_iff this (fun v ↦ by simp)

lemma exVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝚺-[m + 1].Boldface fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝚺-[m + 1].Boldface fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝚺-[m + 1].Boldface fun v : Fin k → V ↦ ∃ y, ∃ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply ex; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · simp only [Matrix.cons_val_zero, g]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ, g]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝚷-[m+1].Boldface fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝚷-[m+1].Boldface fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝚷-[m+1].Boldface fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · simp only [Matrix.cons_val_zero, g]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ, g]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

private lemma substitution_sigma {f : Fin k → (Fin l → V) → V} (hP : 𝚺-[m+1].Boldface P) (hf : ∀ i, 𝚺-[m+1].BoldfaceFunction (f i)) :
    𝚺-[m+1].Boldface fun z ↦ P (fun i ↦ f i z) := by
  have : 𝚺-[m+1].Boldface fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys := by
    apply exVec; apply and
    · apply fintype_all; intro i
      simpa using retraction (of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro hP
      exact ⟨(f · v), by simp, hP⟩
    · rintro ⟨ys, hys, hP⟩
      have : ys = fun i ↦ f i v := funext hys
      rcases this; exact hP

private lemma substitution_pi {f : Fin k → (Fin l → V) → V} (hP : 𝚷-[m+1].Boldface P) (hf : ∀ i, 𝚺-[m+1].BoldfaceFunction (f i)) :
    𝚷-[m+1].Boldface fun z ↦ P (fun i ↦ f i z) := by
  have : 𝚷-[m+1].Boldface fun z ↦ ∀ ys : Fin k → V, (∀ i, ys i = f i z) → P ys := by
    apply allVec; apply imp
    · apply fintype_all; intro i
      simpa using retraction (of_sigma (hf i)) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro h ys e
      have : ys = (f · v) := funext e
      rcases this; exact h
    · intro h; apply h _ (by simp)

lemma substitution {f : Fin k → (Fin l → V) → V}
    (hP : Γ-[m + 1].Boldface P) (hf : ∀ i, 𝚺-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].Boldface fun z ↦ P (fun i ↦ f i z) :=
  match Γ with
  | 𝚺 => substitution_sigma hP hf
  | 𝚷 => substitution_pi hP hf
  | 𝚫 => of_sigma_of_pi (substitution_sigma (of_delta hP) hf) (substitution_pi (of_delta hP) hf)

end Boldface

lemma BoldfacePred.comp {P : V → Prop} {k} {f : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfacePred P) (hf : 𝚺-[m + 1].BoldfaceFunction f) :
    Γ-[m + 1].Boldface (fun v ↦ P (f v)) :=
  Boldface.substitution (f := ![f]) hP (by simpa using hf)

lemma BoldfaceRel.comp {P : V → V → Prop} {k} {f g : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel P)
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (hg : 𝚺-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface fun v ↦ P (f v) (g v) :=
  Boldface.substitution (f := ![f, g]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma BoldfaceRel₃.comp {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₃ P)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma BoldfaceRel₄.comp {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₄ P)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃, f₄]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma BoldfaceRel₅.comp {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hP : Γ-[m + 1].BoldfaceRel₅ P)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄)
    (hf₅ : 𝚺-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Boldface.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])

namespace Boldface

lemma comp₁ {k} {P : V → Prop} {f : (Fin k → V) → V}
    [Γ-[m + 1].BoldfacePred P]
    (hf : 𝚺-[m + 1].BoldfaceFunction f) : Γ-[m + 1].Boldface fun v ↦ P (f v) :=
  BoldfacePred.comp inferInstance hf

lemma comp₂ {k} {P : V → V → Prop} {f g : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel P]
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (hg : 𝚺-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].Boldface (fun v ↦ P (f v) (g v)) :=
  BoldfaceRel.comp inferInstance hf hg

lemma comp₃ {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₃ P]
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂) (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceRel₃.comp inferInstance hf₁ hf₂ hf₃

lemma comp₄ {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₄ P]
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceRel₄.comp inferInstance hf₁ hf₂ hf₃ hf₄

lemma comp₅ {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    [Γ-[m + 1].BoldfaceRel₅ P]
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄)
    (hf₅ : 𝚺-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].Boldface (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceRel₅.comp inferInstance hf₁ hf₂ hf₃ hf₄ hf₅

end Boldface

section

variable {ℌ : HierarchySymbol}

lemma BoldfacePred.of_iff {P Q : V → Prop}
    (H : ℌ.BoldfacePred Q) (h : ∀ x, P x ↔ Q x) : ℌ.BoldfacePred P := by
  rwa [show P = Q from by funext v; simp [h]]

instance BoldfaceFunction₁.graph {f : V → V} [h : ℌ.BoldfaceFunction₁ f] :
  ℌ.BoldfaceRel (Function.Graph f) := h

instance BoldfaceFunction₂.graph {f : V → V → V} [h : ℌ.BoldfaceFunction₂ f] :
  ℌ.BoldfaceRel₃ (Function.Graph₂ f) := h

instance BoldfaceFunction₃.graph {f : V → V → V → V} [h : ℌ.BoldfaceFunction₃ f] :
  ℌ.BoldfaceRel₄ (Function.Graph₃ f) := h

end

namespace BoldfaceFunction

variable {ℌ : HierarchySymbol}

lemma graph_delta {k} {f : (Fin k → V) → V}
    (h : 𝚺-[m].BoldfaceFunction f) : 𝚫-[m].BoldfaceFunction f := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.graphDelta, by
    cases' m with m
    case zero => simp [HierarchySymbol.Semiformula.graphDelta]
    case succ =>
      simp only [Semiformula.graphDelta]
      intro e; simp [Empty.eq_elim, h.df.iff]; tauto,
  by intro v; simp [h.df.iff]⟩

instance {k} {f : (Fin k → V) → V} [h : 𝚺-[m].BoldfaceFunction f] : 𝚫-[m].BoldfaceFunction f :=
  BoldfaceFunction.graph_delta h

instance {k} {f : (Fin k → V) → V} [𝚺₀.BoldfaceFunction f] : ℌ.BoldfaceFunction f := inferInstance

lemma of_sigmaOne {k} {f : (Fin k → V) → V}
    (h : 𝚺₁.BoldfaceFunction f) {Γ m} : Γ-[m + 1].BoldfaceFunction f := Boldface.of_deltaOne (graph_delta h)

@[simp] lemma var {k} (i : Fin k) : ℌ.BoldfaceFunction (fun v : Fin k → V ↦ v i) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. x = !!#i.succ” (by simp), by intro _; simp⟩

@[simp] lemma const {k} (c : V) : ℌ.BoldfaceFunction (fun _ : Fin k → V ↦ c) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. #0 = &c” (by simp), by intro v; simp⟩

@[simp] lemma term_retraction (t : Semiterm ℒₒᵣ V n) (e : Fin n → Fin k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V (fun x ↦ v (e x)) id t :=
  .of_zero (Γ' := 𝚺)
    ⟨.mkSigma “x. x = !!(Rew.substs (fun x ↦ #(e x).succ) t)” (by simp), by intro v; simp [Semiterm.val_substs]⟩

@[simp] lemma term (t : Semiterm ℒₒᵣ V k) :
    ℌ.BoldfaceFunction fun v : Fin k → V ↦ Semiterm.valm V v id t :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. x = !!(Rew.bShift t)” (by simp), by intro v; simp [Semiterm.val_bShift']⟩

lemma of_eq {f : (Fin k → V) → V} (g) (h : ∀ v, f v = g v) (H : ℌ.BoldfaceFunction f) : ℌ.BoldfaceFunction g := by
  rwa [show g = f from by funext v; simp [h]]

lemma retraction {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f) (e : Fin k → Fin n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ v (e i)) := by
  have := Boldface.retraction (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff (by intro x; simp)

lemma retractiont {n k} {f : (Fin k → V) → V} (hf : ℌ.BoldfaceFunction f) (t : Fin k → Semiterm ℒₒᵣ V n) :
    ℌ.BoldfaceFunction fun v ↦ f (fun i ↦ Semiterm.valm V v id (t i)) := by
  have := Boldface.retractiont (n := n + 1) hf (#0 :> fun i ↦ Rew.bShift (t i)); simp at this
  exact this.of_iff (by intro x; simp [Semiterm.val_bShift'])

lemma rel {f : (Fin k → V) → V} (h : ℌ.BoldfaceFunction f) :
  ℌ.Boldface (fun v ↦ v 0 = f (v ·.succ)) := h

@[simp] lemma nth (ℌ : HierarchySymbol) (i : Fin k) : ℌ.BoldfaceFunction fun w : Fin k → V ↦ w i := by
  apply Boldface.of_zero (Γ' := 𝚺)
  exact ⟨.mkSigma “x. x = #i.succ” (by simp), by intro v; simp⟩

lemma substitution {f : Fin k → (Fin l → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction F) (hf : ∀ i, 𝚺-[m + 1].BoldfaceFunction (f i)) :
    Γ-[m + 1].BoldfaceFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using Boldface.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases' i using Fin.cases with i
    · simp
    · simpa using Boldface.retraction (hf i) (0 :> (·.succ.succ))

end BoldfaceFunction

lemma BoldfaceFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₁ F) (hf : 𝚺-[m + 1].BoldfaceFunction f) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f v)) :=
  BoldfaceFunction.substitution (f := ![f]) hF (by simp [hf])

lemma BoldfaceFunction₂.comp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₂ F)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma BoldfaceFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₃ F)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma BoldfaceFunction₄.comp {k} {F : V → V → V → V → V} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₄ F)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃, f₄]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma BoldfaceFunction₅.comp {k} {F : V → V → V → V → V → V} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hF : Γ-[m + 1].BoldfaceFunction₅ F)
    (hf₁ : 𝚺-[m + 1].BoldfaceFunction f₁) (hf₂ : 𝚺-[m + 1].BoldfaceFunction f₂)
    (hf₃ : 𝚺-[m + 1].BoldfaceFunction f₃) (hf₄ : 𝚺-[m + 1].BoldfaceFunction f₄)
    (hf₅ : 𝚺-[m + 1].BoldfaceFunction f₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  BoldfaceFunction.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

namespace BoldfaceFunction

lemma comp₁ {k} {f : V → V} [Γ-[m + 1].BoldfaceFunction₁ f]
    {g : (Fin k → V) → V} (hg : 𝚺-[m + 1].BoldfaceFunction g) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g v)) :=
  BoldfaceFunction₁.comp inferInstance hg

lemma comp₂{k} {f : V → V → V} [Γ-[m + 1].BoldfaceFunction₂ f]
    {g₁ g₂ : (Fin k → V) → V} (hg₁ : 𝚺-[m + 1].BoldfaceFunction g₁) (hg₂ : 𝚺-[m + 1].BoldfaceFunction g₂) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v)) :=
  BoldfaceFunction₂.comp inferInstance hg₁ hg₂

lemma comp₃ {k} {f : V → V → V → V} [Γ-[m + 1].BoldfaceFunction₃ f]
    {g₁ g₂ g₃ : (Fin k → V) → V}
    (hg₁ : 𝚺-[m + 1].BoldfaceFunction g₁) (hg₂ : 𝚺-[m + 1].BoldfaceFunction g₂) (hg₃ : 𝚺-[m + 1].BoldfaceFunction g₃) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  BoldfaceFunction₃.comp inferInstance hg₁ hg₂ hg₃

lemma comp₄ {k} {f : V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₄ f]
    {g₁ g₂ g₃ g₄ : (Fin k → V) → V}
    (hg₁ : 𝚺-[m + 1].BoldfaceFunction g₁) (hg₂ : 𝚺-[m + 1].BoldfaceFunction g₂)
    (hg₃ : 𝚺-[m + 1].BoldfaceFunction g₃) (hg₄ : 𝚺-[m + 1].BoldfaceFunction g₄) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v)) :=
  BoldfaceFunction₄.comp inferInstance hg₁ hg₂ hg₃ hg₄

lemma comp₅ {k} {f : V → V → V → V → V → V} [Γ-[m + 1].BoldfaceFunction₅ f]
    {g₁ g₂ g₃ g₄ g₅ : (Fin k → V) → V}
    (hg₁ : 𝚺-[m + 1].BoldfaceFunction g₁) (hg₂ : 𝚺-[m + 1].BoldfaceFunction g₂)
    (hg₃ : 𝚺-[m + 1].BoldfaceFunction g₃) (hg₄ : 𝚺-[m + 1].BoldfaceFunction g₄)
    (hg₅ : 𝚺-[m + 1].BoldfaceFunction g₅) :
    Γ-[m + 1].BoldfaceFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₅ v)) :=
  BoldfaceFunction₅.comp inferInstance hg₁ hg₂ hg₃ hg₄ hg₅

end BoldfaceFunction

namespace Boldface

lemma ball_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] φ.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ➝ (∀[“#0 < #1”] φ.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] φ.sigma.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ➝ (∀[“#0 < #1”] φ.pi.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma bex_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] φ.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ➝ (∃[“#0 < #1”] φ.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] φ.sigma.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ➝ (∃[“#0 < #1”] φ.pi.val ⇜ (#0 :> (#·.succ.succ))))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma ball_le [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Boldface (fun v ↦ ∀ x < f v + 1, P v x) := ball_lt (BoldfaceFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma bex_le [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∃ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Boldface (fun v ↦ ∃ x < f v + 1, P v x) := bex_lt (BoldfaceFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma ball_lt' {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x < f v → P v x) := ball_lt hf h

lemma ball_le' [V ⊧ₘ* 𝐏𝐀⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].BoldfaceFunction f) (h : Γ-[m + 1].Boldface (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Boldface (fun v ↦ ∀ {x}, x ≤ f v → P v x) := ball_le hf h

end Boldface

end

end Arithmetic.HierarchySymbol

end LO.FirstOrder
