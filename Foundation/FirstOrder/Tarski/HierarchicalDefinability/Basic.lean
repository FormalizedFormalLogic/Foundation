module

public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Hierarchy
public import Foundation.FirstOrder.Tarski.Definability

/-!
# Definability in a bounding hierarchy

This set-parametric formulation follows the arithmetical definability API. Delta formulas
are pairs of Sigma and Pi formulas, with equivalence required separately on the structure.
The closure properties are standard elementary facts about definability; their formulation
with bounding operators and the semantic induction principle are specific to this formalization.
-/

@[expose] public section

-- Retain the established arithmetic API's implicit index binders in this port.
set_option autoImplicit true

namespace FFL.FirstOrder.Bounding

open scoped Bounding

namespace HierarchySymbol

variable {L : Language} {ℬ : FirstOrder.Bounding L}

variable {V : Type*} [Tarski.Structure L V]

abbrev IsDefinedBy (R : (Fin k → V) → Prop) : {ℌ : HierarchySymbol ℬ} → ℌ.Semisentence k → Prop
  | 𝚺-[ℬ, _], φ => FirstOrder.IsDefinedBy R φ.val
  | 𝚷-[ℬ, _], φ => FirstOrder.IsDefinedBy R φ.val
  | 𝚫-[ℬ, _], φ => φ.ProperOn V ∧ FirstOrder.IsDefinedBy R φ.val

abbrev IsDefinedByWithParam (R : (Fin k → V) → Prop) :
    {ℌ : HierarchySymbol ℬ} → ℌ.Semiformula V k → Prop
  | 𝚺-[ℬ, _], φ => FirstOrder.IsDefinedByWithParam R φ.val
  | 𝚷-[ℬ, _], φ => FirstOrder.IsDefinedByWithParam R φ.val
  | 𝚫-[ℬ, _], φ => φ.ProperWithParamOn V ∧ FirstOrder.IsDefinedByWithParam R φ.val

class Defined (R : outParam ((Fin k → V) → Prop)) {ℌ : HierarchySymbol ℬ}
    (φ : ℌ.Semisentence k) where
  defined : IsDefinedBy R φ

variable {ℌ : HierarchySymbol ℬ} {Γ : SigmaPiDelta}

variable (ℌ)

class Definable {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : ℌ.Semiformula V k, IsDefinedByWithParam P φ

abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ

abbrev DefinedRel (R : V → V → Prop) (φ : ℌ.Semisentence 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : ℌ.Semisentence 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : ℌ.Semisentence 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

variable {ℌ}

abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop :=
  Defined (fun v ↦ v 0 = f (v ·.succ)) φ

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

abbrev DefinablePred (P : V → Prop) : Prop := ℌ.Definable (k := 1) (fun v ↦ P (v 0))

abbrev DefinableRel (P : V → V → Prop) : Prop := ℌ.Definable (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : V → V → V → Prop) : Prop :=
  ℌ.Definable (k := 3) fun v ↦ P (v 0) (v 1) (v 2)

abbrev DefinableRel₄ (P : V → V → V → V → Prop) : Prop :=
  ℌ.Definable (k := 4) fun v ↦ P (v 0) (v 1) (v 2) (v 3)

abbrev DefinableRel₅ (P : V → V → V → V → V → Prop) : Prop :=
  ℌ.Definable (k := 5) fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4)

abbrev DefinableRel₆ (P : V → V → V → V → V → V → Prop) : Prop :=
  ℌ.Definable (k := 6) fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)

abbrev DefinableFunction (f : (Fin k → V) → V) : Prop :=
  ℌ.Definable (k := k + 1) fun v ↦ v 0 = f (v ·.succ)

abbrev DefinableFunction₀ (c : V) : Prop := ℌ.DefinableFunction (k := 0) (fun _ ↦ c)

abbrev DefinableFunction₁ (f : V → V) : Prop := ℌ.DefinableFunction (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : V → V → V) : Prop :=
  ℌ.DefinableFunction (k := 2) fun v ↦ f (v 0) (v 1)

abbrev DefinableFunction₃ (f : V → V → V → V) : Prop :=
  ℌ.DefinableFunction (k := 3) fun v ↦ f (v 0) (v 1) (v 2)

abbrev DefinableFunction₄ (f : V → V → V → V → V) : Prop :=
  ℌ.DefinableFunction (k := 4) fun v ↦ f (v 0) (v 1) (v 2) (v 3)

abbrev DefinableFunction₅ (f : V → V → V → V → V → V) : Prop :=
  ℌ.DefinableFunction (k := 5) fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4)

variable {ℌ}

variable {k} {P Q : (Fin k → V) → Prop}

namespace Defined

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} (h : Defined R φ) :
  FirstOrder.IsDefinedBy R φ.val :=
  match ℌ with
  | 𝚺-[ℬ, _] => h.defined
  | 𝚷-[ℬ, _] => h.defined
  | 𝚫-[ℬ, _] => h.defined.2

@[simp] lemma proper {R : (Fin k → V) → Prop} {m} {φ : 𝚫-[ℬ, m].Semisentence k}
    [h : Defined R φ] : φ.ProperOn V := h.defined.1

@[simp] lemma iff {R : (Fin k → V) → Prop} {φ : ℌ.Semisentence k} [h : Defined R φ] :
    φ.val.Evalb v ↔ R v := h.df _

@[simp] lemma iff_delta_pi {R : (Fin k → V) → Prop} {φ : (𝚫-[ℬ, m]).Semisentence k}
    [h : Defined R φ] : φ.pi.val.Evalb v ↔ R v := by
  simp [h.proper.iff']

@[simp] lemma iff_delta_sigma {R : (Fin k → V) → Prop} {φ : (𝚫-[ℬ, m]).Semisentence k}
    [h : Defined R φ] : φ.sigma.val.Evalb v ↔ R v := by simp [h.proper.iff]

lemma of_zero {R : (Fin k → V) → Prop} {φ : 𝚺-[ℬ, 0].Semisentence k}
    (h : Defined R φ) : Defined R (φ.ofZero ℌ) := Defined.mk <|
  match ℌ with
  | 𝚺-[ℬ, m] => by intro _; simp
  | 𝚷-[ℬ, m] => by intro _; simp
  | 𝚫-[ℬ, m] =>
    ⟨HierarchySymbol.Semiformula.ProperOn.of_zero (ℬ := ℬ) (M := V)
        (Γ' := 𝚺) φ m, by intro _; simp⟩

lemma of_iff {P Q : (Fin k → V) → Prop} (h : ∀ x, P x ↔ Q x)
    {φ : ℌ.Semisentence k} (H : Defined Q φ) : Defined P φ := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable (φ : ℌ.Semisentence k) (hP : Defined P φ) :
    ℌ.Definable P := ⟨φ.rew Rew.emb, by
      match ℌ with
      | 𝚺-[ℬ, _] => intro; simp [hP.iff]
      | 𝚷-[ℬ, _] => intro; simp [hP.iff]
      | 𝚫-[ℬ, _] => exact ⟨
          fun v ↦ by rcases φ; simpa [HierarchySymbol.Semiformula.rew]
            using hP.proper.rew Rew.emb v,
          by intro; simp⟩⟩

lemma to_definable₀ {φ : 𝚺-[ℬ, 0].Semisentence k} (hP : Defined P φ) :
    ℌ.Definable P := Defined.to_definable (φ.ofZero ℌ) hP.of_zero

end Defined

namespace DefinedFunction

lemma of_eq {f g : (Fin k → V) → V} (h : ∀ x, f x = g x)
    {φ : ℌ.Semisentence (k + 1)} (H : DefinedFunction f φ) : DefinedFunction g φ :=
  Defined.of_iff (by intro; simp [h]) H

lemma graph_delta [L.Eq] [Tarski.Structure.Eq L V] {f : (Fin k → V) → V}
    {φ : 𝚺-[ℬ, m].Semisentence (k + 1)}
    (h : DefinedFunction f φ) : DefinedFunction f φ.graphDelta :=
  ⟨by
      cases m with
      | zero =>
        exact HierarchySymbol.Semiformula.ProperOn.of_zero (ℬ := ℬ) (M := V)
          (Γ' := 𝚺) φ 0
      | succ m =>
        simp only [Semiformula.graphDelta]
        intro e
        simp; tauto,
   by intro v; simp⟩

end DefinedFunction

namespace IsDefinedByWithParam

lemma df {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : IsDefinedByWithParam R φ) :
  FirstOrder.IsDefinedByWithParam R φ.val :=
  match ℌ with
  | 𝚺-[ℬ, _] => h
  | 𝚷-[ℬ, _] => h
  | 𝚫-[ℬ, _] => h.2

lemma iff {R : (Fin k → V) → Prop} {φ : ℌ.Semiformula V k} (h : IsDefinedByWithParam R φ) {v} :
    φ.val.Eval v id ↔ R v := h.df _

lemma proper {R : (Fin k → V) → Prop} {m} {φ : 𝚫-[ℬ, m].Semiformula V k}
    (h : IsDefinedByWithParam R φ) : φ.ProperWithParamOn V := h.1

end IsDefinedByWithParam

namespace DefinableRel

@[simp] instance eq [L.Eq] [Tarski.Structure.Eq L V] : ℌ.DefinableRel (Eq : V → V → Prop) :=
  Defined.to_definable₀ (φ := .mkSigma “#0 = #1” (Hierarchy.of_open (by simp))) ⟨by intro _; simp⟩

@[simp] instance lt [L.LT] [LT V] [Tarski.Structure.LT L V] :
    ℌ.DefinableRel (LT.lt : V → V → Prop) :=
  Defined.to_definable₀ (φ := .mkSigma “#0 < #1” (Hierarchy.of_open (by simp))) ⟨by intro _; simp⟩

@[simp] instance mem [L.Mem] [Membership V V] [Tarski.Structure.Mem L V] :
    ℌ.DefinableRel (fun x y : V ↦ x ∈ y) :=
  Defined.to_definable₀ (φ := .mkSigma “#0 ∈ #1” (Hierarchy.of_open (by simp))) ⟨by intro _; simp⟩

end DefinableRel

namespace Definable

lemma mk' {ℌ : HierarchySymbol ℬ} (φ : ℌ.Semiformula V k) (H : IsDefinedByWithParam P φ) :
  ℌ.Definable P := ⟨φ, H⟩

lemma mkPolarity {Γ : Polarity} (φ : FirstOrder.Semiformula L V k)
    (hp : ℬ.Hierarchy Γ m φ) (hP : ∀ v, P v ↔ φ.Eval v id) :
    Γ-[ℬ, m].Definable P :=
  match Γ with
  | 𝚺 => ⟨.mkSigma φ hp, by intro v; simp [hP]⟩
  | 𝚷 => ⟨.mkPi φ hp, by intro v; simp [hP]⟩

lemma of_zero (h : (Γ'-[ℬ, 0]).Definable P) {ℌ : HierarchySymbol ℬ} : ℌ.Definable P := by
  rcases h with ⟨φ, hφ⟩
  apply Definable.mk' (φ.ofZero ℌ)
  match ℌ with
  | 𝚺-[ℬ, m] | 𝚷-[ℬ, m] => intro _; simp [hφ.iff]
  | 𝚫-[ℬ, m] =>
    constructor
    · simp [HierarchySymbol.Semiformula.ProperWithParamOn,
        HierarchySymbol.Semiformula.ofZero]
    · intro _; simp [hφ.iff]

instance [𝚺-[ℬ, 0].Definable P] (ℌ : HierarchySymbol ℬ) :
    ℌ.Definable P := of_zero (Γ' := 𝚺) inferInstance

lemma of_deltaOne {Γ m} (h : 𝚫-[ℬ, 1].Definable P) : Γ-[ℬ, m+1].Definable P := by
  rcases h with ⟨φ, h⟩
  apply Definable.mk' (φ.ofDeltaOne Γ m)
  match Γ with
  | 𝚺 => intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.iff,
    HierarchySymbol.Semiformula.val_sigma]
  | 𝚷 => intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.iff, h.proper.iff']
  | 𝚫 => exact ⟨by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.iff,
    HierarchySymbol.Semiformula.val_sigma, h.proper.iff'],
    by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff,
      HierarchySymbol.Semiformula.val_sigma]⟩

lemma of_delta (h : 𝚫-[ℬ, m].Definable P) : Γ-[ℬ, m].Definable P := by
  rcases h with ⟨φ, h⟩
  match Γ with
  | 𝚺 => exact ⟨φ.sigma, by intro v; simp [HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | 𝚷 => exact ⟨φ.pi, by intro v; simp [←h.proper v, HierarchySymbol.Semiformula.val_sigma,
    h.df.iff]⟩
  | 𝚫 => exact ⟨φ, h⟩

instance [𝚫-[ℬ, m].Definable P] (Γ) : Γ-[ℬ, m].Definable P := of_delta inferInstance

lemma delta_iff_sigma_and_pi : 𝚫-[ℬ, m].Definable P ↔
    𝚷-[ℬ, m].Definable P ∧ 𝚺-[ℬ, m].Definable P := by
  constructor
  · intro h
    exact ⟨of_delta (Γ := 𝚷) h, of_delta (Γ := 𝚺) h⟩
  · rintro ⟨hπ, hσ⟩
    rcases hσ with ⟨φ, hφ⟩
    rcases hπ with ⟨ψ, hψ⟩
    exact ⟨.mkDelta φ ψ, by intro v; simp [hφ.df.iff, hψ.df.iff],
      by intro v; simp [hφ.df.iff]⟩

lemma of_sigma_of_pi (hσ : 𝚺-[ℬ, m].Definable P) (hπ : 𝚷-[ℬ, m].Definable P) :
    Γ-[ℬ, m].Definable P :=
  match Γ with
  | 𝚺 => hσ
  | 𝚷 => hπ
  | 𝚫 => by
    rcases hσ with ⟨φ, hp⟩; rcases hπ with ⟨ψ, hq⟩
    exact ⟨.mkDelta φ ψ, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩

lemma of_lt {C : HierarchySymbol ℬ} {s : ℕ} (hP : C.Definable P) (h : C.rank < s) :
    Γ-[ℬ, s].Definable P := by
  rcases hP with ⟨φ, hφ⟩
  exact .of_sigma_of_pi
    (.mkPolarity (Γ := 𝚺) φ.val (φ.hierarchy_of_lt h) fun _ ↦ hφ.iff.symm)
    (.mkPolarity (Γ := 𝚷) φ.val (φ.hierarchy_of_lt h) fun _ ↦ hφ.iff.symm)

lemma of_iff (H : ℌ.Definable Q) (h : ∀ x, P x ↔ Q x) : ℌ.Definable P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma retraction (h : ℌ.Definable P) (f : Fin k → Fin l) :
    ℌ.Definable fun v ↦ P fun i ↦ v (f i) := by
  rcases h with ⟨φ, h⟩
  apply Definable.mk' (φ.rew <| Rew.subst fun x ↦ #(f x))
  match ℌ with
  | 𝚺-[ℬ, _] | 𝚷-[ℬ, _] => intro; simp [h.iff, Function.comp_def]
  | 𝚫-[ℬ, _] => exact ⟨h.proper.rew _, by intro; simp [h.iff, Function.comp_def]⟩

lemma retractiont (h : ℌ.Definable P) (f : Fin k → Semiterm L V n) :
    ℌ.Definable fun v ↦ P (fun i ↦ (f i).val v id) := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.rew (Rew.subst f),
  match ℌ with
  | 𝚺-[ℬ, _] | 𝚷-[ℬ, _] => by intro; simp [h.df.iff, Function.comp_def]
  | 𝚫-[ℬ, _] => ⟨h.proper.rew _, by intro; simp [h.df.iff, Function.comp_def]⟩⟩

@[simp] instance const {P : Prop} : ℌ.Definable (fun _ : Fin k → V ↦ P) := by
  by_cases hP : P
  · apply Definable.mk' ⊤
    match ℌ with
    | 𝚺-[ℬ, m] | 𝚷-[ℬ, m] => intro v; simp [hP]
    | 𝚫-[ℬ, m] => exact ⟨by simp, by intro v; simp [hP]⟩
  · apply Definable.mk' ⊥
    match ℌ with
    | 𝚺-[ℬ, m] | 𝚷-[ℬ, m] => intro v; simp [hP]
    | 𝚫-[ℬ, m] => exact ⟨by simp, by intro v; simp [hP]⟩

lemma and (hP : ℌ.Definable P) (hQ : ℌ.Definable Q) : ℌ.Definable fun x ↦ P x ∧ Q x := by
  rcases hP with ⟨φ, hP⟩
  rcases hQ with ⟨ψ, hQ⟩
  apply Definable.mk' (φ ⋏ ψ)
  match ℌ with
  | 𝚺-[ℬ, m] | 𝚷-[ℬ, m] => intro v; simp [hP.iff, hQ.iff]
  | 𝚫-[ℬ, m] => exact ⟨hP.proper.and hQ.proper, by intro v; simp [hP.iff, hQ.iff]⟩

lemma or (hP : ℌ.Definable P) (hQ : ℌ.Definable Q) : ℌ.Definable fun x ↦ P x ∨ Q x := by
  rcases hP with ⟨φ, hP⟩
  rcases hQ with ⟨ψ, hQ⟩
  apply Definable.mk' (φ ⋎ ψ)
  match ℌ with
  | 𝚺-[ℬ, m] | 𝚷-[ℬ, m] => intro v; simp [hP.iff, hQ.iff]
  | 𝚫-[ℬ, m] => exact ⟨hP.proper.or hQ.proper, by intro v; simp [hP.iff, hQ.iff]⟩

lemma notSigma (h : 𝚺-[ℬ, m].Definable P) : 𝚷-[ℬ, m].Definable fun x ↦ ¬P x := by
  rcases h with ⟨φ, h⟩; exact Definable.mk' φ.negSigma fun v ↦ by simp [h.iff]

lemma notPi (h : 𝚷-[ℬ, m].Definable P) : 𝚺-[ℬ, m].Definable fun x ↦ ¬P x := by
  rcases h with ⟨φ, h⟩
  exact Definable.mk' φ.negPi fun v ↦ by simp [h.iff]

lemma notDelta (h : 𝚫-[ℬ, m].Definable P) : 𝚫-[ℬ, m].Definable fun x ↦ ¬P x := by
  rcases h with ⟨φ, h⟩
  exact Definable.mk' (∼φ) ⟨h.proper.neg, by intro v; simp [h.proper.eval_neg, h.iff]⟩

lemma not (h : Γ.alt-[ℬ, m].Definable P) :
    Γ-[ℬ, m].Definable (fun v ↦ ¬P v) :=
  match Γ with
  | 𝚺 => h.notPi
  | 𝚷 => h.notSigma
  | 𝚫 => h.notDelta

lemma impDelta (hp : 𝚫-[ℬ, m].Definable P) (hq : 𝚫-[ℬ, m].Definable Q) :
    𝚫-[ℬ, m].Definable fun x ↦ P x → Q x := (hp.notDelta.or hq).of_iff (by intro x; simp
      [imp_iff_not_or])

lemma imp (h₁ : Γ.alt-[ℬ, m].Definable P) (h₂ : Γ-[ℬ, m].Definable Q) :
    Γ-[ℬ, m].Definable (fun v ↦ P v → Q v) :=
  (h₁.not.or h₂).of_iff fun _ ↦ imp_iff_not_or

lemma biconditional (h₁ : 𝚫-[ℬ, m].Definable P) (h₂ : 𝚫-[ℬ, m].Definable Q) {Γ} :
    Γ-[ℬ, m].Definable (fun v ↦ P v ↔ Q v) :=
  .of_delta <| ((h₁.impDelta h₂).and (h₂.impDelta h₁)).of_iff <| by intro v; simp
    [iff_iff_implies_and_implies]

lemma ball {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm L V k) :
    ℌ.Definable fun v ↦ ∀ x, R.val ![x, t.val v id] → P v x := by
  rcases h with ⟨φ, h⟩
  match ℌ with
  | 𝚺-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.ball hR t φ, by intro v; simp [h.iff]⟩
  | 𝚷-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.ball hR t φ, by intro v; simp [h.iff]⟩
  | 𝚫-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.ball hR t φ, ⟨h.proper.ball hR,
    by intro v; simp [h.iff]⟩⟩

lemma bexs {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm L V k) :
    ℌ.Definable fun v ↦ ∃ x, R.val ![x, t.val v id] ∧ P v x := by
  rcases h with ⟨φ, h⟩
  match ℌ with
  | 𝚺-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.bexs hR t φ, by intro v; simp [h.iff]⟩
  | 𝚷-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.bexs hR t φ, by intro v; simp [h.iff]⟩
  | 𝚫-[ℬ, m] => exact ⟨HierarchySymbol.Semiformula.bexs hR t φ, ⟨h.proper.bexs hR,
    by intro v; simp [h.iff]⟩⟩

lemma exs {P : (Fin k → V) → V → Prop} (h : 𝚺-[ℬ, m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    𝚺-[ℬ, m + 1].Definable fun v ↦ ∃ x, P v x := by
  rcases h with ⟨φ, h⟩; exact ⟨φ.exs, by intro _; simp [h.iff]⟩

lemma all {P : (Fin k → V) → V → Prop} (h : 𝚷-[ℬ, m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    𝚷-[ℬ, m + 1].Definable fun v ↦ ∀ x, P v x := by
  rcases h with ⟨φ, h⟩; exact ⟨φ.all, by intro _; simp [h.iff]⟩

lemma ballCons {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin (k + 1) → V) → Prop}
    (h : ℌ.Definable P) (t : Semiterm L V k) :
    ℌ.Definable fun v ↦ ∀ x, R.val ![x, t.val v id] → P (x :> v) :=
  ball hR (P := fun v x ↦ P (x :> v)) (h.of_iff fun w ↦ by simp) t

lemma bexsCons {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin (k + 1) → V) → Prop}
    (h : ℌ.Definable P) (t : Semiterm L V k) :
    ℌ.Definable fun v ↦ ∃ x, R.val ![x, t.val v id] ∧ P (x :> v) :=
  bexs hR (P := fun v x ↦ P (x :> v)) (h.of_iff fun w ↦ by simp) t

lemma exsCons {P : (Fin (k + 1) → V) → Prop} (h : 𝚺-[ℬ, m + 1].Definable P) :
    𝚺-[ℬ, m + 1].Definable fun v ↦ ∃ x, P (x :> v) :=
  exs (P := fun v x ↦ P (x :> v)) (h.of_iff fun w ↦ by simp)

lemma conj₂ (Γ : List ι) {R : ι → (Fin k → V) → Prop} (hR : ∀ i, ℌ.Definable (R i)) :
    ℌ.Definable fun x ↦ ∀ i ∈ Γ, R i x :=
  match Γ with
  |          [] => by simp
  |         [i] => by simpa using hR i
  | i :: j :: Γ => by simpa using (hR i).and (conj₂ (j :: Γ) hR)

lemma disj₂ (Γ : List ι) {R : ι → (Fin k → V) → Prop} (hR : ∀ i, ℌ.Definable (R i)) :
    ℌ.Definable fun x ↦ ∃ i ∈ Γ, R i x :=
  match Γ with
  |          [] => by simp
  |         [i] => by simpa using hR i
  | i :: j :: Γ => by simpa using (hR i).or (disj₂ (j :: Γ) hR)

open Classical in
lemma fconj (s : Finset ι) {R : ι → (Fin k → V) → Prop} (h : ∀ i, ℌ.Definable (R i)) :
    ℌ.Definable fun x ↦ ∀ i ∈ s, R i x := by simpa using conj₂ s.toList h

open Classical in
lemma fdisj (s : Finset ι) {R : ι → (Fin k → V) → Prop} (h : ∀ i, ℌ.Definable (R i)) :
    ℌ.Definable fun x ↦ ∃ i ∈ s, R i x := by simpa using disj₂ s.toList h

lemma fintype_all {ι : Type*} [Finite ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Definable fun w : Fin k → V ↦ P i w) :
    ℌ.Definable fun v : Fin k → V ↦ ∀ i, P i v := by
  classical
  simpa using fconj (s := @Finset.univ ι (Fintype.ofFinite ι)) h

lemma fintype_exs {ι : Type*} [Finite ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, ℌ.Definable fun w : Fin k → V ↦ P i w) :
    ℌ.Definable fun v : Fin k → V ↦ ∃ i, P i v := by
  classical
  simpa using fdisj (s := @Finset.univ ι (Fintype.ofFinite ι)) h

lemma equal' [L.Eq] [Tarski.Structure.Eq L V] (i j : Fin k) : ℌ.Definable fun v : Fin k → V
  ↦ v i = v j := by
  simpa using retraction DefinableRel.eq ![i, j]

lemma of_sigma [L.Eq] [Tarski.Structure.Eq L V] {f : (Fin k → V) → V}
    (h : 𝚺-[ℬ, m].DefinableFunction f) {Γ} : Γ-[ℬ, m].DefinableFunction f := by
  cases m with
  | zero => exact of_zero h
  | succ m =>
    apply of_sigma_of_pi
    · exact h
    · have : 𝚷-[ℬ, m + 1].Definable fun v ↦ ∀ y, y = f (v ·.succ) → v 0 = y := all <| imp
        (by simpa using retraction h (0 :> (·.succ.succ)))
        (by simpa using equal' 1 0)
      exact this.of_iff fun v ↦ by simp

lemma exsVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝚺-[ℬ, m + 1].Definable fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦
      w (j.natAdd k))) :
    𝚺-[ℬ, m + 1].Definable fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝚺-[ℬ, m + 1].Definable fun v : Fin k → V ↦ ∃ y, ∃ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply exs
    apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦
      x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases i using Fin.cases with
        | zero => simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        | succ i => simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : 𝚷-[ℬ, m + 1].Definable fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦
      w (j.natAdd k))) :
    𝚷-[ℬ, m + 1].Definable fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices 𝚷-[ℬ, m + 1].Definable fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦
      x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases i using Fin.cases with
        | zero => simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        | succ i => simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

private lemma substitution_sigma {f : Fin k → (Fin l → V) → V}
    (hP : 𝚺-[ℬ, m + 1].Definable P)
    (hf : ∀ i, 𝚺-[ℬ, m + 1].DefinableFunction (f i)) :
    𝚺-[ℬ, m + 1].Definable fun z ↦ P (fun i ↦ f i z) := by
  have : 𝚺-[ℬ, m + 1].Definable fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys := by
    apply exsVec; apply and
    · apply fintype_all; intro i
      simpa using retraction (hf i) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro hP
      exact ⟨(f · v), by simp, hP⟩
    · rintro ⟨ys, hys, hP⟩
      have : ys = fun i ↦ f i v := funext hys
      rcases this; exact hP

private lemma substitution_pi {f : Fin k → (Fin l → V) → V}
    (hP : 𝚷-[ℬ, m + 1].Definable P)
    (hf : ∀ i, 𝚺-[ℬ, m + 1].DefinableFunction (f i)) :
    𝚷-[ℬ, m + 1].Definable fun z ↦ P (fun i ↦ f i z) := by
  have : 𝚷-[ℬ, m + 1].Definable fun z ↦ ∀ ys : Fin k → V, (∀ i, ys i = f i z) → P ys := by
    apply allVec; apply imp
    · apply fintype_all; intro i
      simpa using retraction (hf i) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro h ys e
      have : ys = (f · v) := funext e
      rcases this; exact h
    · intro h; apply h _ (by simp)

lemma substitution {f : Fin k → (Fin l → V) → V}
    (hP : Γ-[ℬ, m + 1].Definable P) (hf : ∀ i, 𝚺-[ℬ, m + 1].DefinableFunction (f i)) :
    Γ-[ℬ, m + 1].Definable fun z ↦ P (fun i ↦ f i z) :=
  match Γ with
  | 𝚺 => substitution_sigma hP hf
  | 𝚷 => substitution_pi hP hf
  | 𝚫 => of_sigma_of_pi (substitution_sigma (of_delta hP) hf) (substitution_pi (of_delta hP) hf)

end Definable

lemma DefinablePred.comp {P : V → Prop} {k} {f : (Fin k → V) → V}
    (hP : Γ-[ℬ, m + 1].DefinablePred P) (hf : 𝚺-[ℬ, m + 1].DefinableFunction f) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f v)) :=
  Definable.substitution (f := ![f]) hP (by simpa using hf)

lemma DefinableRel.comp {P : V → V → Prop} {k} {f g : (Fin k → V) → V}
    (hP : Γ-[ℬ, m + 1].DefinableRel P)
    (hf : 𝚺-[ℬ, m + 1].DefinableFunction f) (hg : 𝚺-[ℬ, m + 1].DefinableFunction g) :
    Γ-[ℬ, m + 1].Definable fun v ↦ P (f v) (g v) :=
  Definable.substitution (f := ![f, g]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf,
    hg])

lemma DefinableRel₃.comp {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hP : Γ-[ℬ, m + 1].DefinableRel₃ P)
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ,
    hf₁, hf₂, hf₃])

lemma DefinableRel₄.comp {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    (hP : Γ-[ℬ, m + 1].DefinableRel₄ P)
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃,
    f₄]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma DefinableRel₅.comp {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hP : Γ-[ℬ, m + 1].DefinableRel₅ P)
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄)
    (hf₅ : 𝚺-[ℬ, m + 1].DefinableFunction f₅) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄,
    f₅]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])

namespace Definable

lemma comp₁ {k} {P : V → Prop} {f : (Fin k → V) → V}
    [Γ-[ℬ, m + 1].DefinablePred P]
    (hf : 𝚺-[ℬ, m + 1].DefinableFunction f) : Γ-[ℬ, m + 1].Definable fun v ↦ P (f v) :=
  DefinablePred.comp inferInstance hf

lemma comp₂ {k} {P : V → V → Prop} {f g : (Fin k → V) → V}
    [Γ-[ℬ, m + 1].DefinableRel P]
    (hf : 𝚺-[ℬ, m + 1].DefinableFunction f) (hg : 𝚺-[ℬ, m + 1].DefinableFunction g) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f v) (g v)) :=
  DefinableRel.comp inferInstance hf hg

lemma comp₃ {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    [Γ-[ℬ, m + 1].DefinableRel₃ P]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableRel₃.comp inferInstance hf₁ hf₂ hf₃

lemma comp₄ {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [Γ-[ℬ, m + 1].DefinableRel₄ P]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  DefinableRel₄.comp inferInstance hf₁ hf₂ hf₃ hf₄

lemma comp₅ {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    [Γ-[ℬ, m + 1].DefinableRel₅ P]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄)
    (hf₅ : 𝚺-[ℬ, m + 1].DefinableFunction f₅) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  DefinableRel₅.comp inferInstance hf₁ hf₂ hf₃ hf₄ hf₅

end Definable

section

variable {ℌ : HierarchySymbol ℬ}

lemma DefinablePred.of_iff {P Q : V → Prop}
    (H : ℌ.DefinablePred Q) (h : ∀ x, P x ↔ Q x) : ℌ.DefinablePred P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma DefinableFunction.graph {f : (Fin k → V) → V} (h : ℌ.DefinableFunction f) :
  ℌ.Definable fun v ↦ v 0 = f (v ·.succ) := h

instance DefinableFunction₁.graph {f : V → V} [h : ℌ.DefinableFunction₁ f] :
  ℌ.DefinableRel (Function.Graph f) := h

instance DefinableFunction₂.graph {f : V → V → V} [h : ℌ.DefinableFunction₂ f] :
  ℌ.DefinableRel₃ (Function.Graph₂ f) := h

instance DefinableFunction₃.graph {f : V → V → V → V} [h : ℌ.DefinableFunction₃ f] :
  ℌ.DefinableRel₄ (Function.Graph₃ f) := h

end

namespace DefinableFunction

variable {ℌ : HierarchySymbol ℬ} {f : (Fin k → V) → V}

lemma graph_delta [L.Eq] [Tarski.Structure.Eq L V]
    (h : 𝚺-[ℬ, m].DefinableFunction f) : 𝚫-[ℬ, m].DefinableFunction f := by
  rcases h with ⟨φ, h⟩
  exact ⟨φ.graphDelta, by
    cases m with
    | zero =>
      exact HierarchySymbol.Semiformula.ProperWithParamOn.of_zero (ℬ := ℬ) (M := V)
        (Γ' := 𝚺) φ 0
    | succ m =>
      simp only [Semiformula.graphDelta]
      intro e; simp [h.df.iff]; tauto,
  by intro v; simp [h.df.iff]⟩

instance [L.Eq] [Tarski.Structure.Eq L V] [h : 𝚺-[ℬ, m].DefinableFunction f] :
  𝚫-[ℬ, m].DefinableFunction f :=
  DefinableFunction.graph_delta h

instance [𝚺-[ℬ, 0].DefinableFunction f] : ℌ.DefinableFunction f := inferInstance

lemma of_sigmaOne [L.Eq] [Tarski.Structure.Eq L V]
    (h : 𝚺-[ℬ, 1].DefinableFunction f) {Γ m} : Γ-[ℬ, m + 1].DefinableFunction f :=
      Definable.of_deltaOne (graph_delta h)

@[simp] lemma var [L.Eq] [Tarski.Structure.Eq L V] {k} (i : Fin k) :
    ℌ.DefinableFunction (fun v : Fin k → V ↦ v i) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. x = !!#i.succ” (Hierarchy.of_open (by simp)), by intro _; simp⟩

@[simp] lemma const [L.Eq] [Tarski.Structure.Eq L V] {k} (c : V) :
    ℌ.DefinableFunction (fun _ : Fin k → V ↦ c) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. #0 = &c” (Hierarchy.of_open (by simp)), by intro v; simp⟩

@[simp] lemma term_retraction [L.Eq] [Tarski.Structure.Eq L V] (t : Semiterm L V n)
    (e : Fin n → Fin k) :
    ℌ.DefinableFunction fun v : Fin k → V ↦ t.val (fun x ↦ v (e x)) id :=
  .of_zero (Γ' := 𝚺)
    ⟨.mkSigma “x. x = !!(Rew.subst (fun x ↦ #(e x).succ) t)” (Hierarchy.of_open (by simp)),
      fun v ↦ by
    simp [Semiterm.val_substs, Function.comp_def]⟩

@[simp] lemma term [L.Eq] [Tarski.Structure.Eq L V] (t : Semiterm L V k) :
    ℌ.DefinableFunction fun v : Fin k → V ↦ t.val v id :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x. x = !!(Rew.bShift t)” (Hierarchy.of_open (by simp)),
    fun v ↦ by simp [Semiterm.val_bShift']⟩

lemma of_eq (g) (h : ∀ v, f v = g v) (H : ℌ.DefinableFunction f) : ℌ.DefinableFunction g := by
  rwa [show g = f from by funext v; simp [h]]

lemma retraction {n} (hf : ℌ.DefinableFunction f) (e : Fin k → Fin n) :
    ℌ.DefinableFunction fun v ↦ f (fun i ↦ v (e i)) :=
  have : ℌ.Definable fun v ↦ v 0 = f fun x ↦ v (e x).succ :=
    Definable.retraction hf (0 :> fun i ↦ (e i).succ)
  this.of_iff (by intro x; simp)

lemma retractiont {n} (hf : ℌ.DefinableFunction f) (t : Fin k → Semiterm L V n) :
    ℌ.DefinableFunction fun v ↦ f (fun i ↦ (t i).val v id) :=
  have := Definable.retractiont (n := n + 1) hf (#0 :> fun i ↦ Rew.bShift (t i))
  this.of_iff (by intro x; simp [Semiterm.val_bShift'])

lemma rel (h : ℌ.DefinableFunction f) :
  ℌ.Definable (fun v ↦ v 0 = f (v ·.succ)) := h

@[simp] lemma nth [L.Eq] [Tarski.Structure.Eq L V] (ℌ : HierarchySymbol ℬ) (i : Fin k) :
  ℌ.DefinableFunction fun w : Fin k → V ↦ w i := by
  apply Definable.of_zero (Γ' := 𝚺)
  exact ⟨.mkSigma “x. x = #i.succ” (Hierarchy.of_open (by simp)), by intro v; simp⟩

lemma substitution [L.Eq] [Tarski.Structure.Eq L V] {f : Fin k → (Fin l → V) → V}
    (hF : Γ-[ℬ, m + 1].DefinableFunction F) (hf : ∀ i, 𝚺-[ℬ, m + 1].DefinableFunction (f i)) :
    Γ-[ℬ, m + 1].DefinableFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using Definable.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using Definable.retraction (hf i) (0 :> (·.succ.succ))

end DefinableFunction

lemma DefinableFunction₁.comp [L.Eq] [Tarski.Structure.Eq L V] {k} {F : V → V} {f : (Fin k → V) → V}
    [hF : Γ-[ℬ, m + 1].DefinableFunction₁ F] (hf : 𝚺-[ℬ, m + 1].DefinableFunction f) :
    Γ-[ℬ, m + 1].DefinableFunction (fun v ↦ F (f v)) :=
  DefinableFunction.substitution (f := ![f]) hF (by simp [hf])

lemma DefinableFunction₂.comp [L.Eq] [Tarski.Structure.Eq L V] {k} {F : V → V → V}
    {f₁ f₂ : (Fin k → V) → V}
    [hF : Γ-[ℬ, m + 1].DefinableFunction₂ F]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂) :
    Γ-[ℬ, m + 1].DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableFunction.substitution (f := ![f₁,
    f₂]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₃.comp [L.Eq] [Tarski.Structure.Eq L V] {k} {F : V → V → V → V}
    {f₁ f₂ f₃ : (Fin k → V) → V}
    [hF : Γ-[ℬ, m + 1].DefinableFunction₃ F]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) :
    Γ-[ℬ, m + 1].DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂,
    f₃]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₄.comp [L.Eq] [Tarski.Structure.Eq L V] {k} {F : V → V → V → V → V}
  {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [hF : Γ-[ℬ, m + 1].DefinableFunction₄ F]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄) :
    Γ-[ℬ, m + 1].DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃,
    f₄]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₅.comp [L.Eq] [Tarski.Structure.Eq L V] {k}
    {F : V → V → V → V → V → V} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    [hF : Γ-[ℬ, m + 1].DefinableFunction₅ F]
    (hf₁ : 𝚺-[ℬ, m + 1].DefinableFunction f₁) (hf₂ : 𝚺-[ℬ, m + 1].DefinableFunction f₂)
    (hf₃ : 𝚺-[ℬ, m + 1].DefinableFunction f₃) (hf₄ : 𝚺-[ℬ, m + 1].DefinableFunction f₄)
    (hf₅ : 𝚺-[ℬ, m + 1].DefinableFunction f₅) :
    Γ-[ℬ, m + 1].DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄,
    f₅]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

namespace Definable

lemma ball_operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {Γ}
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[ℬ, m + 1].DefinableFunction f)
    (h : Γ-[ℬ, m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ ∀ x, R.val ![x, f v] → P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃¹ (bf.val ⋏ (∀¹[R.operator ![#0, #1]] φ.val ⇜ (#0 :> (#·.succ.succ)))))
        (.exs (.and bf.sigma_prop (Hierarchy.ball hR (by simp) (φ.sigma_prop.rew _)))),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀¹ (bf.val 🡒 (∀¹[R.operator ![#0, #1]] φ.val ⇜ (#0 :> (#·.succ.succ)))))
        (.all (Hierarchy.imp_iff.mpr ⟨bf.sigma_prop,
          Hierarchy.ball hR (by simp) (φ.pi_prop.rew _)⟩)),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃¹ (bf.val ⋏ (∀¹[R.operator ![#0, #1]] φ.sigma.val ⇜ (#0 :> (#·.succ.succ)))))
        (.exs (.and bf.sigma_prop (Hierarchy.ball hR (by simp) (φ.sigma.sigma_prop.rew _)))),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀¹ (bf.val 🡒 (∀¹[R.operator ![#0, #1]] φ.pi.val ⇜ (#0 :> (#·.succ.succ)))))
        (.all (Hierarchy.imp_iff.mpr ⟨bf.sigma_prop,
          Hierarchy.ball hR (by simp) (φ.pi.pi_prop.rew _)⟩)),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma bexs_operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {Γ}
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[ℬ, m + 1].DefinableFunction f)
    (h : Γ-[ℬ, m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[ℬ, m + 1].Definable (fun v ↦ ∃ x, R.val ![x, f v] ∧ P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨φ, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃¹ (bf.val ⋏ (∃¹[R.operator ![#0, #1]] φ.val ⇜ (#0 :> (#·.succ.succ)))))
        (.exs (.and bf.sigma_prop (Hierarchy.bexs hR (by simp) (φ.sigma_prop.rew _)))),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀¹ (bf.val 🡒 (∃¹[R.operator ![#0, #1]] φ.val ⇜ (#0 :> (#·.succ.succ)))))
        (.all (Hierarchy.imp_iff.mpr ⟨bf.sigma_prop,
          Hierarchy.bexs hR (by simp) (φ.pi_prop.rew _)⟩)),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃¹ (bf.val ⋏ (∃¹[R.operator ![#0, #1]] φ.sigma.val ⇜ (#0 :> (#·.succ.succ)))))
        (.exs (.and bf.sigma_prop (Hierarchy.bexs hR (by simp) (φ.sigma.sigma_prop.rew _)))),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀¹ (bf.val 🡒 (∃¹[R.operator ![#0, #1]] φ.pi.val ⇜ (#0 :> (#·.succ.succ)))))
        (.all (Hierarchy.imp_iff.mpr ⟨bf.sigma_prop,
          Hierarchy.bexs hR (by simp) (φ.pi.pi_prop.rew _)⟩)),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

end Definable

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction₁.comp
  DefinableFunction₂.comp
  DefinableFunction₃.comp
  DefinableFunction₄.comp
  DefinableFunction₅.comp

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Definable.comp₁
  Definable.comp₂
  Definable.comp₃
  Definable.comp₄
  Definable.comp₅
  Definable.const

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.ball_operator
  Definable.bexs_operator

attribute [aesop 10 (rule_sets := [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.biconditional

attribute [aesop 11 (rule_sets := [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.exs

/-! ### Auxiliary lemmata for aesop  -/

section

variable (P : (Fin k → V) → Prop) (f : (Fin k → V) → V)

instance [𝚺-[ℬ, 1].Definable P] : 𝚺-[ℬ, 0+1].Definable P := inferInstance

instance [𝚷-[ℬ, 1].Definable P] : 𝚷-[ℬ, 0+1].Definable P := inferInstance

instance [𝚫-[ℬ, 1].Definable P] : 𝚫-[ℬ, 0+1].Definable P := inferInstance

instance [𝚺-[ℬ, 1].DefinableFunction f] : 𝚺-[ℬ, 0+1].DefinableFunction f := inferInstance

instance [𝚷-[ℬ, 1].DefinableFunction f] : 𝚷-[ℬ, 0+1].DefinableFunction f := inferInstance

instance [𝚫-[ℬ, 1].DefinableFunction f] : 𝚫-[ℬ, 0+1].DefinableFunction f := inferInstance

instance [𝚺-[ℬ, 2].Definable P] : 𝚺-[ℬ, 0+1+1].Definable P := inferInstance

instance [𝚷-[ℬ, 2].Definable P] : 𝚷-[ℬ, 0+1+1].Definable P := inferInstance

instance [𝚫-[ℬ, 2].Definable P] : 𝚫-[ℬ, 0+1+1].Definable P := inferInstance

instance [𝚺-[ℬ, 2].DefinableFunction f] : 𝚺-[ℬ, 0+1+1].DefinableFunction f := inferInstance

instance [𝚷-[ℬ, 2].DefinableFunction f] : 𝚷-[ℬ, 0+1+1].DefinableFunction f := inferInstance

instance [𝚫-[ℬ, 2].DefinableFunction f] : 𝚫-[ℬ, 0+1+1].DefinableFunction f := inferInstance

end



end HierarchySymbol

variable {L : Language} {ℬ : FirstOrder.Bounding L}
variable {V : Type*} [Tarski.Structure L V] {Γ : Polarity} {s k : ℕ}

variable {ξ : Type*}

lemma definable_of_hierarchy {φ : FirstOrder.Semiformula L ξ k} (hφ : ℬ.Hierarchy Γ s φ)
    (e : ξ → V) :
    Γ-[ℬ, s].Definable fun v ↦ φ.Eval v e :=
  .mkPolarity (Rew.rewriteMap e ▹ φ) (hφ.rew _) fun _ ↦ by simp [Semiformula.eval_rewriteMap]

lemma definablePred_of_hierarchy {φ : FirstOrder.Semiformula L ξ 1} (hφ : ℬ.Hierarchy Γ s φ)
    (e : ξ → V) : Γ-[ℬ, s].DefinablePred fun x ↦ φ.Eval ![x] e :=
  (definable_of_hierarchy hφ e).of_iff fun v ↦ by
    have h : ![v 0] = v := (Matrix.fun_eq_vec_one v).symm
    simp [h]

lemma definableRel_of_hierarchy {φ : FirstOrder.Semiformula L ξ 2} (hφ : ℬ.Hierarchy Γ s φ)
    (e : ξ → V) : Γ-[ℬ, s].DefinableRel fun x y ↦ φ.Eval ![x, y] e :=
  (definable_of_hierarchy hφ e).of_iff fun v ↦ by
    have h : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
    simp [h]

namespace HierarchySymbol.Definable

@[elab_as_elim]
theorem sigma_succ_induction {V : Type*} [Tarski.Structure L V] {s : ℕ}
    {motive : (k : ℕ) → (P : (Fin k → V) → Prop) → 𝚺-[ℬ, s + 1].Definable P → Prop}
    (pi : ∀ {k} {P : (Fin k → V) → Prop} (hP : 𝚷-[ℬ, s].Definable P),
      motive k P (hP.of_lt (Nat.lt_succ_self s)))
    (and : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺-[ℬ, s + 1].Definable P)
      (hQ : 𝚺-[ℬ, s + 1].Definable Q),
      motive k P hP → motive k Q hQ →
      motive k (fun v ↦ P v ∧ Q v) (.and hP hQ))
    (or : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺-[ℬ, s + 1].Definable P)
      (hQ : 𝚺-[ℬ, s + 1].Definable Q),
      motive k P hP → motive k Q hQ →
      motive k (fun v ↦ P v ∨ Q v) (.or hP hQ))
    (ball : ∀ {k} {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin (k + 1) → V) → Prop}
      (t : Semiterm L V k)
      (hP : 𝚺-[ℬ, s + 1].Definable P),
      motive (k + 1) P hP →
      motive k (fun v ↦ ∀ x, R.val ![x, t.val v id] → P (x :> v)) (.ballCons hR hP t))
    (bexs : ∀ {k} {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {P : (Fin (k + 1) → V) → Prop}
      (t : Semiterm L V k)
      (hP : 𝚺-[ℬ, s + 1].Definable P),
      motive (k + 1) P hP →
      motive k (fun v ↦ ∃ x, R.val ![x, t.val v id] ∧ P (x :> v)) (.bexsCons hR hP t))
    (exs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (hP : 𝚺-[ℬ, s + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x, P (x :> v)) (.exsCons hP))
    (k : ℕ) (P : (Fin k → V) → Prop) (hP : 𝚺-[ℬ, s + 1].Definable P) : motive k P hP := by
  obtain ⟨φ, hφ⟩ := id hP
  obtain rfl : P = fun v ↦ φ.val.Eval v id := funext fun v ↦ by simp [hφ.iff]
  have hd : ∀ {k} (ψ : FirstOrder.Semiformula L V k), ℬ.Hierarchy 𝚺 (s + 1) ψ →
    𝚺-[ℬ, s + 1].Definable fun v ↦ ψ.Eval v id := fun ψ hψ ↦ .mkPolarity ψ hψ fun _ ↦ Iff.rfl
  revert hP
  exact Hierarchy.sigma_succ_induction
    (P := fun k ψ ↦ ∀ h : 𝚺-[ℬ, s + 1].Definable fun v ↦ ψ.Eval v id,
      motive k (fun v ↦ ψ.Eval v id) h)
    (fun _ ψ h _ ↦ pi (.mkPolarity ψ h fun _ ↦ Iff.rfl))
    (fun _ ψ χ hψ hχ ihψ ihχ _ ↦ by
      simpa using and (hd ψ hψ) (hd χ hχ) (ihψ <| hd ψ hψ) (ihχ <| hd χ hχ))
    (fun _ ψ χ hψ hχ ihψ ihχ _ ↦ by
      simpa using or (hd ψ hψ) (hd χ hχ) (ihψ <| hd ψ hψ) (ihχ <| hd χ hχ))
    (fun _ hR _ t ψ hψ ih _ ↦ by simpa using ball hR t (hd ψ hψ) (ih <| hd ψ hψ))
    (fun _ hR _ t ψ hψ ih _ ↦ by simpa using bexs hR t (hd ψ hψ) (ih <| hd ψ hψ))
    (fun _ ψ hψ ih _ ↦ by simpa using exs (hd ψ hψ) (ih <| hd ψ hψ))
    k φ.val φ.sigma_prop

end HierarchySymbol.Definable

open HierarchySymbol

scoped notation Γ "-Predicate " P " via " φ => HierarchySymbol.DefinedPred Γ P φ
scoped notation Γ "-Relation " P " via " φ => HierarchySymbol.DefinedRel Γ P φ
scoped notation Γ "-Relation₃ " P " via " φ => HierarchySymbol.DefinedRel₃ Γ P φ
scoped notation Γ "-Relation₄ " P " via " φ => HierarchySymbol.DefinedRel₄ Γ P φ
scoped notation Γ "-Function₀ " c " via " φ => HierarchySymbol.DefinedFunction₀ Γ c φ
scoped notation Γ "-Function₁ " f " via " φ => HierarchySymbol.DefinedFunction₁ Γ f φ
scoped notation Γ "-Function₂ " f " via " φ => HierarchySymbol.DefinedFunction₂ Γ f φ
scoped notation Γ "-Function₃ " f " via " φ => HierarchySymbol.DefinedFunction₃ Γ f φ
scoped notation Γ "-Function₄ " f " via " φ => HierarchySymbol.DefinedFunction₄ Γ f φ
scoped notation Γ "-Function₅ " f " via " φ => HierarchySymbol.DefinedFunction₅ Γ f φ
scoped notation Γ "-Predicate " P => DefinablePred Γ P
scoped notation Γ "-Relation " P => DefinableRel Γ P
scoped notation Γ "-Relation₃ " P => DefinableRel₃ Γ P
scoped notation Γ "-Relation₄ " P => DefinableRel₄ Γ P
scoped notation Γ "-Relation₅ " P => DefinableRel₅ Γ P
scoped notation Γ "-Function₁ " f => DefinableFunction₁ Γ f
scoped notation Γ "-Function₂ " f => DefinableFunction₂ Γ f
scoped notation Γ "-Function₃ " f => DefinableFunction₃ Γ f
scoped notation Γ "-Function₄ " f => DefinableFunction₄ Γ f
scoped notation Γ "-Predicate[" V "] " P " via " φ => HierarchySymbol.DefinedPred (V := V) Γ P φ
scoped notation Γ "-Relation[" V "] " P " via " φ => HierarchySymbol.DefinedRel (V := V) Γ P φ
scoped notation Γ "-Relation₃[" V "] " P " via " φ => HierarchySymbol.DefinedRel₃ (V := V) Γ P φ
scoped notation Γ "-Relation₄[" V "] " P " via " φ => HierarchySymbol.DefinedRel₄ (V := V) Γ P φ
scoped notation Γ "-Function₀[" V "] " c " via " φ =>
  HierarchySymbol.DefinedFunction₀ (V := V) Γ c φ
scoped notation Γ "-Function₁[" V "] " f " via " φ =>
  HierarchySymbol.DefinedFunction₁ (V := V) Γ f φ
scoped notation Γ "-Function₂[" V "] " f " via " φ =>
  HierarchySymbol.DefinedFunction₂ (V := V) Γ f φ
scoped notation Γ "-Function₃[" V "] " f " via " φ =>
  HierarchySymbol.DefinedFunction₃ (V := V) Γ f φ
scoped notation Γ "-Function₄[" V "] " f " via " φ =>
  HierarchySymbol.DefinedFunction₄ (V := V) Γ f φ
scoped notation Γ "-Function₅[" V "] " f " via " φ =>
  HierarchySymbol.DefinedFunction₅ (V := V) Γ f φ
scoped notation Γ "-Predicate[" V "] " P => DefinablePred (V := V) Γ P
scoped notation Γ "-Relation[" V "] " P => DefinableRel (V := V) Γ P
scoped notation Γ "-Relation₃[" V "] " P => DefinableRel₃ (V := V) Γ P
scoped notation Γ "-Relation₄[" V "] " P => DefinableRel₄ (V := V) Γ P
scoped notation Γ "-Relation₅[" V "] " P => DefinableRel₅ (V := V) Γ P
scoped notation Γ "-Function₁[" V "] " f => DefinableFunction₁ (V := V) Γ f
scoped notation Γ "-Function₂[" V "] " f => DefinableFunction₂ (V := V) Γ f
scoped notation Γ "-Function₃[" V "] " f => DefinableFunction₃ (V := V) Γ f
scoped notation Γ "-Function₄[" V "] " f => DefinableFunction₄ (V := V) Γ f

end FFL.FirstOrder.Bounding
