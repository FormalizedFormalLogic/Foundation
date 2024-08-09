import Arithmetization.Definability.HSemiformula
import Arithmetization.Vorspiel.Graph

namespace LO.FirstOrder.Arith

end Arith

def Defined {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm M v p

def DefinedWithParam {k} (R : (Fin k → M) → Prop) [Structure L M] (p : Semiformula L M k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm M v id p

lemma Defined.iff [Structure L M] {k} {R : (Fin k → M) → Prop} {p : Semisentence L k} (h : Defined R p) (v) :
    Semiformula.Evalbm M v p ↔ R v := (h v).symm

lemma DefinedWithParam.iff [Structure L M] {k} {R : (Fin k → M) → Prop} {p : Semiformula L M k} (h : DefinedWithParam R p) (v) :
    Semiformula.Evalm M v id p ↔ R v := (h v).symm

namespace Arith.HierarchySymbol

variable (ξ : Type*) (n : ℕ)

open LO.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

variable {Γ : HierarchySymbol}

def Defined (R : (Fin k → M) → Prop) : {Γ : HierarchySymbol} → Γ.Semisentence k → Prop
  | 𝚺-[_], p => FirstOrder.Defined R p.val
  | 𝚷-[_], p => FirstOrder.Defined R p.val
  | 𝚫-[_], p => p.ProperOn M ∧ FirstOrder.Defined R p.val

def DefinedWithParam (R : (Fin k → M) → Prop) : {Γ : HierarchySymbol} → Γ.Semiformula M k → Prop
  | 𝚺-[_], p => FirstOrder.DefinedWithParam R p.val
  | 𝚷-[_], p => FirstOrder.DefinedWithParam R p.val
  | 𝚫-[_], p => p.ProperWithParamOn M ∧ FirstOrder.DefinedWithParam R p.val

variable (L Γ)

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ p : Γ.Semisentence k, Defined P p

class DefinableWithParam {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ p : Γ.Semiformula M k, DefinedWithParam P p

abbrev DefinedPred (P : M → Prop) (p : Γ.Semisentence 1) : Prop :=
  Defined (λ v ↦ P (v 0)) p

abbrev DefinedRel (R : M → M → Prop) (p : Γ.Semisentence 2) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1)) p

abbrev DefinedRel₃ (R : M → M → M → Prop) (p : Γ.Semisentence 3) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2)) p

abbrev DefinedRel₄ (R : M → M → M → M → Prop) (p : Γ.Semisentence 4) : Prop :=
  Defined (λ v ↦ R (v 0) (v 1) (v 2) (v 3)) p

variable {L Γ}

abbrev DefinedFunction {k} (f : (Fin k → M) → M) (p : Γ.Semisentence (k + 1)) : Prop :=
  Defined (fun v => v 0 = f (v ·.succ)) p

variable (L Γ)

abbrev DefinedFunction₁ (f : M → M) (p : Γ.Semisentence 2) : Prop :=
  DefinedFunction (fun v => f (v 0)) p

abbrev DefinedFunction₂ (f : M → M → M) (p : Γ.Semisentence 3) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1)) p

abbrev DefinedFunction₃ (f : M → M → M → M) (p : Γ.Semisentence 4) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2)) p

abbrev DefinedFunction₄ (f : M → M → M → M → M) (p : Γ.Semisentence 5) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3)) p

abbrev DefinedFunction₅ (f : M → M → M → M → M → M) (p : Γ.Semisentence 6) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3) (v 4)) p

abbrev DefinableWithParamPred (P : M → Prop) : Prop := Γ.DefinableWithParam (k := 1) (fun v ↦ P (v 0))

abbrev DefinableWithParamRel (P : M → M → Prop) : Prop := Γ.DefinableWithParam (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableWithParamRel₃ (P : M → M → M → Prop) : Prop := Γ.DefinableWithParam (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableWithParamRel₄ (P : M → M → M → M → Prop) : Prop := Γ.DefinableWithParam (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev DefinableWithParamRel₅ (P : M → M → M → M → M → Prop) : Prop := Γ.DefinableWithParam (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

abbrev DefinableWithParamRel₆ (P : M → M → M → M → M → M → Prop) : Prop := Γ.DefinableWithParam (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

abbrev DefinableWithParamFunction (f : (Fin k → M) → M) : Prop := Γ.DefinableWithParam (k := k + 1) (fun v ↦ v 0 = f (v ·.succ))

abbrev DefinableWithParamFunction₁ (f : M → M) : Prop := Γ.DefinableWithParamFunction (k := 1) (fun v ↦ f (v 0))

abbrev DefinableWithParamFunction₂ (f : M → M → M) : Prop := Γ.DefinableWithParamFunction (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableWithParamFunction₃ (f : M → M → M → M) : Prop := Γ.DefinableWithParamFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

abbrev DefinableWithParamFunction₄ (f : M → M → M → M → M) : Prop := Γ.DefinableWithParamFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

abbrev DefinableWithParamFunction₅ (f : M → M → M → M → M → M) : Prop := Γ.DefinableWithParamFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {L Γ}

section

variable {k} {P Q : (Fin k → M) → Prop}

namespace Defined

lemma df {R : (Fin k → M) → Prop} {Γ : HierarchySymbol} {p : Γ.Semisentence k} (h : Defined R p) : FirstOrder.Defined R p.val :=
  match Γ with
  | 𝚺-[_] => h
  | 𝚷-[_] => h
  | 𝚫-[_] => h.2

lemma proper {R : (Fin k → M) → Prop} {m} {p : 𝚫-[m].Semisentence k} (h : Defined R p) : p.ProperOn M := h.1

lemma of_zero {R : (Fin k → M) → Prop} {Γ : HierarchySymbol} {p : 𝚺₀.Semisentence k} (h : Defined R p) : Defined R (p.ofZero Γ) :=
  match Γ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simp, by intro _; simp [h.iff]⟩

lemma emb {R : (Fin k → M) → Prop} {Γ : HierarchySymbol} {p : Γ.Semisentence k} (h : Defined R p) : Defined R p.emb :=
  match Γ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → M) → Prop} (h : ∀ x, P x ↔ Q x)
    {p : Γ.Semisentence k} (H : Defined Q p) : Defined P p := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable {Γ : HierarchySymbol} (p : Γ.Semisentence k) (hP : Defined P p) : Γ.DefinableWithParam P := ⟨p.rew Rew.emb, by
  match Γ with
  | 𝚺-[_] => intro; simp [hP.iff]
  | 𝚷-[_] => intro; simp [hP.iff]
  | 𝚫-[_] => exact ⟨
    fun v ↦ by rcases p; simpa [HierarchySymbol.Semiformula.rew] using hP.proper.rew Rew.emb v,
    by intro; simp [hP.df.iff]⟩⟩

lemma to_definable₀ (p : 𝚺₀.Semisentence k) (hP : Defined P p) :
    Γ.DefinableWithParam P := Defined.to_definable (p.ofZero Γ) hP.of_zero

lemma to_definable_oRing (p : Γ.Semisentence k) (hP : Defined P p) :
    Γ.DefinableWithParam P := Defined.to_definable p.emb hP.emb

lemma to_definable_oRing₀ (p : 𝚺₀.Semisentence k) (hP : Defined P p) :
    Γ.DefinableWithParam P := Defined.to_definable₀ p.emb hP.emb

end Defined

namespace DefinedFunction

lemma of_eq {f g : (Fin k → M) → M} (h : ∀ x, f x = g x)
    {p : Γ.Semisentence (k + 1)} (H : DefinedFunction f p) : DefinedFunction g p :=
  Defined.of_iff (by intro; simp [h]) H

lemma graph_delta {f : (Fin k → M) → M} {p : 𝚺-[m].Semisentence (k + 1)}
    (h : DefinedFunction f p) : DefinedFunction f p.graphDelta :=
  ⟨by cases' m with m <;> simp [HierarchySymbol.Semiformula.graphDelta]
      intro e; simp [Empty.eq_elim, h.df.iff]
      rw [eq_comm],
   by intro v; simp [h.df.iff]⟩

end DefinedFunction

namespace DefinedWithParam

lemma df {R : (Fin k → M) → Prop} {Γ : HierarchySymbol} {p : Γ.Semiformula M k} (h : DefinedWithParam R p) : FirstOrder.DefinedWithParam R p.val :=
  match Γ with
  | 𝚺-[_] => h
  | 𝚷-[_] => h
  | 𝚫-[_] => h.2

lemma proper {R : (Fin k → M) → Prop} {m} {p : 𝚫-[m].Semiformula M k} (h : DefinedWithParam R p) : p.ProperWithParamOn M := h.1

lemma of_zero {R : (Fin k → M) → Prop} {Γ'} {p : Γ'-[0].Semiformula M k}
    (h : DefinedWithParam R p) {Γ} : DefinedWithParam R (p.ofZero Γ) :=
  match Γ with
  | 𝚺-[m] => by intro _; simp [h.df.iff]
  | 𝚷-[m] => by intro _; simp [h.df.iff]
  | 𝚫-[m] => ⟨by simp , by intro _; simp [h.df.iff]⟩

lemma of_deltaOne {R : (Fin k → M) → Prop} {Γ m} {p : 𝚫₁.Semiformula M k}
    (h : DefinedWithParam R p) : DefinedWithParam R (p.ofDeltaOne Γ m) :=
  match Γ with
  | 𝚺 => by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]
  | 𝚷 => by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, h.proper.iff']
  | 𝚫 => ⟨by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma, h.proper.iff'],
    by intro _; simp [HierarchySymbol.Semiformula.ofDeltaOne, h.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩

lemma emb {R : (Fin k → M) → Prop} {Γ : HierarchySymbol} {p : Γ.Semiformula M k}
    (h : DefinedWithParam R p) : DefinedWithParam R p.emb :=
  match Γ with
  | 𝚺-[m] => by intro _; simp [h.iff]
  | 𝚷-[m] => by intro _; simp [h.iff]
  | 𝚫-[m] => ⟨by simpa using h.proper, by intro _; simp [h.df.iff]⟩

lemma of_iff {P Q : (Fin k → M) → Prop} (h : ∀ x, P x ↔ Q x)
    {p : Γ.Semiformula M k} (H : DefinedWithParam Q p) : DefinedWithParam P p := by
  rwa [show P = Q from by funext v; simp [h]]

lemma to_definable {p : Γ.Semiformula M k} (h : DefinedWithParam P p) : Γ.DefinableWithParam P := ⟨p, h⟩

lemma to_definable₀ {p : Γ'-[0].Semiformula M k}
    (h : DefinedWithParam P p) : Γ.DefinableWithParam P := ⟨p.ofZero Γ, h.of_zero⟩

lemma to_definable_deltaOne {p : 𝚫₁.Semiformula M k} {Γ m}
    (h : DefinedWithParam P p) : Γ-[m + 1].DefinableWithParam P := ⟨p.ofDeltaOne Γ m, h.of_deltaOne⟩

variable {Γ : HierarchySymbol}

lemma retraction {p : Γ.Semiformula M k} (hp : DefinedWithParam P p) (f : Fin k → Fin l) :
    DefinedWithParam (fun v ↦ P fun i ↦ v (f i)) (p.rew <| Rew.substs fun x ↦ #(f x)) :=
  match Γ with
  | 𝚺-[_] => by intro; simp [hp.df.iff]
  | 𝚷-[_] => by intro; simp [hp.df.iff]
  | 𝚫-[_] => ⟨hp.proper.rew _, by intro; simp [hp.df.iff]⟩

@[simp] lemma verum :
    DefinedWithParam (fun _ ↦ True) (⊤ : Γ.Semiformula M k) :=
  match Γ with
  | 𝚺-[m] => by intro v; simp
  | 𝚷-[m] => by intro v; simp
  | 𝚫-[m] => ⟨by simp, by intro v; simp⟩

@[simp] lemma falsum :
    DefinedWithParam (fun _ ↦ False) (⊥ : Γ.Semiformula M k) :=
  match Γ with
| 𝚺-[m] => by intro v; simp
  | 𝚷-[m] => by intro v; simp
  | 𝚫-[m] => ⟨by simp, by intro v; simp⟩

lemma and {p q : Γ.Semiformula M k} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ∧ Q x) (p ⋏ q) :=
  match Γ with
  | 𝚺-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚷-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚫-[m] => ⟨hp.proper.and hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma or {p q : Γ.Semiformula M k} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ∨ Q x) (p ⋎ q) :=
  match Γ with
  | 𝚺-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚷-[m] => by intro v; simp [hp.iff, hq.iff]
  | 𝚫-[m] => ⟨hp.proper.or hq.proper, by intro v; simp [hp.df.iff, hq.df.iff]⟩

lemma negSigma {p : 𝚺-[m].Semiformula M k} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) p.negSigma := by intro v; simp [hp.iff]

lemma negPi {p : 𝚷-[m].Semiformula M k} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) p.negPi := by intro v; simp [hp.iff]

lemma not {p : 𝚫-[m].Semiformula M k} (hp : DefinedWithParam P p) :
    DefinedWithParam (fun x ↦ ¬P x) (~p) := ⟨hp.proper.neg, by intro v; simp [hp.proper.eval_neg, hp.df.iff]⟩

lemma imp {p q : 𝚫-[m].Semiformula M k} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x → Q x) (p ⟶ q) := (hp.not.or hq).of_iff (by intro x; simp [imp_iff_not_or])

lemma iff {p q : 𝚫-[m].Semiformula M k} (hp : DefinedWithParam P p) (hq : DefinedWithParam Q q) :
    DefinedWithParam (fun x ↦ P x ↔ Q x) (p ⟷ q) := ((hp.imp hq).and (hq.imp hp)).of_iff <| by intro v; simp [iff_iff_implies_and_implies]

lemma ball {P : (Fin (k + 1) → M) → Prop} {p : Γ.Semiformula M (k + 1)}
    (hp : DefinedWithParam P p) (t : Semiterm ℒₒᵣ M k) :
    DefinedWithParam (fun v ↦ ∀ x < t.valm M v id, P (x :> v)) (HierarchySymbol.Semiformula.ball t p) :=
  match Γ with
  | 𝚺-[m] => by intro v; simp [hp.df.iff]
  | 𝚷-[m] => by intro v; simp [hp.df.iff]
  | 𝚫-[m] => ⟨hp.proper.ball, by intro v; simp [hp.df.iff]⟩

lemma bex {P : (Fin (k + 1) → M) → Prop} {p : Γ.Semiformula M (k + 1)}
    (hp : DefinedWithParam P p) (t : Semiterm ℒₒᵣ M k) :
    DefinedWithParam (fun v ↦ ∃ x < t.valm M v id, P (x :> v)) (HierarchySymbol.Semiformula.bex t p) :=
  match Γ with
  | 𝚺-[m] => by intro v; simp [hp.df.iff]
  | 𝚷-[m] => by intro v; simp [hp.df.iff]
  | 𝚫-[m] => ⟨hp.proper.bex, by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin (k + 1) → M) → Prop} {p : 𝚺-[m + 1].Semiformula M (k + 1)}
    (hp : DefinedWithParam P p) :
    DefinedWithParam (fun v ↦ ∃ x, P (x :> v)) p.ex := by intro _; simp [hp.df.iff]

lemma all {P : (Fin (k + 1) → M) → Prop} {p : 𝚷-[m + 1].Semiformula M (k + 1)}
    (hp : DefinedWithParam P p) :
    DefinedWithParam (fun v ↦ ∀ x, P (x :> v)) p.all := by intro _; simp [hp.df.iff]

end DefinedWithParam

namespace DefinableWithParam

lemma mkPolarity {P : (Fin k → M) → Prop} {Γ : Polarity}
    (p : Semiformula ℒₒᵣ M k) (hp : Hierarchy Γ m p) (hP : ∀ v, P v ↔ Semiformula.Evalm M v id p) : Γ-[m].DefinableWithParam P :=
  match Γ with
  | 𝚺 => ⟨.mkSigma p hp, by intro v; simp [hP]⟩
  | 𝚷 => ⟨.mkPi p hp, by intro v; simp [hP]⟩

lemma of_iff (Q : (Fin k → M) → Prop) (h : ∀ x, P x ↔ Q x) (H : Γ.DefinableWithParam Q) : Γ.DefinableWithParam P := by
  rwa [show P = Q from by funext v; simp [h]]

lemma of_oRing (h : Γ.DefinableWithParam P) : Γ.DefinableWithParam P := by
  rcases h with ⟨p, hP⟩; exact ⟨p.emb, hP.emb⟩

lemma of_delta (h : 𝚫-[m].DefinableWithParam P) {Γ} : Γ-[m].DefinableWithParam P := by
  rcases h with ⟨p, h⟩
  match Γ with
  | 𝚺 => exact ⟨p.sigma, by intro v; simp [HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | 𝚷 => exact ⟨p.pi, by intro v; simp [←h.proper v, HierarchySymbol.Semiformula.val_sigma, h.df.iff]⟩
  | 𝚫 => exact ⟨p, h⟩

instance [𝚫-[m].DefinableWithParam P] (Γ) : Γ-[m].DefinableWithParam P := of_delta inferInstance

lemma of_sigma_of_pi (hσ : 𝚺-[m].DefinableWithParam P) (hπ : 𝚷-[m].DefinableWithParam P) : 𝚫-[m].DefinableWithParam P := by
  rcases hσ with ⟨p, hp⟩; rcases hπ with ⟨q, hq⟩
  exact ⟨.mkDelta p q, by intro v; simp [hp.df.iff, hq.df.iff], by intro v; simp [hp.df.iff]⟩

lemma of_zero (h : Γ'-[0].DefinableWithParam P) : Γ.DefinableWithParam P := by
  rcases h with ⟨⟨p, hp⟩⟩; exact hp.to_definable₀

lemma of_deltaOne (h : 𝚫₁.DefinableWithParam P) (Γ m) : Γ-[m + 1].DefinableWithParam P := by
  rcases h with ⟨⟨p, hp⟩⟩; exact hp.to_definable_deltaOne

instance [𝚺₀.DefinableWithParam P] (Γ : HierarchySymbol) : Γ.DefinableWithParam P := DefinableWithParam.of_zero (Γ' := 𝚺) (Γ := Γ) inferInstance

variable {Γ : HierarchySymbol}

lemma retraction (h : Γ.DefinableWithParam P) (f : Fin k → Fin n) :
    Γ.DefinableWithParam fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨p, h⟩
  exact ⟨p.rew (Rew.substs (fun i ↦ #(f i))),
  match Γ with
  | 𝚺-[_] => by intro; simp [h.df.iff]
  | 𝚷-[_] => by intro; simp [h.df.iff]
  | 𝚫-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

lemma retractiont (h : Γ.DefinableWithParam P) (f : Fin k → Semiterm ℒₒᵣ M n) :
    Γ.DefinableWithParam fun v ↦ P (fun i ↦ Semiterm.valm M v id (f i)) := by
  rcases h with ⟨p, h⟩
  exact ⟨p.rew (Rew.substs f),
  match Γ with
  | 𝚺-[_] => by intro; simp [h.df.iff]
  | 𝚷-[_] => by intro; simp [h.df.iff]
  | 𝚫-[_] => ⟨h.proper.rew _, by intro; simp [h.df.iff]⟩⟩

lemma const {P : Prop} : Γ.DefinableWithParam (fun _ : Fin k → M ↦ P) := of_zero (by
  by_cases hP : P
  · exact ⟨.mkSigma ⊤ (by simp), by intro; simp[hP]⟩
  · exact ⟨.mkSigma ⊥ (by simp), by intro; simp[hP]⟩)

lemma and (h₁ : Γ.DefinableWithParam P) (h₂ : Γ.DefinableWithParam Q) :
    Γ.DefinableWithParam (fun v ↦ P v ∧ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋏ p₂, h₁.and h₂⟩

lemma or (h₁ : Γ.DefinableWithParam P) (h₂ : Γ.DefinableWithParam Q) :
    Γ.DefinableWithParam (fun v ↦ P v ∨ Q v) := by
  rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
  exact ⟨p₁ ⋎ p₂, h₁.or h₂⟩

lemma not {Γ : SigmaPiDelta} (h : Γ.alt-[m].DefinableWithParam P) :
    Γ-[m].DefinableWithParam (fun v ↦ ¬P v) := by
  match Γ with
  | 𝚺 => rcases h with ⟨p, h⟩; exact ⟨p.negPi, h.negPi⟩
  | 𝚷 => rcases h with ⟨p, h⟩; exact ⟨p.negSigma, h.negSigma⟩
  | 𝚫 => rcases h with ⟨p, h⟩; exact ⟨p.negDelta, h.not⟩

lemma imp {Γ : SigmaPiDelta} (h₁ : Γ.alt-[m].DefinableWithParam P) (h₂ : Γ-[m].DefinableWithParam Q) :
    Γ-[m].DefinableWithParam (fun v ↦ P v → Q v) := by
  match Γ with
  | 𝚺 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negPi.or p₂, (h₁.negPi.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚷 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩
    exact ⟨p₁.negSigma.or p₂, (h₁.negSigma.or h₂).of_iff (fun x ↦ by simp [imp_iff_not_or])⟩
  | 𝚫 =>
    rcases h₁ with ⟨p₁, h₁⟩; rcases h₂ with ⟨p₂, h₂⟩; exact ⟨p₁ ⟶ p₂, h₁.imp h₂⟩

lemma iff (h₁ : 𝚫-[m].DefinableWithParam P) (h₂ : 𝚫-[m].DefinableWithParam Q) {Γ} :
    Γ-[m].DefinableWithParam (fun v ↦ P v ↔ Q v) :=
  .of_delta (by rcases h₁ with ⟨p, hp⟩; rcases h₂ with ⟨q, hq⟩; exact ⟨p ⟷ q, hp.iff hq⟩)

lemma all {P : (Fin k → M) → M → Prop} (h : 𝚷-[s + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    𝚷-[s + 1].DefinableWithParam (fun v ↦ ∀ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨.mkPi (∀' p.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma ex {P : (Fin k → M) → M → Prop} (h : 𝚺-[s + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    𝚺-[s + 1].DefinableWithParam (fun v ↦ ∃ x, P v x) := by
  rcases h with ⟨p, hp⟩
  exact ⟨.mkSigma (∃' p.val) (by simp), by intro v; simp [hp.df.iff]⟩

lemma comp₁ {k} {P : M → Prop} {f : (Fin k → M) → M} (hf : 𝚺-[m + 1].DefinableWithParamFunction f)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamPred P) : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f v)) := by
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact ⟨(pf ⋏ (p.rew (Rew.substs ![#0]))).ex, by intro v; simp [hp.df.iff, hpf.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact ⟨(pf.negSigma ⋎ (p.rew (Rew.substs ![#0]))).all, by intro v; simp [hp.df.iff, hpf.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩
    exact of_sigma_of_pi
      ⟨(pf ⋏ (p.sigma.rew (Rew.substs ![#0]))).ex, by intro v; simp [hp.df.iff, hpf.df.iff, HierarchySymbol.Semiformula.val_sigma]  ⟩
      ⟨(pf.negSigma ⋎ (p.pi.rew (Rew.substs ![#0]))).all, by intro v; simp [hp.df.iff, hpf.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₁_infer {k} {P : M → Prop} {f : (Fin k → M) → M} (hf : 𝚺-[m + 1].DefinableWithParamFunction f)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamPred P] : Γ-[m + 1].DefinableWithParam fun v ↦ P (f v) :=
  comp₁ hf inferInstance

lemma comp₂ {k} {P : M → M → Prop} {f g : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (hg : 𝚺-[m + 1].DefinableWithParamFunction g)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamRel P) : Γ-[m + 1].DefinableWithParam fun v ↦ P (f v) (g v) := by
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact ⟨(pf.rew (Rew.substs $ #0 :> (#·.succ.succ)) ⋏ pg.rew (Rew.substs $ #1 :> (#·.succ.succ)) ⋏ (p.rew (Rew.substs ![#0, #1]))).ex.ex, by
      intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact ⟨((pf.rew (Rew.substs $ #0 :> (#·.succ.succ))).negSigma ⋎ (pg.rew (Rew.substs $ #1 :> (#·.succ.succ))).negSigma ⋎ (p.rew (Rew.substs ![#0, #1]))).all.all, by
      intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩; rcases hf with ⟨pf, hpf⟩; rcases hg with ⟨pg, hpg⟩
    exact of_sigma_of_pi
      ⟨(pf.rew (Rew.substs $ #0 :> (#·.succ.succ)) ⋏ pg.rew (Rew.substs $ #1 :> (#·.succ.succ)) ⋏ (p.sigma.rew (Rew.substs ![#0, #1]))).ex.ex, by
        intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
      ⟨((pf.rew (Rew.substs $ #0 :> (#·.succ.succ))).negSigma
          ⋎ (pg.rew (Rew.substs $ #1 :> (#·.succ.succ))).negSigma ⋎ (p.pi.rew (Rew.substs ![#0, #1]))).all.all, by
        intro v; simp [hp.df.iff, hpf.df.iff, hpg.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₂_infer {k} {P : M → M → Prop} {f g : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (hg : 𝚺-[m + 1].DefinableWithParamFunction g)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamRel P] : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f v) (g v)) :=
  comp₂ hf hg inferInstance

lemma comp₃ {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂) (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamRel₃ P) : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))
        ⋏ (p.rew (Rew.substs ![#0, #1, #2]))).ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))).negSigma
        ⋎ (p.rew (Rew.substs ![#0, #1, #2]))).all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))
        ⋏ (p.sigma.rew (Rew.substs ![#0, #1, #2]))).ex.ex.ex, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew (Rew.substs ![#0, #1, #2]))).all.all.all, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₃_infer {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂) (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamRel₃ P] : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  comp₃ hf₁ hf₂ hf₃ inferInstance

lemma comp₄ {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamRel₄ P) : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩; rcases hf₄ with ⟨pf₄, hpf₄⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))
        ⋏ (p.rew (Rew.substs ![#0, #1, #2, #3]))).ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (p.rew (Rew.substs ![#0, #1, #2, #3]))).all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))
        ⋏ (p.sigma.rew (Rew.substs ![#0, #1, #2, #3]))).ex.ex.ex.ex, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew (Rew.substs ![#0, #1, #2, #3]))).all.all.all.all, by
        intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₄_infer {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamRel₄ P] : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  comp₄ hf₁ hf₂ hf₃ hf₄ inferInstance

lemma comp₅ {k} {P : M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    (hf₅ : 𝚺-[m + 1].DefinableWithParamFunction f₅)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamRel₅ P) : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩
  rcases hf₄ with ⟨pf₄, hpf₄⟩; rcases hf₅ with ⟨pf₅, hpf₅⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ))
        ⋏ (p.rew (Rew.substs ![#0, #1, #2, #3, #4]))).ex.ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (p.rew (Rew.substs ![#0, #1, #2, #3, #4]))).all.all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ))
        ⋏ pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ))
        ⋏ (p.sigma.rew (Rew.substs ![#0, #1, #2, #3, #4]))).ex.ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew (Rew.substs ![#0, #1, #2, #3, #4]))).all.all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₅_infer {k} {P : M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    (hf₅ : 𝚺-[m + 1].DefinableWithParamFunction f₅)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamRel₅ P] : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  comp₅ hf₁ hf₂ hf₃ hf₄ hf₅  inferInstance

lemma comp₆ {k} {P : M → M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ f₆ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    (hf₅ : 𝚺-[m + 1].DefinableWithParamFunction f₅) (hf₆ : 𝚺-[m + 1].DefinableWithParamFunction f₆)
    {Γ : SigmaPiDelta} (hP : Γ-[m + 1].DefinableWithParamRel₆ P) : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v) (f₆ v)) := by
  rcases hf₁ with ⟨pf₁, hpf₁⟩; rcases hf₂ with ⟨pf₂, hpf₂⟩; rcases hf₃ with ⟨pf₃, hpf₃⟩
  rcases hf₄ with ⟨pf₄, hpf₄⟩; rcases hf₅ with ⟨pf₅, hpf₅⟩; rcases hf₆ with ⟨pf₆, hpf₆⟩
  match Γ with
  | 𝚺 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₆.rew (Rew.substs $ #5 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ (p.rew (Rew.substs ![#0, #1, #2, #3, #4, #5]))).ex.ex.ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, hpf₆.df.iff]⟩
  | 𝚷 =>
    rcases hP with ⟨p, hp⟩
    exact
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₆.rew (Rew.substs $ #5 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (p.rew (Rew.substs ![#0, #1, #2, #3, #4, #5]))).all.all.all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, hpf₆.df.iff, ←imp_iff_not_or]⟩
  | 𝚫 =>
    rcases hP with ⟨p, hp⟩
    exact of_sigma_of_pi
      ⟨(  pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ pf₆.rew (Rew.substs $ #5 :> (#·.succ.succ.succ.succ.succ.succ))
        ⋏ (p.sigma.rew (Rew.substs ![#0, #1, #2, #3, #4, #5]))).ex.ex.ex.ex.ex.ex, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, hpf₆.df.iff, HierarchySymbol.Semiformula.val_sigma]⟩
      ⟨(  (pf₁.rew (Rew.substs $ #0 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₂.rew (Rew.substs $ #1 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₃.rew (Rew.substs $ #2 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₄.rew (Rew.substs $ #3 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₅.rew (Rew.substs $ #4 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (pf₆.rew (Rew.substs $ #5 :> (#·.succ.succ.succ.succ.succ.succ))).negSigma
        ⋎ (p.pi.rew (Rew.substs ![#0, #1, #2, #3, #4, #5]))).all.all.all.all.all.all, by
      intro v; simp [hp.df.iff, hpf₁.df.iff, hpf₂.df.iff, hpf₃.df.iff, hpf₄.df.iff, hpf₅.df.iff, hpf₆.df.iff, ←imp_iff_not_or, hp.proper.iff']⟩

lemma comp₆_infer {k} {P : M → M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ f₆ : (Fin k → M) → M}
    (hf₁ : 𝚺-[m + 1].DefinableWithParamFunction f₁) (hf₂ : 𝚺-[m + 1].DefinableWithParamFunction f₂)
    (hf₃ : 𝚺-[m + 1].DefinableWithParamFunction f₃) (hf₄ : 𝚺-[m + 1].DefinableWithParamFunction f₄)
    (hf₅ : 𝚺-[m + 1].DefinableWithParamFunction f₅) (hf₆ : 𝚺-[m + 1].DefinableWithParamFunction f₆)
    {Γ : SigmaPiDelta} [Γ-[m + 1].DefinableWithParamRel₆ P] : Γ-[m + 1].DefinableWithParam (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v) (f₆ v)) :=
  comp₆ hf₁ hf₂ hf₃ hf₄ hf₅ hf₆ inferInstance

end DefinableWithParam

lemma DefinableWithParamPred.of_iff {P : M → Prop} (Q : M → Prop) (h : ∀ x, P x ↔ Q x) (H : Γ.DefinableWithParamPred Q) : Γ.DefinableWithParamPred P := by
  rwa [show P = Q from by funext v; simp [h]]

instance DefinableWithParamFunction₁.graph {f : M → M} [h : Γ.DefinableWithParamFunction₁ f] :
  Γ.DefinableWithParamRel (Function.Graph f) := h

instance DefinableWithParamFunction₂.graph {f : M → M → M} [h : Γ.DefinableWithParamFunction₂ f] :
  Γ.DefinableWithParamRel₃ (Function.Graph₂ f) := h

instance DefinableWithParamFunction₃.graph {f : M → M → M → M} [h : Γ.DefinableWithParamFunction₃ f] :
  Γ.DefinableWithParamRel₄ (Function.Graph₃ f) := h

namespace DefinableWithParamFunction

lemma graph_delta {k} {f : (Fin k → M) → M}
    (h : 𝚺-[m].DefinableWithParamFunction f) : 𝚫-[m].DefinableWithParamFunction f := by
  rcases h with ⟨p, h⟩
  exact ⟨p.graphDelta, by
    cases' m with m <;> simp [HierarchySymbol.Semiformula.graphDelta]
    intro e; simp [Empty.eq_elim, h.df.iff]
    exact eq_comm, by
    intro v; simp [h.df.iff]⟩

instance {k} {f : (Fin k → M) → M} [h : 𝚺-[m].DefinableWithParamFunction f] : 𝚫-[m].DefinableWithParamFunction f :=
  DefinableWithParamFunction.graph_delta h

instance {k} {f : (Fin k → M) → M} [𝚺₀.DefinableWithParamFunction f] : Γ.DefinableWithParamFunction f := inferInstance

lemma of_sigmaOne {k} {f : (Fin k → M) → M}
    (h : 𝚺₁.DefinableWithParamFunction f) (Γ m) : Γ-[m + 1].DefinableWithParamFunction f := DefinableWithParam.of_deltaOne (graph_delta h) Γ m

@[simp] lemma var {k} (i : Fin k) : Γ.DefinableWithParamFunction (fun v : Fin k → M ↦ v i) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x | x = !!#i.succ” (by simp), by intro _; simp⟩

@[simp] lemma const {k} (c : M) : Γ.DefinableWithParamFunction (fun _ : Fin k → M ↦ c) :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x | #0 = &c” (by simp), by intro v; simp⟩

@[simp] lemma term_retraction (t : Semiterm ℒₒᵣ M n) (e : Fin n → Fin k) :
    Γ.DefinableWithParamFunction fun v : Fin k → M ↦ Semiterm.valm M (fun x ↦ v (e x)) id t :=
  .of_zero (Γ' := 𝚺)
    ⟨.mkSigma “x | x = !!(Rew.substs (fun x ↦ #(e x).succ) t)” (by simp), by intro v; simp [Semiterm.val_substs]⟩

@[simp] lemma term (t : Semiterm ℒₒᵣ M k) :
    Γ.DefinableWithParamFunction fun v : Fin k → M ↦ Semiterm.valm M v id t :=
  .of_zero (Γ' := 𝚺) ⟨.mkSigma “x | x = !!(Rew.bShift t)” (by simp), by intro v; simp [Semiterm.val_bShift']⟩

lemma of_eq {f : (Fin k → M) → M} (g) (h : ∀ v, f v = g v) (H : Γ.DefinableWithParamFunction f) : Γ.DefinableWithParamFunction g := by
  rwa [show g = f from by funext v; simp [h]]

lemma retraction {n k} {f : (Fin k → M) → M} (hf : Γ.DefinableWithParamFunction f) (e : Fin k → Fin n) :
    Γ.DefinableWithParamFunction fun v ↦ f (fun i ↦ v (e i)) := by
  have := DefinableWithParam.retraction (n := n + 1) hf (0 :> fun i ↦ (e i).succ); simp at this
  exact this.of_iff _ (by intro x; simp)

lemma retractiont {f : (Fin k → M) → M} (hf : Γ.DefinableWithParamFunction f) (t : Fin k → Semiterm ℒₒᵣ M n) :
    Γ.DefinableWithParamFunction fun v ↦ f (fun i ↦ Semiterm.valm M v id (t i)) := by
  have := DefinableWithParam.retractiont (n := n + 1) hf (#0 :> fun i ↦ Rew.bShift (t i)); simp at this
  exact this.of_iff _ (by intro x; simp [Semiterm.val_bShift'])

lemma rel {f : (Fin k → M) → M} (h : Γ.DefinableWithParamFunction f) :
  Γ.DefinableWithParam (fun v ↦ v 0 = f (v ·.succ)) := h

end DefinableWithParamFunction

lemma DefinableWithParamFunction₁.comp {Γ} {k} {f : M → M} {g : (Fin k → M) → M}
    (hf : Γ-[m + 1].DefinableWithParamFunction₁ f) (hg : 𝚺-[m + 1].DefinableWithParamFunction g) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g v)) := by
  simpa using DefinableWithParam.comp₂ (P := Function.Graph f) (DefinableWithParamFunction.var 0) (hg.retraction Fin.succ) hf

lemma DefinableWithParamFunction₂.comp {Γ} {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : Γ-[m + 1].DefinableWithParamFunction₂ f) (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁) (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v)) := by
  simpa using DefinableWithParam.comp₃ (P := Function.Graph₂ f) (DefinableWithParamFunction.var 0) (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) hf

lemma DefinableWithParamFunction₃.comp {Γ} {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : Γ-[m + 1].DefinableWithParamFunction₃ f) (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁)
    (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := by
  simpa using DefinableWithParam.comp₄ (P := Function.Graph₃ f) (DefinableWithParamFunction.var 0)
    (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) (hg₃.retraction Fin.succ) hf

lemma DefinableWithParamFunction₄.comp {Γ} {k} {f : M → M → M → M → M} {g₁ g₂ g₃ g₄ : (Fin k → M) → M}
    (hf : Γ-[m + 1].DefinableWithParamFunction₄ f) (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁)
    (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃)
    (hg₄ : 𝚺-[m + 1].DefinableWithParamFunction g₄) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v)) := by
  simpa using DefinableWithParam.comp₅ (P := Function.Graph₄ f) (DefinableWithParamFunction.var 0)
    (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) (hg₃.retraction Fin.succ) (hg₄.retraction Fin.succ) hf

lemma DefinableWithParamFunction₅.comp {Γ} {k} {f : M → M → M → M → M → M} {g₁ g₂ g₃ g₄ g₅ : (Fin k → M) → M}
    (hf : Γ-[m + 1].DefinableWithParamFunction₅ f) (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁)
    (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃)
    (hg₄ : 𝚺-[m + 1].DefinableWithParamFunction g₄) (hg₅ : 𝚺-[m + 1].DefinableWithParamFunction g₅) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₅ v)) := by
  simpa using DefinableWithParam.comp₆ (P := Function.Graph₅ f) (DefinableWithParamFunction.var 0)
    (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) (hg₃.retraction Fin.succ)
    (hg₄.retraction Fin.succ) (hg₅.retraction Fin.succ) hf

lemma DefinableWithParamFunction.comp₁_infer {Γ} {k} {f : M → M} [Γ-[m + 1].DefinableWithParamFunction₁ f]
    {g : (Fin k → M) → M} (hg : 𝚺-[m + 1].DefinableWithParamFunction g) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g v)) :=
  DefinableWithParamFunction₁.comp inferInstance hg

lemma DefinableWithParamFunction.comp₂_infer {Γ} {k} {f : M → M → M} [Γ-[m + 1].DefinableWithParamFunction₂ f]
    {g₁ g₂ : (Fin k → M) → M} (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁) (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v)) :=
  DefinableWithParamFunction₂.comp inferInstance hg₁ hg₂

lemma DefinableWithParamFunction.comp₃_infer {Γ} {k} {f : M → M → M → M} [Γ-[m + 1].DefinableWithParamFunction₃ f]
    {g₁ g₂ g₃ : (Fin k → M) → M}
    (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁) (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂) (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) :=
  DefinableWithParamFunction₃.comp inferInstance hg₁ hg₂ hg₃

lemma DefinableWithParamFunction.comp₄_infer {Γ} {k} {f : M → M → M → M → M} [Γ-[m + 1].DefinableWithParamFunction₄ f]
    {g₁ g₂ g₃ g₄ : (Fin k → M) → M}
    (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁) (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂)
    (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃) (hg₄ : 𝚺-[m + 1].DefinableWithParamFunction g₄) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v)) :=
  DefinableWithParamFunction₄.comp inferInstance hg₁ hg₂ hg₃ hg₄

lemma DefinableWithParamFunction.comp₅_infer {Γ} {k} {f : M → M → M → M → M → M} [Γ-[m + 1].DefinableWithParamFunction₅ f]
    {g₁ g₂ g₃ g₄ g₅ : (Fin k → M) → M}
    (hg₁ : 𝚺-[m + 1].DefinableWithParamFunction g₁) (hg₂ : 𝚺-[m + 1].DefinableWithParamFunction g₂)
    (hg₃ : 𝚺-[m + 1].DefinableWithParamFunction g₃) (hg₄ : 𝚺-[m + 1].DefinableWithParamFunction g₄)
    (hg₅ : 𝚺-[m + 1].DefinableWithParamFunction g₅) :
    Γ-[m + 1].DefinableWithParamFunction (fun v ↦ f (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₅ v)) :=
  DefinableWithParamFunction₅.comp inferInstance hg₁ hg₂ hg₃ hg₄ hg₅

namespace DefinableWithParamRel

@[simp] instance eq : Γ.DefinableWithParamRel (Eq : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1” (by simp)) (by intro _; simp)

@[simp] instance lt : Γ.DefinableWithParamRel (LT.lt : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 < #1” (by simp)) (by intro _; simp)

@[simp] instance le : Γ.DefinableWithParamRel (LE.le : M → M → Prop) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 ≤ #1” (by simp)) (by intro _; simp)

end DefinableWithParamRel

namespace DefinableWithParamFunction₂

@[simp] instance add : Γ.DefinableWithParamFunction₂ ((· + ·) : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance mul : Γ.DefinableWithParamFunction₂ ((· * ·) : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

@[simp] instance hAdd : Γ.DefinableWithParamFunction₂ (HAdd.hAdd : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 + #2” (by simp)) (by intro _; simp)

@[simp] instance hMul : Γ.DefinableWithParamFunction₂ (HMul.hMul : M → M → M) :=
  Defined.to_definable_oRing₀ (.mkSigma “#0 = #1 * #2” (by simp)) (by intro _; simp)

end DefinableWithParamFunction₂

namespace DefinableWithParam

lemma ball_lt {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨p, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ⟶ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.sigma.val))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ⟶ (∀[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.pi.val))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma bex_lt {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf with ⟨bf, hbf⟩
  rcases h with ⟨p, hp⟩
  match Γ with
  | 𝚺 => exact
    ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚷 => exact
    ⟨ .mkPi (∀' (bf.val ⟶ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.val))) (by simp),
      by intro v; simp [hbf.df.iff, hp.df.iff] ⟩
  | 𝚫 =>
    exact .of_sigma_of_pi
      ⟨ .mkSigma (∃' (bf.val ⋏ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.sigma.val))) (by simp),
          by intro v; simp [hbf.df.iff, hp.df.iff, HierarchySymbol.Semiformula.val_sigma] ⟩
      ⟨ .mkPi (∀' (bf.val ⟶ (∃[“#0 < #1”] Rew.substs (#0 :> (#·.succ.succ)) |>.hom p.pi.val))) (by simp),
        by intro v; simp [hbf.df.iff, hp.df.iff, hp.proper.iff'] ⟩

lemma ball_le {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∀ x ≤ f v, P v x) := by
  have : Γ-[m + 1].DefinableWithParam (fun v ↦ ∀ x < f v + 1, P v x) := ball_lt (DefinableWithParamFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma bex_le {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∃ x ≤ f v, P v x) := by
  have : Γ-[m + 1].DefinableWithParam (fun v ↦ ∃ x < f v + 1, P v x) := bex_lt (DefinableWithParamFunction₂.comp (by simp) hf (by simp)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma ball_lt' {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∀ {x}, x < f v → P v x) := ball_lt hf h

lemma ball_le' {Γ} {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : 𝚺-[m + 1].DefinableWithParamFunction f) (h : Γ-[m + 1].DefinableWithParam (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].DefinableWithParam (fun v ↦ ∀ {x}, x ≤ f v → P v x) := ball_le hf h

end DefinableWithParam

end

end Arith.HierarchySymbol

end LO.FirstOrder
