module

public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Bounded definability in a bounding hierarchy

This module defines bounded functions using a selected binary operator from a bounding set
and a term bound. It develops substitution and composition for functions whose graphs are Σ₀.
No monotonicity or order properties of the selected operators are assumed.
These definitions and closure lemmas are specific to this formalization.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding

open scoped Bounding

variable {L : Language}
variable {V : Type*} [Tarski.Structure L V]
variable {k l n : ℕ}

/-- A function is bounded when a selected bounding relation bounds it by a term. -/
class Bounded (ℬ : Bounding L) (f : (Fin k → V) → V) : Prop where
  bounded : ∃ R ∈ ℬ, ∃ t : Semiterm L V k, ∀ v, R.val ![f v, t.val v id]

variable {ℬ : Bounding L}

abbrev Bounded₁ (ℬ : Bounding L) (f : V → V) : Prop :=
  ℬ.Bounded (fun v : Fin 1 → V ↦ f (v 0))

abbrev Bounded₂ (ℬ : Bounding L) (f : V → V → V) : Prop :=
  ℬ.Bounded (fun v : Fin 2 → V ↦ f (v 0) (v 1))

abbrev Bounded₃ (ℬ : Bounding L) (f : V → V → V → V) : Prop :=
  ℬ.Bounded (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2))

namespace Bounded

lemma retraction {f : (Fin k → V) → V} (hf : ℬ.Bounded f)
    (e : Fin k → Fin n) : ℬ.Bounded fun v ↦ f (fun i ↦ v (e i)) := by
  obtain ⟨R, hR, t, ht⟩ := hf.bounded
  exact ⟨⟨R, hR, Rew.subst (fun i ↦ #(e i)) t, fun v ↦ by
    simpa [Semiterm.val_substs, Function.comp_def] using ht (fun i ↦ v (e i))⟩⟩

lemma retractiont {f : (Fin k → V) → V} (hf : ℬ.Bounded f)
    (t : Fin k → Semiterm L V n) :
    ℬ.Bounded fun v ↦ f (fun i ↦ (t i).val v id) := by
  obtain ⟨R, hR, u, hu⟩ := hf.bounded
  exact ⟨⟨R, hR, Rew.subst t u, fun v ↦ by
    simpa [Semiterm.val_substs, Function.comp_def] using
      hu (fun i ↦ (t i).val v id)⟩⟩

lemma of_iff {f g : (Fin k → V) → V} (hf : ℬ.Bounded f)
    (h : ∀ v, f v = g v) : ℬ.Bounded g := by
  obtain ⟨R, hR, t, ht⟩ := hf.bounded
  exact ⟨⟨R, hR, t, fun v ↦ by simpa [h v] using ht v⟩⟩

end Bounded

/-- A function is definable-bounded when it is bounded and has a Σ₀ graph. -/
def DefinableBoundedFunction (ℬ : Bounding L) (f : (Fin k → V) → V) : Prop :=
  ℬ.Bounded f ∧ (𝚺-[ℬ, 0]).DefinableFunction f

abbrev DefinableBoundedFunction₁ (ℬ : Bounding L) (f : V → V) : Prop :=
  ℬ.DefinableBoundedFunction (fun v : Fin 1 → V ↦ f (v 0))

abbrev DefinableBoundedFunction₂ (ℬ : Bounding L) (f : V → V → V) : Prop :=
  ℬ.DefinableBoundedFunction (fun v : Fin 2 → V ↦ f (v 0) (v 1))

abbrev DefinableBoundedFunction₃ (ℬ : Bounding L) (f : V → V → V → V) : Prop :=
  ℬ.DefinableBoundedFunction (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2))

namespace DefinableBoundedFunction

lemma bounded {f : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f) :
    ℬ.Bounded f := hf.1

lemma definable {f : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f)
    {Γ : HierarchySymbol ℬ} : Γ.DefinableFunction f := hf.2.of_zero

lemma retraction {f : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f)
    (e : Fin k → Fin n) :
    ℬ.DefinableBoundedFunction fun v ↦ f (fun i ↦ v (e i)) :=
  ⟨hf.1.retraction e, hf.2.retraction e⟩

lemma retractiont {f : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f)
    (t : Fin k → Semiterm L V n) :
    ℬ.DefinableBoundedFunction fun v ↦ f (fun i ↦ (t i).val v id) :=
  ⟨hf.1.retractiont t, hf.2.retractiont t⟩

lemma of_iff {f g : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f)
    (h : ∀ v, f v = g v) : ℬ.DefinableBoundedFunction g := by
  have hfg : f = g := by funext v; exact h v
  cases hfg
  exact hf

end DefinableBoundedFunction

namespace HierarchySymbol

variable {ℌ : HierarchySymbol ℬ}

namespace Definable

lemma bounded_substitution₁ {P : (Fin k → V) → V → Prop}
    (hP : ℌ.Definable fun w ↦ P (w ·.succ) (w 0))
    {f : (Fin k → V) → V} (hf : ℬ.DefinableBoundedFunction f) :
    ℌ.Definable fun v ↦ P v (f v) := by
  obtain ⟨R, hR, t, ht⟩ := hf.bounded.bounded
  have hGraph : ℌ.Definable fun w : Fin (k + 1) → V ↦ w 0 = f (w ·.succ) :=
    hf.definable
  have hBody := hGraph.and hP
  have h := Definable.bexs hR (P := fun v x ↦ x = f v ∧ P v x) hBody t
  exact h.of_iff fun v ↦ ⟨fun hPv ↦ ⟨f v, ht v, rfl, hPv⟩,
    fun ⟨x, hx, he, hPx⟩ ↦ by simpa [he] using hPx⟩

lemma ball_bounded {R : Semiformula.Operator L 2} (hR : R ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : ℬ.DefinableBoundedFunction f)
    (hP : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∀ x, R.val ![x, f v] → P v x := by
  have h := Definable.ball hR (P := fun u x ↦ P (u ·.succ) x)
    (hP.retraction (0 :> fun i ↦ i.succ.succ)) #0
  exact h.bounded_substitution₁ (P := fun v y ↦ ∀ x, R.val ![x, y] → P v x) hf

lemma bexs_bounded {R : Semiformula.Operator L 2} (hR : R ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : ℬ.DefinableBoundedFunction f)
    (hP : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∃ x, R.val ![x, f v] ∧ P v x := by
  have h := Definable.bexs hR (P := fun u x ↦ P (u ·.succ) x)
    (hP.retraction (0 :> fun i ↦ i.succ.succ)) #0
  exact h.bounded_substitution₁ (P := fun v y ↦ ∃ x, R.val ![x, y] ∧ P v x) hf

lemma bounded_substitution_with_param {P : (Fin k → V) → (Fin n → V) → Prop}
    {f : Fin k → (Fin n → V) → V}
    (hP : ℌ.Definable fun w : Fin (k + n) → V ↦
      P (fun i ↦ w (i.castAdd n)) (fun j ↦ w (j.natAdd k)))
    (hf : ∀ i, ℬ.DefinableBoundedFunction (f i)) :
    ℌ.Definable fun v ↦ P (f · v) v := by
  induction k generalizing n with
  | zero =>
    let e : Fin (0 + n) → Fin n := Fin.cast (Nat.zero_add n)
    have h₀ : ℌ.Definable fun v : Fin n → V ↦ P ![] v := by
      apply (hP.retraction e).of_iff
      intro v
      apply iff_of_eq
      congr 1
      · funext i
        exact Fin.elim0 i
      · funext j
        apply congrArg v
        apply Fin.ext
        simp [e]
    simpa [Matrix.empty_eq] using h₀
  | succ k ih =>
    let e : Fin ((k + 1) + n) → Fin ((k + n) + 1) := Fin.cast (by omega)
    let Q (u : Fin (k + n) → V) (x : V) :=
      P (x :> fun i ↦ u (i.castAdd n)) (fun j ↦ u (j.natAdd k))
    have hP' : ℌ.Definable fun w : Fin ((k + n) + 1) → V ↦ Q (w ·.succ) (w 0) := by
      apply (hP.retraction e).of_iff
      intro w
      apply iff_of_eq
      change P (w 0 :> fun i ↦ w ((i.castAdd n).succ))
          (fun j ↦ w ((j.natAdd k).succ)) =
        P (fun i ↦ w (e (i.castAdd n))) (fun j ↦ w (e (j.natAdd (k + 1))))
      congr 1
      · funext i
        cases i using Fin.cases <;> (apply congrArg w; apply Fin.ext; simp [e])
      · funext j
        apply congrArg w
        apply Fin.ext
        simp [e, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hf₀ : ℬ.DefinableBoundedFunction
        (fun u : Fin (k + n) → V ↦ f 0 (fun j ↦ u (j.natAdd k))) :=
      (hf 0).retraction (Fin.natAdd k)
    have h₁ := hP'.bounded_substitution₁ hf₀
    let P' (u : Fin k → V) (v : Fin n → V) := P (f 0 v :> u) v
    have hP₁ : ℌ.Definable fun w : Fin (k + n) → V ↦
        P' (fun i ↦ w (i.castAdd n)) (fun j ↦ w (j.natAdd k)) :=
      h₁.of_iff fun w ↦ by simp [P', Q]
    have hf₁ : ∀ i : Fin k, ℬ.DefinableBoundedFunction (f i.succ) := fun i ↦ hf i.succ
    have h₂ := ih hP₁ hf₁
    exact h₂.of_iff fun v ↦ by
      apply iff_of_eq
      congr 1
      ext i
      cases i using Fin.cases <;> simp

lemma bounded_substitution {P : (Fin k → V) → Prop} {f : Fin k → (Fin n → V) → V}
    (hP : ℌ.Definable P) (hf : ∀ i, ℬ.DefinableBoundedFunction (f i)) :
    ℌ.Definable fun v ↦ P (f · v) := by
  have hP' : ℌ.Definable fun w : Fin (k + n) → V ↦
      P (fun i ↦ w (i.castAdd n)) := hP.retraction (fun i ↦ i.castAdd n)
  simpa using hP'.bounded_substitution_with_param (P := fun x _ ↦ P x) hf

lemma bounded_comp₁ {P : V → Prop} (hP : ℌ.DefinablePred P)
    {f : (Fin n → V) → V} (hf : ℬ.DefinableBoundedFunction f) :
    ℌ.Definable fun v ↦ P (f v) := by
  simpa using hP.bounded_substitution (f := ![f]) (by simp [hf])

lemma bounded_comp₂ {P : V → V → Prop} (hP : ℌ.DefinableRel P)
    {f₁ f₂ : (Fin n → V) → V}
    (hf₁ : ℬ.DefinableBoundedFunction f₁) (hf₂ : ℬ.DefinableBoundedFunction f₂) :
    ℌ.Definable fun v ↦ P (f₁ v) (f₂ v) := by
  simpa using hP.bounded_substitution (f := ![f₁, f₂]) (by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂])

lemma bounded_comp₃ {P : V → V → V → Prop} (hP : ℌ.DefinableRel₃ P)
    {f₁ f₂ f₃ : (Fin n → V) → V}
    (hf₁ : ℬ.DefinableBoundedFunction f₁) (hf₂ : ℬ.DefinableBoundedFunction f₂)
    (hf₃ : ℬ.DefinableBoundedFunction f₃) :
    ℌ.Definable fun v ↦ P (f₁ v) (f₂ v) (f₃ v) := by
  simpa using hP.bounded_substitution (f := ![f₁, f₂, f₃]) (by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma bounded_comp₄ {P : V → V → V → V → Prop} (hP : ℌ.DefinableRel₄ P)
    {f₁ f₂ f₃ f₄ : (Fin n → V) → V}
    (hf₁ : ℬ.DefinableBoundedFunction f₁) (hf₂ : ℬ.DefinableBoundedFunction f₂)
    (hf₃ : ℬ.DefinableBoundedFunction f₃) (hf₄ : ℬ.DefinableBoundedFunction f₄) :
    ℌ.Definable fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) := by
  simpa using hP.bounded_substitution (f := ![f₁, f₂, f₃, f₄]) (by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

end Definable

namespace DefinableFunction

lemma bounded_comp {F : (Fin l → V) → V} {f : Fin l → (Fin k → V) → V}
    (hF : ℌ.DefinableFunction F) (hf : ∀ i, ℬ.DefinableBoundedFunction (f i)) :
    ℌ.DefinableFunction fun v ↦ F (f · v) := by
  let e : Fin (l + 1) → Fin (l + (k + 1)) :=
    Fin.cases (Fin.natAdd l (0 : Fin (k + 1))) (fun i ↦ i.castAdd (k + 1))
  let P (x : Fin l → V) (u : Fin (k + 1) → V) := u 0 = F x
  have hP : ℌ.Definable fun w : Fin (l + (k + 1)) → V ↦
      P (fun i ↦ w (i.castAdd (k + 1))) (fun j ↦ w (j.natAdd l)) := by
    apply (hF.rel.retraction e).of_iff
    intro w
    apply iff_of_eq
    congr 1
  have hf' : ∀ i, ℬ.DefinableBoundedFunction
      (fun u : Fin (k + 1) → V ↦ f i (u ·.succ)) := fun i ↦
    (hf i).retraction Fin.succ
  have h := hP.bounded_substitution_with_param (P := P) hf'
  exact h.of_iff fun v ↦ by simp [P]

end DefinableFunction

lemma DefinableFunction₁.bounded_comp {F : V → V} {f : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₁ F) (hf : ℬ.DefinableBoundedFunction f) :
    ℌ.DefinableFunction fun v ↦ F (f v) := by
  simpa using DefinableFunction.bounded_comp
    (F := fun v : Fin 1 → V ↦ F (v 0)) (f := ![f]) hF (by simp [hf])

lemma DefinableFunction₂.bounded_comp {F : V → V → V}
    {f₁ f₂ : (Fin k → V) → V} (hF : ℌ.DefinableFunction₂ F)
    (hf₁ : ℬ.DefinableBoundedFunction f₁) (hf₂ : ℬ.DefinableBoundedFunction f₂) :
    ℌ.DefinableFunction fun v ↦ F (f₁ v) (f₂ v) := by
  simpa using DefinableFunction.bounded_comp
    (F := fun v : Fin 2 → V ↦ F (v 0) (v 1)) (f := ![f₁, f₂]) hF (by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂])

lemma DefinableFunction₃.bounded_comp {F : V → V → V → V}
    {f₁ f₂ f₃ : (Fin k → V) → V} (hF : ℌ.DefinableFunction₃ F)
    (hf₁ : ℬ.DefinableBoundedFunction f₁) (hf₂ : ℬ.DefinableBoundedFunction f₂)
    (hf₃ : ℬ.DefinableBoundedFunction f₃) :
    ℌ.DefinableFunction fun v ↦ F (f₁ v) (f₂ v) (f₃ v) := by
  simpa using DefinableFunction.bounded_comp
    (F := fun v : Fin 3 → V ↦ F (v 0) (v 1) (v 2))
    (f := ![f₁, f₂, f₃]) hF (by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

end HierarchySymbol

end FFL.FirstOrder.Bounding
