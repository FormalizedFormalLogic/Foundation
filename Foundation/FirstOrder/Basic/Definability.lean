import Foundation.FirstOrder.Basic.Semantics.Elementary
import Foundation.FirstOrder.Basic.Operator
import Foundation.FirstOrder.Basic.BinderNotation

/-!
# relations and functions defined by a first-order formula (with parameter)
-/

namespace Matrix

lemma appendr_castAdd (v : Fin l → α) (w : Fin k → α) : appendr v w (Fin.castAdd l i) = w i := by {
  simp [appendr, ]
 }

end Matrix

namespace LO.FirstOrder

variable {L : Language} {V : Type*} [Structure L V]

class Defined {k} (R : (Fin k → V) → Prop) (φ : Semisentence L k) : Prop where
  iff : ∀ v, R v ↔ Semiformula.Evalbm V v φ

abbrev DefinedFunction (f : (Fin k → V) → V) (φ : Semisentence L (k + 1)) : Prop :=
  Defined (L := L) (fun v ↦ v 0 = f (v ·.succ)) φ

variable (L)

abbrev DefinedPred (P : V → Prop) (φ : Semisentence L 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ

abbrev DefinedRel (R : V → V → Prop) (φ : Semisentence L 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : Semisentence L 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : Semisentence L 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₀ (c : V) (φ : Semisentence L 1) : Prop :=
  DefinedFunction (fun _ => c) φ

abbrev DefinedFunction₁ (f : V → V) (φ : Semisentence L 2) : Prop :=
  DefinedFunction (fun v ↦ f (v 0)) φ

abbrev DefinedFunction₂ (f : V → V → V) (φ : Semisentence L 3) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1)) φ

abbrev DefinedFunction₃ (f : V → V → V → V) (φ : Semisentence L 4) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2)) φ

abbrev DefinedFunction₄ (f : V → V → V → V → V) (φ : Semisentence L 5) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₅ (f : V → V → V → V → V → V) (φ : Semisentence L 6) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

variable {L}

class DefinedWithParam {k} (R : (Fin k → V) → Prop) (φ : Semiformula L V k) : Prop where
  iff : ∀ v, R v ↔ Semiformula.Evalm V v id φ

variable (L)

class IsDefinable {k} (P : (Fin k → V) → Prop) : Prop where
  definable : ∃ φ : Semiformula L V k, DefinedWithParam P φ

abbrev IsDefinablePred (P : V → Prop) : Prop := IsDefinable L (k := 1) fun v ↦ P (v 0)

abbrev IsDefinableRel (P : V → V → Prop) : Prop := IsDefinable L (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev IsDefinableRel₃ (P : V → V → V → Prop) : Prop := IsDefinable L (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev IsDefinableRel₄ (P : V → V → V → V → Prop) : Prop := IsDefinable L (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev IsDefinableRel₅ (P : V → V → V → V → V → Prop) : Prop := IsDefinable L (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

abbrev IsDefinableRel₆ (P : V → V → V → V → V → V → Prop) : Prop := IsDefinable L (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

abbrev IsDefinableFunction (f : (Fin k → V) → V) : Prop :=
  IsDefinable (k := k + 1) L fun v ↦ v 0 = f (v ·.succ)

abbrev IsDefinableFunction₀ (c : V) : Prop := IsDefinableFunction L (k := 0) (fun _ ↦ c)

abbrev IsDefinableFunction₁ (f : V → V) : Prop := IsDefinableFunction L (k := 1) (fun v ↦ f (v 0))

abbrev IsDefinableFunction₂ (f : V → V → V) : Prop := IsDefinableFunction L (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev IsDefinableFunction₃ (f : V → V → V → V) : Prop := IsDefinableFunction L (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

abbrev IsDefinableFunction₄ (f : V → V → V → V → V) : Prop := IsDefinableFunction L (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

abbrev IsDefinableFunction₅ (f : V → V → V → V → V → V) : Prop := IsDefinableFunction L (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {L}

notation L "-relation " P " via " φ => DefinedRel L P φ

notation L "-relation₃ " P " via " φ => DefinedRel₃ L P φ

notation L "-relation₄ " P " via " φ => DefinedRel₄ L P φ

notation L "-function₀ " c " via " φ => DefinedFunction₀ L c φ

notation L "-function₁ " f " via " φ => DefinedFunction₁ L f φ

notation L "-function₂ " f " via " φ => DefinedFunction₂ L f φ

notation L "-function₃ " f " via " φ => DefinedFunction₃ L f φ

notation L "-function₄ " f " via " φ => DefinedFunction₄ L f φ

notation L "-function₅ " f " via " φ => DefinedFunction₅ L f φ


notation L "-predicate " P => IsDefinablePred L P

notation L "-relation " P => IsDefinableRel L P

notation L "-relation₃ " P => IsDefinableRel₃ L P

notation L "-relation₄ " P => IsDefinableRel₄ L P

notation L "-relation₅ " P => IsDefinableRel₅ L P

notation L "-function₁ " f => IsDefinableFunction₁ L f

notation L "-function₂ " f => IsDefinableFunction₂ L f

notation L "-function₃ " f => IsDefinableFunction₃ L f

notation L "-function₄ " f => IsDefinableFunction₄ L f


notation L "-predicate[" V "] " P " via " φ => DefinedPred (V := V) L P φ

notation L "-relation[" V "] " P " via " φ => DefinedRel (V := V) L P φ

notation L "-relation₃[" V "] " P " via " φ => DefinedRel₃ (V := V) L P φ

notation L "-relation₄[" V "] " P " via " φ => DefinedRel₄ (V := V) L P φ

notation L "-function₀[" V "] " c " via " φ => DefinedFunction₀ (V := V) L c φ

notation L "-function₁[" V "] " f " via " φ => DefinedFunction₁ (V := V) L f φ

notation L "-function₂[" V "] " f " via " φ => DefinedFunction₂ (V := V) L f φ

notation L "-function₃[" V "] " f " via " φ => DefinedFunction₃ (V := V) L f φ

notation L "-function₄[" V "] " f " via " φ => DefinedFunction₄ (V := V) L f φ

notation L "-function₅[" V "] " f " via " φ => DefinedFunction₅ (V := V) L f φ


notation L "-predicate[" V "] " P => IsDefinablePred (V := V) L P

notation L "-relation[" V "] " P => IsDefinableRel (V := V) L P

notation L "-relation₃[" V "] " P => IsDefinableRel₃ (V := V) L P

notation L "-relation₄[" V "] " P => IsDefinableRel₄ (V := V) L P

notation L "-relation₅[" V "] " P => IsDefinableRel₅ (V := V) L P

notation L "-function₁[" V "] " f => IsDefinableFunction₁ (V := V) L f

notation L "-function₂[" V "] " f => IsDefinableFunction₂ (V := V) L f

notation L "-function₃[" V "] " f => IsDefinableFunction₃ (V := V) L f

notation L "-function₄[" V "] " f => IsDefinableFunction₄ (V := V) L f

namespace Defined

lemma to_definable {R : (Fin k → V) → Prop} {φ : Semisentence L k} (hR : Defined R φ) : IsDefinable L R :=
  ⟨Rewriting.embedding φ, ⟨fun v ↦ by simp [Semiformula.eval_emb, hR.iff]⟩⟩

end Defined

namespace DefinedFunction

lemma to_definable {f : (Fin k → V) → V} {φ : Semisentence L (k + 1)} (hf : DefinedFunction f φ) : IsDefinableFunction L f :=
  Defined.to_definable hf

end DefinedFunction

namespace IsDefinable

variable {P Q R : (Fin k → V) → Prop}

lemma of_iff {P Q : (Fin k → V) → Prop} (H : IsDefinable L Q) (h : ∀ x, P x ↔ Q x) : IsDefinable L P := by
  rwa [show P = Q from by funext v; simp [h]]

@[simp, grind] lemma top : IsDefinable L fun _ : Fin k → V ↦ ⊤ := ⟨⊤, ⟨by simp⟩⟩

@[simp, grind] lemma bot : IsDefinable L fun _ : Fin k → V ↦ ⊥ := ⟨⊥, ⟨by simp⟩⟩

@[grind] lemma and {R S : (Fin k → V) → Prop} (hR : IsDefinable L R) (hS : IsDefinable L S) :
    IsDefinable L fun v : Fin k → V ↦ R v ∧ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋏ ψ, ⟨by simp [hR.iff, hS.iff]⟩⟩

@[grind] lemma or {R S : (Fin k → V) → Prop} (hR : IsDefinable L R) (hS : IsDefinable L S) :
    IsDefinable L fun v : Fin k → V ↦ R v ∨ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋎ ψ, ⟨by simp [hR.iff, hS.iff]⟩⟩

@[grind] lemma imp {R S : (Fin k → V) → Prop} (hR : IsDefinable L R) (hS : IsDefinable L S) :
    IsDefinable L fun v : Fin k → V ↦ R v → S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ➝ ψ, ⟨by simp [hR.iff, hS.iff]⟩⟩

@[grind] lemma not {R : (Fin k → V) → Prop} (hR : IsDefinable L R) :
    IsDefinable L fun v : Fin k → V ↦ ¬R v := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∼φ, ⟨by simp [hR.iff]⟩⟩

@[grind] lemma biconditional {R S : (Fin k → V) → Prop} (hR : IsDefinable L R) (hS : IsDefinable L S) :
    IsDefinable L fun v : Fin k → V ↦ R v ↔ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⭤ ψ, ⟨by simp [hR.iff, hS.iff]⟩⟩

lemma all {R : (Fin k → V) → V → Prop} (hR : IsDefinable L fun w ↦ R (w ·.succ) (w 0)) :
    IsDefinable L fun v : Fin k → V ↦ ∀ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∀' φ, ⟨fun v ↦ by simp [←hR.iff]⟩⟩

lemma ex {R : (Fin k → V) → V → Prop} (hR : IsDefinable L fun w ↦ R (w ·.succ) (w 0)) :
    IsDefinable L fun v : Fin k → V ↦ ∃ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∃' φ, ⟨fun v ↦ by simp [←hR.iff]⟩⟩

instance eq [L.Eq] [Structure.Eq L V] : L-relation[V] (· = ·) := ⟨“x y. x = y”, ⟨by simp⟩⟩

instance lt [L.LT] [LT V] [Structure.LT L V] : L-relation[V] (· < ·) := ⟨“x y. x < y”, ⟨by simp⟩⟩

instance mem [L.Mem] [Membership V V] [Structure.Mem L V] : L-relation[V] (· ∈ ·) := ⟨“x y. x ∈ y”, ⟨by simp⟩⟩

lemma fconj {P : ι → (Fin k → V) → Prop} (s : Finset ι)
    (h : ∀ i, IsDefinable L fun w : Fin k → V ↦ P i w) : IsDefinable L fun v : Fin k → V ↦ ∀ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩕ i ∈ s, φ i, ⟨fun v ↦ by simp [fun i ↦ (H i).iff]⟩⟩

lemma fdisj {P : ι → (Fin k → V) → Prop} (s : Finset ι)
    (h : ∀ i, IsDefinable L fun w : Fin k → V ↦ P i w) : IsDefinable L fun v : Fin k → V ↦ ∃ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩖ i ∈ s, φ i, ⟨fun v ↦ by simp [fun i ↦ (H i).iff]⟩⟩

lemma fintype_all [Fintype ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, IsDefinable L fun w : Fin k → V ↦ P i w) : IsDefinable L fun v : Fin k → V ↦ ∀ i, P i v := by
  simpa using fconj Finset.univ h

lemma fintype_ex [Fintype ι] {P : ι → (Fin k → V) → Prop}
    (h : ∀ i, IsDefinable L fun w : Fin k → V ↦ P i w) : IsDefinable L fun v : Fin k → V ↦ ∃ i, P i v := by
  simpa using fdisj Finset.univ h

lemma retraction (h : IsDefinable L P) {n} (f : Fin k → Fin n) :
    IsDefinable L fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨(Rew.substs fun i ↦ #(f i)) ▹ φ, ⟨fun v ↦ by simp [←hφ.iff]⟩⟩

lemma exVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : IsDefinable L fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    IsDefinable L fun v : Fin k → V ↦ ∃ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices IsDefinable L fun v : Fin k → V ↦ ∃ y, ∃ ys : Fin l → V, P v (y :> ys) by
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
        · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → V) → (Fin l → V) → Prop}
    (h : IsDefinable L fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    IsDefinable L fun v : Fin k → V ↦ ∀ ys : Fin l → V, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices IsDefinable L fun v : Fin k → V ↦ ∀ y, ∀ ys : Fin l → V, P v (y :> ys) by
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
        · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma substitution {P : (Fin k → V) → Prop} {f : Fin k → (Fin l → V) → V}
    (hP : IsDefinable L P) (hf : ∀ i, IsDefinableFunction L (f i)) :
    IsDefinable L fun z ↦ P (f · z) := by
  have : IsDefinable L fun z ↦ ∃ ys : Fin k → V, (∀ i, ys i = f i z) ∧ P ys := by
    apply exVec; apply and
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

end IsDefinable


lemma BoldfacePred.comp {P : V → Prop} {k} {f : (Fin k → V) → V}
    (hP : IsDefinablePred L P) (hf : IsDefinableFunction L f) :
    IsDefinable L (fun v ↦ P (f v)) :=
  IsDefinable.substitution (f := ![f]) hP (by simpa using hf)

lemma BoldfaceRel.comp {P : V → V → Prop} {k} {f g : (Fin k → V) → V}
    (hP : IsDefinableRel L P)
    (hf : IsDefinableFunction L f) (hg : IsDefinableFunction L g) :
    IsDefinable L fun v ↦ P (f v) (g v) :=
  IsDefinable.substitution (f := ![f, g]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma BoldfaceRel₃.comp {k} {P : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hP : IsDefinableRel₃ L P)
    (hf₁ : IsDefinableFunction L f₁) (hf₂ : IsDefinableFunction L f₂)
    (hf₃ : IsDefinableFunction L f₃) :
    IsDefinable L (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  IsDefinable.substitution (f := ![f₁, f₂, f₃]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma BoldfaceRel₄.comp {k} {P : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    (hP : IsDefinableRel₄ L P)
    (hf₁ : IsDefinableFunction L f₁) (hf₂ : IsDefinableFunction L f₂)
    (hf₃ : IsDefinableFunction L f₃) (hf₄ : IsDefinableFunction L f₄) :
    IsDefinable L (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  IsDefinable.substitution (f := ![f₁, f₂, f₃, f₄]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma BoldfaceRel₅.comp {k} {P : V → V → V → V → V → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → V) → V}
    (hP : IsDefinableRel₅ L P)
    (hf₁ : IsDefinableFunction L f₁) (hf₂ : IsDefinableFunction L f₂)
    (hf₃ : IsDefinableFunction L f₃) (hf₄ : IsDefinableFunction L f₄)
    (hf₅ : IsDefinableFunction L f₅) :
    IsDefinable L (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  IsDefinable.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])



end LO.FirstOrder
