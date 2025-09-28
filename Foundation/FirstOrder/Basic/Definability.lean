import Foundation.FirstOrder.Basic.Semantics.Elementary
import Foundation.FirstOrder.Basic.Operator
import Foundation.FirstOrder.Basic.BinderNotation
import Foundation.FirstOrder.Basic.AesopInit
import Foundation.Vorspiel.Graph

/-!
# Relations and functions defined by a first-order formula (with parameter)
-/

namespace LO.FirstOrder

variable {L : Language} {M : Type*} [Structure L M]

class Defined (R : outParam ((Fin k → M) → Prop)) (φ : Semisentence L k) : Prop where
  iff : ∀ v, R v ↔ Semiformula.Evalbm M v φ

def DefinedWithParam (R : (Fin k → M) → Prop) (φ : Semiformula L M k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm M v id φ

@[simp] lemma Defined.eval_iff {R : (Fin k → M) → Prop} {φ : Semisentence L k} [h : Defined R φ] (v) :
    Semiformula.Evalbm M v φ ↔ R v := (h.iff v).symm

lemma DefinedWithParam.iff {R : (Fin k → M) → Prop} {φ : Semiformula L M k} (h : DefinedWithParam R φ) (v) :
    Semiformula.Evalm M v id φ ↔ R v := (h v).symm

abbrev DefinedFunction (f : (Fin k → M) → M) (φ : Semisentence L (k + 1)) : Prop :=
  Defined (fun v ↦ v 0 = f (v ·.succ)) φ

abbrev DefinedPred (P : M → Prop) (φ : Semisentence L 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ

abbrev DefinedRel (R : M → M → Prop) (φ : Semisentence L 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

abbrev DefinedRel₃ (R : M → M → M → Prop) (φ : Semisentence L 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

abbrev DefinedRel₄ (R : M → M → M → M → Prop) (φ : Semisentence L 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₀ (c : M) (φ : Semisentence L 1) : Prop :=
  DefinedFunction (fun _ => c) φ

abbrev DefinedFunction₁ (f : M → M) (φ : Semisentence L 2) : Prop :=
  DefinedFunction (fun v ↦ f (v 0)) φ

abbrev DefinedFunction₂ (f : M → M → M) (φ : Semisentence L 3) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1)) φ

abbrev DefinedFunction₃ (f : M → M → M → M) (φ : Semisentence L 4) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2)) φ

abbrev DefinedFunction₄ (f : M → M → M → M → M) (φ : Semisentence L 5) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₅ (f : M → M → M → M → M → M) (φ : Semisentence L 6) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

notation K "-relation " P " via " φ => DefinedRel (L := K) P φ

notation K "-relation₃ " P " via " φ => DefinedRel₃ (L := K) P φ

notation K "-relation₄ " P " via " φ => DefinedRel₄ (L := K) P φ

notation K "-function₀ " c " via " φ => DefinedFunction₀ (L := K) c φ

notation K "-function₁ " f " via " φ => DefinedFunction₁ (L := K) f φ

notation K "-function₂ " f " via " φ => DefinedFunction₂ (L := K) f φ

notation K "-function₃ " f " via " φ => DefinedFunction₃ (L := K) f φ

notation K "-function₄ " f " via " φ => DefinedFunction₄ (L := K) f φ

notation K "-function₅ " f " via " φ => DefinedFunction₅ (L := K) f φ

notation K "-predicate[" N "] " P " via " φ => DefinedPred (L := K) (M := N) P φ

notation K "-relation[" N "] " P " via " φ => DefinedRel (L := K) (M := N) P φ

notation K "-relation₃[" N "] " P " via " φ => DefinedRel₃ (L := K) (M := N) P φ

notation K "-relation₄[" N "] " P " via " φ => DefinedRel₄ (L := K) (M := N) P φ

notation K "-function₀[" N "] " c " via " φ => DefinedFunction₀ (L := K) (M := N) c φ

notation K "-function₁[" N "] " f " via " φ => DefinedFunction₁ (L := K) (M := N) f φ

notation K "-function₂[" N "] " f " via " φ => DefinedFunction₂ (L := K) (M := N) f φ

notation K "-function₃[" N "] " f " via " φ => DefinedFunction₃ (L := K) (M := N) f φ

notation K "-function₄[" N "] " f " via " φ => DefinedFunction₄ (L := K) (M := N) f φ

notation K "-function₅[" N "] " f " via " φ => DefinedFunction₅ (L := K) (M := N) f φ

namespace Language

variable (L)

class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ φ : Semiformula L M k, DefinedWithParam P φ

abbrev DefinablePred (P : M → Prop) : Prop := L.Definable (k := 1) fun v ↦ P (v 0)

abbrev DefinableRel (P : M → M → Prop) : Prop := L.Definable (k := 2) (fun v ↦ P (v 0) (v 1))

abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := L.Definable (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop := L.Definable (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

abbrev DefinableRel₅ (P : M → M → M → M → M → Prop) : Prop := L.Definable (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

abbrev DefinableRel₆ (P : M → M → M → M → M → M → Prop) : Prop := L.Definable (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

abbrev DefinableFunction (f : (Fin k → M) → M) : Prop := Definable (k := k + 1) L fun v ↦ v 0 = f (v ·.succ)

abbrev DefinableFunction₀ (c : M) : Prop := L.DefinableFunction (k := 0) (fun _ ↦ c)

abbrev DefinableFunction₁ (f : M → M) : Prop := L.DefinableFunction (k := 1) (fun v ↦ f (v 0))

abbrev DefinableFunction₂ (f : M → M → M) : Prop := L.DefinableFunction (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := L.DefinableFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

abbrev DefinableFunction₄ (f : M → M → M → M → M) : Prop := L.DefinableFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

abbrev DefinableFunction₅ (f : M → M → M → M → M → M) : Prop := L.DefinableFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {L}

notation L "-predicate " P => DefinablePred L P

notation L "-relation " P => DefinableRel L P

notation L "-relation₃ " P => DefinableRel₃ L P

notation L "-relation₄ " P => DefinableRel₄ L P

notation L "-relation₅ " P => DefinableRel₅ L P

notation L "-function₁ " f => DefinableFunction₁ L f

notation L "-function₂ " f => DefinableFunction₂ L f

notation L "-function₃ " f => DefinableFunction₃ L f

notation L "-function₄ " f => DefinableFunction₄ L f

notation L "-predicate[" N "] " P => DefinablePred (M := N) L P

notation L "-relation[" N "] " P => DefinableRel (M := N) L P

notation L "-relation₃[" N "] " P => DefinableRel₃ (M := N) L P

notation L "-relation₄[" N "] " P => DefinableRel₄ (M := N) L P

notation L "-relation₅[" N "] " P => DefinableRel₅ (M := N) L P

notation L "-function₁[" N "] " f => DefinableFunction₁ (M := N) L f

notation L "-function₂[" N "] " f => DefinableFunction₂ (M := N) L f

notation L "-function₃[" N "] " f => DefinableFunction₃ (M := N) L f

notation L "-function₄[" N "] " f => DefinableFunction₄ (M := N) L f

end Language

namespace Defined

lemma to_definable {R : (Fin k → M) → Prop} {φ : Semisentence L k} (hR : Defined R φ) : L.Definable R :=
  ⟨Rewriting.emb φ, fun v ↦ by simp [Semiformula.eval_emb]⟩

end Defined

namespace DefinedFunction

lemma to_definable {f : (Fin k → M) → M} {φ : Semisentence L (k + 1)} (hf : DefinedFunction f φ) : L.DefinableFunction f :=
  Defined.to_definable hf

end DefinedFunction

namespace Language

namespace Definable

variable {P Q R : (Fin k → M) → Prop}

lemma of_iff {P Q : (Fin k → M) → Prop} (H : L.Definable Q) (h : ∀ x, P x ↔ Q x) : L.Definable P := by
  rwa [show P = Q from by funext v; simp [h]]

@[simp] lemma const (p : Prop) : L.Definable fun _ : Fin k → M ↦ p := by
  by_cases hp : p
  · exact ⟨⊤, by intro _; simp [hp]⟩
  · exact ⟨⊥, by intro _; simp [hp]⟩

@[grind] lemma and {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∧ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋏ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind] lemma or {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∨ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋎ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind] lemma imp {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v → S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ➝ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind] lemma not {R : (Fin k → M) → Prop} (hR : L.Definable R) :
    L.Definable fun v : Fin k → M ↦ ¬R v := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∼φ, by intro _; simp [hR.iff]⟩

@[grind] lemma biconditional {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ↔ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⭤ ψ, by intro _; simp [hR.iff, hS.iff]⟩

lemma all {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∀ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∀' φ, fun v ↦ by simp [hR.iff]⟩

lemma ex {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∃ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∃' φ, fun v ↦ by simp [hR.iff]⟩

instance eq [L.Eq] [Structure.Eq L M] : L-relation[M] Eq := ⟨“x y. x = y”, fun _ ↦ by simp⟩

instance lt [L.LT] [LT M] [Structure.LT L M] : L-relation[M] _root_.LT.lt := ⟨“x y. x < y”, fun _ ↦ by simp⟩

instance mem [L.Mem] [Membership M M] [Structure.Mem L M] : L-relation[M] Membership.mem := ⟨“x y. y ∈ x”, fun _ ↦ by simp⟩

lemma fconj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∀ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩕ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fdisj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∃ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, DefinedWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩖ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fintype_all [Fintype ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∀ i, P i v := by
  simpa using fconj Finset.univ h

lemma fintype_ex [Fintype ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∃ i, P i v := by
  simpa using fdisj Finset.univ h

lemma retraction (h : L.Definable P) {n} (f : Fin k → Fin n) :
    L.Definable fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨(Rew.subst fun i ↦ #(f i)) ▹ φ, fun v ↦ by simp [←hφ.iff]⟩

lemma exVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h : L.Definable fun w : Fin (k + l) → M ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∃ ys : Fin l → M, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∃ y, ∃ ys : Fin l → M, P v (y :> ys) by
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

lemma allVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h : L.Definable fun w : Fin (k + l) → M ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∀ ys : Fin l → M, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∀ y, ∀ ys : Fin l → M, P v (y :> ys) by
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

lemma substitution {P : (Fin k → M) → Prop} {f : Fin k → (Fin l → M) → M}
    (hP : L.Definable P) (hf : ∀ i, L.DefinableFunction (f i)) :
    L.Definable fun z ↦ P (f · z) := by
  have : L.Definable fun z ↦ ∃ ys : Fin k → M, (∀ i, ys i = f i z) ∧ P ys := by
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

end Definable

lemma DefinablePred.comp {P : M → Prop} {k} {f : (Fin k → M) → M}
    [hP : L.DefinablePred P] (hf : L.DefinableFunction f) :
    L.Definable (fun v ↦ P (f v)) :=
  Definable.substitution (f := ![f]) hP (by simpa using hf)

lemma DefinableRel.comp {P : M → M → Prop} {k} {f g : (Fin k → M) → M}
    [hP : L.DefinableRel P]
    (hf : L.DefinableFunction f) (hg : L.DefinableFunction g) :
    L.Definable fun v ↦ P (f v) (g v) :=
  Definable.substitution (f := ![f, g]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma DefinableRel₃.comp {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hP : L.DefinableRel₃ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma DefinableRel₄.comp {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hP : L.DefinableRel₄ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma DefinableRel₅.comp {k} {P : M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hP : L.DefinableRel₅ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])

lemma DefinablePred.of_iff {P Q : M → Prop}
    (H : L.DefinablePred Q) (h : ∀ x, P x ↔ Q x) : L.DefinablePred P := by
  rwa [show P = Q from by funext v; simp [h]]

instance DefinableFunction₁.graph {f : M → M} [h : L.DefinableFunction₁ f] :
  L.DefinableRel (Function.Graph f) := h

instance DefinableFunction₂.graph {f : M → M → M} [h : L.DefinableFunction₂ f] :
  L.DefinableRel₃ (Function.Graph₂ f) := h

instance DefinableFunction₃.graph {f : M → M → M → M} [h : L.DefinableFunction₃ f] :
  L.DefinableRel₄ (Function.Graph₃ f) := h

/-!
### Definable functions
-/

variable [L.Eq] [Structure.Eq L M]

namespace DefinableFunction

instance projection (i : Fin k) : L.DefinableFunction fun w : Fin k → M ↦ w i :=
  ⟨“x. x = #i.succ”, fun _ ↦ by simp⟩

instance const (c : M) :  L.DefinableFunction fun _ : Fin k → M ↦ c :=
  ⟨“x. x = &c”, fun _ ↦ by simp⟩

lemma substitution {f : Fin k → (Fin l → M) → M}
    (hF : L.DefinableFunction F) (hf : ∀ i, L.DefinableFunction (f i)) :
    L.DefinableFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using Definable.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases' i using Fin.cases with i
    · simpa using projection _
    · simpa using Definable.retraction (hf i) (0 :> (·.succ.succ))

instance hAdd [L.Add] [Add M] [Structure.Add L M] : L-function₂[M] HAdd.hAdd := ⟨“x y z. x = y + z”, fun _ ↦ by simp⟩

instance hMul [L.Mul] [Mul M] [Structure.Mul L M] : L-function₂[M] HMul.hMul := ⟨“x y z. x = y * z”, fun _ ↦ by simp⟩

end DefinableFunction

lemma DefinableFunction₁.comp {k} {F : M → M} {f : (Fin k → M) → M}
    [hF : L.DefinableFunction₁ F] (hf : L.DefinableFunction f) :
    L.DefinableFunction (fun v ↦ F (f v)) :=
  DefinableFunction.substitution (f := ![f]) hF (by simp [hf])

lemma DefinableFunction₂.comp {k} {F : M → M → M} {f₁ f₂ : (Fin k → M) → M}
    [hF : L.DefinableFunction₂ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₃.comp {k} {F : M → M → M → M} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hF : L.DefinableFunction₃ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₄.comp {k} {F : M → M → M → M → M} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hF : L.DefinableFunction₄ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₅.comp {k} {F : M → M → M → M → M → M} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hF : L.DefinableFunction₅ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

section aesop

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

attribute [aesop (rule_sets := [Definability]) norm]
  Function.comp_def

attribute [aesop 4 (rule_sets := [Definability]) safe]
  DefinableFunction.const
  DefinableFunction.projection
  Definable.const

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction₁.comp
  DefinableFunction₂.comp
  DefinableFunction₃.comp

attribute [aesop 6 (rule_sets := [Definability]) safe]
  DefinablePred.comp
  DefinableRel.comp
  DefinableRel₃.comp
  DefinableRel₄.comp

attribute [aesop 10 (rule_sets := [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.biconditional

attribute [aesop 11 (rule_sets := [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.ex

macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)

macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

example {f : M → M} {g : M → M → M} [L.DefinableFunction₁ f] [L.DefinableFunction₂ g] (c : M) :
    L.DefinableRel fun x y : M ↦ ∀ z, f x = g y (g (f z) c) := by
  definability?

example [L.Mem] [Membership M M] [Structure.Mem L M] {f : M → M} [L.DefinableFunction₁ f] :
    L.DefinableRel fun x y : M ↦ f x = y ↔ ∀ z, z ∈ f x ↔ z ∈ y := by
  definability?

end aesop

end LO.FirstOrder.Language
