import Arithmetization.Definability.Basic
import Arithmetization.Definability.Init

/-!

# Boolean System


-/

namespace LO

variable {V : Type*}

structure BooleanSystem (V : Type*) where
  VecPr : {k : ℕ} → ((Fin k → V) → Prop) → Prop
  verum : VecPr fun _ : Fin k → V ↦ ⊤
  and {P Q : (Fin k → V) → Prop} : VecPr P → VecPr Q → VecPr fun v ↦ P v ∧ Q v
  not {P : (Fin k → V) → Prop} : VecPr P → VecPr fun v ↦ ¬P v
  equal : VecPr fun v : Fin 2 → V ↦ v 0 = v 1
  replace {k l} {P : (Fin k → V) → Prop} (hP : VecPr P) (f : Fin k → Fin l) : VecPr fun v ↦ P fun i ↦ v (f i)

namespace BooleanSystem

variable {𝔅 : BooleanSystem V} {P Q : (Fin k → V) → Prop}

lemma of_iff (hP : 𝔅.VecPr P) (h : ∀ x, P x ↔ Q x) : 𝔅.VecPr Q := by
  have : P = Q := funext fun x ↦ by simp [h]
  rcases this; exact hP

lemma of_not (h : 𝔅.VecPr fun v ↦ ¬P v) : 𝔅.VecPr P := by simpa using 𝔅.not h

lemma falsum : 𝔅.VecPr fun _ : Fin k → V ↦ ⊥ := of_not <| by simpa using 𝔅.verum

@[simp] lemma constant (P : Prop) : 𝔅.VecPr fun _ : Fin k → V ↦ P := by
  by_cases h : P <;> simp [h]
  · exact 𝔅.verum
  · exact 𝔅.falsum

lemma or (hP : 𝔅.VecPr P) (hQ : 𝔅.VecPr Q) : 𝔅.VecPr fun v ↦ P v ∨ Q v := of_not <| by
  simp; apply 𝔅.and
  · apply 𝔅.not hP
  · apply 𝔅.not hQ

lemma imply (hP : 𝔅.VecPr P) (hQ : 𝔅.VecPr Q) : 𝔅.VecPr fun v ↦ P v → Q v := by
  simp only [imp_iff_not_or]; apply or
  · apply 𝔅.not hP
  · exact hQ

lemma iff (hP : 𝔅.VecPr P) (hQ : 𝔅.VecPr Q) : 𝔅.VecPr fun v ↦ P v ↔ Q v := by
  simp only [iff_iff_implies_and_implies]
  exact 𝔅.and (imply hP hQ) (imply hQ hP)

lemma conj {P : Fin l → (Fin k → V) → Prop} (hP : ∀ i, 𝔅.VecPr (P i)) : 𝔅.VecPr fun v ↦ ∀ i, P i v := by
  induction l
  case zero => simp
  case succ l ih =>
    simp [forall_fin_iff_zero_and_forall_succ]
    apply and
    · exact hP 0
    · exact ih (fun i ↦ hP i.succ)

lemma equal' (i j : Fin k) : 𝔅.VecPr fun v ↦ v i = v j := by
  simpa using 𝔅.replace 𝔅.equal ![i, j]

variable (𝔅)

class Quantifer where
  all {k} {P : (Fin k → V) → V → Prop} : 𝔅.VecPr (fun x ↦ P (x ·.succ) (x 0)) → 𝔅.VecPr fun x ↦ ∀ z, P x z
  ex {k} {P : (Fin k → V) → V → Prop} : 𝔅.VecPr (fun x ↦ P (x ·.succ) (x 0)) → 𝔅.VecPr fun x ↦ ∃ z, P x z

variable {𝔅}

end BooleanSystem

namespace Arith

variable [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐏𝐀⁻]

variable (V)

structure BoundedSystem extends BooleanSystem V where
  Polynomial : {k : ℕ} → ((Fin k → V) → V) → Prop
  polynomial_comp {k} (F : (Fin k → V) → V) (fs : Fin k → (Fin l → V) → V) :
    Polynomial F → (∀ i, Polynomial (fs i)) → Polynomial (fun v ↦ F (fun i ↦ fs i v))
  polynomial_replace {p : (Fin k → V) → V} (hp : Polynomial p) (f : Fin k → Fin l) : Polynomial (fun v ↦ p (fun i ↦ v (f i)))
  polynomial_nth (i : Fin k) : Polynomial (· i)
  polynomial_monotone {p : (Fin k → V) → V} (h : Polynomial p) {v w} : v ≤ w → p v ≤ p w
  ball_poly {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop} :
    Polynomial f → VecPr (fun v ↦ P (v ·.succ) (v 0)) → VecPr fun v ↦ ∀ x ≤ f v, P v x
  lessThan : VecPr fun v : Fin 2 → V ↦ v 0 < v 1

variable {V}

namespace BoundedSystem

open LO.BooleanSystem

variable {𝔅 : Arith.BoundedSystem V} {P Q : (Fin k → V) → Prop}

variable (𝔅)

abbrev Pred (P : V → Prop) : Prop := 𝔅.VecPr (k := 1) fun v ↦ P (v 0)

abbrev Rel (R : V → V → Prop) : Prop := 𝔅.VecPr (k := 2) fun v ↦ R (v 0) (v 1)

abbrev Rel₃ (R : V → V → V → Prop) : Prop := 𝔅.VecPr (k := 3) fun v ↦ R (v 0) (v 1) (v 2)

abbrev Rel₄ (R : V → V → V → V → Prop) : Prop := 𝔅.VecPr (k := 4) fun v ↦ R (v 0) (v 1) (v 2) (v 3)

abbrev UBVecFunc {k} (f : (Fin k → V) → V) : Prop := 𝔅.VecPr (Function.Graphᵥ f)

abbrev UBConstant (c : V) : Prop := 𝔅.UBVecFunc (k := 0) fun _ ↦ c

abbrev UBFunction (f : V → V) : Prop := 𝔅.UBVecFunc (k := 1) fun v ↦ f (v 0)

abbrev UBFunction₂ (f : V → V → V) : Prop := 𝔅.UBVecFunc (k := 2) fun v ↦ f (v 0) (v 1)

abbrev UBFunction₃ (f : V → V → V → V) : Prop := 𝔅.UBVecFunc (k := 3) fun v ↦ f (v 0) (v 1) (v 2)

def BoundedVecFunc {k} (f : (Fin k → V) → V) : Prop := 𝔅.VecPr (Function.Graphᵥ f) ∧ ∃ p, 𝔅.Polynomial p ∧ f ≤ p

abbrev BoundedConstant (c : V) : Prop := 𝔅.BoundedVecFunc (k := 0) fun _ ↦ c

abbrev BoundedFunction (f : V → V) : Prop := 𝔅.BoundedVecFunc (k := 1) fun v ↦ f (v 0)

abbrev BoundedFunction₂ (f : V → V → V) : Prop := 𝔅.BoundedVecFunc (k := 2) fun v ↦ f (v 0) (v 1)

abbrev BoundedFunction₃ (f : V → V → V → V) : Prop := 𝔅.BoundedVecFunc (k := 3) fun v ↦ f (v 0) (v 1) (v 2)

variable {𝔅}

lemma BoundedVecFunc.vecPr {k} {f : (Fin k → V) → V} (h : 𝔅.BoundedVecFunc f) : 𝔅.VecPr (Function.Graphᵥ f) := h.1

lemma BoundedVecFunc.le_poly {k} {f : (Fin k → V) → V} (h : 𝔅.BoundedVecFunc f) : ∃ p, 𝔅.Polynomial p ∧ f ≤ p := h.2

lemma UBVecFunc.boundedVecFunc_of_le {f g : (Fin k → V) → V} (hf : 𝔅.UBVecFunc f) (hg : 𝔅.BoundedVecFunc g)
    (h : f ≤ g) : 𝔅.BoundedVecFunc f := by
  constructor
  · exact hf
  · rcases hg.le_poly with ⟨p, hp, hgp⟩
    exact ⟨p, hp, le_trans h hgp⟩

lemma UBFunction.boundedVecFunc_of_le {f g : V → V} (hf : 𝔅.UBFunction f) (hg : 𝔅.BoundedFunction g) (h : f ≤ g) : 𝔅.BoundedFunction f :=
  UBVecFunc.boundedVecFunc_of_le hf hg (by intro v; simpa using h _)

lemma UBFunction₂.boundedVecFunc_of_le {f g : V → V → V} (hf : 𝔅.UBFunction₂ f) (hg : 𝔅.BoundedFunction₂ g) (h : f ≤ g) : 𝔅.BoundedFunction₂ f :=
  UBVecFunc.boundedVecFunc_of_le hf hg (by intro v; simpa using h _ _)

lemma UBFunction₃.boundedVecFunc_of_le {f g : V → V → V → V} (hf : 𝔅.UBFunction₃ f) (hg : 𝔅.BoundedFunction₃ g) (h : f ≤ g) : 𝔅.BoundedFunction₃ f :=
  UBVecFunc.boundedVecFunc_of_le hf hg (by intro v; simpa using h _ _ _)

@[simp] lemma BoundedVecFunc.nth (i : Fin k) : 𝔅.BoundedVecFunc (· i) := by
  constructor
  · apply equal'
  · exact ⟨(· i), 𝔅.polynomial_nth i, by simp⟩

lemma BoundedVecFunc.replace {f : (Fin k → V) → V} (hf : 𝔅.BoundedVecFunc f) (c : Fin k → Fin l) :
    𝔅.BoundedVecFunc (fun v ↦ f (fun i ↦ v (c i))) := by
  constructor
  · apply of_iff (𝔅.replace (l := l + 1) hf.vecPr (0 :> fun x ↦ (c x).succ)) <| by
      intro v; simp [Function.Graphᵥ]
  · rcases hf.le_poly with ⟨p, pp, hfp⟩
    refine ⟨fun v ↦ p (fun i ↦ v (c i)), by apply 𝔅.polynomial_replace pp, by intro v; simpa using hfp _⟩

lemma lessThan' (i j : Fin k) : 𝔅.VecPr fun v ↦ v i < v j := by
  simpa using 𝔅.replace 𝔅.lessThan ![i, j]

lemma lessThanOrEq (i j : Fin k) : 𝔅.VecPr fun v ↦ v i ≤ v j := by
  simp [le_iff_lt_or_eq]
  apply 𝔅.or
  · apply lessThan'
  · apply equal'

lemma BoundedQuantifier.bex_poly {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (pf : Polynomial 𝔅 f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∃ x ≤ f v, P v x := of_not <| by
  simp only [not_exists, not_and]; exact 𝔅.ball_poly pf (𝔅.not hP)

lemma BoundedQuantifier.bex_vec_poly {k} {p : Fin l → (Fin k → V) → V} {P : (Fin k → V) → (Fin l → V) → Prop}
    (pp : ∀ i, Polynomial 𝔅 (p i)) (hP : 𝔅.VecPr fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝔅.VecPr fun v ↦ ∃ w ≤ (p · v), P v w := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [exists_le_vec_iff_exists_le_exists_vec]
    apply bex_poly (pp 0)
    apply ih
    · intro i; apply 𝔅.polynomial_replace (pp i.succ)
    · let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
      exact of_iff (𝔅.replace hP g) <| by
        intro v; simp [g]
        apply iff_of_eq; congr
        · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · ext i
          cases' i using Fin.cases with i
          · congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · congr 1; ext; simp [Matrix.vecAppend_eq_ite]

lemma substitution {f : Fin k → (Fin l → V) → V} (hP : 𝔅.VecPr P) (hf : ∀ i, 𝔅.BoundedVecFunc (f i)) :
    𝔅.VecPr fun z ↦ P (fun i ↦ f i z) := by
  choose p hp using fun i ↦ (hf i).le_poly
  have : 𝔅.VecPr fun v ↦ ∃ w ≤ (p · v), (∀ i, w i = f i v) ∧ P w := by
    apply BoundedQuantifier.bex_vec_poly (fun i ↦ (hp i).1)
    apply 𝔅.and
    · apply conj; intro i
      simpa using 𝔅.replace (hf i).vecPr (i.natAdd l :> Fin.castAdd k)
    · apply 𝔅.replace hP
  apply of_iff this <| by
    intro v; constructor
    · rintro ⟨w, hw, e, h⟩
      rcases funext e
      exact h
    · intro h; exact ⟨(f · v), by intro i; simpa using (hp i).2 v, by simp, h⟩

lemma BoundedVecFunc.substitution {F : (Fin k → V) → V} {f : Fin k → (Fin l → V) → V}
    (hF : 𝔅.BoundedVecFunc F) (hf : ∀ i, 𝔅.BoundedVecFunc (f i)) :
    𝔅.BoundedVecFunc fun v ↦ F (fun i ↦ f i v) := by
  constructor
  · simpa [Function.Graphᵥ] using
      BoundedSystem.substitution (l := l + 1) hF.vecPr (f := (· 0) :> fun i v ↦ f i (v ·.succ))
        (by intro i; cases' i using Fin.cases with i
            · simp
            · simpa using BoundedVecFunc.replace (hf i) _)
  · rcases hF.le_poly with ⟨p, hp, hFp⟩
    choose ps hps using fun i ↦ (hf i).le_poly
    refine ⟨fun v ↦ p fun i ↦ ps i v, 𝔅.polynomial_comp p ps hp (fun i ↦ (hps i).1), ?_⟩
    intro v; exact le_trans (hFp (f · v)) (𝔅.polynomial_monotone hp (fun i ↦ (hps i).2 v))

lemma ball_le {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (hf : 𝔅.BoundedVecFunc f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∀ x ≤ f v, P v x := by
  rcases hf.le_poly with ⟨p, hp, hfp⟩
  have : 𝔅.VecPr fun v ↦ ∀ x ≤ p v, x ≤ f v → P v x := by
    apply 𝔅.ball_poly hp
    apply imply
    · simpa using substitution (𝔅.lessThanOrEq 0 1)
        (f := ![(· 0), fun v ↦ f (v ·.succ)])
        (by simpa [forall_fin_iff_zero_and_forall_succ] using hf.replace Fin.succ)
    · exact hP
  exact of_iff this <| by
    intro v; constructor
    · intro h x hx
      exact h x (le_trans hx (hfp v)) hx
    · intro h x _ hx
      exact h x hx

lemma bex_le {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (hf : 𝔅.BoundedVecFunc f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∃ x ≤ f v, P v x := of_not <| by
  simp only [not_exists, not_and]
  exact ball_le hf (𝔅.not hP)

lemma ball_lt {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (hf : 𝔅.BoundedVecFunc f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∀ x < f v, P v x := by
  have : 𝔅.VecPr fun v ↦ ∀ x ≤ f v, x < f v → P v x := by
    apply ball_le hf
    apply imply ?_ hP
    simpa using substitution (𝔅.lessThan' 0 1)
      (f := ![(· 0), fun v ↦ f (v ·.succ)])
      (by simpa [forall_fin_iff_zero_and_forall_succ] using hf.replace Fin.succ)
  exact of_iff this <| by
    intro v; constructor
    · intro h x hx
      exact h x (le_of_lt hx) hx
    · intro h x _ hx
      exact h x hx

lemma bex_lt {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (hf : 𝔅.BoundedVecFunc f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∃ x < f v, P v x := of_not <| by
  simp only [not_exists, not_and]
  exact ball_lt hf (𝔅.not hP)

variable (𝔅)

abbrev FactVecPr {k} (P : (Fin k → V) → Prop) : Prop := Fact (𝔅.VecPr P)

abbrev IsPred (P : V → Prop) : Prop := Fact (𝔅.Pred P)

abbrev IsRel (R : V → V → Prop) : Prop := Fact (𝔅.Rel R)

abbrev IsRel₃ (R : V → V → V → Prop) : Prop := Fact (𝔅.Rel₃ R)

abbrev IsBoundedConstant (c : V) : Prop := Fact (𝔅.BoundedConstant c)

abbrev IsBoundedFunction (f : V → V) : Prop := Fact (𝔅.BoundedFunction f)

abbrev IsBoundedFunction₂ (f : V → V → V) : Prop := Fact (𝔅.BoundedFunction₂ f)

abbrev IsBoundedFunction₃ (f : V → V → V → V) : Prop := Fact (𝔅.BoundedFunction₃ f)

variable {𝔅}

instance : 𝔅.IsRel (· = ·) := ⟨equal' 0 1⟩

instance : 𝔅.IsRel (· < ·) := ⟨lessThan' 0 1⟩

instance : 𝔅.IsRel (· ≤ ·) := ⟨lessThanOrEq 0 1⟩

lemma Pred.comp {P : V → Prop} [hP : 𝔅.IsPred P] {f : (Fin k → V) → V} (hf : 𝔅.BoundedVecFunc f) :
    𝔅.VecPr fun v ↦ P (f v) := by
  simpa using substitution hP.out (f := ![f]) (by simp [hf])

lemma Rel.comp {R : V → V → Prop} [hR : 𝔅.IsRel R] {f₁ f₂ : (Fin k → V) → V} (hf₁ : 𝔅.BoundedVecFunc f₁) (hf₂ : 𝔅.BoundedVecFunc f₂) :
    𝔅.VecPr fun v ↦ R (f₁ v) (f₂ v) := by
  simpa using substitution hR.out (f := ![f₁, f₂]) (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂])

lemma Rel₃.comp {R : V → V → V → Prop} [hR : 𝔅.IsRel₃ R] {f₁ f₂ f₃ : (Fin k → V) → V}
    (hf₁ : 𝔅.BoundedVecFunc f₁) (hf₂ : 𝔅.BoundedVecFunc f₂) (hf₃ : 𝔅.BoundedVecFunc f₃) :
    𝔅.VecPr fun v ↦ R (f₁ v) (f₂ v) (f₃ v) := by
  simpa using substitution hR.out (f := ![f₁, f₂, f₃]) (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

@[simp] lemma Constant.comp (c : V) [hc : 𝔅.IsBoundedConstant c] :
    𝔅.BoundedVecFunc fun _ : Fin k → V ↦ c :=
  BoundedVecFunc.substitution (l := k) hc.out (f := ![]) (by simp)

lemma Function.comp {F : V → V} [hF : 𝔅.IsBoundedFunction F] {f : (Fin k → V) → V} (hf : 𝔅.BoundedVecFunc f) :
    𝔅.BoundedVecFunc fun v ↦ F (f v) := by
  simpa using BoundedVecFunc.substitution hF.out (f := ![f]) (by simp [hf])

lemma Function₂.comp {F : V → V → V} [hF : 𝔅.IsBoundedFunction₂ F] {f₁ f₂ : (Fin k → V) → V}
    (hf₁ : 𝔅.BoundedVecFunc f₁) (hf₂ : 𝔅.BoundedVecFunc f₂) :
    𝔅.BoundedVecFunc fun v ↦ F (f₁ v) (f₂ v) := by
  simpa using BoundedVecFunc.substitution hF.out (f := ![f₁, f₂]) (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂])

lemma Function₃.comp {F : V → V → V → V} [hF : 𝔅.IsBoundedFunction₃ F] {f₁ f₂ f₃ : (Fin k → V) → V}
    (hf₁ : 𝔅.BoundedVecFunc f₁) (hf₂ : 𝔅.BoundedVecFunc f₂) (hf₃ : 𝔅.BoundedVecFunc f₃) :
    𝔅.BoundedVecFunc fun v ↦ F (f₁ v) (f₂ v) (f₃ v) := by
  simpa using BoundedVecFunc.substitution hF.out (f := ![f₁, f₂, f₃]) (by simp [forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

variable (𝔅)

class Arithmetical where
  zero : 𝔅.BoundedConstant 0
  one  : 𝔅.BoundedConstant 1
  add  : 𝔅.BoundedFunction₂ (· + ·)
  mul  : 𝔅.BoundedFunction₂ (· * ·)

variable {𝔅}

section Arithmetical

variable [𝔅.Arithmetical]

instance : 𝔅.IsBoundedConstant 0 := ⟨Arithmetical.zero⟩

instance : 𝔅.IsBoundedConstant 1 := ⟨Arithmetical.one⟩

instance : 𝔅.IsBoundedFunction₂ (· + ·) := ⟨Arithmetical.add⟩

instance : 𝔅.IsBoundedFunction₂ (· * ·) := ⟨Arithmetical.mul⟩

instance (n : ℕ) : 𝔅.IsBoundedConstant n := ⟨by
  induction n
  case zero => simp
  case succ n ih =>
    simpa using Function₂.comp ih (by simp)⟩

end Arithmetical

variable (𝔅)

class Boldface where
  const (z : V) : 𝔅.BoundedVecFunc (k := 0) fun _ ↦ z

variable {𝔅}

instance [𝔅.Boldface] (z : V) : 𝔅.IsBoundedConstant z := ⟨Boldface.const z⟩

end BoundedSystem

section

open Lean.Parser.Tactic (config)

attribute [aesop (rule_sets := [Definability]) norm]
  sq
  Arith.pow_three
  pow_four

attribute [aesop 5 (rule_sets := [Definability]) safe]
  BoundedSystem.Function.comp
  BoundedSystem.Function₂.comp
  BoundedSystem.Function₃.comp
  BoundedSystem.Pred.comp
  BoundedSystem.Rel.comp
  BoundedSystem.Rel₃.comp

attribute [aesop 8 (rule_sets := [Definability]) safe]
  BoundedSystem.ball_le
  BoundedSystem.bex_le
  BoundedSystem.ball_lt
  BoundedSystem.bex_lt

attribute [aesop 10 (rule_sets := [Definability]) safe]
  BooleanSystem.not
  BooleanSystem.imply
  BooleanSystem.iff

attribute [aesop 11 (rule_sets := [Definability]) safe]
  BooleanSystem.and
  BooleanSystem.or

macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)

macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

end

end LO.Arith
