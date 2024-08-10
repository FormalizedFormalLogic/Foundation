import Arithmetization.Vorspiel.Lemmata
import Arithmetization.Vorspiel.Graph
import Logic.FirstOrder.Arith.StrictHierarchy

/-!

# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `𝚺-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `𝚺-[m]`.
- `𝚷-[m].Semiformula ξ n` is a `Semiformula ℒₒᵣ ξ n` which is `𝚷-[m]`.
- `𝚫-[m].Semiformula ξ n` is a pair of `𝚺-[m].Semiformula ξ n` and `𝚷-[m].Semiformula ξ n`.
- `ProperOn` : `p.ProperOn M` iff `p`'s two element `p.sigma` and `p.pi` are equivalent on model `M`.

-/

namespace LO.Arith

variable {V : Type*}

structure BooleanSystem (V : Type*) where
  VecPr : {k : ℕ} → ((Fin k → V) → Prop) → Prop
  verum : VecPr fun _ : Fin k → V ↦ ⊤
  and {P Q : (Fin k → V) → Prop} : VecPr P → VecPr Q → VecPr fun v ↦ P v ∧ Q v
  not {P : (Fin k → V) → Prop} : VecPr P → VecPr fun v ↦ ¬P v
  equal : VecPr fun v : Fin 2 → V ↦ v 0 = v 1
  replace {k l} {P : (Fin k → V) → Prop} (hP : VecPr P) (f : Fin k → Fin l) : VecPr fun v ↦ P fun i ↦ v (f i)

variable [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐏𝐀⁻]

variable (V)

class BooleanSystem.BoundedQuantifier (𝔅 : BooleanSystem V) where
  IsPolynomial : {k : ℕ} → ((Fin k → V) → V) → Prop
  polynomial_comp {k} (F : (Fin k → V) → V) (fs : Fin k → (Fin l → V) → V) :
    IsPolynomial F → (∀ i, IsPolynomial (fs i)) → IsPolynomial (fun v ↦ F (fun i ↦ fs i v))
  polynomial_replace {p : (Fin k → V) → V} (hp : IsPolynomial p) (f : Fin k → Fin l) : IsPolynomial (fun v ↦ p (fun i ↦ v (f i)))
  polynomial_nth (i : Fin k) : IsPolynomial (· i)
  polynomial_monotone {p : (Fin k → V) → V} (h : IsPolynomial p) {v w} : v ≤ w → p v ≤ p w
  ball_poly {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop} :
    IsPolynomial f → 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0)) → 𝔅.VecPr fun v ↦ ∀ x ≤ f v, P v x
  lessThan : 𝔅.VecPr fun v : Fin 2 → V ↦ v 0 < v 1

variable {V}

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

section BoundedQuantifier

open BoundedQuantifier

variable [𝔅.BoundedQuantifier]

variable (𝔅)

def BoundedVecFunc {k} (f : (Fin k → V) → V) : Prop := 𝔅.VecPr (Function.Graphᵥ f) ∧ ∃ p, IsPolynomial 𝔅 p ∧ f ≤ p

variable {𝔅}

lemma BoundedVecFunc.vecPr {k} {f : (Fin k → V) → V} (h : 𝔅.BoundedVecFunc f) : 𝔅.VecPr (Function.Graphᵥ f) := h.1

lemma BoundedVecFunc.le_poly {k} {f : (Fin k → V) → V} (h : 𝔅.BoundedVecFunc f) : ∃ p, IsPolynomial 𝔅 p ∧ f ≤ p := h.2

@[simp] lemma BoundedVecFunc.nth (i : Fin k) : 𝔅.BoundedVecFunc (· i) := by
  constructor
  · apply equal'
  · exact ⟨(· i), polynomial_nth i, by simp⟩

lemma BoundedVecFunc.replace {f : (Fin k → V) → V} (hf : 𝔅.BoundedVecFunc f) (c : Fin k → Fin l) :
    𝔅.BoundedVecFunc (fun v ↦ f (fun i ↦ v (c i))) := by
  constructor
  · apply of_iff (𝔅.replace (l := l + 1) hf.vecPr (0 :> fun x ↦ (c x).succ)) <| by
      intro v; simp [Function.Graphᵥ]
  · rcases hf.le_poly with ⟨p, pp, hfp⟩
    refine ⟨fun v ↦ p (fun i ↦ v (c i)), by apply polynomial_replace pp, by intro v; simpa using hfp _⟩

lemma lessThan' (i j : Fin k) : 𝔅.VecPr fun v ↦ v i < v j := by
  simpa using 𝔅.replace lessThan ![i, j]

lemma lessThanOrEq (i j : Fin k) : 𝔅.VecPr fun v ↦ v i ≤ v j := by
  simp [le_iff_lt_or_eq]
  apply or
  · apply lessThan'
  · apply equal'

lemma BoundedQuantifier.bex_poly {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (pf : IsPolynomial 𝔅 f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∃ x ≤ f v, P v x := of_not <| by
  simp only [not_exists, not_and]; exact ball_poly pf (𝔅.not hP)

lemma BoundedQuantifier.bex_vec_poly {k} {p : Fin l → (Fin k → V) → V} {P : (Fin k → V) → (Fin l → V) → Prop}
    (pp : ∀ i, IsPolynomial 𝔅 (p i)) (hP : 𝔅.VecPr fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    𝔅.VecPr fun v ↦ ∃ w ≤ (p · v), P v w := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [exists_le_vec_iff_exists_le_exists_vec]
    apply bex_poly (pp 0)
    apply ih
    · intro i; apply polynomial_replace (pp i.succ)
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
    apply and
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
      BooleanSystem.substitution (l := l + 1) hF.vecPr (f := (· 0) :> fun i v ↦ f i (v ·.succ))
        (by intro i; cases' i using Fin.cases with i
            · simp
            · simpa using BoundedVecFunc.replace (hf i) _)
  · rcases hF.le_poly with ⟨p, hp, hFp⟩
    choose ps hps using fun i ↦ (hf i).le_poly
    refine ⟨fun v ↦ p fun i ↦ ps i v, polynomial_comp p ps hp (fun i ↦ (hps i).1), ?_⟩
    intro v; exact le_trans (hFp (f · v)) (polynomial_monotone hp (fun i ↦ (hps i).2 v))

lemma ball_le {k} {f : (Fin k → V) → V} {P : (Fin k → V) → V → Prop}
    (hf : 𝔅.BoundedVecFunc f) (hP : 𝔅.VecPr (fun v ↦ P (v ·.succ) (v 0))) :
    𝔅.VecPr fun v ↦ ∀ x ≤ f v, P v x := by
  rcases hf.le_poly with ⟨p, hp, hfp⟩
  have : 𝔅.VecPr fun v ↦ ∀ x ≤ p v, x ≤ f v → P v x := by
    apply ball_poly hp
    apply imply
    · simpa using substitution (𝔅.lessThanOrEq 0 1)
        (f := ![(· 0), fun v ↦ f (v ·.succ)]) (by simpa using hf.replace Fin.succ)
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
      (f := ![(· 0), fun v ↦ f (v ·.succ)]) (by simpa using hf.replace Fin.succ)
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

end BoundedQuantifier

end BooleanSystem
