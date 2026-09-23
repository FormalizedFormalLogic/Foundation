module

public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic
public import Foundation.FirstOrder.Tarski.Monotone

/-!
# Term-bounded definable functions

The arithmetic definition of boundedness is retained using an arbitrary language and `≤`.
`CompatibleLE` connects this bound to the bounding operator. Closure under composition
additionally uses a preorder and monotone interpretations of function symbols.
These operator-parametric closure lemmas follow the arithmetic formalization and are
technical generalizations of its elementary bounded-witness arguments.
-/

@[expose] public section
namespace FFL.FirstOrder.Bounding

open scoped Bounding

variable {ξ : Type*} {n : ℕ}

variable {L : Language} {ℬ : FirstOrder.Bounding L}
variable {R : FirstOrder.Semiformula.Operator L 2}
variable {V : Type*} [Tarski.Structure L V]

/-- The non-strict bound is equality or the relation used for bounded quantifiers. -/
class CompatibleLE (R : FirstOrder.Semiformula.Operator L 2) (V : Type*)
    [Tarski.Structure L V] [LE V] : Prop where
  le_iff (x y : V) : x ≤ y ↔ x = y ∨ R.val ![x, y]

instance compatibleLT [L.LT] [PartialOrder V] [Tarski.Structure.LT L V] :
    CompatibleLE (FirstOrder.Semiformula.Operator.LT.lt (L := L)) V where
  le_iff x y := by simpa using (le_iff_eq_or_lt : x ≤ y ↔ x = y ∨ x < y)

variable {ℌ : HierarchySymbol} {Γ Γ' : SigmaPiDelta}

section

variable [LE V] (L)

class Bounded (f : (Fin k → V) → V) : Prop where
  bounded : ∃ t : Semiterm L V k, ∀ v : Fin k → V, f v ≤ t.val v id

abbrev Bounded₁ (f : V → V) : Prop := Bounded (L := L) (k := 1) (fun v ↦ f (v 0))

abbrev Bounded₂ (f : V → V → V) : Prop := Bounded (L := L) (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev Bounded₃ (f : V → V → V → V) : Prop := Bounded (L := L) (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

instance (f : (Fin k → V) → V) [h : Bounded (L := L) f] : Bounded (L := L) f := by
  rcases h with ⟨t, ht⟩
  exact ⟨t, by simpa⟩

end

namespace Bounded

@[simp] lemma var [Preorder V] {k} (i : Fin k) : Bounded (L := L) fun v : Fin k → V ↦ v i := ⟨#i, by intro _; simp⟩

@[simp] lemma const [Preorder V] {k} (c : V) : Bounded (L := L) (fun _ : Fin k → V ↦ c) := ⟨&c, by intro _; simp⟩

@[simp] lemma term_retraction [Preorder V] (t : Semiterm L V n) (e : Fin n → Fin k) :
    Bounded (L := L) fun v : Fin k → V ↦ t.val (fun x ↦ v (e x)) id :=
  ⟨Rew.subst (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs, Function.comp_def]⟩

@[simp] lemma term [Preorder V] (t : Semiterm L V k) : Bounded (L := L) fun v : Fin k → V => t.val v id :=
  ⟨t, by intro _; simp⟩

lemma retraction [LE V] {f : (Fin k → V) → V} (hf : Bounded (L := L) f) (e : Fin k → Fin n) :
    Bounded (L := L) fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.subst (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs, Function.comp_def, ht]⟩

lemma comp [Preorder V] [Tarski.Structure.Monotone L V] {k} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V} (hf : Bounded (L := L) f) (hg : ∀ i, Bounded (L := L) (g i)) :
    Bounded (L := L) (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.subst tg tf, by
      intro v
      simpa [Semiterm.val_substs, Function.comp_def]
        using! le_trans (htf (g · v)) (Tarski.Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by simp))⟩

end Bounded

lemma Bounded₁.comp [Preorder V] [Tarski.Structure.Monotone L V] {f : V → V} {k} {g : (Fin k → V) → V} (hf : Bounded₁ (L := L) f) (hg : Bounded (L := L) g) :
    Bounded (L := L) (fun v ↦ f (g v)) := Bounded.comp hf (l := 1) (fun _ ↦ hg)

lemma Bounded₂.comp [Preorder V] [Tarski.Structure.Monotone L V] {f : V → V → V} {k} {g₁ g₂ : (Fin k → V) → V}
    (hf : Bounded₂ (L := L) f) (hg₁ : Bounded (L := L) g₁) (hg₂ : Bounded (L := L) g₂) :
    Bounded (L := L) (fun v ↦ f (g₁ v) (g₂ v)) := Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma Bounded₃.comp [Preorder V] [Tarski.Structure.Monotone L V] {f : V → V → V → V} {k} {g₁ g₂ g₃ : (Fin k → V) → V}
    (hf : Bounded₃ (L := L) f) (hg₁ : Bounded (L := L) g₁) (hg₂ : Bounded (L := L) g₂) (hg₃ : Bounded (L := L) g₃) :
    Bounded (L := L) (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Bounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases' i using Fin.cases with i <;> simp [*]
        cases' i using Fin.cases with i <;> simp [*])

section

variable [LE V] (ℬ)

def DefinableBoundedFunction {k} (f : (Fin k → V) → V) := Bounded (L := L) f ∧ 𝚺₀.DefinableFunction ℬ f

abbrev DefinableBoundedFunction₁ (f : V → V) : Prop := DefinableBoundedFunction ℬ (k := 1) (fun v => f (v 0))

abbrev DefinableBoundedFunction₂ (f : V → V → V) : Prop := DefinableBoundedFunction ℬ (k := 2) (fun v => f (v 0) (v 1))

abbrev DefinableBoundedFunction₃ (f : V → V → V → V) : Prop := DefinableBoundedFunction ℬ (k := 3) (fun v => f (v 0) (v 1) (v 2))

variable {ℬ}

lemma DefinableBoundedFunction.bounded {f : (Fin k → V) → V} (h : DefinableBoundedFunction ℬ f) : Bounded (L := L) f := h.1

lemma DefinableBoundedFunction₁.bounded {f : V → V} (h : DefinableBoundedFunction₁ ℬ f) : Bounded₁ (L := L) f := h.1

lemma DefinableBoundedFunction₂.bounded {f : V → V → V} (h : DefinableBoundedFunction₂ ℬ f) : Bounded₂ (L := L) f := h.1

lemma DefinableBoundedFunction₃.bounded {f : V → V → V → V} (h : DefinableBoundedFunction₃ ℬ f) : Bounded₃ (L := L) f := h.1

lemma DefinableBoundedFunction.definable {f : (Fin k → V) → V} (h : DefinableBoundedFunction ℬ f) : ℌ.DefinableFunction ℬ f := .of_zero h.2

lemma DefinableBoundedFunction₁.definable {f : V → V} (h : DefinableBoundedFunction₁ ℬ f) : ℌ.DefinableFunction₁ ℬ f := .of_zero h.2

lemma DefinableBoundedFunction₂.definable {f : V → V → V} (h : DefinableBoundedFunction₂ ℬ f) : ℌ.DefinableFunction₂ ℬ f := .of_zero h.2

lemma DefinableBoundedFunction₃.definable {f : V → V → V → V} (h : DefinableBoundedFunction₃ ℬ f) : ℌ.DefinableFunction₃ ℬ f := .of_zero h.2

namespace DefinableBoundedFunction

lemma of_polybounded_of_definable (f : (Fin k → V) → V) [hb : Bounded (L := L) f] [hf : 𝚺₀.DefinableFunction ℬ f] :
    DefinableBoundedFunction ℬ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : V → V) [hb : Bounded₁ (L := L) f] [hf : 𝚺₀.DefinableFunction₁ ℬ f] :
    DefinableBoundedFunction₁ ℬ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : V → V → V) [hb : Bounded₂ (L := L) f] [hf : 𝚺₀.DefinableFunction₂ ℬ f] :
    DefinableBoundedFunction₂ ℬ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : V → V → V → V) [hb : Bounded₃ (L := L) f] [hf : 𝚺₀.DefinableFunction₃ ℬ f] :
    DefinableBoundedFunction₃ ℬ f := ⟨hb, hf⟩

lemma retraction {f : (Fin k → V) → V} (hf : DefinableBoundedFunction ℬ f) (e : Fin k → Fin n) :
    DefinableBoundedFunction ℬ fun v ↦ f (fun i ↦ v (e i)) := ⟨hf.bounded.retraction e, hf.definable.retraction e⟩

end DefinableBoundedFunction

end

namespace HierarchySymbol.Definable

variable [hV : Preorder V] [hR : CompatibleLE R V]
variable (hmem : R ∈ ℬ)
include hV hR hmem

variable  {P Q : (Fin k → V) → Prop}

lemma ball' {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm L V k) :
    ℌ.Definable ℬ fun v ↦ ∀ x ≤ t.val v id, P v x := by
  have ht : ℌ.Definable ℬ fun v ↦ P v (t.val v id) := by
    simpa using h.retractiont (t :> fun i ↦ #i)
  exact (ht.and (h.ball hmem t)).of_iff fun v ↦ by
    simp [CompatibleLE.le_iff (R := R), or_imp, forall_and]

lemma bexs' {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm L V k) :
    ℌ.Definable ℬ fun v ↦ ∃ x ≤ t.val v id, P v x := by
  have ht : ℌ.Definable ℬ fun v ↦ P v (t.val v id) := by
    simpa using h.retractiont (t :> fun i ↦ #i)
  exact (ht.or (h.bexs hmem t)).of_iff fun v ↦ by
    simp [CompatibleLE.le_iff (R := R), or_and_right, exists_or]

lemma ball_boperator {S : Semiformula.Operator L 2} (hS : S ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable ℬ fun v ↦ ∀ x, S.val ![x, f v] → P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable ℬ fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∀ y, S.val ![y, x] → P v y := by
    apply bexs' hmem; apply and
    · exact hf.definable
    · suffices ℌ.Definable ℬ fun x ↦ ∀ y, S.val ![y, (#0).val (L := L) x id] → P (fun x_1 ↦ x x_1.succ) y by simpa
      apply ball hS ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma bexs_boperator {S : Semiformula.Operator L 2} (hS : S ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable ℬ fun v ↦ ∃ x, S.val ![x, f v] ∧ P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable ℬ fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∃ y, S.val ![y, x] ∧ P v y := by
    apply bexs' hmem; apply and
    · exact hf.definable
    · suffices ℌ.Definable ℬ fun x ↦ ∃ y, S.val ![y, (#0).val (L := L) x id] ∧ P (fun x_1 ↦ x x_1.succ) y by simpa
      apply bexs hS ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma ball_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable ℬ fun v ↦ ∀ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable ℬ fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∀ y ≤ x, P v y := by
    apply bexs' hmem; apply and
    · exact hf.definable
    · suffices ℌ.Definable ℬ fun x ↦ ∀ y ≤ (#0).val (L := L) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply ball' hmem ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma bexs_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : ℌ.Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable ℬ fun v ↦ ∃ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable ℬ fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∃ y ≤ x, P v y := by
    apply bexs' hmem; apply and
    · exact hf.definable
    · suffices ℌ.Definable ℬ fun x ↦ ∃ y ≤ (#0).val (L := L) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply bexs' hmem ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma ball_boperator_zero {S : Semiformula.Operator L 2} (hS : S ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : Γ-[0].Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Definable ℬ fun v ↦ ∀ x, S.val ![x, f v] → P v x := ball_boperator hmem hS hf h

lemma bexs_boperator_zero {S : Semiformula.Operator L 2} (hS : S ∈ ℬ)
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : Γ-[0].Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Definable ℬ fun v ↦ ∃ x, S.val ![x, f v] ∧ P v x := bexs_boperator hmem hS hf h

lemma ball_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : Γ-[0].Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Definable ℬ fun v ↦ ∀ x ≤ f v, P v x := ball_ble hmem hf h

lemma bexs_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction ℬ f) (h : Γ-[0].Definable ℬ fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[0].Definable ℬ fun v ↦ ∃ x ≤ f v, P v x := bexs_ble hmem hf h

lemma bexs_vec_le_boldfaceBoundedFunction {k} {φ : Fin l → (Fin k → V) → V} {P : (Fin k → V) → (Fin l → V) → Prop}
    (pp : ∀ i, DefinableBoundedFunction ℬ (φ i)) (hP : ℌ.Definable ℬ fun w : Fin (k + l) → V ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    ℌ.Definable ℬ fun v ↦ ∃ w ≤ (φ · v), P v w := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [Fin.exists_le_vec_iff_exists_le_exists_vec]
    apply bexs_ble hmem (pp 0)
    apply ih
    · intro i; apply DefinableBoundedFunction.retraction (pp i.succ)
    · let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
      exact of_iff (retraction hP g) <| by
        intro v; simp only [g]
        apply iff_of_eq; congr
        · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · ext i
          cases' i using Fin.cases with i
          · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]

lemma substitution_boldfaceBoundedFunction {f : Fin k → (Fin l → V) → V}
    (hP : ℌ.Definable ℬ P) (hf : ∀ i, DefinableBoundedFunction ℬ (f i)) :
    ℌ.Definable ℬ fun z ↦ P (f · z) := by
  have : ℌ.Definable ℬ fun v ↦ ∃ w ≤ (f · v), (∀ i, w i = f i v) ∧ P w := by
    apply bexs_vec_le_boldfaceBoundedFunction hmem hf
    apply and
    · apply fintype_all; intro i
      simpa using retraction (.of_zero (hf i).2) (i.natAdd l :> Fin.castAdd k)
    · apply retraction hP
  apply of_iff this <| by
    intro v; constructor
    · intro h; exact ⟨(f · v), by intro i; simp, by simp, h⟩
    · rintro ⟨w, hw, e, h⟩
      rcases funext e
      exact h

end HierarchySymbol.Definable

namespace DefinableBoundedFunction

lemma of_iff [LE V] {f g : (Fin k → V) → V} (H : DefinableBoundedFunction ℬ f) (h : ∀ v, f v = g v) : DefinableBoundedFunction ℬ g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

variable [Preorder V] [L.Eq] [Tarski.Structure.Eq L V]

@[simp] lemma var {k} (i : Fin k) : DefinableBoundedFunction ℬ (fun v : Fin k → V ↦ v i) := ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : V) : DefinableBoundedFunction ℬ (fun _ : Fin k → V ↦ c) := ⟨by simp, by simp⟩

@[simp] lemma term_retraction (t : Semiterm L V n) (e : Fin n → Fin k) :
    DefinableBoundedFunction ℬ fun v : Fin k → V ↦ t.val (fun x ↦ v (e x)) id := ⟨by simp, by simp⟩

@[simp] lemma term (t : Semiterm L V k) :
  DefinableBoundedFunction ℬ fun v : Fin k → V ↦ t.val v id := ⟨by simp, by simp⟩

end DefinableBoundedFunction

namespace HierarchySymbol.Definable

open DefinableBoundedFunction

variable [hV : Preorder V] [hR : CompatibleLE R V]
variable (hmem : R ∈ ℬ)
include hV hR hmem

lemma bcomp₁ {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : ℌ.DefinablePred ℬ P] (hf : DefinableBoundedFunction ℬ f) :
    ℌ.Definable ℬ fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f]) hP (by simp [*])

lemma bcomp₂ {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : ℌ.DefinableRel ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂) :
    ℌ.Definable ℬ fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃ {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR : ℌ.DefinableRel₃ ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) :
    ℌ.Definable ℬ fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂, f₃]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄ {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : ℌ.DefinableRel₄ ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) (hf₄ : DefinableBoundedFunction ℬ f₄) :
    ℌ.Definable ℬ fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂, f₃, f₄]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₁_zero {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : Γ-[0].DefinablePred ℬ P] (hf : DefinableBoundedFunction ℬ f) :
    Γ-[0].Definable ℬ fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f]) hP (by simp [*])

lemma bcomp₂_zero {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : Γ-[0].DefinableRel ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂) :
    Γ-[0].Definable ℬ fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃_zero {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR : Γ-[0].DefinableRel₃ ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) :
    Γ-[0].Definable ℬ fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂, f₃]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄_zero {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : Γ-[0].DefinableRel₄ ℬ R]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) (hf₄ : DefinableBoundedFunction ℬ f₄) :
    Γ-[0].Definable ℬ fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction hmem (f := ![f₁, f₂, f₃, f₄]) hR (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

end HierarchySymbol.Definable

section Functions

variable [hV : Preorder V] [hR : CompatibleLE R V] [L.Eq] [Tarski.Structure.Eq L V]
variable (hmem : R ∈ ℬ)
include hV hR hmem

lemma HierarchySymbol.DefinableFunction.bcomp {k} {F : (Fin l → V) → V} {f : Fin l → (Fin k → V) → V}
    (hF : ℌ.DefinableFunction ℬ F) (hf : ∀ i, DefinableBoundedFunction ℬ (f i)) :
    ℌ.DefinableFunction ℬ (fun v ↦ F (f · v)) := by
  simpa using Definable.substitution_boldfaceBoundedFunction hmem (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases' i using Fin.cases with i
    · simp
    · simpa using DefinableBoundedFunction.retraction (hf i) Fin.succ

lemma HierarchySymbol.DefinableFunction₁.bcomp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₁ ℬ F) (hf : DefinableBoundedFunction ℬ f) :
    ℌ.DefinableFunction ℬ (fun v ↦ F (f v)) :=
  HierarchySymbol.DefinableFunction.bcomp hmem (f := ![f]) hF (by simp [*])

lemma HierarchySymbol.DefinableFunction₂.bcomp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₂ ℬ F)
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂) :
    ℌ.DefinableFunction ℬ (fun v ↦ F (f₁ v) (f₂ v)) :=
  HierarchySymbol.DefinableFunction.bcomp hmem (f := ![f₁, f₂]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma HierarchySymbol.DefinableFunction₃.bcomp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₃ ℬ F)
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) :
    ℌ.DefinableFunction ℬ (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  HierarchySymbol.DefinableFunction.bcomp hmem (f := ![f₁, f₂, f₃]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

variable [Tarski.Structure.Monotone L V]

lemma DefinableBoundedFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₁ ℬ F) (hf : DefinableBoundedFunction ℬ f) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f v)) := ⟨hF.bounded.comp hf.bounded, hF.definable.bcomp hmem hf⟩

lemma DefinableBoundedFunction₂.comp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₂ ℬ F)
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f₁ v) (f₂ v)) := ⟨hF.bounded.comp hf₁.bounded hf₂.bounded, hF.definable.bcomp hmem hf₁ hf₂⟩

lemma DefinableBoundedFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₃ ℬ F)
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  ⟨hF.bounded.comp hf₁.bounded hf₂.bounded hf₃.bounded, hF.definable.bcomp hmem hf₁ hf₂ hf₃⟩

lemma DefinableBoundedFunction.comp₁ {k} {F : V → V} {f : (Fin k → V) → V}
    [hFb : Bounded₁ (L := L) F] [hFd : 𝚺₀.DefinableFunction₁ ℬ F] (hf : DefinableBoundedFunction ℬ f) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f v)) := DefinableBoundedFunction₁.comp hmem ⟨hFb, hFd⟩ hf

lemma DefinableBoundedFunction.comp₂ {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    [hFb : Bounded₂ (L := L) F] [hFd : 𝚺₀.DefinableFunction₂ ℬ F]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f₁ v) (f₂ v)) := DefinableBoundedFunction₂.comp hmem ⟨hFb, hFd⟩ hf₁ hf₂

lemma DefinableBoundedFunction.comp₃ {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    [hFb : Bounded₃ (L := L) F] [hFd : 𝚺₀.DefinableFunction₃ ℬ F]
    (hf₁ : DefinableBoundedFunction ℬ f₁) (hf₂ : DefinableBoundedFunction ℬ f₂)
    (hf₃ : DefinableBoundedFunction ℬ f₃) :
    DefinableBoundedFunction ℬ (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) := DefinableBoundedFunction₃.comp hmem ⟨hFb, hFd⟩ hf₁ hf₂ hf₃

section

open HierarchySymbol

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableBoundedFunction.comp₁
  DefinableBoundedFunction.comp₂
  DefinableBoundedFunction.comp₃

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Definable.bcomp₁_zero
  Definable.bcomp₂_zero
  Definable.bcomp₃_zero
  Definable.bcomp₄_zero

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.ball_boperator_zero
  Definable.ball_ble_zero
  Definable.bexs_boperator_zero
  Definable.bexs_ble_zero

end

end Functions

end FFL.FirstOrder.Bounding
