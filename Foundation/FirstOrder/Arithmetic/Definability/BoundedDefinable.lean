module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Tarski.Monotone

@[expose] public section
namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic
open PeanoMinus

variable {ξ : Type*} {n k l : ℕ}

variable {V : Type*} [ORingStructure V]

variable {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} {Γ Γ' : SigmaPiDelta}

variable (ℌ)

class Bounded (f : (Fin k → V) → V) : Prop where
  bounded : ∃ t : ArithmeticSemiterm V k, ∀ v : Fin k → V, f v ≤ t.val v id

abbrev Bounded₁ (f : V → V) : Prop := Bounded (k := 1) (fun v ↦ f (v 0))

abbrev Bounded₂ (f : V → V → V) : Prop := Bounded (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev Bounded₃ (f : V → V → V → V) : Prop := Bounded (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

instance (f : (Fin k → V) → V) [h : Bounded f] : Bounded f := by
  rcases h with ⟨t, ht⟩
  exact ⟨t, by simpa⟩

variable {ℌ}

namespace Bounded

@[simp] lemma var [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {k} (i : Fin k) : Bounded fun v : Fin k → V ↦ v i :=
  ⟨#i, by intro _; simp⟩

@[simp] lemma const [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {k} (c : V) : Bounded (fun _ : Fin k → V ↦ c) :=
  ⟨&c, by intro _; simp⟩

@[simp] lemma term_retraction [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (t : ArithmeticSemiterm V n) (e : Fin n → Fin k) :
    Bounded fun v : Fin k → V ↦ t.val (fun x ↦ v (e x)) id :=
  ⟨Rew.subst (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs, Function.comp_def]⟩

@[simp] lemma term [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (t : ArithmeticSemiterm V k) :
    Bounded fun v : Fin k → V => t.val v id :=
  ⟨t, by intro _; simp⟩

lemma retraction {f : (Fin k → V) → V} (hf : Bounded f) (e : Fin k → Fin n) :
    Bounded fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.subst (fun x ↦ #(e x)) t,
    by intro _; simp [Semiterm.val_substs, Function.comp_def, ht]⟩

lemma comp [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {k} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V}
    (hf : Bounded f) (hg : ∀ i, Bounded (g i)) :
    Bounded (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.subst tg tf, by
      intro v
      simpa [Semiterm.val_substs, Function.comp_def]
        using! le_trans (htf (g · v))
          (Tarski.Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by simp))⟩

end Bounded

lemma Bounded₁.comp [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {f : V → V} {k} {g : (Fin k → V) → V}
    (hf : Bounded₁ f) (hg : Bounded g) :
    Bounded (fun v ↦ f (g v)) := Bounded.comp hf (l := 1) (fun _ ↦ hg)

lemma Bounded₂.comp [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {f : V → V → V} {k} {g₁ g₂ : (Fin k → V) → V}
    (hf : Bounded₂ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂) :
    Bounded (fun v ↦ f (g₁ v) (g₂ v)) :=
  Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma Bounded₃.comp [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {f : V → V → V → V} {k} {g₁ g₂ g₃ : (Fin k → V) → V}
    (hf : Bounded₃ f) (hg₁ : Bounded g₁) (hg₂ : Bounded g₂) (hg₃ : Bounded g₃) :
    Bounded (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Bounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases i using Fin.cases with
        | zero => simp [*]
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [*]
          | succ i => simp [*])

namespace Bounded₂

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

instance add : Bounded₂ ((· + ·) : V → V → V) where
  bounded := ⟨‘x y. x + y’, by intro _; simp⟩

instance mul : Bounded₂ ((· * ·) : V → V → V) where
  bounded := ⟨‘x y. x * y’, by intro _; simp⟩

instance hAdd : Bounded₂ (HAdd.hAdd : V → V → V) where
  bounded := ⟨‘x y. x + y’, by intro _; simp⟩

instance hMul : Bounded₂ (HMul.hMul : V → V → V) where
  bounded := ⟨‘x y. x * y’, by intro _; simp⟩

end Bounded₂

def DefinableBoundedFunction {k} (f : (Fin k → V) → V) :=
  Bounded f ∧ 𝚺ᴬ₀.DefinableFunction f

abbrev DefinableBoundedFunction₁ (f : V → V) : Prop :=
  DefinableBoundedFunction (k := 1) (fun v => f (v 0))

abbrev DefinableBoundedFunction₂ (f : V → V → V) : Prop :=
  DefinableBoundedFunction (k := 2) (fun v => f (v 0) (v 1))

abbrev DefinableBoundedFunction₃ (f : V → V → V → V) : Prop :=
  DefinableBoundedFunction (k := 3) (fun v => f (v 0) (v 1) (v 2))

lemma DefinableBoundedFunction.bounded {f : (Fin k → V) → V} (h : DefinableBoundedFunction f) :
    Bounded f := h.1

lemma DefinableBoundedFunction₁.bounded {f : V → V} (h : DefinableBoundedFunction₁ f) :
    Bounded₁ f := h.1

lemma DefinableBoundedFunction₂.bounded {f : V → V → V} (h : DefinableBoundedFunction₂ f) :
    Bounded₂ f := h.1

lemma DefinableBoundedFunction₃.bounded {f : V → V → V → V} (h : DefinableBoundedFunction₃ f) :
    Bounded₃ f := h.1

lemma DefinableBoundedFunction.definable {f : (Fin k → V) → V} (h : DefinableBoundedFunction f) :
    ℌ.DefinableFunction f := .of_zero h.2

lemma DefinableBoundedFunction₁.definable {f : V → V} (h : DefinableBoundedFunction₁ f) :
    ℌ.DefinableFunction₁ f := .of_zero h.2

lemma DefinableBoundedFunction₂.definable {f : V → V → V} (h : DefinableBoundedFunction₂ f) :
    ℌ.DefinableFunction₂ f := .of_zero h.2

lemma DefinableBoundedFunction₃.definable {f : V → V → V → V} (h : DefinableBoundedFunction₃ f) :
    ℌ.DefinableFunction₃ f := .of_zero h.2

namespace DefinableBoundedFunction

lemma of_polybounded_of_definable (f : (Fin k → V) → V) [hb : Bounded f]
    [hf : 𝚺ᴬ₀.DefinableFunction f] :
    DefinableBoundedFunction f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : V → V) [hb : Bounded₁ f]
    [hf : 𝚺ᴬ₀.DefinableFunction₁ f] :
    DefinableBoundedFunction₁ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : V → V → V) [hb : Bounded₂ f]
    [hf : 𝚺ᴬ₀.DefinableFunction₂ f] :
    DefinableBoundedFunction₂ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : V → V → V → V) [hb : Bounded₃ f]
    [hf : 𝚺ᴬ₀.DefinableFunction₃ f] :
    DefinableBoundedFunction₃ f := ⟨hb, hf⟩

lemma retraction {f : (Fin k → V) → V} (hf : DefinableBoundedFunction f) (e : Fin k → Fin n) :
    DefinableBoundedFunction fun v ↦ f (fun i ↦ v (e i)) := ⟨hf.bounded.retraction e,
      Bounding.HierarchySymbol.DefinableFunction.retraction hf.definable e⟩

end DefinableBoundedFunction

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable

open scoped FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic
open Bounding.HierarchySymbol.Definable

variable {ξ : Type*} {n k l : ℕ}
variable {V : Type*} [ORingStructure V]
variable {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} {Γ Γ' : SigmaPiDelta}
variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

variable {P Q : (Fin k → V) → Prop}

lemma ball_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∀ x < f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∀ y < x, P v y := by
    apply bexs'; apply Bounding.HierarchySymbol.Definable.and
    · exact hf.definable
    · suffices ℌ.Definable fun x ↦
          ∀ y < (#0).val (L := ℒₒᵣ) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply ball ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma bexs_blt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∃ x < f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∃ y < x, P v y := by
    apply bexs'; apply Bounding.HierarchySymbol.Definable.and
    · exact hf.definable
    · suffices ℌ.Definable fun x ↦
          ∃ y < (#0).val (L := ℒₒᵣ) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply bexs ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma ball_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∀ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∀ y ≤ x, P v y := by
    apply bexs'; apply Bounding.HierarchySymbol.Definable.and
    · exact hf.definable
    · suffices ℌ.Definable fun x ↦
          ∀ y ≤ (#0).val (L := ℒₒᵣ) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply ball' ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma bexs_ble {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∃ x ≤ f v, P v x := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : ℌ.Definable fun v ↦ ∃ x ≤ bf.val v id, x = f v ∧ ∃ y ≤ x, P v y := by
    apply bexs'; apply Bounding.HierarchySymbol.Definable.and
    · exact hf.definable
    · suffices ℌ.Definable fun x ↦
          ∃ y ≤ (#0).val (L := ℒₒᵣ) x id, P (fun x_1 ↦ x x_1.succ) y by simpa
      apply bexs' ?_ #0
      simpa using h.retraction (0 :> (·.succ.succ))
  exact this.of_iff <| fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩

lemma ball_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ-[0].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[0].Definable fun v ↦ ∀ x < f v, P v x := ball_blt hf h

lemma bexs_blt_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ-[0].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[0].Definable fun v ↦ ∃ x < f v, P v x := bexs_blt hf h

lemma ball_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ-[0].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[0].Definable fun v ↦ ∀ x ≤ f v, P v x := ball_ble hf h

lemma bexs_ble_zero {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ-[0].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[0].Definable fun v ↦ ∃ x ≤ f v, P v x := bexs_ble hf h

lemma bexs_vec_le_boldfaceBoundedFunction {k} {φ : Fin l → (Fin k → V) → V}
    {P : (Fin k → V) → (Fin l → V) → Prop}
    (pp : ∀ i, DefinableBoundedFunction (φ i))
    (hP : ℌ.Definable fun w : Fin (k + l) → V ↦
      P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    ℌ.Definable fun v ↦ ∃ w ≤ (φ · v), P v w := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq (α := V)] using hP
  case succ l ih =>
    simp only [Fin.exists_le_vec_iff_exists_le_exists_vec]
    apply bexs_ble (pp 0)
    apply ih
    · intro i; apply DefinableBoundedFunction.retraction (pp i.succ)
    · let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
        Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
          (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
      exact of_iff (retraction hP g) <| by
        intro v; simp only [g]
        apply iff_of_eq; congr
        · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · ext i
          cases i using Fin.cases with
          | zero => simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          | succ i => simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]

lemma substitution_boldfaceBoundedFunction {f : Fin k → (Fin l → V) → V}
    (hP : ℌ.Definable P) (hf : ∀ i, DefinableBoundedFunction (f i)) :
    ℌ.Definable fun z ↦ P (f · z) := by
  have : ℌ.Definable fun v ↦ ∃ w ≤ (f · v), (∀ i, w i = f i v) ∧ P w := by
    apply bexs_vec_le_boldfaceBoundedFunction hf
    apply Bounding.HierarchySymbol.Definable.and
    · apply fintype_all; intro i
      simpa using retraction (.of_zero (hf i).2) (i.natAdd l :> Fin.castAdd k)
    · apply retraction hP
  apply of_iff this <| by
    intro v; constructor
    · intro h; exact ⟨(f · v), by intro i; simp, by simp, h⟩
    · rintro ⟨w, hw, e, h⟩
      rcases funext e
      exact h

end FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic
open PeanoMinus

variable {ξ : Type*} {n k l : ℕ}
variable {V : Type*} [ORingStructure V]
variable {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} {Γ Γ' : SigmaPiDelta}
namespace DefinableBoundedFunction

lemma of_iff {f g : (Fin k → V) → V} (H : DefinableBoundedFunction f) (h : ∀ v, f v = g v) :
    DefinableBoundedFunction g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

@[simp] lemma var {k} (i : Fin k) : DefinableBoundedFunction (fun v : Fin k → V ↦ v i) :=
  ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : V) : DefinableBoundedFunction (fun _ : Fin k → V ↦ c) :=
  ⟨by simp, by simp⟩

@[simp] lemma term_retraction (t : ArithmeticSemiterm V n) (e : Fin n → Fin k) :
    DefinableBoundedFunction fun v : Fin k → V ↦ t.val (fun x ↦ v (e x)) id := ⟨by simp, by simp⟩

@[simp] lemma term (t : ArithmeticSemiterm V k) :
  DefinableBoundedFunction fun v : Fin k → V ↦ t.val v id := ⟨by simp, by simp⟩

end DefinableBoundedFunction

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable

open scoped FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic
open Bounding.HierarchySymbol.Definable
open DefinableBoundedFunction

variable {ξ : Type*} {n k l : ℕ}
variable {V : Type*} [ORingStructure V]
variable {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} {Γ Γ' : SigmaPiDelta}
variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma bcomp₁ {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : ℌ.DefinablePred P]
    (hf : DefinableBoundedFunction f) :
    ℌ.Definable fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])

lemma bcomp₂ {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V} [hR : ℌ.DefinableRel R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃ {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V} [hR : ℌ.DefinableRel₃ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂, f₃]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄ {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : ℌ.DefinableRel₄ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) (hf₄ : DefinableBoundedFunction f₄) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂, f₃, f₄]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₁_zero {k} {P : V → Prop} {f : (Fin k → V) → V} [hP : Γᴬ-[0].DefinablePred P]
    (hf : DefinableBoundedFunction f) :
    Γᴬ-[0].Definable fun v ↦ P (f v) :=
  substitution_boldfaceBoundedFunction (f := ![f]) hP (by simp [*])

lemma bcomp₂_zero {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V}
    [hR : Γᴬ-[0].DefinableRel R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    Γᴬ-[0].Definable fun v ↦ R (f₁ v) (f₂ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₃_zero {k} {R : V → V → V → Prop} {f₁ f₂ f₃ : (Fin k → V) → V}
    [hR : Γᴬ-[0].DefinableRel₃ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    Γᴬ-[0].Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂, f₃]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma bcomp₄_zero {k} {R : V → V → V → V → Prop} {f₁ f₂ f₃ f₄ : (Fin k → V) → V}
    [hR : Γᴬ-[0].DefinableRel₄ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) (hf₄ : DefinableBoundedFunction f₄) :
    Γᴬ-[0].Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) :=
  substitution_boldfaceBoundedFunction (f := ![f₁, f₂, f₃, f₄]) hR
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

end FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical

open scoped FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic

variable {n k l : ℕ}
variable {V : Type*} [ORingStructure V]
variable {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]}
variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

namespace DefinableFunction

lemma bcomp {k} {F : (Fin l → V) → V}
    {f : Fin l → (Fin k → V) → V}
    (hF : ℌ.DefinableFunction F) (hf : ∀ i, DefinableBoundedFunction (f i)) :
    ℌ.DefinableFunction (fun v ↦ F (f · v)) := by
  simpa using
    Bounding.HierarchySymbol.Arithmetical.Definable.substitution_boldfaceBoundedFunction
      (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using DefinableBoundedFunction.retraction (hf i) Fin.succ

end DefinableFunction

namespace DefinableFunction₁

lemma bcomp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₁ F) (hf : DefinableBoundedFunction f) :
    ℌ.DefinableFunction (fun v ↦ F (f v)) :=
  Bounding.HierarchySymbol.Arithmetical.DefinableFunction.bcomp (f := ![f]) hF (by simp [*])

end DefinableFunction₁

namespace DefinableFunction₂

lemma bcomp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₂ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    ℌ.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  Bounding.HierarchySymbol.Arithmetical.DefinableFunction.bcomp (f := ![f₁, f₂]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

end DefinableFunction₂

namespace DefinableFunction₃

lemma bcomp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₃ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    ℌ.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  Bounding.HierarchySymbol.Arithmetical.DefinableFunction.bcomp (f := ![f₁, f₂, f₃]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

end DefinableFunction₃

end FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical
namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic
open PeanoMinus
open Bounding.HierarchySymbol

variable {ξ : Type*} {n k l : ℕ}
variable {V : Type*} [ORingStructure V]
variable {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} {Γ Γ' : SigmaPiDelta}
variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma DefinableBoundedFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₁ F) (hf : DefinableBoundedFunction f) :
    DefinableBoundedFunction (fun v ↦ F (f v)) :=
  ⟨hF.bounded.comp hf.bounded,
    Bounding.HierarchySymbol.Arithmetical.DefinableFunction₁.bcomp hF.definable hf⟩

lemma DefinableBoundedFunction₂.comp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₂ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  ⟨hF.bounded.comp hf₁.bounded hf₂.bounded,
    Bounding.HierarchySymbol.Arithmetical.DefinableFunction₂.bcomp hF.definable hf₁ hf₂⟩

lemma DefinableBoundedFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₃ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  ⟨hF.bounded.comp hf₁.bounded hf₂.bounded hf₃.bounded,
    Bounding.HierarchySymbol.Arithmetical.DefinableFunction₃.bcomp hF.definable
      hf₁ hf₂ hf₃⟩

lemma DefinableBoundedFunction.comp₁ {k} {F : V → V} {f : (Fin k → V) → V}
    [hFb : Bounded₁ F] [hFd : 𝚺ᴬ₀.DefinableFunction₁ F]
    (hf : DefinableBoundedFunction f) :
    DefinableBoundedFunction (fun v ↦ F (f v)) := DefinableBoundedFunction₁.comp ⟨hFb, hFd⟩ hf

lemma DefinableBoundedFunction.comp₂ {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    [hFb : Bounded₂ F] [hFd : 𝚺ᴬ₀.DefinableFunction₂ F]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableBoundedFunction₂.comp ⟨hFb, hFd⟩ hf₁ hf₂

lemma DefinableBoundedFunction.comp₃ {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    [hFb : Bounded₃ F] [hFd : 𝚺ᴬ₀.DefinableFunction₃ F]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableBoundedFunction₃.comp ⟨hFb, hFd⟩ hf₁ hf₂ hf₃

section

open Bounding.HierarchySymbol

attribute [aesop (rule_sets := [Definability]) norm]
  sq
  Arithmetic.pow_three
  pow_four

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableBoundedFunction.comp₁
  DefinableBoundedFunction.comp₂
  DefinableBoundedFunction.comp₃

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Arithmetical.Definable.bcomp₁_zero
  Arithmetical.Definable.bcomp₂_zero
  Arithmetical.Definable.bcomp₃_zero
  Arithmetical.Definable.bcomp₄_zero

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Arithmetical.Definable.ball_blt_zero
  Arithmetical.Definable.ball_ble_zero
  Arithmetical.Definable.bexs_blt_zero
  Arithmetical.Definable.bexs_ble_zero

example (c : V) : DefinableBoundedFunction₂ (fun x _ : V ↦ c + 2 * x^2) := by definability

example {ex : V → V} [h : 𝚫ᴬ₁.DefinableFunction₁ ex] :
    𝚺ᴬ₁.DefinableRel (fun x y : V ↦ ∃ z, x < y ↔ ex (ex (ex (ex x))) = z) := by
  definability

example {ex : V → V} [h : 𝚺ᴬ₁.DefinableFunction₁ ex] :
    𝚺ᴬ₁.DefinableRel (fun x y : V ↦ ∀ z < ex y, x < y ↔ ex (ex x) = z) := by
  definability

end

end FFL.FirstOrder.Arithmetic
