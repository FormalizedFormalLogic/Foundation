module

public import Foundation.FirstOrder.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section
namespace LO

namespace FirstOrder

section

universe u v

variable {L : Language.{u}} {ξ : Type v}
  {I : Type u} (A : I → Type u)
  [s : (i : I) → FirstOrder.Structure L (A i)]
  (𝓤 : Ultrafilter I)

namespace Structure

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance UprodStruc : Structure L (Uprod A 𝓤) where
  func := fun _ f v => ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩
  rel  := fun _ r v => {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤

instance [Nonempty I] [(i : I) → Nonempty (A i)] : Nonempty (Uprod A 𝓤) := Nonempty.map (⟨·⟩) inferInstance

@[simp] lemma func_Uprod {k} (f : L.Func k) (v : Fin k → Uprod A 𝓤) :
    Structure.func f v = ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.Rel k) (v : Fin k → Uprod A 𝓤) :
    Structure.rel r v ↔ {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤 := of_eq rfl

end Structure

namespace Semiterm

open Structure

variable (e : Fin n → Uprod A 𝓤) (ε : ξ → Uprod A 𝓤)

lemma val_Uprod (t : Semiterm L ξ n) :
    t.val e ε = ⟨fun i ↦ t.val (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i)⟩ := by
  induction t <;> simp [*, val_func, Function.comp_def]

end Semiterm

open Structure

variable {A} {𝓤}

namespace Semiformula

variable {e : Fin n → Uprod A 𝓤} {ε : ξ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {i : I} :
    (z.val i :> fun x ↦ (e x).val i) = (fun x ↦ ((z :> e) x).val i) := by
  simp [Matrix.comp_vecCons (Uprod.val · i), Function.comp_def]

lemma eval_Uprod [(i : I) → Nonempty (A i)] {φ : Semiformula L ξ n} :
    φ.Eval e ε ↔ {i | Eval (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ} ∈ 𝓤 := by
  induction φ using rec'
  case hverum =>
    suffices Set.univ ∈ 𝓤 by simp [*]
    exact Filter.univ_mem
  case hfalsum =>
    simp
  case hrel k r v =>
    simp [Semiterm.val_Uprod, Function.comp_def]
  case hnrel k r v =>
    simpa [*, eval_nrel, Semiterm.val_Uprod]
    using Ultrafilter.compl_mem_iff_notMem.symm
  case hand =>
    simpa [*, -Filter.inter_mem_iff] using Filter.inter_mem_iff.symm
  case hor φ ψ ihp ihq =>
    simpa [*, -Ultrafilter.union_mem_iff] using Ultrafilter.union_mem_iff.symm
  case hall φ _ =>
    suffices
      (∀ x : Uprod A 𝓤, {i | (Eval (fun j ↦ ((x :> e) j).val i) fun x ↦ (ε x).val i) φ} ∈ 𝓤) ↔
      {i | ∀ a : A i, (Eval (a :> fun x ↦ (e x).val i) fun z ↦ (ε z).val i) φ} ∈ 𝓤 by simp [*]
    constructor
    · intro h
      let z : Uprod A 𝓤 := ⟨fun i =>
        Classical.epsilon (fun z => ¬Eval (z :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ)⟩
      exact Filter.mem_of_superset (h z) (by
        intro i hι a
        have : Eval (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ :=
          by rw [val_vecCons_val_eq]; exact hι
        by_contra hc
        have : ¬Eval (M := A i) (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ :=
          Classical.epsilon_spec (p := fun z ↦ ¬(Eval (z :> fun x ↦ (e x).val i) _ φ)) ⟨a, hc⟩
        contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro i h; simpa [val_vecCons_val_eq] using h (x.val i))
  case hexs φ _ =>
    suffices
      (∃ x, {i | (Eval (fun x_1 ↦ ((x :> e) x_1).val i) fun x ↦ (ε x).val i) φ} ∈ 𝓤) ↔
      {i | ∃ x, (Eval (x :> fun x ↦ (e x).val i) fun x ↦ (ε x).val i) φ} ∈ 𝓤 by simp [*]
    constructor
    · rintro ⟨x, hx⟩
      exact Filter.mem_of_superset hx (by intro i h; use x.val i; simpa [val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 := ⟨fun i =>
        Classical.epsilon (fun z => Eval (z :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ)⟩
      use z
      exact Filter.mem_of_superset h (by
        intro i; rintro ⟨x, hx⟩
        have : Eval (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) φ :=
          Classical.epsilon_spec (p := fun z ↦ Eval (z :> fun x ↦ (e x).val i) _ φ) ⟨x, hx⟩
        rw [val_vecCons_val_eq] at this; exact this)

lemma val_Uprod [(i : I) → Nonempty (A i)] {φ : Formula L ξ} :
    Evalf ε φ ↔ {i | Evalf (fun x ↦ (ε x).val i) φ} ∈ 𝓤 := by
  simp [Evalf, eval_Uprod, Matrix.empty_eq]

end Semiformula

lemma models_Uprod [Nonempty I] [(i : I) → Nonempty (A i)] {φ : Sentence L} :
    (Uprod A 𝓤)↓[L] ⊧ φ ↔ {i | (A i)↓[L] ⊧ φ} ∈ 𝓤 := by simp [models_iff, Semiformula.val_Uprod, Empty.eq_elim]

variable (A)

def Sentence.domain [(i : I) → Nonempty (A i)] (φ : Sentence L) := {i | (A i)↓[L] ⊧ φ}

end

section

variable {L : Language.{u}} {T : Theory L}

abbrev FinSubtheory (T : Theory L) := {t : Finset (Sentence L) // ↑t ⊆ T}

variable (A : FinSubtheory T → Type u) [s : (i : FinSubtheory T) → Structure L (A i)]

instance : Nonempty (FinSubtheory T) := ⟨∅, by simp⟩

lemma ultrafilter_exists [(t : FinSubtheory T) → Nonempty (A t)]
    (H : ∀ (i : FinSubtheory T), (A i)↓[L] ⊧* (i.val : Theory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Sentence.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    haveI : DecidableEq (Set (FinSubtheory T)) := fun _ _ => Classical.propDecidable _
    intro t ht
    have : ∃ t' : Finset (Sentence L), ↑t' ⊆ T ∧ Finset.image (Sentence.domain A) t' = t := by
      simpa [Finset.subset_set_image_iff] using ht
    rcases this with ⟨t, htT, rfl⟩
    exact ⟨⟨t, htT⟩, by
      suffices ∀ i ∈ t, (A ⟨t, htT⟩)↓[L] ⊧ i by simpa [Sentence.domain] using this
      intro i hi; exact (H ⟨t, htT⟩).models_set hi⟩)

lemma compactness_aux :
    Satisfiable T ↔ ∀ i : FinSubtheory T, Satisfiable (i.val : Theory L) := by
  constructor
  · rintro h ⟨t, ht⟩; exact Semantics.Satisfiable.of_subset h ht
  · intro h
    have : ∀ i : FinSubtheory T, ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M), M ↓[L] ⊧* (i.val : Theory L) :=
      by intro i; exact satisfiable_iff.mp (h i)
    choose A si s hA using this
    have : ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Sentence.domain A) T ⊆ 𝓤.sets := ultrafilter_exists A hA
    rcases this with ⟨𝓤, h𝓤⟩
    have : (Structure.Uprod A 𝓤)↓[L] ⊧* T := ⟨by intro σ hσ; exact models_Uprod.mpr (h𝓤 $ Set.mem_image_of_mem (Sentence.domain A) hσ)⟩
    exact satisfiable_intro (Structure.Uprod A 𝓤) this

theorem compact :
    Satisfiable T ↔ ∀ u : Finset (Sentence L), ↑u ⊆ T → Satisfiable (u : Theory L) := by
  rw [compactness_aux]; simp

instance : Compact (SmallStruc L) := ⟨compact⟩

end

end FirstOrder

end LO
