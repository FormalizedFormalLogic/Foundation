import Foundation.Propositional.Formula
import Foundation.Logic.Semantics

namespace LO.Propositional

variable {α : Type*}

structure Classical.Valuation (α : Type*) where
  val : α → Prop

instance : CoeFun (Classical.Valuation α) (fun _ ↦ α → Prop) := ⟨Classical.Valuation.val⟩


namespace Formula.Classical

def val (v : Classical.Valuation α) : Formula α → Prop
  | atom a  => v a
  | ⊥       => False
  | φ ➝ ψ   => val v φ → val v ψ
  | φ ⋏ ψ   => val v φ ∧ val v ψ
  | φ ⋎ ψ   => val v φ ∨ val v ψ

variable {v : Classical.Valuation α} {φ ψ : Formula α}

instance semantics : Semantics (Formula α) (Classical.Valuation α) := ⟨fun v ↦ val v⟩

lemma models_iff_val : v ⊧ φ ↔ val v φ := iff_of_eq rfl

instance : Semantics.Tarski (Classical.Valuation α) where
  realize_top := by simp [models_iff_val, val]
  realize_bot := by simp [models_iff_val, val]
  realize_and := by simp [models_iff_val, val]
  realize_or  := by simp [models_iff_val, val]
  realize_not := by simp [models_iff_val, val]
  realize_imp := by simp [models_iff_val, val]

@[simp] protected lemma realize_atom : v ⊧ (.atom a) ↔ v a := iff_of_eq rfl

lemma eq_fml_of_eq_atom {v u : Classical.Valuation α} (h : ∀ {a : α}, v a ↔ u a) : (∀ {φ : Formula α}, v ⊧ φ ↔ u ⊧ φ) := by
  intro φ;
  induction φ using Formula.rec' with
  | hatom => apply h;
  | _ => simp [*]

lemma iff_subst_self (s) :
  (⟨(λ a => val v ((.atom a)⟦s⟧))⟩ : Classical.Valuation α) ⊧ φ ↔ v ⊧ (φ⟦s⟧) := by
  induction φ using Formula.rec' with
  | hatom a => simp [val, models_iff_val];
  | hfalsum => simp [val];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ hφ;
      apply ihψ.mp;
      apply hφψ;
      apply ihφ.mpr;
      exact hφ;
    . intro hφψs hφ;
      apply ihψ.mpr;
      apply hφψs;
      apply ihφ.mp;
      exact hφ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; apply ihφ.mp hφ;
      . right; apply ihψ.mp hψ;
    . rintro (hφ | hψ);
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;

end Formula.Classical


namespace Classical

variable {v : Classical.Valuation α} {φ ψ : Formula α}

open Semantics (Valid)

lemma tautology_subst_instance (h : Valid (Valuation _) φ) : ∀ s, Valid (Valuation _) (φ⟦s⟧) := by
  intro s v;
  apply Formula.Classical.iff_subst_self s |>.mp;
  apply h;

end Classical

end LO.Propositional
