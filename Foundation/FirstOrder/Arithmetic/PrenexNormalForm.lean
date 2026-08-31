module

public import Foundation.FirstOrder.Arithmetic.Basic.Prenex
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Prenex normal form theorem

Every `Hierarchy Γ s φ` formula is, over models of `𝗣𝗔`, equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level, and this
equivalence is provable in `𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.FirstOrder

universe u

namespace LO.FirstOrder.Arithmetic

-- Every declaration below whose *type* mentions the private `StrictEquivOnPA` must itself be
-- `private`: this module's public/private visibility check forbids a public declaration's
-- signature from referring to a private identifier (bodies may still call private lemmas
-- freely). Only the three theorems in `namespace Hierarchy` at the end of the file, whose
-- statements are fully inlined, are exposed publicly.
namespace StrictEquivOnPA

private def StrictEquivOnPA (Γ : Polarity) (s : ℕ) {n : ℕ} (φ : ArithmeticSemiformula Empty n) : Prop :=
  ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ

variable {Γ Γ' : Polarity} {s s' : ℕ} {n : ℕ} {φ ψ : ArithmeticSemiformula Empty n}

private lemma refl (h : StrictHierarchy Γ s φ) : StrictEquivOnPA.{u} Γ s φ := sorry

private lemma of_iff (h : StrictEquivOnPA.{u} Γ s φ)
    (hiff : ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    StrictEquivOnPA.{u} Γ s ψ := sorry

private lemma neg (h : StrictEquivOnPA.{u} Γ s φ) : StrictEquivOnPA.{u} Γ.alt s (∼φ) := sorry

@[simp] private lemma neg_iff : StrictEquivOnPA.{u} Γ.alt s (∼φ) ↔ StrictEquivOnPA.{u} Γ s φ := sorry

private lemma alt_up (h : StrictEquivOnPA.{u} Γ s φ) : StrictEquivOnPA.{u} Γ.alt (s + 1) φ := sorry

private lemma of_deltaZero (hp : Hierarchy 𝚺 0 φ) : StrictEquivOnPA.{u} Γ s φ := sorry

/-- The core closure properties needed at a fixed level `s`. -/
private structure CoreClosure (s : ℕ) : Prop where
  and  : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s ψ → StrictEquivOnPA.{u} Γ s (φ ⋏ ψ)
  or   : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s ψ → StrictEquivOnPA.{u} Γ s (φ ⋎ ψ)
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s (∃¹[“x. x < !!t”] φ)

private lemma coreClosure_zero : CoreClosure 0 := sorry

private lemma or_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) ψ → StrictEquivOnPA.{u} 𝚺 (s + 1) (φ ⋎ ψ) := sorry

private lemma and_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) ψ → StrictEquivOnPA.{u} 𝚺 (s + 1) (φ ⋏ ψ) := sorry

private lemma bexs_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := sorry

private lemma ball_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := sorry

private lemma coreClosure_succ (ih : CoreClosure s) : CoreClosure (s + 1) := sorry

private lemma coreClosure : CoreClosure s := sorry

private lemma exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚺 (s + 1) φ) :
    StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹ φ) := sorry

private lemma all {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚷 (s + 1) φ) :
    StrictEquivOnPA.{u} 𝚷 (s + 1) (∀¹ φ) := sorry

private lemma exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚷 s φ) :
    StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹ φ) := sorry

private lemma all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚺 s φ) :
    StrictEquivOnPA.{u} 𝚷 (s + 1) (∀¹ φ) := sorry

private lemma strictEquivOnPA_of_hierarchy (h : Hierarchy Γ s φ) : StrictEquivOnPA.{u} Γ s φ := sorry

end StrictEquivOnPA

namespace Hierarchy

lemma exists_strictHierarchy_form {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ :=
  StrictEquivOnPA.strictEquivOnPA_of_hierarchy h

theorem exists_strictHierarchy_provable {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨ψ, hψ, H⟩ := exists_strictHierarchy_form.{0} h;
  use ψ;
  and_intros;
  . exact hψ;
  . apply FirstOrder.Arithmetic.complete.{0} 𝗣𝗔 _ ?_;
    intro M _ _;
    simpa [models_iff] using fun e => H M e;

theorem exists_strictHierarchy_provable_of_sentence {Γ s} {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end Hierarchy

end LO.FirstOrder.Arithmetic
