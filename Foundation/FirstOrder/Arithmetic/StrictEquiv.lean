module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-!
# `T`-provable strict hierarchy equivalence

`StrictEquiv T Γ s φ` witnesses that `φ` is `T`-provably equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

/-- A `Type 0` model-theoretic equivalence between two formulas, valid in every model of `T`,
yields a `T`-provable biconditional via completeness. Converse of `models_iff_of_provable_iff`. -/
lemma provable_iff_of_models_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply Arithmetic.complete T _;
  intro V _ _;
  simpa [models_iff] using h V;

/-- A `T`-provable biconditional yields a model-theoretic equivalence in every model of `T`,
via soundness. Converse of `provable_iff_of_models_iff`. -/
lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have := consequence_iff.mp (Theory.Proof.sound h) V inferInstance;
  simp only [models_iff, Semiformula.eval_allClosure] at this;
  simpa using this e;

/-- A witness that `φ` is `T`-provably equivalent to some formula in `StrictHierarchy Γ s`. -/
structure StrictEquiv (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ}
    (φ : ArithmeticSemiformula Empty n) where
  witness : ArithmeticSemiformula Empty n
  hierarchy : StrictHierarchy Γ s witness
  provable : T ⊢ ∀¹* (φ 🡘 witness)

namespace StrictEquiv

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}
  {φ ψ : ArithmeticSemiformula Empty n}

lemma iff_models (d : StrictEquiv T Γ s φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → V) : V ⊧/e φ ↔ V ⊧/e d.witness :=
  models_iff_of_provable_iff d.provable V e

def refl (h : StrictHierarchy Γ s φ) : StrictEquiv T Γ s φ :=
  ⟨φ, h, provable_iff_of_models_iff fun _ _ _ _ => Iff.rfl⟩

def of_iff (h : StrictEquiv T Γ s φ)
    (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    StrictEquiv T Γ s ψ :=
  ⟨h.witness, h.hierarchy, provable_iff_of_models_iff fun V _ _ e => (hiff V e).symm.trans (h.iff_models V e)⟩

def neg (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt s (∼φ) :=
  ⟨∼h.witness, h.hierarchy.neg, provable_iff_of_models_iff fun V _ _ e => by simp [h.iff_models V e]⟩

-- `StrictEquiv` carries data (the witness formula), so an `Iff` between two instances of it
-- is not itself a `Prop`; state the analogue of `neg`'s converse between the truncated
-- (`Nonempty`) versions instead.
@[simp] lemma neg_iff :
    Nonempty (StrictEquiv T Γ.alt s (∼φ)) ↔ Nonempty (StrictEquiv T Γ s φ) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨by simpa using neg h⟩;
  . rintro ⟨h⟩; exact ⟨neg h⟩;

def alt_up (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt (s + 1) φ := by
  rcases Γ with _ | _;
  . use ∀¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).pi;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      have : Nonempty V := ⟨0⟩;
      simp [h.iff_models V e];
  . use ∃¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).sigma;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      simp [h.iff_models V e];

def of_deltaZero (hp : Hierarchy 𝚺 0 φ) : StrictEquiv T Γ s φ := by
  induction s generalizing Γ with
  | zero => exact refl (StrictHierarchy.zero hp);
  | succ s ih => simpa using alt_up (ih (Γ := Γ.alt));

def exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚷 s φ) :
    StrictEquiv T 𝚺 (s + 1) (∃¹ φ) := by
  use ∃¹ h.witness;
  . exact h.hierarchy.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex];
    exact exists_congr (fun x => h.iff_models V (x :> e));

def all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚺 s φ) :
    StrictEquiv T 𝚷 (s + 1) (∀¹ φ) := by
  use ∀¹ h.witness;
  . exact h.hierarchy.pi;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_all];
    exact forall_congr' (fun x => h.iff_models V (x :> e));

end StrictEquiv

/-- A `Type 0` model-theoretic equivalence between two formulas, valid in every model of `T`.
This is the `iff_models`-only counterpart of `StrictEquiv`, useful for building up equivalences
purely by model theory before crossing to the `T`-provable `StrictEquiv` via completeness. -/
structure ModelEquiv (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ}
    (φ : ArithmeticSemiformula Empty n) where
  witness : ArithmeticSemiformula Empty n
  hierarchy : StrictHierarchy Γ s witness
  iff_models : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e witness

namespace ModelEquiv

variable {T : ArithmeticTheory} {Γ : Polarity} {s : ℕ} {n : ℕ} {φ : ArithmeticSemiformula Empty n}

def refl (h : StrictHierarchy Γ s φ) : ModelEquiv T Γ s φ :=
  ⟨φ, h, fun _ _ _ _ => Iff.rfl⟩

def neg (h : ModelEquiv T Γ s φ) : ModelEquiv T Γ.alt s (∼φ) :=
  ⟨∼h.witness, h.hierarchy.neg, fun V _ _ e => by simp [h.iff_models V e]⟩

/-- Convert to the `T`-provable `StrictEquiv`, via completeness. -/
def toStrictEquiv [𝗘𝗤 ℒₒᵣ ⪯ T] (h : ModelEquiv T Γ s φ) : StrictEquiv T Γ s φ :=
  ⟨h.witness, h.hierarchy, provable_iff_of_models_iff h.iff_models⟩

/-- Convert from the `T`-provable `StrictEquiv`, via soundness. -/
def ofStrictEquiv [𝗘𝗤 ℒₒᵣ ⪯ T] (d : StrictEquiv T Γ s φ) : ModelEquiv T Γ s φ :=
  ⟨d.witness, d.hierarchy, fun V _ _ e => d.iff_models V e⟩

end ModelEquiv

end LO.FirstOrder.Arithmetic
