module

public import Foundation.Modal.Entailment.GL
public import Foundation.Modal.Entailment.Grz
public import Foundation.Modal.Entailment.K4Hen
public import Foundation.Modal.Entailment.K4Henkin
public import Foundation.Modal.Entailment.S5Grz
public import Foundation.Modal.Logic.Basic
public import Foundation.Propositional.Entailment.Cl.Łukasiewicz

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {α : Type*}

structure Hilbert (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

namespace Hilbert

instance : SetLike (Hilbert α) (Formula α) where
  coe := Hilbert.schema
  coe_injective' := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa

inductive HilbertProof (Λ : Hilbert α) : Formula α → Type _
| axm {φ}       : φ ∈ Λ → HilbertProof Λ φ
| mdp {φ ψ}     : HilbertProof Λ (φ 🡒 ψ) → HilbertProof Λ φ → HilbertProof Λ ψ
| nec {φ}       : HilbertProof Λ φ → HilbertProof Λ (□φ)
| implyK φ ψ    : HilbertProof Λ $ Axioms.ImplyK φ ψ
| implyS φ ψ χ  : HilbertProof Λ $ Axioms.ImplyS φ ψ χ
| ec φ ψ        : HilbertProof Λ $ Axioms.ElimContra φ ψ

instance : Entailment (Hilbert α) (Formula α) := ⟨HilbertProof⟩

namespace HilbertProof

open HilbertProof

variable {Λ Λ₁ Λ₂ : Hilbert α}

@[grind <=]
lemma of_schema {φ} (h : φ ∈ Λ) : Λ ⊢ φ := ⟨axm h⟩

def ofLE (h : Λ₁ ≤ Λ₂) : Λ₁ ⊢! φ → Λ₂ ⊢! φ
  | axm h₁       => axm $ h h₁
  | mdp h₁ h₂    => mdp (ofLE h h₁) (ofLE h h₂)
  | nec h₁       => nec (ofLE h h₁)
  | implyK φ ψ   => implyK φ ψ
  | implyS φ ψ χ => implyS φ ψ χ
  | ec φ ψ       => ec φ ψ

@[grind <=]
lemma of_le (h : Λ₁ ≤ Λ₂) : Λ₁ ⊢ φ → Λ₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofLE h hφ⟩

@[grind <=]
lemma weakerThan_of_le (h : Λ₁ ≤ Λ₂) : Λ₁ ⪯ Λ₂ := Entailment.weakerThan_iff.mpr $ of_le h

def Subst {Λ : Hilbert α} (s) : Λ ⊢! φ → Λ ⊢! φ⟦s⟧
  | axm h₁       => axm $ Λ.schema_closed _ h₁ s
  | mdp h₁ h₂    => mdp (Subst s h₁) (Subst s h₂)
  | nec h₁       => nec (Subst s h₁)
  | implyK φ ψ   => implyK φ ψ
  | implyS φ ψ χ => implyS φ ψ χ
  | ec φ ψ       => ec φ ψ

@[grind <=]
lemma subst {Λ : Hilbert α} (s) : Λ ⊢ φ → Λ ⊢ φ⟦s⟧ := λ ⟨hφ⟩ => ⟨Subst s hφ⟩

def ofProofSchema (h : Λ₂ ⊢!* Λ₁.schema) : Λ₁ ⊢! φ → Λ₂ ⊢! φ
  | axm h₁       => h h₁
  | mdp h₁ h₂    => mdp (ofProofSchema h h₁) (ofProofSchema h h₂)
  | nec h₁       => nec (ofProofSchema h h₁)
  | implyK φ ψ   => implyK φ ψ
  | implyS φ ψ χ => implyS φ ψ χ
  | ec φ ψ       => ec φ ψ

@[grind <=]
lemma of_proof_schema (h : Λ₂ ⊢* Λ₁.schema) : Λ₁ ⊢ φ → Λ₂ ⊢ φ :=
  λ ⟨hφ⟩ => ⟨ofProofSchema (h · |>.get) hφ⟩

@[grind <=]
lemma weakerThan_of_provable_schema (h : Λ₂ ⊢* Λ₁.schema) : Λ₁ ⪯ Λ₂ :=
  Entailment.weakerThan_iff.mpr $ of_proof_schema h

open Entailment.Łukasiewicz in
@[induction_eliminator]
protected lemma rec_provable
  {Λ : Hilbert α}
  {motive  : (φ : Formula α) → (Λ ⊢ φ) → Prop}
  (axm     : ∀ {φ}, (h : φ ∈ Λ) → motive φ (of_schema h))
  (mdp     : ∀ {φ ψ}, {hφψ : Λ ⊢ φ 🡒 ψ} → {hφ : Λ ⊢ φ} → motive (φ 🡒 ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec     : ∀ {φ}, {hφ : Λ ⊢ φ} → motive φ hφ → motive (□φ) (nec! hφ))
  (implyK  : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) (by simp))
  (implyS  : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) (by simp))
  (ec      : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) (by simp))
  : ∀ {φ}, (d : Λ ⊢ φ) → motive φ d := by rintro φ ⟨d⟩; induction d <;> sorry;

instance : Entailment.Łukasiewicz Λ where
  implyK {_ _}   := by constructor; apply HilbertProof.implyK;
  implyS {_ _ _} := by constructor; apply HilbertProof.implyS;
  elimContra {_ _} := by constructor; apply HilbertProof.ec;
  mdp h₁ h₂ := ⟨HilbertProof.mdp h₁.get h₂.get⟩

instance : Entailment.Necessitation Λ where
  nec h := ⟨HilbertProof.nec h.get⟩

instance : Logic.Substitution Λ where
  subst s h := subst s h

end HilbertProof


protected def K : Hilbert α := ⟨{ Axioms.K φ ψ | (φ) (ψ) }, by grind⟩
protected def KT : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def KD : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def KP : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.P },
  by rintro φ (_ | _) <;> sorry⟩
protected def KB : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.B φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def KDB : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) } ∪ { Axioms.B φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KTB : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.B φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KMcK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.McK φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def K4 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def K4n (n : ℕ) : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.FourN n φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def K4McK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.McK φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def K4Point2 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.WeakPoint2 φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def K4Point3 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.WeakPoint3 φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KT4B : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.B φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def K45 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KD4 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) } ∪ { Axioms.Four φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KD5 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KD45 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def KB4 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.B φ | (φ) } ∪ { Axioms.Four φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def KB5 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.B φ | (φ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def S4 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def S4McK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.McK φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def S4Point2McK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.McK φ | (φ) } ∪ { Axioms.Point2 φ | (φ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def S4Point3McK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.McK φ | (φ) } ∪ { Axioms.Point3 φ ψ | (φ) (ψ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def S4Point4McK : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.McK φ | (φ) } ∪ { Axioms.Point4 φ | (φ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def S4Point2 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Point2 φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def S4Point3 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Point3 φ ψ | (φ) (ψ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def S4Point4 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Point4 φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def K5 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def S5 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Five φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def GL : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.L φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def GLPoint2 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.L φ | (φ) } ∪ { Axioms.WeakPoint2 φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def GLPoint3 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.L φ | (φ) } ∪ { Axioms.WeakPoint3 φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def K4Z : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Z φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def K4Point2Z : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Z φ | (φ) } ∪ { Axioms.WeakPoint2 φ ψ | (φ) (ψ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def K4Point3Z : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Z φ | (φ) } ∪ { Axioms.WeakPoint3 φ ψ | (φ) (ψ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def KHen : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Hen φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def K4Hen : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Hen φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def Grz : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Grz φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def GrzPoint2 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Grz φ | (φ) } ∪ { Axioms.Point2 φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def GrzPoint3 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Grz φ | (φ) } ∪ { Axioms.Point3 φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def Dum : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Dum φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def DumPoint2 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Dum φ | (φ) } ∪ { Axioms.Point2 φ | (φ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def DumPoint3 : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.Dum φ | (φ) } ∪ { Axioms.Point3 φ ψ | (φ) (ψ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def KTc : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Tc φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def KD4Point3Z : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.D φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.WeakPoint3 φ ψ | (φ) (ψ) } ∪ { Axioms.Z φ | (φ) },
  by rintro φ ((((_ | _) | _) | _) | _) <;> sorry⟩
protected def KTMk : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Mk φ ψ | (φ) (ψ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
/--
  - `S4H` in Segerberg 1971.
  - `K1.2` in Sobocinski 1964, "Family $K$ of the non-Lewis modal systems"
-/
protected def S4H : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Four φ | (φ) } ∪ { Axioms.H φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def Ver : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.Ver φ | (φ) },
  by rintro φ (_ | _) <;> sorry⟩
protected def Triv : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Tc φ | (φ) },
  by rintro φ ((_ | _) | _) <;> sorry⟩
protected def S5Grz : Hilbert α := ⟨
  { Axioms.K φ ψ | (φ) (ψ) } ∪ { Axioms.T φ | (φ) } ∪ { Axioms.Five φ | (φ) } ∪ { Axioms.Grz φ | (φ) },
  by rintro φ (((_ | _) | _) | _) <;> sorry⟩
protected def N : Hilbert α := ⟨∅, by grind⟩
protected def NP : Hilbert α := ⟨{ Axioms.P }, by grind⟩


section instances

open HilbertProof

instance : Entailment.K (Hilbert.K : Hilbert α) where
  K {φ ψ} := of_schema (by use φ, ψ)

instance : Logic.IsNormal (Hilbert.K : Hilbert α) where

instance {H : Hilbert α} [h : Logic.IsNormal H] : Hilbert.K ⪯ H := by
  apply Logic.weakerThan_of_provable;
  intro φ ⟨hφ⟩;
  induction hφ with
  | axm h =>
    obtain ⟨φ, ψ, rfl⟩ := h;
    apply Logic.iff_provable.mpr;
    exact ⟨HilbertProof.axm rfl⟩
  | mdp h₁ h₂ ih₁ ih₂ => exact Logic.iff_provable.mp ih₁ ⨀ Logic.iff_provable.mp ih₂
  | nec hφ ihφ => exact nec! (Logic.iff_provable.mp ihφ)
  | implyK φ ψ => simp
  | implyS φ ψ χ => simp
  | ec φ ψ => simp

instance : Entailment.KT (Hilbert.KT : Hilbert α) where
  T {φ}   := of_schema (by right; use φ)

instance : Entailment.KD (Hilbert.KD : Hilbert α) where
  D {φ}   := of_schema (by right; use φ)

instance : Entailment.KP (Hilbert.KP : Hilbert α) where
  P       := of_schema (by right; tauto)

instance : Modal.KP ≊ Modal.KD := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor
  · apply HilbertProof.weakerThan_of_provable_schema
    intro φ hφ
    rcases hφ with (⟨ψ, rfl⟩ | rfl) | (⟨ψ, rfl⟩)
    · exact of_schema (by left; use ψ)
    · simp
    · exact of_schema (by right; use ψ)
  · apply HilbertProof.weakerThan_of_provable_schema
    intro φ hφ
    rcases hφ with (⟨ψ, rfl⟩ | rfl) | (⟨ψ, rfl⟩)
    · exact of_schema (by left; use ψ)
    · exact of_schema (by right; use ψ)
    · simp

instance : Entailment.KB (Hilbert.KB : Hilbert α) where
  B {φ}   := of_schema (by right; use φ)

instance : Entailment.KDB (Hilbert.KDB : Hilbert α) where
  D {φ}   := of_schema (by left; right; use φ)
  B {φ}   := of_schema (by right; use φ)

instance : Entailment.KTB (Hilbert.KTB : Hilbert α) where
  T {φ}   := of_schema (by left; right; use φ)
  B {φ}   := of_schema (by right; use φ)

instance : Entailment.KMcK (Hilbert.KMcK : Hilbert α) where
  McK {φ} := of_schema (by right; use φ)

instance : Entailment.K4 (Hilbert.K4 : Hilbert α) where
  Four {φ} := of_schema (by right; use φ)

instance {n : ℕ} : Entailment.K4n n (Hilbert.K4n n : Hilbert α) where
  FourN {φ} := of_schema (by right; use φ)

instance : Entailment.K4McK (Hilbert.K4McK : Hilbert α) where
  Four {φ} := of_schema (by left; right; use φ)
  McK {φ}  := of_schema (by right; use φ)

noncomputable instance [Entailment.K H] [Hilbert.K4McK ⪯ H] : Entailment.K4McK H where
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4McK) (by simp) |>.some
  McK _  := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4McK) (by simp) |>.some

instance : Entailment.K4Point2 (Hilbert.K4Point2 : Hilbert α) where
  WeakPoint2 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Entailment.K4Point3 (Hilbert.K4Point3 : Hilbert α) where
  WeakPoint3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Entailment.KT4B (Hilbert.KT4B : Hilbert α) where
  T {φ}    := of_schema (by left; left; right; use φ)
  Four {φ} := of_schema (by left; right; use φ)
  B {φ}    := of_schema (by right; use φ)

instance : Entailment.K45 (Hilbert.K45 : Hilbert α) where
  Four {φ} := of_schema (by left; right; use φ)
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.KD4 (Hilbert.KD4 : Hilbert α) where
  D {φ}    := of_schema (by left; right; use φ)
  Four {φ} := of_schema (by right; use φ)

instance : Entailment.KD5 (Hilbert.KD5 : Hilbert α) where
  D {φ}    := of_schema (by left; right; use φ)
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.KD45 (Hilbert.KD45 : Hilbert α) where
  D {φ}    := of_schema (by left; left; right; use φ)
  Four {φ} := of_schema (by left; right; use φ)
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.KB4 (Hilbert.KB4 : Hilbert α) where
  B {φ}    := of_schema (by left; right; use φ)
  Four {φ} := of_schema (by right; use φ)

instance : Entailment.KB5 (Hilbert.KB5 : Hilbert α) where
  B {φ}    := of_schema (by left; right; use φ)
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.S4 (Hilbert.S4 : Hilbert α) where
  T {φ}    := of_schema (by left; right; use φ)
  Four {φ} := of_schema (by right; use φ)

instance : Hilbert.K4 ⪯ (Hilbert.S4 : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.S4McK (Hilbert.S4McK : Hilbert α) where
  T {φ}    := of_schema (by left; left; right; use φ)
  Four {φ} := of_schema (by left; right; use φ)
  McK {φ}  := of_schema (by right; use φ)

instance : Hilbert.K4McK ⪯ (Hilbert.S4McK : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.S4Point2McK (Hilbert.S4Point2McK : Hilbert α) where
  T {φ}      := of_schema (by left; left; left; right; use φ)
  Four {φ}   := of_schema (by left; left; right; use φ)
  McK {φ}    := of_schema (by left; right; use φ)
  Point2 {φ} := of_schema (by right; use φ)

instance : Hilbert.K4McK ⪯ (Hilbert.S4Point2McK : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.S4Point3McK (Hilbert.S4Point3McK : Hilbert α) where
  T {φ}        := of_schema (by left; left; left; right; use φ)
  Four {φ}     := of_schema (by left; left; right; use φ)
  McK {φ}      := of_schema (by left; right; use φ)
  Point3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Hilbert.K4McK ⪯ (Hilbert.S4Point3McK : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.S4Point4McK (Hilbert.S4Point4McK : Hilbert α) where
  T {φ}      := of_schema (by left; left; left; right; use φ)
  Four {φ}   := of_schema (by left; left; right; use φ)
  McK {φ}    := of_schema (by left; right; use φ)
  Point4 {φ} := of_schema (by right; use φ)

instance : Hilbert.K4McK ⪯ (Hilbert.S4Point4McK : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.S4Point2 (Hilbert.S4Point2 : Hilbert α) where
  T {φ}      := of_schema (by left; left; right; use φ)
  Four {φ}   := of_schema (by left; right; use φ)
  Point2 {φ} := of_schema (by right; use φ)

instance : Entailment.S4Point3 (Hilbert.S4Point3 : Hilbert α) where
  T {φ}        := of_schema (by left; left; right; use φ)
  Four {φ}     := of_schema (by left; right; use φ)
  Point3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Entailment.S4Point4 (Hilbert.S4Point4 : Hilbert α) where
  T {φ}      := of_schema (by left; left; right; use φ)
  Four {φ}   := of_schema (by left; right; use φ)
  Point4 {φ} := of_schema (by right; use φ)

instance : Entailment.K5 (Hilbert.K5 : Hilbert α) where
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.S5 (Hilbert.S5 : Hilbert α) where
  T {φ}    := of_schema (by left; right; use φ)
  Five {φ} := of_schema (by right; use φ)

instance : Entailment.GL (Hilbert.GL : Hilbert α) where
  L {φ}    := of_schema (by right; use φ)

instance : Entailment.GLPoint2 (Hilbert.GLPoint2 : Hilbert α) where
  L {φ}        := of_schema (by left; right; use φ)
  WeakPoint2 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Hilbert.GL ⪯ (Hilbert.GLPoint2 : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Entailment.GLPoint3 (Hilbert.GLPoint3 : Hilbert α) where
  L {φ}        := of_schema (by left; right; use φ)
  WeakPoint3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Entailment.K4Z (Hilbert.K4Z : Hilbert α) where
  Four {φ} := of_schema (by left; right; use φ)
  Z {φ}    := of_schema (by right; use φ)

instance : Hilbert.K4 ⪯ (Hilbert.K4Z : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.K4Z ⪯ (Hilbert.GL : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with ((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp

instance : Entailment.K4Point2Z (Hilbert.K4Point2Z : Hilbert α) where
  Four {φ}     := of_schema (by left; left; right; use φ)
  Z {φ}        := of_schema (by left; right; use φ)
  WeakPoint2 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Hilbert.K4Point2 ⪯ (Hilbert.K4Point2Z : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.K4Z ⪯ (Hilbert.K4Point2Z : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.K4Point2Z ⪯ (Hilbert.GLPoint2 : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, χ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · exact of_schema (by right; use ψ, χ)

instance : Entailment.K4Point3Z (Hilbert.K4Point3Z : Hilbert α) where
  Four {φ}     := of_schema (by left; left; right; use φ)
  Z {φ}        := of_schema (by left; right; use φ)
  WeakPoint3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Hilbert.K4Point3 ⪯ (Hilbert.K4Point3Z : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with ((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, χ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · exact of_schema (by right; use ψ, χ)

instance : Hilbert.K4Z ⪯ (Hilbert.K4Point3Z : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with ((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp

instance : Hilbert.K4Point3Z ⪯ (Hilbert.GLPoint3 : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, χ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · exact of_schema (by right; use ψ, χ)

instance : Entailment.K4Hen (Hilbert.K4Hen : Hilbert α) where
  Four {φ} := of_schema (by left; right; use φ)
  Hen {φ}  := of_schema (by right; use φ)

instance : Entailment.Grz (Hilbert.Grz : Hilbert α) where
  Grz {φ}  := of_schema (by right; use φ)

instance : Hilbert.KT ⪯ (Hilbert.Grz : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp

instance : Entailment.GrzPoint2 (Hilbert.GrzPoint2 : Hilbert α) where
  Grz {φ}    := of_schema (by left; right; use φ)
  Point2 {φ} := of_schema (by right; use φ)

instance : Entailment.GrzPoint3 (Hilbert.GrzPoint3 : Hilbert α) where
  Grz {φ}      := of_schema (by left; right; use φ)
  Point3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Entailment.Dum (Hilbert.Dum : Hilbert α) where
  T {φ}   := of_schema (by left; left; right; use φ)
  Four {φ} := of_schema (by left; right; use φ)
  Dum {φ}  := of_schema (by right; use φ)

instance : Hilbert.S4 ⪯ (Hilbert.Dum : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto

instance : Hilbert.Dum ⪯ (Hilbert.Grz : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · simp

instance : Entailment.DumPoint2 (Hilbert.DumPoint2 : Hilbert α) where
  T {φ}      := of_schema (by left; left; left; right; use φ)
  Four {φ}   := of_schema (by left; left; right; use φ)
  Dum {φ}    := of_schema (by left; right; use φ)
  Point2 {φ} := of_schema (by right; use φ)

instance : Hilbert.Dum ⪯ (Hilbert.DumPoint2 : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.S4Point2 ⪯ (Hilbert.DumPoint2 : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.DumPoint2 ⪯ (Hilbert.GrzPoint2 : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with ((((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · simp
  · exact of_schema (by right; use ψ)

instance : Entailment.DumPoint3 (Hilbert.DumPoint3 : Hilbert α) where
  T {φ}        := of_schema (by left; left; left; right; use φ)
  Four {φ}     := of_schema (by left; left; right; use φ)
  Dum {φ}      := of_schema (by left; right; use φ)
  Point3 {φ ψ} := of_schema (by right; use φ, ψ)

instance : Hilbert.Dum ⪯ (Hilbert.DumPoint3 : Hilbert α) := HilbertProof.weakerThan_of_le $ by tauto
instance : Hilbert.S4Point3 ⪯ (Hilbert.DumPoint3 : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, χ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · exact of_schema (by right; use ψ, χ)

instance : Hilbert.DumPoint3 ⪯ (Hilbert.GrzPoint3 : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with ((((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, χ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp
  · simp
  · simp
  · exact of_schema (by right; use ψ, χ)

instance : Entailment.KTc (Hilbert.KTc : Hilbert α) where
  Tc {φ}   := of_schema (by right; use φ)

instance : Entailment.KD4Point3Z (Hilbert.KD4Point3Z : Hilbert α) where
  D {φ}        := of_schema (by left; left; left; right; use φ)
  Four {φ}     := of_schema (by left; left; right; use φ)
  WeakPoint3 {φ ψ} := of_schema (by left; right; use φ, ψ)
  Z {φ}        := of_schema (by right; use φ)

instance : Entailment.KTMk (Hilbert.KTMk : Hilbert α) where
  T {φ}      := of_schema (by left; right; use φ)
  Mk {φ ψ}   := of_schema (by right; use φ, ψ)

instance : Entailment.S4H (Hilbert.S4H : Hilbert α) where
  T {φ}    := of_schema (by left; left; right; use φ)
  Four {φ} := of_schema (by left; right; use φ)
  H1 {φ}   := of_schema (by right; use φ)

instance : Entailment.Ver (Hilbert.Ver : Hilbert α) where
  Ver {φ}  := of_schema (by right; use φ)

instance : Entailment.Triv (Hilbert.Triv : Hilbert α) where
  T {φ}    := of_schema (by left; right; use φ)
  Tc {φ}   := of_schema (by right; use φ)

instance : Hilbert.K4 ⪯ (Hilbert.Triv : Hilbert α) := HilbertProof.weakerThan_of_provable_schema $ by
  intro φ hφ;
  rcases hφ with (⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩
  · exact of_schema (by left; use ψ, χ)
  · simp

instance : Entailment.S5Grz (Hilbert.S5Grz : Hilbert α) where
  T {φ}    := of_schema (by left; left; right; use φ)
  Five {φ} := of_schema (by left; right; use φ)
  Grz {φ}  := of_schema (by right; use φ)

instance : Hilbert.S5Grz ≊ (Hilbert.Triv : Hilbert α) := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor
  · apply HilbertProof.weakerThan_of_provable_schema
    intro φ hφ;
    rcases hφ with (((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
    · exact of_schema (by left; use ψ, χ)
    · exact of_schema (by left; right; use ψ)
    · simp
    · simp
  · apply HilbertProof.weakerThan_of_provable_schema
    intro φ hφ;
    rcases hφ with ((⟨ψ, χ, rfl⟩) | ⟨ψ, rfl⟩) | ⟨ψ, rfl⟩
    · exact of_schema (by left; use ψ, χ)
    · exact of_schema (by left; right; use ψ)
    · exact of_schema (by right; use ψ)

instance : Entailment.HasAxiomP (Hilbert.NP : Hilbert α) where
  P := of_schema (by tauto)

end instances

end Hilbert

end LO.Modal
end
