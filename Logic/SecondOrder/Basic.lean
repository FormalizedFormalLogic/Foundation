import Logic.FirstOrder.Basic.Language
import Logic.ManySorted.Basic.Formula

namespace LO

inductive MSO.Srt := | elem | set deriving DecidableEq

abbrev MSO.Srt.type (ξ : Type v) (Ξ : Type v) : Srt → Type v
  | elem => ξ
  | set  => Ξ

protected abbrev MSO.Srt.cases' {α} (x : α) (X : α) : Srt → α
  | elem => x
  | set  => X

namespace FirstOrder.Language
open MSO MSO.Srt

inductive MSO.Func (L : FirstOrder.Language.{u}) : Srt → (Srt → ℕ) → Type u
  | elem {k : ℕ} : L.Func k → MSO.Func L elem (Srt.cases' k 0)

inductive MSO.Rel (L : FirstOrder.Language.{u}) : (Srt → ℕ) → Type u
  | elem {k : ℕ} : L.Rel k → MSO.Rel L (Srt.cases' k 0)
  | mem          : MSO.Rel L (Srt.cases' 1 1)

def mSO (L : FirstOrder.Language.{u}) : ManySorted.Language Srt where
  Func := MSO.Func L
  Rel := MSO.Rel L

end FirstOrder.Language

namespace MSO

open Srt

variable {L : FirstOrder.Language.{u}} {ξ : Type vₑ} {Ξ : Type vₛ}

abbrev ESubterm (L : FirstOrder.Language.{u}) (ξ : Type v) (Ξ : Type v) (m n : ℕ) :=
  ManySorted.Subterm Srt.elem L.mSO (Srt.type ξ Ξ) (Srt.cases' m n)

abbrev SSubterm (L : FirstOrder.Language.{u}) (ξ : Type v) (Ξ : Type v) (m n : ℕ) :=
  ManySorted.Subterm Srt.set L.mSO (Srt.type ξ Ξ) (Srt.cases' m n)

abbrev Subformula (L : FirstOrder.Language.{u}) (ξ : Type v) (Ξ : Type v) (m n : ℕ) :=
  ManySorted.Subformula L.mSO (Srt.type ξ Ξ) (Srt.cases' m n)

end LO.MSO
