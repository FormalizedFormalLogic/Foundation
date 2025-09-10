import Foundation.Vorspiel.Vorspiel

namespace Syntactic

class Variable (Ω : outParam Type*) (ξ : outParam Type*) (n : outParam ℕ) (T : Type*) where
  b : Ω → Fin n → T
  ω : Ω → ξ → T

variable {Ω : Type*} {ξ ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ} {T T₁ T₂ T₃ : Type*} {U U₁ U₂ U₃ : Type*}

variable (T₁ T₂)

@[ext]
structure Manipulation [Variable Ω ξ₁ n₁ T₁] where
  b : Ω → Fin n₁ → T₂
  ω : Ω → ξ₁ → T₂

infix:40 " ⇛ " => Manipulation

class Presyntax [Variable Ω ξ₁ n₁ T₁] where
  app : T₁ ⇛ T₂ → T₁ → T₂
  app_b {s} (ω : T₁ ⇛ T₂) (x : Fin n₁) : app ω (Variable.b s x) = ω.b s x
  app_f {s} (ω : T₁ ⇛ T₂) (x : ξ₁)     : app ω (Variable.ω s x) = ω.ω s x

attribute [simp] Presyntax.app_b Presyntax.app_f

variable {T₁ T₂}

abbrev Manipulation.app [Variable Ω ξ₁ n₁ T₁] [ Presyntax T₁ T₂] (ω : T₁ ⇛ T₂) (t : T₁) : T₂ := Presyntax.app ω t

namespace Presyntax

variable {s : Ω}

variable [Variable Ω ξ₁ n₁ T₁] [Variable Ω ξ₂ n₂ T₂] [Presyntax T₁ T₂]

instance : FunLike (T₁ ⇛ T₂) T₁ T₂ where
  coe := Presyntax.app
  coe_injective' := fun ω g h => by
    ext s x
    · simpa using congr_fun h (Variable.b s x)
    · simpa using congr_fun h (Variable.ω s x)

@[simp] lemma app_bvar (ω : T₁ ⇛ T₂) (x : Fin n₁) : ω (Variable.b s x) = ω.b s x := app_b _ _

@[simp] lemma app_fvar (ω : T₁ ⇛ T₂) (x : ξ₁) : ω (Variable.ω s x) = ω.ω s x := app_f _ _

end Presyntax

namespace Manipulation

protected def id [Variable Ω ξ n T] : T ⇛ T := ⟨Variable.b, Variable.ω⟩

def comp
    [Variable Ω ξ₁ n₁ T₁] [Variable Ω ξ₂ n₂ T₂] [Variable Ω ξ₃ n₃ T₃]
    [Presyntax T₁ T₂] [Presyntax T₂ T₃]
    (f₂ : T₂ ⇛ T₃) (f₁ : T₁ ⇛ T₂) : T₁ ⇛ T₃ :=
  ⟨fun s x ↦ f₂ (f₁.b s x), fun s x ↦ f₂ (f₁.ω s x)⟩

end Manipulation

variable (T T₁ T₂)

class ReflexiveSyntax [Variable Ω ξ n T] extends Presyntax T T where
  id_app (t : T) : Manipulation.id.app t = t

class TransitiveSyntax [Variable Ω ξ₁ n₁ T₁] [Variable Ω ξ₂ n₂ T₂] [Variable Ω ξ₃ n₃ T₃]
    [Presyntax T₁ T₂] [Presyntax T₂ T₃] [Presyntax T₁ T₃] where
  comp_app (f₂ : T₂ ⇛ T₃) (f₁ : T₁ ⇛ T₂) (t : T₁) : (f₂.comp f₁) t = f₂ (f₁ t)
