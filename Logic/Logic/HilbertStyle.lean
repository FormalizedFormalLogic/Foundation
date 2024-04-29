import Logic.Logic.System
import Logic.Logic.Init

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [System S F]

variable (𝓢 : S)

class ModusPonens where
  mdp {p q : F} : 𝓢 ⊢ p ⟶ q → 𝓢 ⊢ p → 𝓢 ⊢ q

class Minimal extends ModusPonens 𝓢 where
  verum              : 𝓢 ⊢ ⊤
  imply₁ (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p
  imply₂ (p q r : F) : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ p
  conj₂  (p q : F)   : 𝓢 ⊢ p ⋏ q ⟶ q
  conj₃  (p q : F)   : 𝓢 ⊢ p ⟶ q ⟶ p ⋏ q
  disj₁  (p q : F)   : 𝓢 ⊢ p ⟶ p ⋎ q
  disj₂  (p q : F)   : 𝓢 ⊢ q ⟶ p ⋎ q
  disj₃  (p q r : F) : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-- Supplymental -/
class EFQ where
  efq (p : F) : 𝓢 ⊢ ⊥ ⟶ p

class HasWeakLEM where
  wlem (p : F) : 𝓢 ⊢ ~p ⋎ ~~p

class HasLEM where
  lem (p : F) : 𝓢 ⊢ p ⋎ ~p

class DNE where
  dne (p : F) : 𝓢 ⊢ ~~p ⟶ p

class Dummett where
  dummett (p q : F) : 𝓢 ⊢ (p ⟶ q) ⋎ (q ⟶ p)

class Peirce where
  peirce (p q : F) : 𝓢 ⊢ ((p ⟶ q) ⟶ p) ⟶ p

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal 𝓢, EFQ 𝓢

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM extends Intuitionistic 𝓢, HasWeakLEM 𝓢

/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic 𝓢, Dummett 𝓢

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Minimal 𝓢, DNE 𝓢

variable {𝓢}

variable [ModusPonens 𝓢]

infixl:90 "⨀" => ModusPonens.mdp

infixl:90 "⨀" => ModusPonens.mdp!

lemma EFQ.efq! {p q} (hp : 𝓢 ⊢! p ⟶ q) (hq : 𝓢 ⊢! p) : 𝓢 ⊢! q := by
  rcases hp with ⟨bp⟩; rcases hq with ⟨bq⟩
  exact ⟨bp ⨀ bq⟩

section EFQ

variable [EFQ 𝓢]

lemma efq' (b : 𝓢 ⊢ ⊥) (f : F) : 𝓢 ⊢ f := EFQ.efq f ⨀ b

lemma efq'! (h : 𝓢 ⊢! ⊥) (f : F) : 𝓢 ⊢! f := by
  rcases h with ⟨b⟩; exact ⟨efq' b f⟩

end EFQ

end LO.System
