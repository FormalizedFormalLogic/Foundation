import Logic.Propositional.Classical.Basic
import Logic.Propositional.Intuitionistic

namespace LO.Propositional

variable {α : Type*}

namespace Intuitionistic

@[simp]
def Formula.toClassical : Formula α → Classical.Formula α
  | Formula.atom a => Classical.Formula.atom a
  | ⊥              => ⊥
  | p ⋏ q          => p.toClassical ⋏ q.toClassical
  | p ⋎ q          => p.toClassical ⋎ q.toClassical
  | p ⟶ q          => p.toClassical ⟶ q.toClassical

instance : Coe (Formula α) (Classical.Formula α) := ⟨Formula.toClassical⟩

instance : Coe (Theory α) (Classical.Theory α) := ⟨(Formula.toClassical '' ·)⟩

def Deduction.toClassical {T : Theory α} {p} : T ⊢ p → (T : Classical.Theory α) ⊢! p
  | axm h                      => Deduction.axm! (Set.mem_image_of_mem _ h)
  | @modusPonens _ _ p q b₁ b₂ => by
      let b₁' : (T : Classical.Theory α) ⊢! p ⟶ q := Deduction.toClassical b₁
      let b₂' : (T : Classical.Theory α) ⊢! p := Deduction.toClassical b₂
      exact Hilbert.modus_ponens'! b₁' b₂'
  | verum _                    => by simp; prover
  | efq _ _                    => by simp; prover
  | imply₁ _ _ _               => by simp; prover
  | imply₂ _ _ _ _             => by simp; prover
  | conj₁ _ _ _                => by simp; prover
  | conj₂ _ _ _                => by simp; prover
  | conj₃ _ _ _                => by simp; prover
  | disj₁ _ _ _                => by simp; prover
  | disj₂ _ _ _                => by simp; prover
  | disj₃ _ _ _ _              => by simp; prover

end Intuitionistic

end LO.Propositional
