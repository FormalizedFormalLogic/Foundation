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

open Deduction

theorem Deducible.toClassical {T : Theory α} {p} : T ⊢ p → (T : Classical.Theory α) ⊢! p
  | axm h                      => Deduction.axm! (Set.mem_image_of_mem _ h)
  | @modusPonens _ _ p q b₁ b₂ => by
      let b₁' : (T : Classical.Theory α) ⊢! p ⟶ q := Deducible.toClassical b₁
      let b₂' : (T : Classical.Theory α) ⊢! p := Deducible.toClassical b₂
      exact b₁' ⨀ b₂'
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

namespace Classical

@[simp]
def Formula.toIntiotionistic : Formula α → Intuitionistic.Formula α
  | Formula.atom a  => Intuitionistic.Formula.atom a
  | Formula.natom a => ~Intuitionistic.Formula.atom a
  | ⊤               => ⊤
  | ⊥               => ⊥
  | p ⋏ q           => p.toIntiotionistic ⋏ q.toIntiotionistic
  | p ⋎ q           => p.toIntiotionistic ⋎ q.toIntiotionistic

instance : Coe (Formula α) (Intuitionistic.Formula α) := ⟨Formula.toIntiotionistic⟩

instance : Coe (Theory α) (Intuitionistic.Theory α) := ⟨(Formula.toIntiotionistic '' ·)⟩

variable [DecidableEq α] [Encodable α]

-- lemma Deducible.toClassical {T : Theory α} {p} : T ⊢! p → (T : Intuitionistic.Theory α) ⊢! ~~p := sorry

end Classical

end LO.Propositional
