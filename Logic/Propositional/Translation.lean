import Logic.Propositional.Classical.Basic
import Logic.Propositional.Superintuitionistic

namespace LO.Propositional

variable {α : Type*}

namespace Superintuitionistic

@[simp]
def Formula.toClassical : Superintuitionistic.Formula α → Classical.Formula α
  | .atom a => Classical.Formula.atom a
  | ⊤              => ⊤
  | ⊥              => ⊥
  | ~p             => ~p.toClassical
  | p ⋏ q          => p.toClassical ⋏ q.toClassical
  | p ⋎ q          => p.toClassical ⋎ q.toClassical
  | p ⟶ q          => p.toClassical ⟶ q.toClassical

instance : Coe (Formula α) (Classical.Formula α) := ⟨Formula.toClassical⟩

instance : Coe (Theory α) (Classical.Theory α) := ⟨(Formula.toClassical '' ·)⟩

/-
def Deduction.toClassical {T : Theory α} {p} : T ⊢ p → (T : Classical.Theory α) ⊢! p
  | axm h                      => Deduction.axm! (Set.mem_image_of_mem _ h)
  | @modusPonens _ _ p q b₁ b₂ => by
      let b₁' : (T : Classical.Theory α) ⊢! p ⟶ q := Deducible.toClassical b₁
      let b₂' : (T : Classical.Theory α) ⊢! p := Deducible.toClassical b₂
      exact b₁' ⨀ b₂'
  | verum _                    => by simp; prover
  | efq _ _                    => by simp; prover
  | imply₁ _ _ _               => by simp; prover
  | imply₂ _ _ _ _             => by simp; prover
  | and₁ _ _ _                => by simp; prover
  | and₂ _ _ _                => by simp; prover
  | and₃ _ _ _                => by simp; prover
  | or₁ _ _ _                => by simp; prover
  | or₂ _ _ _                => by simp; prover
  | or₃ _ _ _ _              => by simp; prover
-/

end Superintuitionistic

namespace Classical

@[simp]
def Formula.toSuperintuitionistic : Formula α → Superintuitionistic.Formula α
  | Formula.atom a  => Superintuitionistic.Formula.atom a
  | Formula.natom a => ~Superintuitionistic.Formula.atom a
  | ⊤               => ⊤
  | ⊥               => ⊥
  | p ⋏ q           => p.toSuperintuitionistic ⋏ q.toSuperintuitionistic
  | p ⋎ q           => p.toSuperintuitionistic ⋎ q.toSuperintuitionistic

instance : Coe (Formula α) (Superintuitionistic.Formula α) := ⟨Formula.toSuperintuitionistic⟩

instance : Coe (Theory α) (Superintuitionistic.Theory α) := ⟨(Formula.toSuperintuitionistic '' ·)⟩

variable [DecidableEq α] [Encodable α]

-- lemma Deducible.toClassical {T : Theory α} {p} : T ⊢! p → (T : Intuitionistic.Theory α) ⊢! ~~p := sorry

end Classical

end LO.Propositional
