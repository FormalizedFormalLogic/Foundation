import Logic.Predicate.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.FirstOrder

namespace Arith.Incompleteness

local notation "Σ" => Bool.true
local notation "Π" => Bool.false

section Conditions

variable (T U : Theory ℒₒᵣ) --  [EqTheory T] [PAminus T] [DecidablePred T]

class HasProvable where
  Provable : Subsentence ℒₒᵣ 1
  -- hier : Hierarchy b n (Provable T)
  spec : ∀ (σ : Sentence ℒₒᵣ), (ℕ ⊧ ([→ ⸢σ⸣].hom Provable)) ↔ (T ⊢! σ)

variable [HasProvable T]

notation "Pr[" T "]" => HasProvable.Provable T

def prsubst (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := [→ ⸢σ⸣].hom Pr[T]

notation "Pr[" T "](⸢ " σ " ⸣)" => prsubst T (σ : Sentence ℒₒᵣ)

class ProvableLimit (b n) where
  hier : Hierarchy b n Pr[T]

class Derivability1 where
  D1 : ∀ {σ : Sentence ℒₒᵣ}, (T ⊢! σ) → (T ⊢! Pr[T](⸢σ⸣))

class Derivability2 where
  D2 : ∀ (σ π : Sentence ℒₒᵣ), T ⊢! Pr[T](⸢σ ⟶ π⸣) ⟶ (Pr[T](⸢σ⸣)) ⟶ (Pr[T](⸢π⸣))

class Derivability3 where
  D3 : ∀ (σ : Sentence ℒₒᵣ), T ⊢! Pr[T](⸢σ⸣) ⟶ Pr[T](⸢Pr[T](⸢σ⸣)⸣)

class FormalizedCompleteness (cb cn) where
  FC : ∀ (σ : Sentence ℒₒᵣ), (Hierarchy cb cn σ) → (T ⊢! σ ⟶ Pr[T](⸢σ⸣))

-- abbrev FormalizedSigmaOneCompleteness := @FormalizedCompleteness T Σ 1

/-
instance [HasProvabilityPred T Σ 1] [FormalizedCompleteness T Σ 1] : (@Derivability3 T b n) :=
  ⟨λ σ => @FormalizedCompleteness.FC T Σ 1 _ ([→ ⸢σ⸣].hom (HasProvabilityPred.Provable T b n)) (by sorry)⟩
-/

/-
class Expandable extends HasProvabilityPred T b n where
  expand : ∀ U, HasProvabilityPred (T ∪ U) b n

instance [HasProvabilityPred T b n] [@Expandable T b n] : HasProvabilityPred (T ∪ {σ}) b n := by exact Expandable.expand {σ}

class FormalizedDeductionTheorem [HasProvabilityPred U b n] where
  FDT : ∀ (σ π : Sentence ℒₒᵣ), (T ⊢! Pr[U](⸢σ ⟶ π⸣)  Pr[T ∪ {σ}](⸢π⸣))
-/

class Diagonizable (b n) where
  diag (δ : Subsentence ℒₒᵣ 1) : (Hierarchy b n δ) → (∃ (σ : Sentence ℒₒᵣ), (Hierarchy b n σ) ∧ (T ⊢! σ ⟷ ([→ ⸢σ⸣].hom δ)))

def Consistency : Sentence ℒₒᵣ := ~Pr[T](⸢⊥⸣)

notation "Con[" T "]" => Consistency T

end Conditions

section ProvablePredCalculus

/-
variable (T : Theory ℒₒᵣ) [HasProvabilityPred T]
variable [Derivability1 T] [Derivability2 T] [Derivability3 T]

lemma Dil : (T ⊢! (Pr[T](⸢σ⸣) ⋏ Pr[T](⸢~σ⸣)) ⟶ Pr[T](⸢⊥⸣)) := by sorry
-/

end ProvablePredCalculus


section FixedPoints

variable (T : Theory ℒₒᵣ) [HasProvable T]

def IsGoedelSentence (G : Sentence ℒₒᵣ) := T ⊢! G ⟷ ~Pr[T](⸢G⸣)

lemma exists_GoedelSentence [ProvableLimit T Σ 1] [Diagonizable T Π 1] : ∃ (G : Sentence ℒₒᵣ), IsGoedelSentence T G := by
  have ⟨G, ⟨_, hd⟩⟩ := @Diagonizable.diag T Π 1 _ (~Pr[T]) (by exact Hierarchy.neg (@ProvableLimit.hier T _ Σ 1 _));
  existsi G; simpa [IsGoedelSentence] using hd;

def IsHenkinSentence (H : Sentence ℒₒᵣ) := T ⊢! H ⟷ Pr[T](⸢H⸣)

lemma exists_HenkinSentence [ProvableLimit T Σ 1] [Diagonizable T Σ 1] : ∃ (H : Sentence ℒₒᵣ), IsHenkinSentence T H := by
  have ⟨H, ⟨_, hd⟩⟩ := @Diagonizable.diag T Σ 1 _ (Pr[T]) ProvableLimit.hier
  existsi H; simpa [IsHenkinSentence] using hd;

def IsKreiselSentence (H : Sentence ℒₒᵣ) := T ⊢! H ⟷ Pr[T](⸢H⸣)

-- def KreiselSentenceExistance (σ : Sentence α) := @Diagonizable.diag T Π 1 _ ([→ ⸢σ⸣].hom Pr[T]) (by exact @ProvabilityPredHierarchy.hie T Π 1 _ _)

end FixedPoints

section provesystem

variable {T : Theory ℒₒᵣ}

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := by sorry

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := by sorry

lemma iff_mp : (T ⊢! σ ⟷ π) → (T ⊢! σ ⟶ π) := by sorry

lemma iff_mpr : (T ⊢! σ ⟷ π) → (T ⊢! π ⟶ σ) := by sorry

lemma imply : (T ⊢! σ ⟶ π) → (T ⊢! σ) → (T ⊢! π) := by sorry

lemma nc : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := by sorry

lemma negneg : (T ⊢! σ) → (T ⊢! ~~σ) := by sorry

end provesystem


section FirstIncompleteness

variable (T : Theory ℒₒᵣ) [HasProvable T] [ProvableLimit T Σ 1] [Diagonizable T Π 1]
variable [Derivability1 T]

variable (hG : IsGoedelSentence T G)

lemma GoedelSentence_Unprovablility : Logic.System.Consistent T → T ⊬! G := by
  intro hConsistency;
  by_contra hP;
  have h₁ : T ⊢! Pr[T](⸢G⸣) := Derivability1.D1 hP;
  have hR : T ⊢! ~G := imply (iff_mpr (iff_contra hG)) (by simp; exact h₁);
  exact hConsistency.false (nc hP hR).some

lemma GoedelSentence_Unrefutability : SigmaOneSound T → T ⊬! ~G := by
  intro hSound;
  by_contra hR;
  have h₁ : T ⊢! Pr[T](⸢G⸣) := by have := imply (iff_mp $ iff_contra hG) hR; simpa;
  have h₂ : ℕ ⊧ Pr[T](⸢G⸣) := hSound.sound (Hierarchy.rew _ ProvableLimit.hier) h₁;
  have hP : T ⊢! G := (HasProvable.spec G).mp h₂;
  exact (consistent_of_sigmaOneSound T).false (nc hP hR).some;

theorem FirstIncompleteness : (SigmaOneSound T) → (¬Logic.System.Complete T) := by
  intro hSound;
  have ⟨G, hG⟩ := exists_GoedelSentence T;
  have hUP : T ⊬! G := GoedelSentence_Unprovablility T hG (consistent_of_sigmaOneSound T);
  have hUR : T ⊬! ~G := GoedelSentence_Unrefutability T hG hSound;
  simp at hUP hUR;
  simpa [Logic.System.Complete, not_or] using ⟨G, hUP, hUR⟩

end FirstIncompleteness



end LO.FirstOrder.Arith.Incompleteness
