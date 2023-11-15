import Logic.Predicate.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.FirstOrder

section Supplymental

/- TODO: 拡大理論は拡大元の理論の全ての文を証明できるはず -/
@[simp] lemma SubTheory.stronger {T U : Theory ℒₒᵣ} [SubTheory T U] {σ} : (T ⊢! σ) → (U ⊢! σ) := by sorry

end Supplymental

namespace Arith

namespace Incompleteness.Provability

local notation "Σ" => Bool.true
local notation "Π" => Bool.false

section Conditions

variable (T U : Theory ℒₒᵣ)

class HasProvable where
  Provable : Subsentence ℒₒᵣ 1
  -- hier : Hierarchy b n (Provable T)
  spec : ∀ (σ : Sentence ℒₒᵣ), (ℕ ⊧ ([→ ⸢σ⸣].hom Provable)) ↔ (T ⊢! σ)

-- variable

notation "Pr[" T "]" => HasProvable.Provable T

def prsubst [HasProvable T] (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := [→ ⸢σ⸣].hom Pr[T]

notation "Pr[" T "](⸢ " σ " ⸣)" => prsubst T (σ : Sentence ℒₒᵣ)

class ProvableLimit [HasProvable T] (b n) where
  hier : Hierarchy b n Pr[T]

variable [HasProvable U]

class Derivability1 [SubTheory T U] where
  D1 : ∀ {σ : Sentence ℒₒᵣ}, (U ⊢! σ) → (T ⊢! Pr[U](⸢σ⸣))

class Derivability2 [SubTheory T U] where
  D2 : ∀ (σ π : Sentence ℒₒᵣ), T ⊢! Pr[U](⸢σ ⟶ π⸣) ⟶ (Pr[U](⸢σ⸣) ⟶ Pr[U](⸢π⸣))

class Derivability3 [SubTheory T U] where
  D3 : ∀ (σ : Sentence ℒₒᵣ), T ⊢! Pr[U](⸢σ⸣) ⟶ Pr[U](⸢Pr[U](⸢σ⸣)⸣)

class FormalizedCompleteness [SubTheory T U] (b n) where
  FC : ∀ (σ : Sentence ℒₒᵣ), (Hierarchy b n σ) → (T ⊢! σ ⟶ Pr[U](⸢σ⸣))

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

def Consistency [HasProvable T] : Sentence ℒₒᵣ := ~Pr[T](⸢⊥⸣)

notation "Con[" T "]" => Consistency T

end Conditions


section FixedPoints

variable (T U : Theory ℒₒᵣ) [HasProvable U] (k)

def IsGoedelSentence (G : Sentence ℒₒᵣ) := T ⊢! G ⟷ ~Pr[U](⸢G⸣)

lemma exists_GoedelSentence [Diagonizable T Π k] [ProvableLimit U Σ k] : ∃ (G : Sentence ℒₒᵣ), (IsGoedelSentence T U G ∧ Hierarchy Π k G) := by
  have ⟨G, ⟨hH, hd⟩⟩ := @Diagonizable.diag T Π k _ (~Pr[U]) (by exact Hierarchy.neg (@ProvableLimit.hier U _ Σ k _));
  existsi G; simpa [IsGoedelSentence, hH] using hd;

abbrev exists_GoedelSentence₁ [Diagonizable T Π 1] [ProvableLimit U Σ 1] := exists_GoedelSentence T U 1

def IsHenkinSentence (H : Sentence ℒₒᵣ) := T ⊢! H ⟷ Pr[U](⸢H⸣)

lemma exists_HenkinSentence [Diagonizable T Σ k] [ProvableLimit U Σ k] : ∃ (H : Sentence ℒₒᵣ), (IsHenkinSentence T U H ∧ Hierarchy Σ k H) := by
  have ⟨H, ⟨hH, hd⟩⟩ := @Diagonizable.diag T Σ k _ (Pr[U]) ProvableLimit.hier
  existsi H; simpa [IsHenkinSentence, hH] using hd;

def IsKreiselSentence (H : Sentence ℒₒᵣ) (σ : Sentence ℒₒᵣ) := T ⊢! H ⟷ (Pr[U](⸢H⸣) ⟶ σ)

-- def KreiselSentenceExistance (σ : Sentence α) := @Diagonizable.diag T Π 1 _ ([→ ⸢σ⸣].hom Pr[T]) (by exact @ProvabilityPredHierarchy.hie T Π 1 _ _)

end FixedPoints


section ProvabilityCalculus

open Subformula

variable {T U : Theory ℒₒᵣ} [SubTheory T U] [HasProvable U]

lemma iff_intro : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ σ) → (T ⊢! σ ⟷ π) := by sorry

lemma iff_trans : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ ρ) → (T ⊢! σ ⟷ ρ) := by sorry

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := by sorry

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := by sorry

lemma iff_mp : (T ⊢! σ ⟷ π) → (T ⊢! σ ⟶ π) := by sorry

lemma iff_mpr : (T ⊢! σ ⟷ π) → (T ⊢! π ⟶ σ) := by sorry

lemma iff_unprov : (T ⊢! σ ⟷ π) → (T ⊬! σ) → (T ⊬! π) := by sorry

lemma imply : (T ⊢! σ ⟶ π) → (T ⊢! σ) → (T ⊢! π) := by sorry

lemma imply_trans : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ ρ) → (T ⊢! σ ⟶ ρ) := by sorry

lemma imply_contra₀ : (T ⊢! σ ⟶ π) → (T ⊢! ~π ⟶ ~σ) := by sorry

lemma imply_contra₃ : (T ⊢! ~σ ⟶ ~π) → (T ⊢! π ⟶ σ) := by sorry

lemma nc : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := by sorry

lemma negneg : (T ⊢! σ) → (T ⊢! ~~σ) := by sorry

lemma efq : (T ⊢! ⊥ ⟶ σ) := by sorry

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by sorry

lemma elim_and_right_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! π ⟶ σ) → (T ⊢! π ⟶ ρ) := by sorry


variable [Derivability1 T U] [Derivability2 T U] [Derivability3 T U]

lemma provDilemma (σ) : (T ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣))) := by
  have a : T ⊢! Pr[U](⸢σ ⟶ ~σ⸣) ⟶ (Pr[U](⸢σ⸣)) ⟶ (Pr[U](⸢~σ⸣)) := Derivability2.D2 σ (~σ);
  have b := imply_contra₀ a;
  simp [imp_eq (Pr[U](⸢σ⸣)), imp_eq σ] at b;
  sorry;

end ProvabilityCalculus


namespace FirstIncompleteness

variable (T U : Theory ℒₒᵣ) [SubTheory T U]
variable [Diagonizable T Π 1]
variable [HasProvable U] [ProvableLimit U Σ 1] [Derivability1 T U]

variable (hG : IsGoedelSentence T U G)

open Derivability1

lemma GoedelSentence_Unprovablility : Logic.System.Consistent U → U ⊬! G := by
  intro hConsistency;
  by_contra hP;
  have h₁ : T ⊢! Pr[U](⸢G⸣) := D1 hP;
  have h₂ : T ⊢! Pr[U](⸢G⸣) ⟶ ~G := by simpa using iff_mpr $ iff_contra hG;
  have hR : U ⊢! ~G := by have := imply h₂ h₁; sorry; -- exact SubTheory.stronger b;
  exact hConsistency.false (nc hP hR).some

lemma GoedelSentence_Unrefutability : SigmaOneSound U → U ⊬! ~G := by
  intro hSound;
  by_contra hR;
  have a : U ⊢! ~G ⟶ ~~Pr[U](⸢G⸣) := by have := (iff_mp $ iff_contra hG); sorry;
  have h₁ : U ⊢! Pr[U](⸢G⸣) := by have := imply a hR; simpa;
  have h₂ : ℕ ⊧ Pr[U](⸢G⸣) := hSound.sound (Hierarchy.rew _ ProvableLimit.hier) h₁;
  have hP : U ⊢! G := (HasProvable.spec G).mp h₂;
  exact (consistent_of_sigmaOneSound U).false (nc hP hR).some;

theorem FirstIncompleteness : (SigmaOneSound U) → (¬Logic.System.Complete U) := by
  intro hSound;
  have ⟨G, ⟨hG, _⟩⟩ := exists_GoedelSentence₁ T U;
  have hUP : U ⊬! G := GoedelSentence_Unprovablility T U hG (consistent_of_sigmaOneSound U);
  have hUR : U ⊬! ~G := GoedelSentence_Unrefutability T U hG hSound;
  simp at hUP hUR;
  simpa [Logic.System.Complete, not_or] using ⟨G, hUP, hUR⟩

end FirstIncompleteness


namespace SecondIncompleteness

variable (T U : Theory ℒₒᵣ) [SubTheory T U]
variable [Diagonizable T Π 1]
variable [HasProvable U] [ProvableLimit U Σ 1] [Derivability1 T U] [Derivability2 T U] [FormalizedCompleteness T U Σ 1]

open Derivability1 Derivability2 FormalizedCompleteness

lemma FormalizedConsistency (σ : Sentence ℒₒᵣ) : T ⊢! (~Pr[U](⸢σ⸣) ⟶ Con[U]) := by
  exact imply_contra₀ $ imply (D2 _ _) $ D1 efq

variable (U' : Theory ℒₒᵣ) [SubTheory T U'] [HasProvable U'] [Derivability1 T U'] [Derivability2 T U'] [Derivability3 T U']

lemma extend : (U' ⊢! Con[U] ⟶ ~Pr[U](⸢σ⸣)) ↔ (U' ⊢! Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) := by
  apply Iff.intro;
  . intro H;
    exact imply_contra₃ $ imply_trans (by have := FormalizedConsistency T U (~σ); sorry) H;
  . intro H;
    have a : T ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := provDilemma σ;
    have b : U' ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := by sorry;
    exact imply_contra₀ $ elim_and_left_dilemma b H;

lemma equality_GoedelSentence_Consistency {G} (hG : IsGoedelSentence T U G) (hGS1 : Hierarchy Π 1 G) : U ⊢! G ⟷ Con[U] := by
  have hnGP1 : Hierarchy Σ 1 (~G) := Hierarchy.neg hGS1;
  have h₁ : T ⊢! ~G ⟶ Pr[U](⸢~G⸣) := FormalizedCompleteness.FC (~G) hnGP1;
  have h₂ : T ⊢! Pr[U](⸢G⸣) ⟶ ~G := by have := iff_mp (iff_contra' hG); simpa;
  have h₃ : U ⊢! Pr[U](⸢G⸣) ⟶ Pr[U](⸢~G⸣) := have := imply_trans h₂ h₁; by sorry;
  have h₄ : U ⊢! Con[U] ⟶ ~Pr[U](⸢G⸣) := (extend T _ _).mpr h₃;
  have h₅ : U ⊢! ~Pr[U](⸢G⸣) ⟶ Con[U] := by have := FormalizedConsistency T U G; sorry;
  exact iff_trans (by have := hG; sorry) $ iff_intro h₅ h₄;

lemma Consistency_Unprovablility : Logic.System.Consistent U → U ⊬! Con[U] := by
  intro hConsistency;
  have ⟨G, ⟨hG, hGS1⟩⟩ := exists_GoedelSentence₁ T U;
  have hI₁ := FirstIncompleteness.GoedelSentence_Unprovablility T U hG hConsistency;
  have hEq := equality_GoedelSentence_Consistency T U hG hGS1;
  exact iff_unprov hEq hI₁;

lemma Consistency_Unrefutability : SigmaOneSound U → U ⊬! ~Con[U] := by
  intro hSound;
  have ⟨G, ⟨hG, hGS1⟩⟩ := exists_GoedelSentence₁ T U;
  have hI₁ := FirstIncompleteness.GoedelSentence_Unrefutability T U hG hSound;
  have hEq := equality_GoedelSentence_Consistency T U hG hGS1;
  exact iff_unprov (iff_contra hEq) hI₁;

end SecondIncompleteness

end LO.FirstOrder.Arith.Incompleteness.Provability
