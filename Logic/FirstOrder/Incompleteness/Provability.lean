import Logic.Predicate.FirstOrder.Incompleteness.FirstIncompleteness

namespace LO.FirstOrder

namespace Arith

namespace Incompleteness.Provability

local notation "Σ" => Bool.true
local notation "Π" => Bool.false

section TheoryCalculus

variable {T U : Theory ℒₒᵣ} [hs : SubTheory T U] {σ π : Sentence ℒₒᵣ}

lemma deduction {σ π} : (T ⊢! σ ⟶ π) ↔ (T ∪ {σ} ⊢! π) := by
  apply Iff.intro;
  . sorry;
  . sorry;

@[simp]
lemma subtheorem : (T ⊢! σ) → (U ⊢! σ) := by
  simp; intro H; exact ⟨Logic.System.weakening H hs.sub⟩;

@[simp]
lemma trivial : T ∪ {σ} ⊢! σ := by sorry

lemma consistent_or : (¬Logic.System.Consistent (T ∪ {σ})) → (T ⊢! ~σ) := by sorry

end TheoryCalculus


section ProvesCalculus

open Subformula

variable {T U : Theory ℒₒᵣ} [SubTheory T U] {σ π ρ : Sentence ℒₒᵣ}

lemma or_intro_left : (T ⊢! σ) → (T ⊢! σ ⋎ π) := by sorry

lemma or_comm : (T ⊢! σ ⋎ π) → (T ⊢! π ⋎ σ) := by
  simp;
  intro H;
  sorry

lemma or_intro_right : (T ⊢! π) → (T ⊢! σ ⋎ π) := λ H => or_comm $ or_intro_left H

lemma or_elim_left : (T ⊢! σ ⋎ π) → (T ⊢! ~σ) → (T ⊢! π) := by sorry

lemma or_elim_right : (T ⊢! σ ⋎ π) → (T ⊢! ~π) → (T ⊢! σ) := λ H₁ H₂ => or_elim_left (or_comm H₁) H₂

lemma and_intro : (T ⊢! σ) → (T ⊢! π) → (T ⊢! σ ⋏ π) := by sorry

lemma and_comm : (T ⊢! σ ⋏ π) → (T ⊢! π ⋏ σ) := by
  simp;
  intro H;
  sorry

lemma and_left : (T ⊢! σ ⋏ π) → (T ⊢! σ) := by
  simp;
  intro H;
  sorry

lemma and_right : (T ⊢! σ ⋏ π) → (T ⊢! π) := λ H => and_left $ and_comm H

lemma mp : (T ⊢! σ ⟶ π) → (T ⊢! σ) → (T ⊢! π) := by
  intro H₁ H₂;
  simp only [imp_eq] at H₁;
  exact or_elim_left H₁ (by simpa [neg_neg']);

alias MP := mp

@[simp]
lemma imply_intro {σ π} : (T ⊢! π) → (T ⊢! σ ⟶ π) := λ H => or_intro_right H

lemma imply_axm : T ⊢! σ ⟶ σ := deduction.mpr trivial

lemma imply_trans : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ ρ) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact MP (subtheorem H₂) (deduction.mp H₁);

lemma imply_contra₀ : (T ⊢! σ ⟶ π) → (T ⊢! ~π ⟶ ~σ) := by
  simp only [imp_eq, neg_neg']; intro H; exact or_comm H;

lemma imply_contra₁ : (T ⊢! σ ⟶ ~π) → (T ⊢! π ⟶ ~σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₂ : (T ⊢! ~σ ⟶ π) → (T ⊢! ~π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₃ : (T ⊢! ~σ ⟶ ~π) → (T ⊢! π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma iff_comm : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ σ) := λ H => and_intro (and_right H) (and_left H)

lemma iff_mp : (T ⊢! σ ⟷ π) → (T ⊢! σ ⟶ π) := λ H => and_left H

lemma iff_mpr : (T ⊢! σ ⟷ π) → (T ⊢! π ⟶ σ) := λ h => iff_mp $ iff_comm h

lemma iff_def : (T ⊢! σ ⟷ π) ↔ ((T ⊢! σ) ↔ (T ⊢! π)) := by
  apply Iff.intro;
  . intro H;
    exact Iff.intro (mp $ iff_mp H) (mp $ iff_mpr H);
  . intro H;
    sorry;
    -- apply and_intro;
    -- have := H.mp;
    -- have := H.mpr;

lemma iff_intro : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ σ) → (T ⊢! σ ⟷ π) := λ H₁ H₂ => and_intro H₁ H₂

lemma iff_trans : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ ρ) → (T ⊢! σ ⟷ ρ) := by
  intro H₁ H₂;
  exact iff_intro (imply_trans (iff_mp H₁) (iff_mp H₂)) (imply_trans (iff_mpr H₂) (iff_mpr H₁));

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := λ H => iff_intro (imply_contra₀ $ iff_mpr H) (imply_contra₀ $ iff_mp H)

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := λ h => iff_comm $ iff_contra h

lemma iff_unprov : (T ⊢! σ ⟷ π) → (T ⊬! σ) → (T ⊬! π) := by sorry;

lemma iff_unprov' : (T ⊬! σ ⟶ π) → (T ⊢! π ⟷ ρ) → (T ⊬! σ ⟶ ρ) := by sorry;

lemma NC : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := by sorry;

lemma neg_neg : (T ⊢! σ) ↔ (T ⊢! ~~σ) := by simp;

lemma EFQ : (T ⊢! ⊥ ⟶ σ) := by sorry
  -- have a := @Logic.System.inConsistent_of_proof _ _ _ (T ∪ {⊥}) trivial.some;
  -- apply deduction.mpr;

lemma imply_dilemma : T ⊢! σ ⟶ (π ⟶ ρ) → T ⊢! (σ ⟶ π) → T ⊢! (σ ⟶ ρ) := by
  intro H₁ H₂;
  exact deduction.mpr $ MP (deduction.mp H₁) (deduction.mp H₂);

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact MP (subtheorem H₁) (and_intro trivial $ deduction.mp H₂);

end ProvesCalculus

section Conditions

variable (T U : Theory ℒₒᵣ)

class HasProvable where
  Provable : Subsentence ℒₒᵣ 1
  -- hier : Hierarchy b n (Provable T)
  spec : ∀ (σ : Sentence ℒₒᵣ), (ℕ ⊧ ([→ ⸢σ⸣].hom Provable)) ↔ (T ⊢! σ)

abbrev HasProvable.Pr := HasProvable.Provable

open HasProvable

notation "Pr[" T "]" => HasProvable.Provable T

abbrev prsubst [HasProvable T] (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := [→ ⸢σ⸣].hom $ Pr T

notation "Pr[" T "](⸢" σ "⸣)" => prsubst T (σ : Sentence ℒₒᵣ)

def Consistency [HasProvable T] : Sentence ℒₒᵣ := ~Pr[T](⸢⊥⸣)

notation "Con[" T "]" => Consistency T

class ProvableLimit [HasProvable T] (b n) where
  hier : Hierarchy b n Pr[T]

variable [SubTheory T U] [HasProvable U]

class Derivability1 where
  D1 : ∀ {σ : Sentence ℒₒᵣ}, (U ⊢! σ) → (T ⊢! Pr[U](⸢σ⸣))

abbrev Derivability1' [HasProvable T] := Derivability1 T T

class Derivability2 where
  D2 : ∀ (σ π : Sentence ℒₒᵣ), T ⊢! Pr[U](⸢σ ⟶ π⸣) ⟶ (Pr[U](⸢σ⸣) ⟶ Pr[U](⸢π⸣))

abbrev Derivability2' [HasProvable T] := Derivability2 T T

lemma Derivability2.D2_iff (σ π : Sentence ℒₒᵣ) : T ⊢! Pr[U](⸢σ ⟷ π⸣) ⟶ (Pr[U](⸢σ⸣) ⟷ Pr[U](⸢π⸣)) := by
  sorry;

class Derivability3 where
  D3 : ∀ (σ : Sentence ℒₒᵣ), T ⊢! Pr[U](⸢σ⸣) ⟶ Pr[U](⸢Pr[U](⸢σ⸣)⸣)

abbrev Derivability3' [HasProvable T] := Derivability3 T T

variable (U' : Theory ℒₒᵣ) [SubTheory U U'] [HasProvable U']
lemma drv1 : Derivability1 T U → Derivability1 T U' := by sorry;
lemma drv2 : Derivability2 T U → Derivability2 T U' := by sorry;
lemma drv3 : Derivability3 T U → Derivability3 T U' := by sorry;
-- instance [Derivability1 T U] : Derivability1 T U' := drv1 T U U';


class FormalizedCompleteness (b n) where
  FC : ∀ (σ : Sentence ℒₒᵣ), (Hierarchy b n σ) → (T ⊢! σ ⟶ Pr[U](⸢σ⸣))

variable [∀ (σ : Sentence ℒₒᵣ), HasProvable (U ∪ {σ})]

class FormalizedDeductionTheorem where
  FDT : ∀ (σ π : Sentence ℒₒᵣ), (T ⊢! Pr[U](⸢σ ⟶ π⸣) ⟷ Pr[U ∪ {σ}](⸢π⸣))

lemma FormalizedDeductionTheorem.FDT_neg [FormalizedDeductionTheorem T U] : T ⊢! ~Pr[U](⸢σ ⟶ π⸣) ⟷ ~Pr[U ∪ {σ}](⸢π⸣) := by
  suffices T ⊢! Pr[U](⸢σ ⟶ π⸣) ⟷ Pr[U ∪ {σ}](⸢π⸣) from iff_contra this
  apply FormalizedDeductionTheorem.FDT

class Diagonizable (b n) where
  diag (δ : Subsentence ℒₒᵣ 1) : (Hierarchy b n δ) → (∃ (σ : Sentence ℒₒᵣ), (Hierarchy b n σ) ∧ (T ⊢! σ ⟷ ([→ ⸢σ⸣].hom δ)))


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

def IsKreiselSentence (K : Sentence ℒₒᵣ) (σ : Sentence ℒₒᵣ) := T ⊢! K ⟷ (Pr[U](⸢K⸣) ⟶ σ)

lemma exists_KreiselSentence [Diagonizable T Σ k] [ProvableLimit U Σ k] (σ : Sentence ℒₒᵣ) : ∃ (K : Sentence ℒₒᵣ), (IsKreiselSentence T U K σ) := by
  -- have ⟨K, ⟨hH, hd⟩⟩ := @Diagonizable.diag T Σ k _ (“!Pr[U] → !(↑σ)”) (by sorry)
  -- existsi K; simpa [IsKreiselSentence, hH] using hd;
  sorry;

-- def KreiselSentenceExistance (σ : Sentence α) := @Diagonizable.diag T Π 1 _ ([→ ⸢σ⸣].hom Pr[T]) (by exact @ProvabilityPredHierarchy.hie T Π 1 _ _)

end FixedPoints


section ProvableCalculus

open Subformula

variable {T U : Theory ℒₒᵣ} [SubTheory T U] [HasProvable U]
variable [Derivability1 T U] [Derivability2 T U] [Derivability3 T U]

open Derivability1 Derivability2 Derivability3

lemma formalized_NC (σ) : T ⊢! (Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := by
  have : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := NC;
  have a : T ⊢! Pr[U](⸢σ ⟶ ~σ⸣) ⟶ (Pr[U](⸢σ⸣)) ⟶ (Pr[U](⸢~σ⸣)) := D2 σ (~σ);
  have b : T ⊢! ~(Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) ⟶ ~Pr[U](⸢σ ⟶ ~σ⸣) := imply_contra₀ (D2 σ (~σ));

  simp [imp_eq Pr[U](⸢σ⸣), imp_eq σ] at b;
  sorry;

lemma formalized_NC' (σ) : T ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := by
  have a : T ⊢! Pr[U](⸢σ ⟶ ~σ⸣) ⟶ (Pr[U](⸢σ⸣)) ⟶ (Pr[U](⸢~σ⸣)) := D2 σ (~σ);
  have b := imply_contra₀ a;
  simp [imp_eq Pr[U](⸢σ⸣), imp_eq σ] at b;
  sorry;

lemma formalized_DNI (σ) : T ⊢! (Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~~σ⸣)) := by simp [neg_neg', imply_axm];

lemma formalized_DNE (σ) : T ⊢! (Pr[U](⸢~~σ⸣) ⟶ Pr[U](⸢σ⸣)) := by simp [neg_neg', imply_axm];

lemma formalized_neg_def (σ) : T ⊢! Pr[U](⸢~σ⸣) ⟷ Pr[U](⸢σ ⟶ ⊥⸣) := by
  apply iff_intro;
  . sorry;
  . sorry;

end ProvableCalculus

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
  have hR : U ⊢! ~G := subtheorem (mp h₂ h₁);
  exact hConsistency.false (NC hP hR).some

lemma GoedelSentence_Unrefutability : SigmaOneSound U → U ⊬! ~G := by
  intro hSound;
  by_contra hR;
  have a : U ⊢! ~G ⟶ ~~Pr[U](⸢G⸣) := subtheorem (iff_mp $ iff_contra hG);
  have h₁ : U ⊢! Pr[U](⸢G⸣) := by have := mp a hR; simpa;
  have h₂ : ℕ ⊧ Pr[U](⸢G⸣) := hSound.sound (Hierarchy.rew _ ProvableLimit.hier) h₁;
  have hP : U ⊢! G := (HasProvable.spec G).mp h₂;
  exact (consistent_of_sigmaOneSound U).false (NC hP hR).some;

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
  exact imply_contra₀ $ mp (D2 _ _) $ D1 EFQ

variable (U' : Theory ℒₒᵣ) [SubTheory T U'] [HasProvable U'] [Derivability1 T U'] [Derivability2 T U'] [Derivability3 T U']

private lemma extend : (U' ⊢! Con[U] ⟶ ~Pr[U](⸢σ⸣)) ↔ (U' ⊢! Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) := by
  apply Iff.intro;
  . intro H;
    exact imply_contra₃ $ imply_trans (subtheorem (FormalizedConsistency T U (~σ))) H;
  . intro H;
    have : T ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := (formalized_NC' σ);
    have : U' ⊢! (Pr[U](⸢σ⸣) ⋏ Pr[U](⸢~σ⸣)) ⟶ (Pr[U](⸢⊥⸣)) := subtheorem this;
    exact imply_contra₀ $ elim_and_left_dilemma this H;

lemma equality_GoedelSentence_Consistency {G} (hG : IsGoedelSentence T U G) (hGS1 : Hierarchy Π 1 G) : U ⊢! G ⟷ Con[U] := by
  have hnGP1 : Hierarchy Σ 1 (~G) := Hierarchy.neg hGS1;
  have h₁ : T ⊢! ~G ⟶ Pr[U](⸢~G⸣) := FormalizedCompleteness.FC (~G) hnGP1;
  have h₂ : T ⊢! Pr[U](⸢G⸣) ⟶ ~G := by have := iff_mp (iff_contra' hG); simpa;
  have h₃ : U ⊢! Pr[U](⸢G⸣) ⟶ Pr[U](⸢~G⸣) := subtheorem (imply_trans h₂ h₁);
  have h₄ : U ⊢! Con[U] ⟶ ~Pr[U](⸢G⸣) := (extend T _ _).mpr h₃;
  have h₅ : U ⊢! ~Pr[U](⸢G⸣) ⟶ Con[U] := subtheorem (FormalizedConsistency T U G);
  exact iff_trans (subtheorem hG) $ iff_intro h₅ h₄;

lemma Consistency_Unprovablility : Logic.System.Consistent U → U ⊬! Con[U] := by
  intro hConsistency;
  have ⟨G, ⟨hG, hGS1⟩⟩ := exists_GoedelSentence₁ T U;
  have hI₁ := FirstIncompleteness.GoedelSentence_Unprovablility T U hG hConsistency;
  have hEq := equality_GoedelSentence_Consistency T U hG hGS1;
  exact iff_unprov hEq hI₁;

lemma Consistent_of_ProvabilityConsistency : (U ⊢! Con[U]) → ¬Logic.System.Consistent U := by simpa using not_imp_not.mpr (Consistency_Unprovablility T U);

lemma Consistency_Unrefutability : SigmaOneSound U → U ⊬! ~Con[U] := by
  intro hSound;
  have ⟨G, ⟨hG, hGS1⟩⟩ := exists_GoedelSentence₁ T U;
  have hI₁ := FirstIncompleteness.GoedelSentence_Unrefutability T U hG hSound;
  have hEq := equality_GoedelSentence_Consistency T U hG hGS1;
  exact iff_unprov (iff_contra hEq) hI₁;

lemma NotSigmaOneSound_of_UnrefutabilityConsistency : (U ⊢! ~Con[U]) → (IsEmpty (SigmaOneSound U)) := by
  intro H;
  by_contra C;
  exact (Consistency_Unrefutability T U (by simp at C; exact C.some)) H;

end SecondIncompleteness

namespace Loeb_with_IT2

variable (T U : Theory ℒₒᵣ) [SubTheory T U] [∀ σ, SubTheory T (U ∪ {~σ})] [∀ σ, SubTheory (T ∪ {σ}) (U ∪ {~σ})] [ss : SigmaOneSound U]
variable [Diagonizable T Π 1]
variable
        [HasProvable U]
        [∀ σ, HasProvable (U ∪ {σ})]
        [ProvableLimit U Σ 1]
        [∀ σ, ProvableLimit (U ∪ {~σ}) Σ 1]
        [∀ σ, Derivability1 T (U ∪ {σ})]
        [∀ σ, Derivability2 T (U ∪ {σ})]
        [∀ σ, FormalizedCompleteness T (U ∪ {σ}) Σ 1]
        [FormalizedDeductionTheorem T U]

open Derivability1 Derivability2 FormalizedCompleteness FormalizedDeductionTheorem SecondIncompleteness

theorem Loeb_with_IT2 (σ) : (U ⊢! σ) ↔ (U ⊢! Pr[U](⸢σ⸣) ⟶ σ) := by
  apply Iff.intro;
  . intro H; simp;
  . intro H;
    have h₁ : U ⊢! ~σ ⟶ ~Pr[U](⸢σ⸣) := imply_contra₀ H;
    have h₂ : U ∪ {~σ} ⊢! ~Pr[U](⸢σ⸣) := deduction.mp h₁;
    have h₃ : U ∪ {~σ} ⊢! ~Pr[U](⸢~σ ⟶ ⊥⸣) := by
      have : U ∪ {~σ} ⊢! ~Pr[U](⸢σ⸣) ⟶ ~Pr[U](⸢~~σ⸣) := imply_contra₀ $ formalized_DNE σ;
      have : U ∪ {~σ} ⊢! ~Pr[U](⸢σ⸣) → U ∪ {~σ} ⊢! ~Pr[U](⸢~~σ⸣) := mp this;
      exact mp (iff_mp (iff_contra (formalized_neg_def _))) (this h₂);
    have h₄ : U ∪ {~σ} ⊢! ~Pr[U](⸢~σ ⟶ ⊥⸣) ⟷ ~Pr[U ∪ {~σ}](⸢⊥⸣) := by
      have : T ⊢! ~Pr[U](⸢~σ ⟶ ⊥⸣) ⟷ ~Pr[U ∪ {~σ}](⸢⊥⸣) := FDT_neg _ _;
      exact subtheorem this;
    have h₅ : U ∪ {~σ} ⊢! Con[U ∪ {~σ}] := mp (iff_mp h₄) h₃;
    have hc : ¬Logic.System.Consistent (U ∪ {~σ}) := Consistent_of_ProvabilityConsistency T _ h₅;
    simpa using consistent_or hc;

variable
        [Derivability1 T U]
        [Derivability1 U U]
        [Derivability2 T U]
        [FormalizedCompleteness T U Σ 1]

/-- Formalized Gödel's 2nd Incompleteness Theorem -/
theorem FormalizedUnprovabilityConsistency : U ⊬! Con[U] ⟶ ~Pr[U](⸢~Con[U]⸣) := by
  by_contra H;
  have h₁ : U ⊢! Pr[U](⸢~Con[U]⸣) ⟶ ~Con[U] := by have := imply_contra₃ H; nth_rw 2 [Consistency]; simpa [neg_neg];
  have h₂ : U ⊢! ~Con[U] := (Loeb_with_IT2 T U _).mpr h₁;
  exact (NotSigmaOneSound_of_UnrefutabilityConsistency T U h₂).false ss;

/-- Formalized Gödel's 1st Incompleteness Theorem -/
theorem FormalizedUnrefutabilityGoedelSentence (hG : IsGoedelSentence T U G) (hGS1 : Hierarchy Π 1 G) :
  U ⊬! Con[U] ⟶ ~Pr[U](⸢~G⸣) := by
  by_contra H;
  have h₁ := iff_contra $ equality_GoedelSentence_Consistency T U hG hGS1;
  have h₂ : U ⊢! ~Pr[U](⸢~Con[U]⸣) ⟷ ~Pr[U](⸢~G⸣) := iff_contra' $ MP (D2_iff U U (~G) (~Con[U])) (D1 h₁);
  have h₃ : U ⊬! Con[U] ⟶ ~Pr[U](⸢~G⸣) := iff_unprov' (FormalizedUnprovabilityConsistency T U) h₂;
  exact h₃ H;

end Loeb_with_IT2


namespace Loeb_without_IT2

variable (T U : Theory ℒₒᵣ) [SubTheory T U] [∀ σ, SubTheory T (U ∪ {~σ})]
variable [Diagonizable T Π 1] [Diagonizable T Σ 1]
variable [HasProvable U] [ProvableLimit U Σ 1] [Derivability1 U U] [Derivability2 U U] [Derivability3 U U]

open Derivability1 Derivability2 Derivability3

theorem Loeb_without_IT2 (σ) : (U ⊢! σ) ↔ (U ⊢! Pr[U](⸢σ⸣) ⟶ σ) := by
  apply Iff.intro;
  . intro H; simp;
  . intro H;
    have ⟨K, hK⟩ := exists_KreiselSentence T U 1 σ;
    have h₂ : U ⊢! Pr[U](⸢K ⟶ (Pr[U](⸢K⸣) ⟶ σ)⸣) := D1 (iff_mp $ subtheorem hK);
    have h₃ : U ⊢! Pr[U](⸢K⸣) ⟶ Pr[U](⸢Pr[U](⸢K⸣) ⟶ σ⸣) := mp (D2 _ _) h₂;
    have h₄ : U ⊢! Pr[U](⸢Pr[U](⸢K⸣) ⟶ σ⸣) ⟶ (Pr[U](⸢Pr[U](⸢K⸣)⸣) ⟶ Pr[U](⸢σ⸣)) := D2 Pr[U](⸢K⸣) σ;
    have h₅ : U ⊢! Pr[U](⸢K⸣) ⟶ (Pr[U](⸢Pr[U](⸢K⸣)⸣) ⟶ Pr[U](⸢σ⸣)) := imply_trans h₃ h₄;
    have h₆ : U ⊢! Pr[U](⸢K⸣) ⟶ Pr[U](⸢Pr[U](⸢K⸣)⸣) := D3 _;
    have h₇ : U ⊢! Pr[U](⸢K⸣) ⟶ Pr[U](⸢σ⸣) := imply_dilemma h₅ h₆;
    have h₈ : U ⊢! Pr[U](⸢K⸣) ⟶ σ := imply_trans h₇ H;
    have h₉ : U ⊢! K := mp (iff_mpr $ subtheorem hK) h₈;
    exact mp h₈ (D1 h₉);

theorem HenkinSentence_Provablility (hH : IsHenkinSentence T U H) : U ⊢! H :=
  (Loeb_without_IT2 T U H).mpr (iff_mpr (subtheorem hH))

end Loeb_without_IT2

end LO.FirstOrder.Arith.Incompleteness.Provability
