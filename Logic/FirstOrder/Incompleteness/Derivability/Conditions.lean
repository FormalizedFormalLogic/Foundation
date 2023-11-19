import Logic.FirstOrder.Incompleteness.Derivability.Theory

notation "Σ" => Bool.true
notation "Π" => Bool.false

namespace LO.FirstOrder.Arith

variable (T₀ T: Theory ℒₒᵣ)

lemma Consistent_of_SigmaOneSound [hs : SigmaOneSound T] : Theory.Consistent T where
  consistent := consistent_of_sound T (Hierarchy.Sigma 1) (by simp);

class HasProvablePred where
  ProvablePred : Subsentence ℒₒᵣ 1
  spec : ∀ {σ}, ℕ ⊧ ([→ ⸢σ⸣].hom ProvablePred) ↔ T ⊢! σ

private def HasProvablePred.PrSubst (T : Theory ℒₒᵣ) [HasProvablePred T] (c : Subterm.Const ℒₒᵣ) : Sentence ℒₒᵣ := [→ c].hom $ ProvablePred T

notation "Pr[" T "]" => HasProvablePred.PrSubst T

namespace HasProvablePred

open Theory FirstOrder.Theory

variable [HasProvablePred T]

class Definable [hp : HasProvablePred T] (P : (Subsentence ℒₒᵣ 1) → Prop) where
  definable : P (ProvablePred T)

abbrev Definable.Sigma (k) := Definable T (Hierarchy Σ k)

abbrev Definable.Pi (k) := Definable T (Hierarchy Π k)

class Derivability1 where
  D1 : ∀ {σ : Sentence ℒₒᵣ}, T₀ ⊢! σ → T₀ ⊢! (Pr[T] ⸢σ⸣)

class Derivability2 where
  D2 : ∀ {σ π : Sentence ℒₒᵣ}, T₀ ⊢! (Pr[T] ⸢σ ⟶ π⸣) ⟶ ((Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢π⸣))

lemma Derivability2.D2_iff {σ π : Sentence ℒₒᵣ} : T₀ ⊢! (Pr[T] ⸢σ ⟷ π⸣) ⟶ ((Pr[T] ⸢σ⸣) ⟷ (Pr[T] ⸢π⸣)) := by
  sorry;

class Derivability3 where
  D3 : ∀ {σ : Sentence ℒₒᵣ}, T₀ ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢Pr[T] ⸢σ⸣⸣)

class FormalizedCompleteness (b n) where
  FC : ∀ {σ : Sentence ℒₒᵣ}, Hierarchy b n σ → T₀ ⊢! σ ⟶ (Pr[T] ⸢σ⸣)

class FormalizedDeductionTheorem where
  FDT : ∀ {σ π : Sentence ℒₒᵣ} [HasProvablePred (T ∪ {σ})], T₀ ⊢! (Pr[T] ⸢σ ⟶ π⸣) ⟷ (Pr[T ∪ {σ}] ⸢π⸣)

lemma FormalizedDeductionTheorem.FDT_neg [HasProvablePred (T ∪ {σ})] [FormalizedDeductionTheorem T₀ T] : T₀ ⊢! ~(Pr[T] ⸢σ ⟶ π⸣) ⟷ ~(Pr[T ∪ {σ}] ⸢π⸣) :=
  iff_contra FormalizedDeductionTheorem.FDT

section PrCalculus

open Subformula FirstOrder.Theory Derivability1 Derivability2 Derivability3

variable {T₀ T : Theory ℒₒᵣ} [SubTheory T₀ T] [HasProvablePred T]
variable [Derivability1 T₀ T] [Derivability2 T₀ T] [Derivability3 T₀ T]

lemma formalized_NC (σ : Sentence ℒₒᵣ) : T₀ ⊢! ((Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢~σ⸣)) ⟶ (Pr[T] ⸢(⊥ : Sentence ℒₒᵣ)⸣) := by
  /-
  have : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := NC;
  have a : T ⊢! Pr[U](⸢σ ⟶ ~σ⸣) ⟶ (Pr[U](⸢σ⸣)) ⟶ (Pr[U](⸢~σ⸣)) := D2 σ (~σ);
  have b : T ⊢! ~(Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) ⟶ ~Pr[U](⸢σ ⟶ ~σ⸣) := imply_contra₀ (D2 σ (~σ));
  simp [imp_eq Pr[U](⸢σ⸣), imp_eq σ] at b;
  -/
  sorry;

lemma formalized_NC' (σ : Sentence ℒₒᵣ) : T₀ ⊢! ((Pr[T] ⸢σ⸣) ⋏ (Pr[T] ⸢~σ⸣)) ⟶ (Pr[T] ⸢(⊥ : Sentence ℒₒᵣ)⸣) := by
  sorry;

lemma formalized_DNI (σ : Sentence ℒₒᵣ) : T₀ ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢~~σ⸣) := by simp [neg_neg'];

lemma formalized_DNE (σ : Sentence ℒₒᵣ) : T₀ ⊢! (Pr[T] ⸢~~σ⸣) ⟶ (Pr[T] ⸢σ⸣) := by simp [neg_neg'];

lemma formalized_neg_def (σ : Sentence ℒₒᵣ) : T ⊢! (Pr[T] ⸢~σ⸣) ⟷ (Pr[T] ⸢σ ⟶ ⊥⸣) := by
  apply iff_intro;
  . sorry; -- apply imply_intro;
  . sorry; -- apply imply_intro;

end PrCalculus

section ConsistencyFormalization

variable (T : Theory ℒₒᵣ) [HasProvablePred T]

/-- Löb style consistency formalization -/
@[simp]
def LConsistenncy : Sentence ℒₒᵣ := ~(Pr[T] ⸢(⊥ : Sentence ℒₒᵣ)⸣)

notation "ConL[" T "]" => LConsistenncy T

end ConsistencyFormalization

end HasProvablePred


class Diagonizable (b n) where
  diag (δ : Subsentence ℒₒᵣ 1) : Hierarchy b n δ → ∃ (σ : Sentence ℒₒᵣ), (Hierarchy b n σ) ∧ (T ⊢! σ ⟷ ([→ ⸢σ⸣].hom δ))


section FixedPoints

open HasProvablePred

variable (T : Theory ℒₒᵣ) [HasProvablePred T] {n}

def IsGoedelSentence (G : Sentence ℒₒᵣ) := T ⊢! G ⟷ ~(Pr[T] ⸢G⸣)

lemma existsGoedelSentence
  [hdiag : Diagonizable T Π n] [hdef : Definable.Sigma T n]
  : ∃ (G : Sentence ℒₒᵣ), (IsGoedelSentence T G ∧ Hierarchy Π n G) := by
  have ⟨G, ⟨hH, hd⟩⟩ := hdiag.diag (~ProvablePred T) (Hierarchy.neg hdef.definable);
  existsi G; simpa [IsGoedelSentence, hH, Rew.neg'] using hd;

def IsHenkinSentence (H : Sentence ℒₒᵣ) := T ⊢! H ⟷ (Pr[T] ⸢H⸣)

lemma existsHenkinSentence
  [hdiag : Diagonizable T Σ n] [hdef : Definable.Sigma T n]
  : ∃ (H : Sentence ℒₒᵣ), (IsHenkinSentence T H ∧ Hierarchy Σ n H) := by
  have ⟨H, ⟨hH, hd⟩⟩ := hdiag.diag (ProvablePred T) hdef.definable;
  existsi H; simpa [IsHenkinSentence, hH] using hd;

def IsKrieselSentence (K σ : Sentence ℒₒᵣ) := T ⊢! K ⟷ ((Pr[T] ⸢K⸣) ⟶ σ)

lemma existsKreiselSentence [hdef : Definable.Sigma T n] (σ)
  : ∃ (K : Sentence ℒₒᵣ), IsKrieselSentence T K σ := by sorry

end FixedPoints



end LO.FirstOrder.Arith
