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
  D1 : ∀ {σ : Sentence ℒₒᵣ}, T ⊢! σ → T₀ ⊢! (Pr[T] ⸢σ⸣)

class Derivability2 where
  D2 : ∀ {σ π : Sentence ℒₒᵣ}, T₀ ⊢! (Pr[T] ⸢σ ⟶ π⸣) ⟶ ((Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢π⸣))

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
variable [hD1 : Derivability1 T₀ T] [hD2 : Derivability2 T₀ T] [hD3 : Derivability3 T₀ T] [hFC : FormalizedCompleteness T₀ T b n]

lemma Derivability1.D1' {σ : Sentence ℒₒᵣ} : T ⊢! σ → T ⊢! (Pr[T] ⸢σ⸣) := by intro h; exact weakening $ hD1.D1 h;

lemma Derivability2.D2' {σ π : Sentence ℒₒᵣ} : T ⊢! (Pr[T] ⸢σ ⟶ π⸣) ⟶ ((Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢π⸣)) := weakening hD2.D2

lemma Derivability2.D2_iff [SubTheory T₀ T] [hd : Derivability2 T₀ T] {σ π : Sentence ℒₒᵣ} : T₀ ⊢! (Pr[T] ⸢σ ⟷ π⸣) ⟶ ((Pr[T] ⸢σ⸣) ⟷ (Pr[T] ⸢π⸣)) := by
  sorry;
  -- have a := @Derivability2.D2 T₀ T _ _ _ σ π;
  -- have b := @Derivability2.D2 T₀ T _ _ _ π σ;
  -- sorry;

lemma Derivability3.D3' {σ : Sentence ℒₒᵣ} : T ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢Pr[T] ⸢σ⸣⸣) := weakening hD3.D3

lemma FormalizedCompleteness.FC' {σ : Sentence ℒₒᵣ} : Hierarchy b n σ → T ⊢! σ ⟶ (Pr[T] ⸢σ⸣) := by
  intro hH;
  exact weakening $ hFC.FC hH;

lemma formalized_imp_intro : (T ⊢! σ ⟶ π) → (T₀ ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢π⸣)) := by
  intro H;
  exact MP D2 $ D1 H;

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

variable (T₀ T : Theory ℒₒᵣ) [HasProvablePred T] [SubTheory T₀ T] {n}

def IsGoedelSentence [SubTheory T₀ T] (G : Sentence ℒₒᵣ) := T₀ ⊢! G ⟷ ~(Pr[T] ⸢G⸣)

lemma existsGoedelSentence
  [hdiag : Diagonizable T₀ Π n] [hdef : Definable.Sigma T n]
  : ∃ (G : Sentence ℒₒᵣ), (IsGoedelSentence T₀ T G ∧ Hierarchy Π n G) := by
  have ⟨G, ⟨hH, hd⟩⟩ := hdiag.diag (~ProvablePred T) (Hierarchy.neg hdef.definable);
  existsi G; simpa [IsGoedelSentence, hH, Rew.neg'] using hd;

def IsHenkinSentence [SubTheory T₀ T] (H : Sentence ℒₒᵣ) := T₀ ⊢! H ⟷ (Pr[T] ⸢H⸣)

lemma existsHenkinSentence
  [hdiag : Diagonizable T₀ Σ n] [hdef : Definable.Sigma T n]
  : ∃ (H : Sentence ℒₒᵣ), (IsHenkinSentence T₀ T H ∧ Hierarchy Σ n H) := by
  have ⟨H, ⟨hH, hd⟩⟩ := hdiag.diag (ProvablePred T) hdef.definable;
  existsi H; simpa [IsHenkinSentence, hH] using hd;

def IsKrieselSentence [SubTheory T₀ T] (K σ : Sentence ℒₒᵣ) := T₀ ⊢! K ⟷ ((Pr[T] ⸢K⸣) ⟶ σ)

lemma existsKreiselSentence [hdef : Definable.Sigma T n] (σ)
  : ∃ (K : Sentence ℒₒᵣ), IsKrieselSentence T₀ T K σ := by sorry

end FixedPoints


end LO.FirstOrder.Arith
