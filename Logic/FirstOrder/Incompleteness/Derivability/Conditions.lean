import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Basic.Semantics

/-
以下の定義はLに依存しないので一般のLについて示したほうがよいと思う
（hereditarily finite setの上で第二不完全性定理を証明するさいなどに結果を応用できる）

ゲーデル数については


のような型クラスで扱えば良い
-/

open LO.System

namespace LO.FirstOrder.Incompleteness

variable {L : Language} [System (Sentence L)] [Gentzen (Sentence L)] [LawfulTwoSided (Sentence L)]

class GoedelNumber (L : Language) (α : Type*) where
  encode : α → Subterm.Const L

local notation:max "⸢" σ "⸣" => @GoedelNumber.encode L _ _ (σ : Sentence L)

variable (T₀ T: Theory L) (M) [Structure L M]

variable [GoedelNumber L (Sentence L)]

class HasProvablePred where
  Pr : Subsentence L 1
  spec : ∀ {σ}, M ⊧ (Pr/[⸢σ⸣]) ↔ T ⊢! σ

namespace HasProvablePred

open Theory FirstOrder.Theory

open HasProvablePred

variable [HasProvablePred T M]

class PrSoundness (P : Sentence L → Prop) where
  sounds : ∀ {σ}, (P σ) → T ⊢! (Pr T M)/[⸢σ⸣] → M ⊧ ((Pr T M)/[⸢σ⸣])

class Derivability1 where
  D1 : ∀ {σ : Sentence L}, T ⊢! σ → T₀ ⊢! (Pr T M)/[⸢σ⸣]

class Derivability2 where
  D2 : ∀ {σ π : Sentence L}, T₀ ⊢! (Pr T M)/[⸢σ ⟶ π⸣] ⟶ (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢π⸣]

class Derivability3 where
  D3 : ∀ {σ : Sentence L}, T₀ ⊢! (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢(Pr T M)/[⸢σ⸣]⸣]

class FormalizedCompleteness (P : Sentence L → Prop) where
  FC : ∀ {σ : Sentence L}, P σ → T₀ ⊢! σ ⟶ (Pr T M)/[⸢σ⸣]

class FormalizedDeductionTheorem where
  FDT : ∀ {σ π : Sentence L} [HasProvablePred (T ∪ {σ}) M], T₀ ⊢! (Pr T M)/[⸢σ ⟶ π⸣] ⟷ (Pr (T ∪ {σ}) M)/[⸢π⸣]

lemma iff_contra (h : T ⊢! σ ⟷ π) : (T ⊢! ~σ ⟷ ~π) := by prover [h];

lemma FormalizedDeductionTheorem.FDT_neg [HasProvablePred (T ∪ {σ}) M] [FormalizedDeductionTheorem T₀ T M]
  : T₀ ⊢! ~((Pr T M)/[⸢σ ⟶ π⸣]) ⟷ ~((Pr (T ∪ {σ}) M)/[⸢π⸣]) := iff_contra T₀ FormalizedDeductionTheorem.FDT

section PrCalculus

open Subformula FirstOrder.Theory Derivability1 Derivability2 Derivability3

variable {T₀ T : Theory L} [Subtheory T₀ T] {M} [Structure L M] [HasProvablePred T M]
variable [hD1 : Derivability1 T₀ T M] [hD2 : Derivability2 T₀ T M] [hD3 : Derivability3 T₀ T M]

lemma Derivability1.D1' {σ : Sentence L} : T ⊢! σ → T ⊢! ((Pr T M)/[⸢σ⸣]) := by intro h; exact weakening $ hD1.D1 h;

lemma Derivability2.D2' {σ π : Sentence L} : T ⊢! (Pr T M)/[⸢σ ⟶ π⸣] ⟶ ((Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢π⸣]) := weakening hD2.D2

lemma Derivability2.D2_iff {σ π : Sentence L}
  : T₀ ⊢! ((Pr T M)/[⸢σ ⟷ π⸣]) ⟶ ((Pr T M)/[⸢σ⸣] ⟷ (Pr T M)/[⸢π⸣]) := by
  have a : T₀ ⊢! (Pr T M)/[⸢σ ⟶ π⸣] ⟶ (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢π⸣] := hD2.D2;
  have b : T₀ ⊢! (Pr T M)/[⸢π ⟶ σ⸣] ⟶ (Pr T M)/[⸢π⸣] ⟶ (Pr T M)/[⸢σ⸣] := hD2.D2;
  sorry

lemma Derivability3.D3' {σ : Sentence L} : T ⊢! (Pr T M)/[⸢σ⸣] ⟶ ((Pr T M)/[⸢(Pr T M)/[⸢σ⸣]⸣]) := weakening hD3.D3

variable (P : Sentence L → Prop) [hFC : FormalizedCompleteness T₀ T M P]

lemma FormalizedCompleteness.FC' {σ : Sentence L} : (P σ) → T ⊢! σ ⟶ ((Pr T M)/[⸢σ⸣]) := by
  intro hH;
  exact weakening $ hFC.FC hH;

lemma formalized_imp_intro (h : T ⊢! σ ⟶ π) : (T₀ ⊢! (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢π⸣]) := by prover [hD2.D2, (hD1.D1 h)];

lemma formalized_NC (σ : Sentence L) : T₀ ⊢! ((Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢~σ⸣]) ⟶ (Pr T M)/[⸢⊥⸣] := by
  have : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := λ h₁ h₂ => by prover [h₁, h₂];
  have a : T₀ ⊢! (Pr T M)/[⸢σ ⟶ ~σ⸣] ⟶ (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢~σ⸣] := hD2.D2;
  have b : T₀ ⊢! ~((Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢~σ⸣]) ⟶ ~(Pr T M)/[⸢σ ⟶ ~σ⸣] := by prover [hD2.D2];
  sorry;
  /-
  have b : T ⊢! ~(Pr[U](⸢σ⸣) ⟶ Pr[U](⸢~σ⸣)) ⟶ ~Pr[U](⸢σ ⟶ ~σ⸣) := imp_contra₀ (D2 σ (~σ));

  simp [imp_eq Pr[U](⸢σ⸣), imp_eq σ] at b;
  -/

lemma formalized_NC' (σ : Sentence L) : T₀ ⊢! (Pr T M)/[⸢σ⸣] ⋏ (Pr T M)/[⸢~σ⸣] ⟶ (Pr T M)/[⸢⊥⸣] := by
  sorry;

lemma formalized_DNI (σ : Sentence L) : T₀ ⊢! (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢~~σ⸣] := by sorry -- simp [neg_neg'];

lemma formalized_DNE (σ : Sentence L) : T₀ ⊢! (Pr T M)/[⸢~~σ⸣] ⟶ (Pr T M)/[⸢σ⸣] := by sorry -- simp [neg_neg'];

lemma formalized_neg_def (σ : Sentence L) : T ⊢! (Pr T M)/[⸢~σ⸣] ⟷ (Pr T M)/[⸢σ ⟶ ⊥⸣] := by
  apply sorry;
  -- . sorry; -- apply imply_intro;
  -- . sorry; -- apply imply_intro;

end PrCalculus

section ConsistencyFormalization

/-- Löb style consistency formalization -/
@[simp] def LConsistency : Sentence L := ~(Pr T M)/[⸢⊥⸣]

notation "Con[" T "," M "]" => LConsistency T M

end ConsistencyFormalization

end HasProvablePred

variable (hDef : ∀ {n : ℕ}, (Subsentence L n) → Prop)

class Diagonizable where
  diag (δ : Subsentence L 1) : (hDef δ) → ∃ (σ : Sentence L), (hDef σ) ∧ (T ⊢! σ ⟷ δ/[⸢σ⸣])

section FixedPoints

open HasProvablePred

variable [Subtheory T₀ T] [HasProvablePred T M]

def IsGoedelSentence (G : Sentence L) := T₀ ⊢! G ⟷ ~(Pr T M)/[⸢G⸣]

variable [hdiag : Diagonizable T₀ hDef]

lemma existsGoedelSentence (h : hDef (~Pr T M)) -- 可証性述語の否定がΠ₁であることの抽象化
  : ∃ (G : Sentence L), (IsGoedelSentence T₀ T M G) ∧ (hDef G) := by
  have ⟨G, ⟨hH, hd⟩⟩ := hdiag.diag (~(Pr T M)) h;
  existsi G; simpa [IsGoedelSentence, hH, Rew.neg'] using hd;

def IsHenkinSentence [Subtheory T₀ T] (H : Sentence L) := T₀ ⊢! H ⟷ (Pr T M)/[⸢H⸣]

lemma existsHenkinSentence (h : hDef (Pr T M)) -- 可証性述語がΣ₁であることの抽象化
  : ∃ (H : Sentence L), (IsHenkinSentence T₀ T M H) ∧ (hDef H) := by
  have ⟨H, ⟨hH, hd⟩⟩ := hdiag.diag (Pr T M) h;
  existsi H; simpa [IsHenkinSentence, hH] using hd;

def IsKrieselSentence [Subtheory T₀ T] (K σ : Sentence L) := T₀ ⊢! K ⟷ ((Pr T M)/[⸢K⸣] ⟶ σ)

lemma existsKreiselSentence (σ : Sentence L)
  : ∃ (K : Sentence L), (IsKrieselSentence T₀ T M K σ) := by
  have ⟨K, ⟨hH, hd⟩⟩ := hdiag.diag ((Pr T M)/[⸢σ⸣]) (by sorry);
  existsi K; simp [IsKrieselSentence, hH]; sorry;

end FixedPoints

end LO.FirstOrder.Incompleteness
