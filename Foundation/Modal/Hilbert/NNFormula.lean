import Foundation.Modal.NNFormula
import Foundation.Modal.Hilbert.K
import Foundation.Modal.Entailment.K

namespace LO.Modal.Hilbert

namespace NNFormula

open
  NNFormula
  Entailment
  Entailment.FiniteContext

lemma iff_neg {φ : NNFormula _} : Hilbert.K ⊢! ∼(φ.toFormula) ⭤ (∼φ).toFormula := by
  induction φ using NNFormula.rec' with
  | hNatom a => apply and₃'! <;> simp;
  | hAnd φ ψ ihφ ihψ =>
    apply and₃'!;
    . apply deduct'!;
      apply or_replace'! $ demorgan₄'! $ show [∼(φ.toFormula ⋏ ψ.toFormula)] ⊢[Hilbert.K]! ∼(φ.toFormula ⋏ ψ.toFormula) by simp;
      . apply of'! $ and₁'! ihφ;
      . apply of'! $ and₁'! ihψ;
    . apply deduct'!;
      apply demorgan₁'!;
      apply or_replace'! $ show [(∼φ).toFormula ⋎ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋎ (∼ψ).toFormula by simp;
      . apply of'! $ and₂'! ihφ;
      . apply of'! $ and₂'! ihψ;
  | hOr φ ψ ihφ ihψ =>
    apply and₃'!;
    . apply deduct'!;
      apply and_replace'! $ demorgan₃'! $ show [∼(φ.toFormula ⋎ ψ.toFormula)] ⊢[Hilbert.K]! (∼(φ.toFormula ⋎ ψ.toFormula)) by simp;
      . apply of'! $ and₁'! ihφ;
      . apply of'! $ and₁'! ihψ;
    . apply deduct'!;
      apply demorgan₂'!;
      apply and_replace'! $ show [(∼φ).toFormula ⋏ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋏ (∼ψ).toFormula by simp;
      . apply of'! $ and₂'! ihφ;
      . apply of'! $ and₂'! ihψ;
  | hBox φ ih =>
    apply and₃'!;
    . apply imp_trans''! ?_ $ and₂'! $ dia_duality!;
      apply contra₀'!;
      apply axiomK'!;
      apply nec!;
      apply contra₂'!;
      exact and₁'! ih;
    . apply contra₁'!;
      apply imp_trans''! (and₁'! $ box_duality!) ?_
      apply contra₀'!;
      apply diaK'!;
      exact and₂'! ih;
  | hDia φ ih =>
    apply and₃'!;
    . apply imp_trans''! ?_ (and₂'! $ box_duality!);
      apply contra₀'!;
      apply diaK'!;
      apply contra₂'!;
      exact and₁'! ih;
    . apply contra₁'!
      apply imp_trans''! (and₁'! $ dia_duality!) ?_;
      apply contra₀'!;
      apply axiomK'!;
      apply nec!;
      exact and₂'! ih;
  | _ => simp;

lemma exists_iff {φ} : ∃ ψ : NNFormula _, Hilbert.K ⊢! φ ⭤ ψ.toFormula := by
  induction φ using Formula.rec' with
  | hatom a => use (.atom a); simp;
  | hfalsum => use ⊥; simp;
  | himp φ ψ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ➝ ψ';
    apply and₃'!;
    . apply deduct'!;
      apply or_replace'! $ not_or_of_imply'! (show [φ ➝ ψ] ⊢[Hilbert.K]! φ ➝ ψ by simp;);
      . apply of'!;
        exact imp_trans''! (contra₀'! $ (and₂'! $ hφ')) $ and₁'! iff_neg
      . exact of'! $ and₁'! hψ';
    . apply or₃''!;
      . apply imp_trans''! (imp_trans''! (and₂'! $ iff_neg) (contra₀'! $ and₁'! hφ'));
        exact efq_imply_not₁!;
      . exact imp_trans''! (and₂'! $ hψ') imply₁!;
  | hbox φ ihφ =>
    obtain ⟨ψ, ih⟩ := ihφ;
    use □ψ;
    apply box_iff! ih;

lemma exists_of_provable {φ} (h : Hilbert.K ⊢! φ) : ∃ ψ : NNFormula _, Hilbert.K ⊢! ψ.toFormula := by
  obtain ⟨ψ, h₂⟩ := exists_iff (φ := φ);
  use ψ;
  exact and₁'! h₂ ⨀ h;

/-
lemma exists_CNFPart_list {φ : NNFormula _} (φ_CNFP : φ.isModalCNFPart)
  : ∃ Γ : List { φ : NNFormula ℕ // φ.isPrebox ∨ φ.isPredia ∨ φ.degree = 0 }, Hilbert.K ⊢! φ.toFormula ⭤ ⋁(Γ.map (·.1)) := by
  induction φ using NNFormula.rec' with
  | hAtom a => use [⟨(NNFormula.atom a), by tauto⟩]; simp;
  | hNatom a => use [⟨(NNFormula.natom a), by tauto⟩]; simp;
  | hVerum => use [⟨⊤, by tauto⟩]; simp;
  | hFalsum => use [⟨⊥, by tauto⟩]; simp;
  | hBox φ ih => use [⟨(□φ), by tauto⟩]; simp;
  | hDia φ ih => use [⟨(◇φ), by tauto⟩]; simp;
  | hAnd φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ : φ.degree = 0 ∧ ψ.degree = 0 := by
      simpa [NNFormula.isPrebox, NNFormula.isPredia, NNFormula.isModalCNFPart, NNFormula.degree]
      using φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ $ NNFormula.isModalCNFPart.of_degree_zero hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ $ NNFormula.isModalCNFPart.of_degree_zero hψ;
    use Γ ++ Δ;
    apply and₃'!;
    . sorry;
    . sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ hψ;
    use Γ ++ Δ;
    simp only [List.map_append, List.map_subtype];
    apply and₃'!;
    . apply or₃''!;
      . apply imp_trans''! (and₁'! hΓ) ?_;
        apply imp_trans''! ?_ (and₂'! iff_concact_disj!)
        simp;
      . apply imp_trans''! (and₁'! hΔ) ?_;
        apply imp_trans''! ?_ (and₂'! iff_concact_disj!)
        simp;
    . apply imp_trans''! (and₁'! iff_concact_disj!) ?_;
      apply or_replace!;
      . simpa using and₂'! hΓ;
      . simpa using and₂'! hΔ;

lemma exists_CNFPart_list {φ : NNFormula _} (φ_CNFP : φ.isModalCNFPart)
  : ∃ Γ : List { φ : NNFormula ℕ // φ.isPrebox ∨ φ.isPredia ∨ φ.degree = 0 }, Hilbert.K ⊢! φ.toFormula ⭤ ⋁(Γ.map (·.1)) := by
  induction φ using NNFormula.rec' with
  | hAtom a => use [⟨(NNFormula.atom a), by tauto⟩]; simp;
  | hNatom a => use [⟨(NNFormula.natom a), by tauto⟩]; simp;
  | hVerum => use [⟨⊤, by tauto⟩]; simp;
  | hFalsum => use [⟨⊥, by tauto⟩]; simp;
  | hBox φ ih => use [⟨(□φ), by tauto⟩]; simp;
  | hDia φ ih => use [⟨(◇φ), by tauto⟩]; simp;
  | hAnd φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ : φ.degree = 0 ∧ ψ.degree = 0 := by
      simpa [NNFormula.isPrebox, NNFormula.isPredia, NNFormula.isModalCNFPart, NNFormula.degree]
      using φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ $ NNFormula.isModalCNFPart.of_degree_zero hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ $ NNFormula.isModalCNFPart.of_degree_zero hψ;
    use List.zipWith
      (λ ⟨ξ₁, hξ₁⟩ ⟨ξ₂, hξ₂⟩ => ⟨
        ξ₁ ⋏ ξ₂,
        by sorry;
      ⟩)
      Γ Δ;
    sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ hψ;
    sorry;
-/

/-
lemma exists_CNF_list {φ : NNFormula _} (φ_CNF : φ.isModalCNF)
  : ∃ Γ : List { φ : NNFormula ℕ // φ.isModalCNFPart }, Hilbert.K ⊢! (φ.toFormula ⭤ ⋀(Γ.map (·.1))) := by
  induction φ using NNFormula.rec' with
  | hAtom a => use [⟨(NNFormula.atom a), by tauto⟩]; simp;
  | hNatom a => use [⟨(NNFormula.natom a), by tauto⟩]; simp;
  | hVerum => use []; simp;
  | hFalsum => use [⟨⊥, by tauto⟩]; simp;
  | hBox φ ih => use [⟨(□φ), by simpa⟩]; simp;
  | hDia φ ih => use [⟨(◇φ), by simpa⟩]; simp;
  | hAnd φ ψ ihφ ihψ =>
    obtain ⟨Γ, hΓ⟩ := ihφ φ_CNF.1;
    obtain ⟨Δ, hΔ⟩ := ihψ φ_CNF.2;
    use Γ ++ Δ;
    sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨Γ, hΓ⟩ : ∃ Γ : NNFormula.ModalCNFPartList ℕ, (φ ⋎ ψ) = ⋁(Γ.map (·.1)) := φ_CNF;
    rw [hΓ];

    sorry;


theorem exists_CNF_DNF {φ : NNFormula _}
  : (∃ ψ : NNFormula _, ψ.isModalCNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula) ∧
    (∃ ξ : NNFormula _, ξ.isModalDNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ξ.toFormula)
  := by
  induction φ using NNFormula.rec' with
  | hAtom a => constructor <;> { use (.atom a); simp; };
  | hNatom a => constructor <;> { use (.natom a); simp; }
  | hVerum => constructor <;> { use ⊤; simp; }
  | hFalsum => constructor <;> { use ⊥; simp; }
  | hBox φ ih => constructor <;> { use (□φ); simp; }
  | hDia φ ih => constructor <;> { use (◇φ); simp; }
  | hAnd φ ψ ihφ ihψ =>
    obtain ⟨⟨φ₁, φ₁_CNF, hφ₁⟩, ⟨φ₂, φ₂_DNF, hφ₂⟩⟩ := ihφ;
    obtain ⟨⟨ψ₁, ψ₁_CNF, hψ₁⟩, ⟨ψ₂, ψ₂_DNF, hψ₂⟩⟩ := ihψ;
    constructor;
    . use (φ₁ ⋏ ψ₁);
      constructor;
      . tauto;
      . apply and₃'!;
        . apply and_replace!
          . exact and₁'! hφ₁;
          . exact and₁'! hψ₁;
        . apply and_replace!;
          . exact and₂'! hφ₁;
          . exact and₂'! hψ₁;
    . obtain ⟨Γ, hΓ⟩ := exists_CNF_list φ₁_CNF;
      obtain ⟨Δ, hΔ⟩ := exists_CNF_list ψ₁_CNF;
      sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨⟨φ₁, φ₁_CNF, hφ₁⟩, ⟨φ₂, φ₂_DNF, hφ₂⟩⟩ := ihφ;
    obtain ⟨⟨ψ₁, ψ₁_CNF, hψ₁⟩, ⟨ψ₂, ψ₂_DNF, hψ₂⟩⟩ := ihψ;
    constructor;
    . sorry;
    . use (φ₂ ⋎ ψ₂);
      constructor;
      . tauto;
      . apply and₃'!;
        . apply or_replace!
          . exact and₁'! hφ₂;
          . exact and₁'! hψ₂;
        . apply or_replace!;
          . exact and₂'! hφ₂;
          . exact and₂'! hψ₂;
-/

lemma exists_CNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalCNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.1

lemma exists_DNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalDNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.2

end NNFormula

end LO.Modal.Hilbert
