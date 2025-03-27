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
  | hNatom a => apply kφψ!_of_φ!_of_ψ! <;> simp;
  | hAnd φ ψ ihφ ihψ =>
    apply kφψ!_of_φ!_of_ψ!;
    . apply deduct'!;
      apply or_replace'! $ demorgan₄'! $ show [∼(φ.toFormula ⋏ ψ.toFormula)] ⊢[Hilbert.K]! ∼(φ.toFormula ⋏ ψ.toFormula) by simp;
      . apply of'! $ φ!_of_kφψ! ihφ;
      . apply of'! $ φ!_of_kφψ! ihψ;
    . apply deduct'!;
      apply demorgan₁'!;
      apply or_replace'! $ show [(∼φ).toFormula ⋎ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋎ (∼ψ).toFormula by simp;
      . apply of'! $ ψ!_of_kφψ! ihφ;
      . apply of'! $ ψ!_of_kφψ! ihψ;
  | hOr φ ψ ihφ ihψ =>
    apply kφψ!_of_φ!_of_ψ!;
    . apply deduct'!;
      apply and_replace'! $ demorgan₃'! $ show [∼(φ.toFormula ⋎ ψ.toFormula)] ⊢[Hilbert.K]! (∼(φ.toFormula ⋎ ψ.toFormula)) by simp;
      . apply of'! $ φ!_of_kφψ! ihφ;
      . apply of'! $ φ!_of_kφψ! ihψ;
    . apply deduct'!;
      apply demorgan₂'!;
      apply and_replace'! $ show [(∼φ).toFormula ⋏ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋏ (∼ψ).toFormula by simp;
      . apply of'! $ ψ!_of_kφψ! ihφ;
      . apply of'! $ ψ!_of_kφψ! ihψ;
  | hBox φ ih =>
    apply kφψ!_of_φ!_of_ψ!;
    . apply c!_trans ?_ $ ψ!_of_kφψ! $ dia_duality!;
      apply contra₀'!;
      apply axiomK'!;
      apply nec!;
      apply contra₂'!;
      exact φ!_of_kφψ! ih;
    . apply contra₁'!;
      apply c!_trans (φ!_of_kφψ! $ box_duality!) ?_
      apply contra₀'!;
      apply diaK'!;
      exact ψ!_of_kφψ! ih;
  | hDia φ ih =>
    apply kφψ!_of_φ!_of_ψ!;
    . apply c!_trans ?_ (ψ!_of_kφψ! $ box_duality!);
      apply contra₀'!;
      apply diaK'!;
      apply contra₂'!;
      exact φ!_of_kφψ! ih;
    . apply contra₁'!
      apply c!_trans (φ!_of_kφψ! $ dia_duality!) ?_;
      apply contra₀'!;
      apply axiomK'!;
      apply nec!;
      exact ψ!_of_kφψ! ih;
  | _ => simp;

lemma exists_iff {φ} : ∃ ψ : NNFormula _, Hilbert.K ⊢! φ ⭤ ψ.toFormula := by
  induction φ using Formula.rec' with
  | hatom a => use (.atom a); simp;
  | hfalsum => use ⊥; simp;
  | himp φ ψ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ➝ ψ';
    apply kφψ!_of_φ!_of_ψ!;
    . apply deduct'!;
      apply or_replace'! $ not_or_of_imply'! (show [φ ➝ ψ] ⊢[Hilbert.K]! φ ➝ ψ by simp;);
      . apply of'!;
        exact c!_trans (contra₀'! $ (ψ!_of_kφψ! $ hφ')) $ φ!_of_kφψ! iff_neg
      . exact of'! $ φ!_of_kφψ! hψ';
    . apply caφψχ!_of_cφχ!_of_cψχ!;
      . apply c!_trans (c!_trans (ψ!_of_kφψ! $ iff_neg) (contra₀'! $ φ!_of_kφψ! hφ'));
        exact efq_imply_not₁!;
      . exact c!_trans (ψ!_of_kφψ! $ hψ') imply₁!;
  | hbox φ ihφ =>
    obtain ⟨ψ, ih⟩ := ihφ;
    use □ψ;
    apply box_iff! ih;

lemma exists_of_provable {φ} (h : Hilbert.K ⊢! φ) : ∃ ψ : NNFormula _, Hilbert.K ⊢! ψ.toFormula := by
  obtain ⟨ψ, h₂⟩ := exists_iff (φ := φ);
  use ψ;
  exact φ!_of_kφψ! h₂ ⨀ h;

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
    apply kφψ!_of_φ!_of_ψ!;
    . sorry;
    . sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ hψ;
    use Γ ++ Δ;
    simp only [List.map_append, List.map_subtype];
    apply kφψ!_of_φ!_of_ψ!;
    . apply caφψχ!_of_cφχ!_of_cψχ!;
      . apply c!_trans (φ!_of_kφψ! hΓ) ?_;
        apply c!_trans ?_ (ψ!_of_kφψ! iff_concact_disj!)
        simp;
      . apply c!_trans (φ!_of_kφψ! hΔ) ?_;
        apply c!_trans ?_ (ψ!_of_kφψ! iff_concact_disj!)
        simp;
    . apply c!_trans (φ!_of_kφψ! iff_concact_disj!) ?_;
      apply or_replace!;
      . simpa using ψ!_of_kφψ! hΓ;
      . simpa using ψ!_of_kφψ! hΔ;

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
      . apply kφψ!_of_φ!_of_ψ!;
        . apply and_replace!
          . exact φ!_of_kφψ! hφ₁;
          . exact φ!_of_kφψ! hψ₁;
        . apply and_replace!;
          . exact ψ!_of_kφψ! hφ₁;
          . exact ψ!_of_kφψ! hψ₁;
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
      . apply kφψ!_of_φ!_of_ψ!;
        . apply or_replace!
          . exact φ!_of_kφψ! hφ₂;
          . exact φ!_of_kφψ! hψ₂;
        . apply or_replace!;
          . exact ψ!_of_kφψ! hφ₂;
          . exact ψ!_of_kφψ! hψ₂;
-/

lemma exists_CNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalCNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.1

lemma exists_DNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalDNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.2

end NNFormula

end LO.Modal.Hilbert
