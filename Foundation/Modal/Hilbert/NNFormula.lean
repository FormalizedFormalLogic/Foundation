import Foundation.Modal.NNFormula
import Foundation.Modal.Entailment.K
import Foundation.Modal.Hilbert.Normal.Basic

namespace LO.Modal.Hilbert

namespace NNFormula

open
  NNFormula
  LO.Entailment
  LO.Entailment.FiniteContext
  LO.Modal.Entailment

lemma iff_neg {φ : NNFormula _} : Hilbert.K ⊢! ∼(φ.toFormula) ⭤ (∼φ).toFormula := by
  induction φ using NNFormula.rec' with
  | hNatom a => apply K!_intro <;> simp;
  | hAnd φ ψ ihφ ihψ =>
    apply K!_intro;
    . apply deduct'!;
      apply A!_replace $ ANN!_of_NK! $ show [∼(φ.toFormula ⋏ ψ.toFormula)] ⊢[Hilbert.K]! ∼(φ.toFormula ⋏ ψ.toFormula) by simp;
      . apply of'! $ K!_left ihφ;
      . apply of'! $ K!_left ihψ;
    . apply deduct'!;
      apply NK!_of_ANN!;
      apply A!_replace $ show [(∼φ).toFormula ⋎ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋎ (∼ψ).toFormula by simp;
      . apply of'! $ K!_right ihφ;
      . apply of'! $ K!_right ihψ;
  | hOr φ ψ ihφ ihψ =>
    apply K!_intro;
    . apply deduct'!;
      apply K!_replace $ KNN!_of_NA! $ show [∼(φ.toFormula ⋎ ψ.toFormula)] ⊢[Hilbert.K]! (∼(φ.toFormula ⋎ ψ.toFormula)) by simp;
      . apply of'! $ K!_left ihφ;
      . apply of'! $ K!_left ihψ;
    . apply deduct'!;
      apply NA!_of_KNN!;
      apply K!_replace $ show [(∼φ).toFormula ⋏ (∼ψ).toFormula] ⊢[Hilbert.K]! (∼φ).toFormula ⋏ (∼ψ).toFormula by simp;
      . apply of'! $ K!_right ihφ;
      . apply of'! $ K!_right ihψ;
  | hBox φ ih =>
    apply K!_intro;
    . apply C!_trans ?_ $ K!_right $ dia_duality!;
      apply contra!;
      apply axiomK'!;
      apply nec!;
      apply CN!_of_CN!_left;
      exact K!_left ih;
    . apply CN!_of_CN!_right;
      apply C!_trans (K!_left $ box_duality!) ?_
      apply contra!;
      apply diaK'!;
      exact K!_right ih;
  | hDia φ ih =>
    apply K!_intro;
    . apply C!_trans ?_ (K!_right $ box_duality!);
      apply contra!;
      apply diaK'!;
      apply CN!_of_CN!_left;
      exact K!_left ih;
    . apply CN!_of_CN!_right
      apply C!_trans (K!_left $ dia_duality!) ?_;
      apply contra!;
      apply axiomK'!;
      apply nec!;
      exact K!_right ih;
  | _ => simp;

lemma exists_iff' {φ} : ∃ ψ : NNFormula _, Hilbert.K ⊢! φ ⭤ ψ.toFormula := by
  induction φ with
  | hatom a => use (.atom a); simp;
  | hfalsum => use ⊥; simp;
  | himp φ ψ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ➝ ψ';
    apply K!_intro;
    . apply deduct'!;
      apply A!_replace $ AN!_of_C! (show [φ ➝ ψ] ⊢[Hilbert.K]! φ ➝ ψ by simp;);
      . apply of'!;
        exact C!_trans (contra! $ (K!_right $ hφ')) $ K!_left iff_neg
      . exact of'! $ K!_left hψ';
    . apply left_A!_intro;
      . apply C!_trans (C!_trans (K!_right $ iff_neg) (contra! $ K!_left hφ'));
        exact CNC!;
      . exact C!_trans (K!_right $ hψ') imply₁!;
  | hbox φ ihφ =>
    obtain ⟨ψ, ih⟩ := ihφ;
    use □ψ;
    apply box_iff! ih;

lemma exists_of_provable {φ} (h : Hilbert.K ⊢! φ) : ∃ ψ : NNFormula _, Hilbert.K ⊢! ψ.toFormula := by
  obtain ⟨ψ, h₂⟩ := exists_iff' (φ := φ);
  use ψ;
  exact K!_left h₂ ⨀ h;

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
    apply K!_intro;
    . sorry;
    . sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ⟩ := φ_CNFP;
    obtain ⟨Γ, hΓ⟩ := ihφ hφ;
    obtain ⟨Δ, hΔ⟩ := ihψ hψ;
    use Γ ++ Δ;
    simp only [List.map_append, List.map_subtype];
    apply K!_intro;
    . apply left_A!_intro;
      . apply C!_trans (K!_left hΓ) ?_;
        apply C!_trans ?_ (K!_right EDisj₂AppendADisj₂Disj₂!)
        simp;
      . apply C!_trans (K!_left hΔ) ?_;
        apply C!_trans ?_ (K!_right EDisj₂AppendADisj₂Disj₂!)
        simp;
    . apply C!_trans (K!_left EDisj₂AppendADisj₂Disj₂!) ?_;
      apply CAA!_of_C!_of_C!;
      . simpa using K!_right hΓ;
      . simpa using K!_right hΔ;

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
      . apply K!_intro;
        . apply CKK!_of_C!_of_C!
          . exact K!_left hφ₁;
          . exact K!_left hψ₁;
        . apply CKK!_of_C!_of_C!;
          . exact K!_right hφ₁;
          . exact K!_right hψ₁;
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
      . apply K!_intro;
        . apply CAA!_of_C!_of_C!
          . exact K!_left hφ₂;
          . exact K!_left hψ₂;
        . apply CAA!_of_C!_of_C!;
          . exact K!_right hφ₂;
          . exact K!_right hψ₂;
-/

lemma exists_CNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalCNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.1

lemma exists_DNF (φ : NNFormula _)
  : ∃ ψ : NNFormula _, ψ.isModalDNF ∧ Hilbert.K ⊢! φ.toFormula ⭤ ψ.toFormula
  := by sorry; -- exists_CNF_DNF.2

end NNFormula

end LO.Modal.Hilbert
