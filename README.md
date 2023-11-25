# lean4-logic
Formalizing Logic in Lean4

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Logic**
  - **Propositional**: Propositional logic
    - **Basic**
  - **ManySorted**: Many-sorted logic
    - **Basic**
  - **FirstOrder**: First-order logic
    - **Basic**
    - **Computability**: encodeing, computability
    - **Completeness**: Completeness theorem
    - **Arith**: Arithmetic
    - **Incompleteness**: Incompleteness theorem
  - **SecondOrder**: Monadic second-order logic

## Definition
### First-Order logic

|                                     |                                     | Definition                      | Notation  |
| :----:                              | ----                                | ----                            | :----:    |
| $\vdash_\mathrm{T} \Gamma$          | Derivation in Tait-Calculus         |  `LO.FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `LO.FirstOrder.DerivationC`    | `⊢ᶜ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.Subformula.Val` | `M ⊧ σ`   |
| $T \vdash \sigma$                   | Proof, Provability                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`, `T ⊢! σ` |

## Theorem
### First-Order logic

|                                | Proof                                    | 
| ----                           | ----                                     |
| Soundness theorem              | `@soundness : ∀ {L : Language} [inst : (k : ℕ) → DecidableEq (Language.func L k)] [inst_1 : (k : ℕ) → DecidableEq (Language.rel L k)] {T : Set (Sentence L)} {σ : Sentence L}, T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `@completeness : {L : Language} → [inst : (k : ℕ) → DecidableEq (Language.func L k)] → [inst_1 : (k : ℕ) → DecidableEq (Language.rel L k)] → {T : Theory L} → {σ : Sentence L} → T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | `@DerivationCR.hauptsatz : {L : Language} → [inst : (k : ℕ) → DecidableEq (Language.func L k)] → [inst_1 : (k : ℕ) → DecidableEq (Language.rel L k)] → {Δ : Sequent L} → ⊢ᶜ Δ → ⊢ᵀ Δ` |
| First incompleteness theorem   | `@Arith.first_incompleteness : ∀ (T : Theory Language.oRing) [inst : DecidablePred T] [inst_1 : EqTheory T] [inst_2 : Arith.PAminus T] [inst_3 : Arith.SigmaOneSound T] [inst : Theory.Computable T], ¬System.Complete T` |

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- 田中 一之, ゲーデルと20世紀の論理学