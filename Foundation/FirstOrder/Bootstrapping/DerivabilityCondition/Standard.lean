module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Standard
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1

@[expose] public section
/-!
# Provability from a checked proof witness

`Proof.check` (`Syntax/Proof/Standard.lean`) decides `Proof T d p` at `V := ℕ`, and
`provable_iff_provable` (`D1.lean`) turns `Provable T ⌜σ⌝` back into `T ⊢ σ`. Composing the two
gives `provable_of_check`: a `Bool` computation the kernel can run, whose success is a proof of
the sentence itself — the conclusion `T ⊢ σ` is ordinary provability, nothing about it internal
or coded.

Checking a supplied witness is decidable and runs; exhibiting one at the scale of arithmetic is
blocked by the representation, not by the checker. `Proof T d φ` is `DerivationOf T d {φ}`, and a
coded set `{φ}` at `V := ℕ` is `2 ^ φ`, so any sequent mentioning `φ` is a numeral of `φ` bits:
the smallest axiom code of `𝗣𝗔⁻` is `⌜Theory.Eq.refl ℒₒᵣ⌝ = 45974842864502507`, whose singleton
is a numeral of some `4.6 · 10 ^ 16` bits — about 5.7 petabytes. No derivation mentioning an
axiom of arithmetic is representable as a machine numeral, at any speed, which is why the
examples here are at `⊤`. The Ackermann membership encoding is load-bearing exactly where it is
expensive — `∈` being `Δ₀` is what keeps the provability predicate `Σ₁` — so this is a boundary
of the representation rather than a defect of the encoding. Whether a length-indexed sequence
encoding of *sequents* could sit alongside it, cheap enough to represent and still tame enough
for the arithmetization, is left open.
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open Encodable LO.FirstOrder.Theory

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
variable {T : Theory L} [T.Δ₁] [T.DecidableΔ₁]

/-- A checked witness yields the theorem. `Proof.check L T d (encode σ)` is a closed `Bool`, so
`decide` discharges the hypothesis whenever `d` is small enough to write down. -/
theorem provable_of_check {d : ℕ} {σ : Sentence L} (h : Proof.check L T d (encode σ) = true) :
    T ⊢ σ :=
  provable_iff_provable.mp
    ⟨d, by rw [Sentence.quote_eq_encode_standard]; exact Proof.check_iff.mp h⟩

/-! ### Examples

`⌜⊤⌝ = 7`, so the sequent `{⌜⊤⌝}` is `2 ^ 7 = 128` and both witnesses below are small numerals. -/

-- `⊤` from no theory at all, by `verumIntro`
example : (∅ : Theory ℒₒᵣ) ⊢ (⊤ : Sentence ℒₒᵣ) :=
  provable_of_check (d := Nat.pair 128 (Nat.pair 1 0) + 1) (by decide)

-- `⊤` from the theory `{⊤}`, by `axm` — `Theory.DecidableΔ₁` runs on the way
example : ({(⊤ : Sentence ℒₒᵣ)} : Theory ℒₒᵣ) ⊢ (⊤ : Sentence ℒₒᵣ) :=
  provable_of_check (d := Nat.pair 128 (Nat.pair 9 7) + 1) (by decide)

-- the `axm` witness is rejected against the empty theory, so the hypothesis of
-- `provable_of_check` does not hold of every numeral
example : Proof.check ℒₒᵣ (∅ : Theory ℒₒᵣ) (Nat.pair 128 (Nat.pair 9 7) + 1)
    (encode (⊤ : Sentence ℒₒᵣ)) = false := by decide

end LO.FirstOrder.Arithmetic.Bootstrapping

end
