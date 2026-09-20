#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Con(T) = $sans("Con")(#T)$
#let Incon(T) = $not#Con(T)$
#let PA = $Theory("PA")$
#let ISigma(n) = $Theory(I)Sigma_#n$
#let IPi(n) = $Theory(I)Pi_#n$
#let LSigma(n) = $Theory(L)Sigma_#n$
#let LPi(n) = $Theory(L)Pi_#n$
#let ISigmaPlus(n) = $Theory(I)Sigma^+_#n$
#let IPiPlus(n) = $Theory(I)Pi^+_#n$
#let LSigmaPlus(n) = $Theory(L)Sigma^+_#n$
#let LPiPlus(n) = $Theory(L)Pi^+_#n$

// Keys are the theories as pretty-printed by `lake exe zoo_arithmetic`; a theory with no entry
// here is drawn under its pretty-printed name.
#figure(caption: [Arithmetic Theory Zoo], numbering: none)[
  #zoo(
    "./arithmetic.json",
    labels: (
      "𝗘𝗤 ℒₒᵣ": $Theory("EQ")$,
      "𝗥₀": $Theory("R"_0)$,
      "𝗤": $Theory("Q")$,
      "𝗣𝗔⁻": $PA^-$,
      "𝗜𝗢𝗽𝗲𝗻": $Theory("IOpen")$,
      "𝗜𝚺₀": ISigma(0),
      "𝗜𝚺₀ ∪ 𝝮₁": $ISigma(0) + Omega_1$,
      "𝗜𝚺₁": ISigma(1),
      "𝗜𝚺⁺₀": ISigmaPlus(0),
      "𝗜𝚺⁺₁": ISigmaPlus(1),
      "𝗜𝚺⁺2": ISigmaPlus(2),
      "𝗜𝚷⁺₁": IPiPlus(1),
      "𝗜𝚷⁺2": IPiPlus(2),
      "𝗟𝚺⁺1": LSigmaPlus(1),
      "𝗟𝚺⁺2": LSigmaPlus(2),
      "𝗟𝚷⁺1": LPiPlus(1),
      "𝗜𝚺⁺₁ ∪ FFL.FirstOrder.Theory.Con 𝗜𝚺⁺₁": $ISigmaPlus(1) + Con(ISigmaPlus(1))$,
      "𝗜𝚺⁺₁ ∪ FFL.FirstOrder.Theory.Incon 𝗜𝚺⁺₁": $ISigmaPlus(1) + Incon(ISigmaPlus(1))$,
      "𝗣𝗔": PA,
      "𝗣𝗔 ∪ FFL.FirstOrder.Theory.Con 𝗣𝗔": $PA + Con(PA)$,
      "𝗣𝗔 ∪ FFL.FirstOrder.Theory.Incon 𝗣𝗔": $PA + Incon(PA)$,
      "𝗣𝗔 ∪ FFL.FirstOrder.Theory.Con 𝗣𝗔 ∪ FFL.FirstOrder.Theory.Incon (𝗣𝗔 ∪ FFL.FirstOrder.Theory.Con 𝗣𝗔)":
        $PA + Con(PA) + Incon(PA + Con(PA))$,
      "𝗧𝗔": $Theory("TA")$,
    ),
    // `𝗣𝗔⁻` is finitely axiomatizable; its single axiom does not deserve a vertex of its own.
    omit: ("{FFL.FirstOrder.Arithmetic.PeanoMinus.finite.toFinset.conj}",),
  )
]
