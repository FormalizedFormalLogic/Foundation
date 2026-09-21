#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Con(T) = $sans("Con")(#T)$
#let Incon(T) = $not#Con(T)$
#let PA = $Theory("PA")$
#let ISigma(n) = $Theory(I)Sigma_#n$
#let IPi(n) = $Theory(I)Pi_#n$
#let LSigma(n) = $Theory(L)Sigma_#n$
#let LPi(n) = $Theory(L)Pi_#n$
#let BSigma(n) = $Theory(B)Sigma_#n$
#let BPi(n) = $Theory(B)Pi_#n$
#let IBroadSigma(n) = $Theory(I)Sigma^+_#n$
#let IBroadPi(n) = $Theory(I)Pi^+_#n$
#let LBroadSigma(n) = $Theory(L)Sigma^+_#n$
#let LBroadPi(n) = $Theory(L)Pi^+_#n$

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
      "𝗜𝚺⁺₁": IBroadSigma(1),
      "𝗜𝚺⁺2": IBroadSigma(2),
      "𝗜𝚷⁺₁": IBroadPi(1),
      "𝗜𝚷⁺2": IBroadPi(2),
      "𝗟𝚺⁺1": LBroadSigma(1),
      "𝗟𝚺⁺2": LBroadSigma(2),
      "𝗟𝚷⁺1": LBroadPi(1),
      "𝗕𝚺₁": BSigma(1),
      "𝗕𝚺2": BSigma(2),
      "𝗕𝚷0": BPi(0),
      "𝗕𝚷1": BPi(1),
      "𝗜𝚺⁺₁ ∪ FFL.FirstOrder.Theory.Con 𝗜𝚺⁺₁": $IBroadSigma(1) + Con(IBroadSigma(1))$,
      "𝗜𝚺⁺₁ ∪ FFL.FirstOrder.Theory.Incon 𝗜𝚺⁺₁": $IBroadSigma(1) + Incon(IBroadSigma(1))$,
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
