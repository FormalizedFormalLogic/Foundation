#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Con(T) = $sans("Con")(#T)$
#let Incon(T) = $not#Con(T)$
#let PA = $Theory("PA")$
#let ISigma0 = $Theory(I)Sigma_0$
#let ISigma1 = $Theory(I)Sigma_1$

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
      "𝗜𝚺₀": $ISigma0$,
      "𝗜𝚺₀ ∪ 𝝮₁": $ISigma0 + Omega_1$,
      "𝗜𝚺₁": $ISigma1$,
      "𝗜𝚺₁ ∪ LO.FirstOrder.Theory.Con 𝗜𝚺₁": $ISigma1 + Con(ISigma1)$,
      "𝗜𝚺₁ ∪ LO.FirstOrder.Theory.Incon 𝗜𝚺₁": $ISigma1 + Incon(ISigma1)$,
      "𝗣𝗔": $PA$,
      "𝗣𝗔 ∪ LO.FirstOrder.Theory.Con 𝗣𝗔": $PA + Con(PA)$,
      "𝗣𝗔 ∪ LO.FirstOrder.Theory.Incon 𝗣𝗔": $PA + Incon(PA)$,
      "𝗣𝗔 ∪ LO.FirstOrder.Theory.Con 𝗣𝗔 ∪ LO.FirstOrder.Theory.Incon (𝗣𝗔 ∪ LO.FirstOrder.Theory.Con 𝗣𝗔)":
        $PA + Con(PA) + Incon(PA + Con(PA))$,
      "𝗧𝗔": $Theory("TA")$,
    ),
    // `𝗣𝗔⁻` is finitely axiomatizable; its single axiom does not deserve a vertex of its own.
    omit: ("{LO.FirstOrder.Arithmetic.PeanoMinus.finite.toFinset.conj}",),
  )
]
