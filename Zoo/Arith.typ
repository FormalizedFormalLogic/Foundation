#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let omitLabels = ()

#let arrows = json("./Arith.json").map(((from, to, type)) => {
  if omitLabels.contains(from) == false and omitLabels.contains(from) == false {
    if type == "ssub" {
      return strfmt("\"{}\" -> \"{}\"", to, from)
    } else if type == "sub" {
      return strfmt("\"{}\" -> \"{}\" [style=dashed] ", to, from)
    } else if type == "sorry" {
      return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", to, from)
    }
  }
})

#let TheoryPA = $Theory("PA")$
#let TheoryISigma0 = $Theory(I)Sigma_0$
#let TheoryISigma1 = $Theory(I)Sigma_1$
#let neg(x) = $not#x$
#let Con(T) = $sans("Con")(#T)$
#let Incon(T) = $neg(Con(#T))$

#figure(caption: [Arithmetic Theory Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalTheorysZoo {
    rankdir = RL;

    node [
      shape=none
      margin=0.05
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.5
    ];

  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝗘𝗤": $Theory("EQ")$,
      "𝗜𝗢𝗽𝗲𝗻": $Theory("IOpen")$,
      "𝗜𝚺₀ + 𝝮₁": $TheoryISigma0 + Omega_1$,
      "𝗜𝚺₀": $TheoryISigma0$,
      "𝗜𝚺₁ + LO.FirstOrder.Theory.Con 𝗜𝚺₁": $TheoryISigma1 + Con(TheoryISigma1)$,
      "𝗜𝚺₁ + LO.FirstOrder.Theory.Incon 𝗜𝚺₁": $TheoryISigma1 + Incon(TheoryISigma1)$,
      "𝗜𝚺₁": $TheoryISigma1$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔 + LO.FirstOrder.Theory.Incon (𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔)": $TheoryPA + Con(TheoryPA) + Incon(TheoryPA + Con(TheoryPA))$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔": $TheoryPA + Con(TheoryPA)$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Incon 𝗣𝗔": $TheoryPA + Incon(TheoryPA)$,
      "𝗣𝗔": $TheoryPA$,
      "𝗣𝗔⁻": $TheoryPA^-$,
      "𝗤": $Theory("Q")$,
      "𝗥₀": $Theory("R"_0)$,
      "𝗧𝗔": $Theory("TA")$,
    ),
    width: 640pt,
  )
]
