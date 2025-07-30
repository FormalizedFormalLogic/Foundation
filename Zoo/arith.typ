#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let omitLabels = ("𝐄𝐐", "𝐑₀'")

#let arrows = json("./arith.json").map(((from, to, type)) => {
  if omitLabels.contains(from) == false and omitLabels.contains(from) == false {
    if type == "ssub" {
      return strfmt("\"{}\" -> \"{}\"", from, to)
    } else if type == "sub" {
      return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
    } else if type == "sorry" {
      return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
    }
  }
})

#let TheoryPA = $Theory("PA")$
#let TheoryISigma0 = $Theory(I Sigma_0)$
#let TheoryISigma1 = $Theory(I Sigma_1)$

#let Con(T) = $op("Con")(#T)$

#figure(caption: [Arithmetic Theory Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalTheorysZoo {
    rankdir = BT;

    node [
      shape=none
      margin=0.1
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
      "𝐈Open": $Theory("IOpen")$,
      "𝐈𝚺₀ + 𝛀₁": $Theory(I Sigma_0 + Omega_1)$,
      "𝐈𝚺₀": $TheoryISigma0$,
      "𝐈𝚺₁": $TheoryISigma1$,
      "𝐏𝐀": $TheoryPA$,
      "𝐏𝐀⁻": $Theory("PA"^-)$,
      "𝐑₀'": $Theory(R'_0)$,
      "𝐑₀": $Theory(R_0)$,
      "𝐓𝐀": $Theory("TA")$,
      "𝐄𝐐": $Theory("EQ")$,
      "𝐏𝐀 + LO.FirstOrder.Theory.Con 𝐏𝐀 + LO.FirstOrder.Theory.Incon (𝐏𝐀 + LO.FirstOrder.Theory.Con 𝐏𝐀)": $TheoryPA + Con(TheoryPA) + not Con(TheoryPA + Con(TheoryPA))$,
      "𝐏𝐀 + LO.FirstOrder.Theory.Incon 𝐏𝐀": $TheoryPA + not Con(TheoryPA)$,
      "𝐏𝐀 + LO.FirstOrder.Theory.Con 𝐏𝐀": $TheoryPA + Con(TheoryPA)$,
      "𝐈𝚺₁ + LO.FirstOrder.Theory.Con 𝐈𝚺₁": $TheoryISigma1 + Con(TheoryISigma1)$,
      "𝐈𝚺₁ + LO.FirstOrder.Theory.Incon 𝐈𝚺₁": $TheoryISigma1 + not Con(TheoryISigma1)$,
    ),
    width: 240pt,
  )
]
