#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

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
#let TheoryISigma0 = $Theory(I)Sigma_0$
#let TheoryISigma1 = $Theory(I)Sigma_1$

#let Con(T) = $sans("Con")(#T)$

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
      "𝗘𝗤": $Theory("EQ")$,
      "𝗜𝗢𝗽𝗲𝗻": $Theory("IOpen")$,
      "𝗜𝚺₀ + 𝝮₁": $TheoryISigma0 + Omega_1$,
      "𝗜𝚺₀": $TheoryISigma0$,
      "𝗜𝚺₁ + LO.FirstOrder.Theory.Con 𝗜𝚺₁": $TheoryISigma1 + Con(TheoryISigma1)$,
      "𝗜𝚺₁ + LO.FirstOrder.Theory.Incon 𝗜𝚺₁": $TheoryISigma1 + not Con(TheoryISigma1)$,
      "𝗜𝚺₁": $TheoryISigma1$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔 + LO.FirstOrder.Theory.Incon (𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔)": $TheoryPA + Con(TheoryPA) + not Con(TheoryPA + Con(TheoryPA))$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Con 𝗣𝗔": $TheoryPA + Con(TheoryPA)$,
      "𝗣𝗔 + LO.FirstOrder.Theory.Incon 𝗣𝗔": $TheoryPA + not Con(TheoryPA)$,
      "𝗣𝗔": $TheoryPA$,
      "𝗣𝗔⁻": $TheoryPA^-$,
      "𝗤": $Theory("Q")$,
      "𝗥₀": $Theory("R"_0)$,
      "𝗧𝗔": $Theory("TA")$,
    ),
    width: 240pt,
  )
]
