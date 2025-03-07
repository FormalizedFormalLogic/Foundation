#import "@preview/diagraph:0.3.1": *
#import "@preview/oxifmt:0.2.1": strfmt

#set page(width: auto, height: auto, margin: 24pt)

#let Theory(T) = $upright(bold(#T))$

#let arrows = json("./Arith.json").map(((from, to, type)) => {
  if type == "strict" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "weaker" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

Kite of First-Order Arithmetics

#raw-render(
  raw(
    "
  digraph ArithmeticsKite {
    rankdir = LR;

    node [
      shape=none
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = none
    ];
  "
      + arrows.join("\n")
      + "}",
  ),
  labels: (
    "CobhamR0": $Theory(R_0)$,
    "ISigma0": $Theory(I Sigma_0)$,
    "ISigma1": $Theory(I Sigma_1)$,
    "PAMinus": $Theory("PA"^-)$,
    "PA": $Theory("PA")$,
    "TA": $Theory("TA")$,
  ),
  width: 360pt,
)

Build on #datetime.today().year()/#datetime.today().month()/#datetime.today().day()
