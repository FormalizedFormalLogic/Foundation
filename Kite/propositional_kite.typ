
#import "@preview/diagraph:0.3.1": *
#import "@preview/oxifmt:0.2.1": strfmt

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $upright(bold(#L))$
#let Axiom(A) = $upright(sans(#A))$

#let arrows = json("./propositional_kite.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Kite of Propositional Logics])[
  #raw-render(
    raw(
      "
  digraph ModalLogicsKite {
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
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "LO.Propositional.Logic.Cl": $Logic("Cl")$,
      "LO.Propositional.Logic.LC": $Logic("LC")$,
      "LO.Propositional.Logic.KC": $Logic("KC")$,
      "LO.Propositional.Logic.Int": $Logic("Int")$,
    ),
    width: 80pt,
  )
]
