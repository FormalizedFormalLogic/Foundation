#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let omitLabels = ("𝗔𝗖")

#let arrows = json("./setTheory.json").map(((from, to, type)) => {
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

#let TheoryZ = $Theory("Z")$
#let TheoryZC = $Theory("ZC")$
#let TheoryZF = $Theory("ZF")$
#let TheoryZFC = $Theory("ZFC")$

#let neg(x) = $not#x$
#let Con(T) = $sans("Con")(#T)$
#let Incon(T) = $neg(Con(#T))$

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
      "𝗭": $TheoryZ$,
      "𝗭𝗖": $TheoryZC$,
      "𝗭𝗙": $TheoryZF$,
      "𝗭𝗙𝗖": $TheoryZFC$,
    ),
    width: 240pt,
  )
]
