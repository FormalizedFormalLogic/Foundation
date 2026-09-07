#import "@preview/diagraph:0.3.5": *
#import "@preview/oxifmt:1.0.0": strfmt

#let Theory(T) = $upright(sans(#T))$

// Renders the JSON emitted by a `zoo_*` executable as a Graphviz digraph.
//
// An edge `a -> b` of the JSON says that `a` is weaker than `b`, so the arrows are drawn from `b`
// to `a`: solid for `⪱`, dashed for `⪯`, and as an undirected double line for `≊`.
//
// Theories listed in `omit` are dropped along with every edge touching them.
//
// `dir` is the Graphviz `rankdir`: "TB" stacks the theories vertically, strongest at the top,
// "RL" lays them out horizontally, strongest on the right.
#let zoo(path, labels: (:), omit: (), dir: "TB", width: 640pt) = {
  let edges = json(path).filter(((from, to, ..)) => {
    not omit.contains(from) and not omit.contains(to)
  }).map(((from, to, type)) => {
    if type == "ssub" {
      strfmt("\"{}\" -> \"{}\"", to, from)
    } else if type == "sub" {
      strfmt("\"{}\" -> \"{}\" [style = dashed]", to, from)
    } else if type == "eq" {
      strfmt("\"{}\" -> \"{}\" [dir = none, color = \"black:black\"]", to, from)
    }
  })

  raw-render(
    raw(
      "digraph Zoo {
        rankdir = " + dir + ";

        node [
          shape = none
          margin = 0.05
          width = 0
          height = 0
        ]

        edge [
          style = solid
          arrowhead = vee
          arrowsize = 0.5
        ];

      " + edges.join("\n") + "}",
    ),
    labels: labels,
    width: width,
  )
}
