#import "@preview/diagraph:0.3.5": *
#import "@preview/oxifmt:1.0.0": strfmt

#let Theory(T) = $upright(sans(#T))$

// Partitions the vertices occurring in `pairs` into the classes they generate.
#let classes(pairs) = {
  let classes = ()
  for pair in pairs {
    let (joined, disjoint) = (pair, ())
    for c in classes {
      if pair.any(v => c.contains(v)) { joined += c } else { disjoint.push(c) }
    }
    disjoint.push(joined.dedup())
    classes = disjoint
  }
  classes
}

// Renders the JSON emitted by a `zoo_*` executable as a Graphviz digraph.
//
// An edge `a -> b` of the JSON says that `a` is weaker than `b`, so the arrows are drawn from `b`
// to `a`: solid for `⪱` and dashed for `⪯`.
//
// Equivalent theories are of the same strength, so each `≊`-class is put on a rank of its own and
// drawn as a chain of undirected double lines. The chain replaces the `≊` edges of the reduction,
// which form a star around whichever theory the equivalences were stated against and would have
// to reach across the rank; the class is what the diagram states either way.
//
// Theories listed in `omit` are dropped along with every edge touching them.
#let zoo(path, labels: (:), omit: (), width: 640pt) = {
  let entries = json(path).filter(((from, to, ..)) => {
    not omit.contains(from) and not omit.contains(to)
  })

  let edges = entries.filter(((type, ..)) => type != "eq").map(((from, to, type)) => {
    if type == "ssub" {
      strfmt("\"{}\" -> \"{}\"", to, from)
    } else {
      strfmt("\"{}\" -> \"{}\" [style = dashed]", to, from)
    }
  })

  let ranks = classes(
    entries.filter(((type, ..)) => type == "eq").map(((from, to, ..)) => (from, to)),
  ).map(c => {
    let chain = range(c.len() - 1).map(i => {
      strfmt("\"{}\" -> \"{}\" [dir = none, color = \"black:black\"];", c.at(i), c.at(i + 1))
    })
    "{ rank = same; " + (c.map(v => strfmt("\"{}\";", v)) + chain).join(" ") + " }"
  })

  raw-render(
    raw(
      "digraph Zoo {
        rankdir = TB;

        // Tighter than the Graphviz defaults, so that the diagram stays legible once the README
        // scales it down to fit.
        ranksep = 0.28;
        nodesep = 0.18;

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

      " + (edges + ranks).join("\n") + "}",
    ),
    labels: labels,
    width: width,
  )
}
