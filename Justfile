# List available recipes
default:
    @just --list

# Format and regenerate keys of references.bib
format-references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of Foundation as import_graph.{png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to Foundation import_graph.png import_graph.pdf import_graph.html

# Count lines of Lean source in Foundation/, excluding blank and comment lines (requires cloc)
cloc:
    cloc --include-lang=Lean Foundation/

# Generate the zoo diagrams as pages/zoo/*.{png,pdf} (requires typst)
zoo:
    lake build zoo_arithmetic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    mkdir -p pages/zoo
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.pdf

# Regenerate Foundation.lean to include all modules (run after adding/removing files).
# Restricted to the Foundation library: Zoo has no aggregator, its modules are executable roots.
mk-all:
    lake exe mk_all --module --lib Foundation

# Remove unused imports/variables and drop unnecessary `public` (run before merging any work)
shake:
    lake shake --keep-public --fix

# Audit Foundation for sorry/native_decide/unauthorized axioms (requires `lake build Foundation` first)
axiom-audit:
    lake exe axiom-audit --root Foundation

# doc-gen4 records that its HTML pass ran by touching an empty marker file, and Lake traces that
# marker by its own -- always identical -- contents. `lake pack` carries the marker into the build
# cache, so every run that restores the cache replays the pass and the generated HTML is never
# rewritten. Clearing the output and the two markers that guard it forces a regeneration:
# `doc/references.bib` comes from the bib prepass, keyed on `doc-data/references.json`, and the rest
# of `doc/` from the HTML pass. The per-module database pass behind them stays incremental.
#
# Generate the API documentation into .lake/build/doc (requires `lake build Foundation` first)
docs:
    rm -rf .lake/build/doc
    rm -f .lake/build/doc-data/references.json .lake/build/doc-data/*.docs_built
    lake build Foundation:docs
