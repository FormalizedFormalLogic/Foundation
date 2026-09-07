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

# Generate the zoo diagrams as pages/zoo/*.{png,pdf}, vertical and horizontal (requires typst)
zoo:
    lake build zoo_arithmetic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    mkdir -p pages/zoo
    typst compile --input dir=TB Zoo/arithmetic.typ pages/zoo/arithmetic_v.png
    typst compile --input dir=TB Zoo/arithmetic.typ pages/zoo/arithmetic_v.pdf
    typst compile --input dir=RL Zoo/arithmetic.typ pages/zoo/arithmetic_h.png
    typst compile --input dir=RL Zoo/arithmetic.typ pages/zoo/arithmetic_h.pdf

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
