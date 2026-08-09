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

# Regenerate Foundation.lean to include all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --module

# Remove unused imports/variables and drop unnecessary `public` (run before merging any work)
shake:
    lake shake --keep-public --fix

# Audit Foundation for sorry/native_decide/unauthorized axioms (requires `lake build Foundation` first)
axiom-audit:
    lake exe axiom-audit --root Foundation
