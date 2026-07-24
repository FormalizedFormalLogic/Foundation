# Format and regenerate keys of references.bib
format-references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph as import_graph.{png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph import_graph.png import_graph.pdf import_graph.html

# Regenerate Foundation.lean to include all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --module

# Remove unused imports/variables and drop unnecessary `public` (run before merging any work)
shake:
    lake shake --keep-public --fix
