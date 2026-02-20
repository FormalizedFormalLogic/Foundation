# Contribution

## Commit convention

Follow usual conventional commit for PR title (we always squash merge).

```
<type>(scope): <subject>
```

Choose `<type>` from below (should be one, but like `fix/doc` might be ok).
- `add`: Adding new results, definition, theorems.
- `fix`: Fixing exists results for something misformalized
- `refactor`: Rename and organize definitons/theorems. (essentially nothing changed about existing facts.)
- `doc`: Adding or updating documents.
- `ci`: Configure GitHub Actions.
- `chore`: Maintaining other things (ex: version-up).

`scope` is optional, specify like `FirstOrder`, `Modal` if needed.

## Usual commands

### Build

```shell
lake build Foundation
```

### References

Format [references.bib](./references.bib) when adding references.

```
bibtool -r .bibtoolrsc -i references.bib -o references.bib
```
