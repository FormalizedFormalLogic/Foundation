# Contributing

## Discuss

GitHub Discussion is [here](https://github.com/iehality/lean4-logic/discussions). Feel free to correct mistakes, ask questions or share ideas.

## Documentation

To compile this book, you need mdbook and some plugins.

- [mdbook](https://github.com/rust-lang/mdBook)
- [mdbook-katex](https://github.com/lzanini/mdbook-katex) for [KaTeX](https://katex.org/)

```
mdbook serve md

mdbook build md
```

But you don't have to install to simply correct mistakes and write documents, since it can be previewed by your editor's markdown preview.

## Developing

### VSCode settings

Some notation is not prepared default by [lean 4 extension for VSCode](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4). Here is example `.vscode/settings.json`.

```json
{
  "lean4.input.customTranslations": {
    "cand": "⋏",
    "cor": "⋎",
    "boxdot": "⊡",
    "^F": "ꟳ",
  }
}
```
