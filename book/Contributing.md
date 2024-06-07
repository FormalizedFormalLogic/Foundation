# Contributing

## Discuss

GitHub Discussion is [here](https://github.com/iehality/lean4-logic/discussions). Feel free to correct mistakes, ask questions or share ideas.

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
