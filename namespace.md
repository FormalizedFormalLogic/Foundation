# 演繹体系・意味論の名前空間改定案

この文書は、ファイル構成の整理に続く名前空間の改定案をまとめる。
以下では、特記しない限り名前の先頭の `FFL.` を省略する。
以下の名前空間変更は実装済みである。ファイル配置は維持し、旧名の互換エイリアスは追加していない。

## 基本方針

- `Derivation` という名前は維持し、親名前空間で演繹体系を明示する。
- `Sequent`・`Derivation`・`Proof` を同じ体系の名前空間に揃える。
- 共通インターフェースと具体的な体系・モデルを区別する。
- 導出木、理論からの証明、算術化された証明述語を区別する。
- 名前空間の改名はファイル分割とは独立に行う。まとまりのよいファイルを分割する必要はない。
- 既存の定理の内容・仮定は維持する。

## 演繹体系

### 改定前

| 体系 | 導出の型 | 単一の式の証明・体系を表す型 | ファイル |
|---|---|---|---|
| 命題論理 LK | `Propositional.Derivation` | `Propositional.Proof`、`Propositional.Proof.Symbol` | [Propositional/LK/Basic.lean](Foundation/Propositional/LK/Basic.lean) |
| 一階 LK | `FirstOrder.Derivation` | `FirstOrder.LK.Proof`、`FirstOrder.LK` | [FirstOrder/LK/Basic.lean](Foundation/FirstOrder/LK/Basic.lean) |
| 一階 LK の簡略版 | `FirstOrder.Derivation2` | `FirstOrder.Theory.Proof2` | [FirstOrder/LK/Simplified.lean](Foundation/FirstOrder/LK/Simplified.lean) |
| 一階 LJ | `FirstOrder.LJ.Derivation` | `FirstOrder.LJ.Proof`、`FirstOrder.LJ` | [FirstOrder/LJ/Basic.lean](Foundation/FirstOrder/LJ/Basic.lean) |
| 二階 LK | `SecondOrder.Derivation` | `SecondOrder.Proof`、`SecondOrder.Proof.Symbol` | [SecondOrder/LK/Basic.lean](Foundation/SecondOrder/LK/Basic.lean) |
| 命題論理 Hilbert | `Propositional.HilbertProof` | `Propositional.Hilbert` が体系を表す | [Propositional/Hilbert/Basic.lean](Foundation/Propositional/Hilbert/Basic.lean) |

一階 LJ は `Sequent`・`Head`・`Derivation`・`Proof` が `LJ` 配下に揃っている。
一階 LK は `Sequent`・`Derivation` が `FirstOrder` 直下にあり、`Proof` のみが `LK` 配下にある。
命題論理 LK・二階 LK も、導出に関する宣言が各論理の直下にある。

### 改定後

| 改定前 | 改定後 |
|---|---|
| `Propositional.Sequent` | `Propositional.LK.Sequent` |
| `Propositional.Derivation` | `Propositional.LK.Derivation` |
| `Propositional.Proof` | `Propositional.LK.Proof` |
| `Propositional.Proof.Symbol` | `Propositional.LK.Proof.Symbol` |
| `FirstOrder.Sequent` | `FirstOrder.LK.Sequent` |
| `FirstOrder.Derivation` | `FirstOrder.LK.Derivation` |
| `FirstOrder.Derivation2` | `FirstOrder.LK2.Derivation` |
| `FirstOrder.Derivable2` | `FirstOrder.LK2.Derivable` |
| `FirstOrder.Theory.Proof2` | `FirstOrder.Theory.Proof2` |
| `SecondOrder.Sequent` | `SecondOrder.LK.Sequent` |
| `SecondOrder.Derivation` | `SecondOrder.LK.Derivation` |
| `SecondOrder.Proof` | `SecondOrder.LK.Proof` |
| `SecondOrder.Proof.Symbol` | `SecondOrder.LK.Proof.Symbol` |
| `Propositional.HilbertProof` | `Propositional.Hilbert.Proof` |

`FirstOrder.LJ` 配下は基本的に現状を維持する。
既存の `FirstOrder.LK`・`FirstOrder.LJ` は型だが、同名の名前空間を併用できる。

体系を表す型には、一階の `LK`・`LJ` と、命題論理・二階の `Proof.Symbol` という別の不統一がある。
上表では既存の型を維持して配置だけを揃える。体系の型名自体を統一するかは別途検討する。

### 関連する宣言

- `FirstOrder.Derivation.Canonical` は、導出の移動に伴い `FirstOrder.LK.Derivation.Canonical` へ移した。カット除去・標準モデル・完全性のファイルも更新した。
- `Derivation.toDerivation2`、`Theory.Proof.toProof2`、`Theory.Proof2.toProof` など、体系間の変換も参照先に合わせて更新する。変換関数の短い名前自体を変更するかは別途決める。
- `FirstOrder.Theory.Proof`・`FirstOrder.Theoryᵢ.Proof` は、有限個の公理と導出をまとめた理論からの証明である。体系単独の `LK.Proof`・`LJ.Proof` とは区別し、既存の名前空間に維持する。
- 二階 LK も `SecondOrder.Theory.Proof` に、有限個の公理・理論への所属・そこからの導出をまとめる。`Schema` と、証明可能性を単なる理論への所属としていた定義は廃止する。理論からの証明は `SecondOrder.Theory.Proof` に維持し、体系単独の証明は `SecondOrder.LK.Proof` に移した。

### Bootstrapping

[Arithmetic/Bootstrapping/Syntax/Proof/Basic.lean](Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Proof/Basic.lean)
の `FirstOrder.Arithmetic.Bootstrapping.Derivation` は、符号が導出を表すという `Prop` である。
導出木そのものを表す `FirstOrder.Derivation : … → Type` と一括置換しない。

同様に、`DerivationOf`・`Derivable`・`Proof`・`Provable` は内部の証明述語として扱う。
[Typed.lean](Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Proof/Typed.lean) の
`TDerivation`・`TProof` は、その述語に基づく型付きの表現である。
一方、[Coding.lean](Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Proof/Coding.lean) は
外部の `FirstOrder.Derivation2` の名前空間も拡張しているため、外部の型の改名に追従させる。

## 意味論

### 改定前

| 意味論 | モデル・構造 | 評価関係 | 主なファイル |
|---|---|---|---|
| 一階 Tarski | `FirstOrder.Structure`、`FirstOrder.Struc`、`FirstOrder.SmallStruc` | `FirstOrder.Semiterm.val`、`FirstOrder.Semiformula.Eval / Evalb / Evalf / Realize` | [FirstOrder/Tarski/Basic.lean](Foundation/FirstOrder/Tarski/Basic.lean) |
| 二階 Tarski | `SecondOrder.Struc₂` | `SecondOrder.Semiformula.EvalAux / Eval` | [SecondOrder/Tarski/Basic.lean](Foundation/SecondOrder/Tarski/Basic.lean) |
| 一階 Kripke | `FirstOrder.KripkeModel`、`FirstOrder.IntKripke`、`FirstOrder.ForcingNotion` | `FirstOrder.KripkeModel.Forces / WeaklyForces` | [Kripke/Basic.lean](Foundation/FirstOrder/Kripke/Basic.lean)、[Intuitionistic.lean](Foundation/FirstOrder/Kripke/Intuitionistic.lean)、[Classical.lean](Foundation/FirstOrder/Kripke/Classical.lean) |
| 命題論理 Boolean | `Propositional.Boolean.Valuation` | `Propositional.Formula.Boolean.val` | [Boolean/Basic.lean](Foundation/Propositional/Boolean/Basic.lean) |
| 命題論理 Heyting | `Propositional.HeytingSemantics` | `Propositional.Formula.hVal`、`Propositional.HeytingSemantics.hVal` | [Heyting/Semantics.lean](Foundation/Propositional/Heyting/Semantics.lean) |

### 改定後

| 改定前 | 改定後 |
|---|---|
| `FirstOrder.Structure` | `FirstOrder.Tarski.Structure` |
| `FirstOrder.Struc` | `FirstOrder.Tarski.Struc` |
| `FirstOrder.SmallStruc` | `FirstOrder.Tarski.SmallStruc` |
| `SecondOrder.Struc₂` | `SecondOrder.Tarski.Struc` |
| `SecondOrder.SmallStruc` | `SecondOrder.Tarski.SmallStruc` |
| `FirstOrder.KripkeModel` | `FirstOrder.Kripke.Model` |
| `FirstOrder.IntKripke` | `FirstOrder.Kripke.Mod` |
| `FirstOrder.ForcingNotion` | `FirstOrder.Kripke.ForcingNotion` |
| `Propositional.HeytingSemantics` | `Propositional.Heyting.Model` |
| `Propositional.Boolean` | `Propositional.Tarski` |
| `Propositional.Formula.Boolean` | `Propositional.Formula` |

具体的な意味論を上表の名前空間へ移し、子名前空間も追従させた。

`Structure L M` は固定した台集合への解釈であり、`Struc L` は非空の台集合もまとめた構造である。
改名しても、この二つの役割の違いは維持する。
`KripkeModel` と `IntKripke` にも、外から与える世界・台集合上のクラスと、それらもまとめた構造という違いがある。
この違いを維持して `Kripke.Mod`・`Kripke.ForcingNotion` に移した。
二階の `Tarski.SmallStruc` は、一階構造の別名になっていた定義を修正し、二階の `Tarski.Struc` を指すようにした。

### 評価関数の配置

`Semiformula.Eval`・`Semiterm.val` は、式・項の名前空間に置かれ、`φ.Eval`・`t.val` の形で使われている。
これらの評価関数は既存の名前空間に維持する。
単にファイルが `Tarski` 配下にあるという理由だけで、すべての評価関数を移動することは前提としない。

`Structure.Eq`・`Structure.Model` は `Tarski.Structure` 配下に移し、`Semiformula.Operator.val` は維持する。
命題論理の `Formula.Boolean.val` とその補題は `Formula.val` と同じ `Formula` 名前空間へ移した。
一般の論理代数への評価である `NNFormula.val` は維持する。

## 共通インターフェース

| 名前 | 役割 | 方針 |
|---|---|---|
| `FFL.Entailment` | 証明の型 `𝓢 ⊢! φ` を与える | 具体的な LK・LJ 等とは分けて維持 |
| `FFL.Entailment.Provable` | 証明の存在 `𝓢 ⊢ φ` | 維持 |
| `FFL.Structural`、`FFL.OneSidedLK` | 導出体系の構造規則・LK 規則 | 共通の規則クラスとして維持 |
| `FFL.Semantics` | 充足関係 `𝓜 ⊧ φ` を与える | Tarski 専用に改名しない |
| `FFL.Semantics.Tarski` | 結合子について古典的な真理条件を満たす性質 | 具体的な一階 Tarski 構造と区別 |
| `FFL.ForcingRelation` | 強制関係 `w ⊩ φ` を与える | 具体的な Kripke モデルと区別 |
| `FFL.Sound`、`FFL.Complete` | 演繹体系と意味論を結ぶ性質 | 共通インターフェースとして維持 |

定義は [Logic/Entailment.lean](Foundation/Logic/Entailment.lean)、
[Logic/Calculus.lean](Foundation/Logic/Calculus.lean)、
[Logic/Semantics.lean](Foundation/Logic/Semantics.lean)、
[Logic/ForcingRelation.lean](Foundation/Logic/ForcingRelation.lean) にある。

`FFL.Semantics` は Boolean・Heyting・Kripke にも使われる一般の充足関係である。
具体的なモデルをまとめる名前空間と混同しない。
また、`FFL.Entailment.Deduction` は既に演繹定理のクラスを表しており、演繹体系一般の意味ではない。

## 実施内容と確認事項

1. LK の `Sequent`・`Derivation`・`Proof` の配置を揃える。
2. `Derivation2`・`Derivable2` を `LK2.Derivation`・`LK2.Derivable` へ移す。`Theory.Proof2` は維持する。
3. Hilbert の証明型を `Hilbert.Proof` に移す。体系を表す型名は維持する。
4. 意味論側のモデル名を整理し、評価関数の配置は独立に判断する。

更新対象は、定義箇所だけでなく、別ファイルで再開された `namespace`、`open`、
完全修飾名、構築子、フィールド記法による参照、記法の右辺、属性・インスタンス、引用・メタコードを含む。
`scoped` 記法については名前空間の変更が利用時のスコープに影響するため、
表示する記号と既存の有効化スコープを維持した。

旧名の互換エイリアスは追加しない。`Theory.Proof`・`Theory.Proof2`・`Theoryᵢ.Proof` は維持する。
体系の型を `LK`・`LJ` と `Proof.Symbol` のどちらに揃えるか、変換関数の短い名前を変更するかは今回の対象外とする。

全体 build は実施していない。変更した主要モジュールを対象に限定 build で確認した。
