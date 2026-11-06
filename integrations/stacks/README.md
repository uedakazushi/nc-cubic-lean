# Axiom Stacks の個別モジュールを使う検証先

版: 0.1.0 / 2026-11-07 JST

このディレクトリは独立した Lake package である。原論文の補題2.1へ向けて、
正則列から Koszul 関係の生成性へ進む接続を用意する。基礎プロジェクトは
mathlib だけで作業でき、この package は必要に応じて取得・検証する。

## 固定する依存

| 対象 | 固定値 |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`) |
| AxiomMath/Stacks | `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` |

Stacks の固定版に含まれる `lean-toolchain` と `lake-manifest.json` を確認して
組み合わせた。Stacks の README に残る旧版の記述ではなく実ファイルを基準にする。
双方とも Lean コードは Apache-2.0 で公開されている。

- [Stacks 固定版](https://github.com/AxiomMath/Stacks/tree/5ed82d14634e8d9576bb844c7bd4e3da66d450e7)
- [Stacks の依存 manifest](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/lake-manifest.json)
- [mathlib 固定版](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)

## 内容

### 既定の `NcCubicStacks` と `NcCubicStacksAudit` target

`NcCubicStacks.lean` は次の2モジュールだけを直接 import する。

- `StacksFrontier.RingTheory.Koszul.Regular`
- `StacksFrontier.RingTheory.Koszul.Relations`

この2つの推移的依存は Lake が解決する。全体を取り込む `import Stacks`、
`import StacksCore`、`import StacksFrontier` は使わない。

プロジェクト側の宣言は次の2つである。

- `NcCubicStacks.h1Regular_of_regular`: mathlib の意味で正則な有限列が
  Stacks の意味で H₁-regular であること。
- `NcCubicStacks.syzygy_mem_relSpan_of_regular`: 正則列 `f` と関係
  `Σ aᵢ fᵢ = 0` から、`a` が Koszul relations の span に属すること。

いずれも upstream 定理を適用する短い証明である。関数 `f` の正則性を
仮定する一般補題であって、三次式の gradient の正則性を仮定なしに得たとは扱わない。

`NcCubicStacksAudit.lean` は `NcCubicStacks` 名前空間の宣言について推移的な
公理依存を機械的に調べる。`propext`、`Classical.choice`、`Quot.sound` 以外が
あればビルドを失敗させる。上記2補題が読み込まれていることも確認する。
Stacks 全体を列挙して監査するものではない。

### 明示的に実行する `NcCubicStacksCM` target

`NcCubicStacksCM.lean` は次を import し、必要な型を `#check` する。

- `StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial`
- `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion`

対応する原典の tag は [0AAI](https://stacks.math.columbia.edu/tag/0AAI)、
[00ND](https://stacks.math.columbia.edu/tag/00ND)、
[02JN](https://stacks.math.columbia.edu/tag/02JN)。
多項式環の Cohen–Macaulay 性と、局所 CM 環における次元降下による正則列判定が
利用候補になる。こちらは依存が大きくなりうるので `defaultTargets` に入れない。

## 実行方法

リポジトリのセットアップ手順で Lean を用意した後、リポジトリ直下から実行する。

```bash
source scripts/env.sh
cd integrations/stacks
lake resolve-deps
python3 fetch_mathlib_cache.py
lake build NcCubicStacks NcCubicStacksAudit
```

Cohen–Macaulay 側も検証するときだけ、続けて実行する。

```bash
python3 fetch_mathlib_cache.py --cm
lake build NcCubicStacksCM
```

`fetch_mathlib_cache.py` は選択した Stacks モジュールの import を辿り、必要な
Mathlib モジュールだけを `lake exe cache get` に渡す。
依存を意図的に更新する場合には `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` とし、
Mathlib hookによる全キャッシュの自動取得を止める。通常の再現では配布したmanifestを
`lake resolve-deps` で使用する。
キャッシュとして取得するのは mathlib のコンパイル済みファイルである。
固定版 Stacks の README は、Stacks 自体のキャッシュを計画段階と記している。
個別 import でも推移的依存が大きくなる場合があるので、ビルド時間とメモリを
確認してから通常の検証に組み込む。`lake-manifest.json` は実際の
`lake update` で生成したものを収録し、直接・間接依存を固定する。

通常の `lake build` も2つの既定 target を実行する。毎回明示的に監査コマンドを
再実行したい場合には `lake env lean NcCubicStacksAudit.lean` を使える。
CM target には `#print axioms` がある。成功時の出力を確認し、標準公理
`propext`、`Classical.choice`、`Quot.sound` 以外への依存があれば原因を調査する。
宣言の型が原典と目的に合うことの確認は、kernel による証明検査とは別に行う。

## 原論文へ接続するために残っていること

1. 三次斉次式の射影的滑らかさから、偏微分の共通零点が原点だけであることを
   Euler 等式を使って示す。
2. この零点条件から gradient ideal の高さ・局所商の次元を求める。
3. 多項式環の Cohen–Macaulay 性と正則列判定を適用し、局所化の議論を含めて
   gradient が正則列であることを得る。
4. ここで用意した `syzygy_mem_relSpan_of_regular` と各偏微分の次数2を使い、
   係数次数0または1の syzygy が零であることを証明する。
5. 基礎プロジェクトの cubic・gradient・Jacobi の定義とこの API を接続する。

`Koszul.Syzygies` にある「生成元が単位イデアルを生成する」ことを仮定した定理は、
原点を共通零点に持つ gradient ideal には直接適用できない。

## 現在の検証状態

2026-11-07 に固定版の取得、実際の `lake update` による lockfile の生成、
選択した Mathlib キャッシュの取得を行い、次を実行して確認した。

| 検証 | 結果 |
|---|---|
| `lake build NcCubicStacks` | 成功。2つのアダプターを kernel が検査した |
| `lake build NcCubicStacksAudit` | 成功。2宣言の推移的公理依存を許可リストと照合した |
| `lake build NcCubicStacksCM` | 成功。3つの CM 公開 API を読み込み、型と公理出力を確認した |
| 基礎プロジェクトとの共有依存の比較 | mathlib を含む9依存の URL とコミットが一致した |

2つのアダプターと3つの CM 公開 API の公理依存は、すべて
`[propext, Classical.choice, Quot.sound]` だった。
upstream の style/deprecation warning は出るが、ビルドエラーはない。
これは選択したソースの実ビルド確認であり、Stacks 全体の再ビルドや
原論文の Theorem 1.1(3) の形式化完了を意味しない。

既定の対象が直接・推移的に読む Stacks ソースは9モジュール、そこから参照される
Mathlib の import 根は33モジュールだった。CM target も含めると、それぞれ
47モジュールと143モジュールになる。Mathlib 自体の推移的依存はキャッシュ
ツールが解決する。これらの数はこの固定版と現在の import に対する値である。

## StacksFrontier を用いる際の確認

今回の直接 import はいずれも `StacksFrontier` に属する。
[公式サイト](https://stacks.axiommath.ai/) は、人手で原典との対応まで確認された
`StacksCore` と、まだそのレビューを通過していない `StacksFrontier` を区別している。
これは利用を妨げるものではない。採用する定理の原典 tag と実際の Lean の型を
照合し、追加仮定・結論・定義の接続を確認して使う。
