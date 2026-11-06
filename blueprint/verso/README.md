# Verso Blueprint

2026-11-07 / Blueprint v0.4.0。
定理1.1(3)の数学的な設計を、公式
[VersoBlueprint](https://github.com/leanprover/verso-blueprint) の **v4.35.0** で記述する。
Lean 4.35.0を使う独立したLake packageであり、本文の数式、依存グラフ、進捗表、
検証済みLean宣言へのリンクをHTMLに生成する。主ライブラリの依存pinは変更しない。

## 本文

| ファイル | 担当する課題 |
|---|---|
| [Blueprint.lean](NcCubicBlueprint/Blueprint.lean) | 元の定理、二段階の目標、実装順、検証の読み方 |
| [Foundations.lean](NcCubicBlueprint/Chapters/Foundations.lean) | P0–P6b：多項式・Hessian・Jacobi・ブロックの逆構成 |
| [LieTheory.lean](NcCubicBlueprint/Chapters/LieTheory.lean) | L0–L5：非退化形式、support、Lie理論の証拠、三次元分解 |
| [Completion.lean](NcCubicBlueprint/Chapters/Completion.lean) | A・G0–G2・T：アフィン分類、表示・持上げ・降下、幾何学的完成 |

全19課題について、主張・仮定・証明設計・実装先候補を記述する。
証明設計の本文は未形式化の論証である。Leanで検証済みの課題は次の二つだけである。

- P6a → `NcCubic.Jacobian.jacobi`：一ブロックのJacobian括弧。関連する9定理を検証済み。
- L2 → `NcCubic.LieObstruction.no_highest_root_witness`：明示された証拠からの矛盾。
  根基型・最高根型・交差括弧に関する計5定理を検証済み。証拠の存在は含めない。

代表宣言との関連付けだけで課題全体を完了とはしない。
AとTは未証明であり、`AffineClassificationStatement` は命題の定義である。
`GeometricClassificationStatement` は今後導入する最終型の予定名である。

## 生成と検査

初回にLeanと主ライブラリを準備する場合は、リポジトリのルートで次を実行する。

```bash
bash scripts/bootstrap.sh
```

本文の生成はルートから次のコマンドで行う。

```bash
bash scripts/build_blueprint.sh
```

生成先は `blueprint/verso/_out/site/html-multi/index.html`。
同じディレクトリに数式のある章、依存グラフ、進捗表とリンクを生成する。
各章に固有の参照名と英字の出力パスを指定し、日本語見出しからのURL衝突を避ける。
生成前にこのHTMLディレクトリを置換し、改名前の章を残さない。
全体ビルド・公理監査を含めて検証するときはルートで `lake build`。
元の分類定理の完成判定は `bash scripts/check.sh --complete` で別に行う。
現在は17課題が未完了であり、最終ゲートは失敗するのが正しい。

2026-11-07、準備済みクラウド環境で全体ビルドとHTML生成を検証した。
初回はVersoBlueprint・Versoと補助依存の取得にネットワーク接続が必要。
固定した `lake-manifest.json` と、ルートと共有する9依存のpinを保持する。
クリーンな新規cloneでの全依存再取得は未検証である。
GitHub ActionsやGitHub Pagesへの公開は設定していない。

## 同期の規則

[../tasks.json](../tasks.json) がラベル・依存関係・受入条件・状態の正本である。
本文の `(uses := "...")` と同時に更新し、ルートで
`python3 scripts/check_blueprint.py` を実行する。
原典の位置は `source`、実装先候補は `planned_module` に置く。
これらの候補は存在するファイル・宣言を保証するものではない。

補題ディレクティブは固定版APIの `:::lemma_`、数式はVersoのmath記法を使う。
本文中のLean宣言名はバッククォートで囲む。章内の最初の見出しは `#` とする。
未証明の設計に `:::proof` やLean関連付けを追加して、完了状態を作らない。
将来Lean側で属性を付ける方式へ移す場合も、文書だけのために主packageへ
Verso依存を追加しない。

上流の仕様は
[Getting started](https://github.com/leanprover/verso-blueprint/blob/v4.35.0/doc/GETTING_STARTED.md) と
[Manual](https://github.com/leanprover/verso-blueprint/blob/v4.35.0/doc/MANUAL.md) を参照する。
