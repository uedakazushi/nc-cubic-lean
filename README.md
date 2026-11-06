# nc-cubic-lean

**滑らかな複素三次超曲面の Poisson 構造の正規形を Lean で形式化するプロジェクト。**

対象は [原論文](paper/cubic_poisson_paper_20261104.pdf) の **定理1.1、第3項**
（Theorem 1.1.3、印刷 pp. 2–3）です。2026-11-07、初期版 v0.1.0。
**定理全体は未証明です。** 現在の到達点と実行済みの検証は
[STATUS](docs/STATUS.md) に記載します。

## 最初に読むもの

1. [研究方針](docs/RESEARCH_PLAN.md)：目標、完成条件、次の課題。
2. [Blueprint](blueprint/README.md)：数学的な依存関係、原論文とLeanの対応。
3. [研究ノート](docs/RESEARCH_NOTES.md)：Bertiniを置き換える線形代数の証明など。
4. [ライブラリ調査](docs/LIBRARIES.md)：mathlib / Axiom Stacks の具体的な利用先。
5. [Codexでの開始手順](docs/CODEX.md)：環境の準備と、そのまま使える最初の指示。

## 実行

Linux/macOS で Bash、Python 3.11以降、Git、curl、tar、zstd を用意します。

```bash
bash scripts/bootstrap.sh  # 必要な場合のみ初回環境準備
lake build
```

`bootstrap.sh` は固定版のLeanを取得・検証し、固定した依存関係を解決し、
必要なmathlibキャッシュを取得してビルドと公理監査を実行します。
既に同じLeanが使える環境ではその実行系を利用します。
最終定理の完成確認は別のコマンドです。

```bash
bash scripts/check.sh --complete
```

未解決の課題が残る初期版では、この最終ゲートは意図的に失敗します。
`lake build` は通常の Lean ビルドに加え、公理監査、Stacks アダプターの検証、Verso HTML の生成まで要求します。分類定理そのものの完成は意味しません。

## 固定した基盤

| 依存 | 固定版 |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| AxiomMath/Stacks（独立した検証用package） | `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` |

通常のターゲットはmathlibに依存します。Stacksの必要部分は
[integrations/stacks](integrations/stacks/README.md) で個別に検証・導入します。
全Stacksを一括importする構成ではありません。

## コードと未証明の目標

- `NcCubic/Statement.lean`：仮定・座標変換・ブロック正規形と、アフィン分類の
  **目標命題の定義**。この定義自体は分類定理の証明ではありません。
- `NcCubic/Jacobian.lean`：三方向のJacobian括弧の基本恒等式。
- `NcCubic/LieObstruction.lean`：原論文の式(3.2)から共通零点を得る補題。
- `blueprint/tasks.json`：依存関係、各課題の受入条件、現在の状態。
- `scripts/Audit.lean`：プロジェクト内の全公開宣言の推移的な公理依存を検査。

全てのプロダクションLeanファイルを `NcCubic.lean` からimportします。
未証明の部分を `sorry` や独自公理で通す方式は採りません。

## 保存と運用

このリポジトリの現行ファイルだけで作業を再開できる構成です。
GitHub Actions、PR、外部サービスへの通知は必須ではありません。
Codexは `AGENTS.md` に従い、小さい証明単位で検証・保存し、次の課題へ進みます。
原論文は変更せず、SHA256を `paper/source.json` に記録しています。
既存論文の内容、今回確認した数学、Leanで検証した命題は区別します。

## Verso Blueprint

The interactive mathematical Blueprint now lives in
[`blueprint/verso`](blueprint/verso/README.md). It uses the upstream
`leanprover/verso-blueprint` package for Lean 4.35.0 with mathematical
chapters, dependency graph, progress summary, and links to proved Lean
declarations. Build locally with `bash scripts/build_blueprint.sh`.
The Blueprint package is separate from the proof library and has no
GitHub Actions deployment. Its first live build remains to be verified.

### 単一コマンドのデフォルトビルド（v0.3.0）

Lean 4.35.0 と Lake が利用できる場合、clone したリポジトリの
**ルートで `lake build` を実行するだけ**で、次が順に実行される設定です。

1. `NcCubic` のビルド
2. ソース整合性チェック、プロジェクト全宣言の公理監査
3. `blueprint/tasks.json` と Verso の依存関係照合
4. Axiom Stacks のKoszulアダプターの個別ビルド・公理監査
5. Verso Blueprint のHTML生成と `index.html` の存在チェック

実装は `lakefile.lean` のデフォルト `fullProject` ターゲットと
`scripts/full_build.sh`。下位のLakeコマンドには明示的なターゲットを
指定しているので、デフォルトターゲットを再帰起動しません。

開発中にLeanソースだけを速く検証するには `lake build NcCubic`。
完全な数学的最終判定には従来通り `bash scripts/check.sh --complete`。
最初の `lake build` はVersoの追加依存をネットワークから取得する必要があり、
依存の競合・環境制限で失敗する可能性があります。失敗は無視しません。
**新しいデフォルトターゲットの実ビルドは未実施です。**

リポジトリ名は `uedakazushi/nc-cubic-lean` です。Lean の `NcCubic` 名前空間と Lake の `nc_cubic` package 名は意図的にそのまま保持します。旧リポジトリ名の GitHub URL はリダイレクトされますが、Codex の環境・Git remote には新URLを使用してください。
