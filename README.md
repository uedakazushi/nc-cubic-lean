# nc-cubic

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
bash scripts/bootstrap.sh
source scripts/env.sh
bash scripts/check.sh
```

`bootstrap.sh` は固定版のLeanを取得・検証し、固定した依存関係を解決し、
必要なmathlibキャッシュを取得してビルドと公理監査を実行します。
既に同じLeanが使える環境ではその実行系を利用します。
最終定理の完成確認は別のコマンドです。

```bash
bash scripts/check.sh --complete
```

未解決の課題が残る初期版では、この最終ゲートは意図的に失敗します。
`lake build` の成功は、現在収録されたコードの検証成功を意味します。

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
