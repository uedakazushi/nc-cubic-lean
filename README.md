# nc-cubic-lean

**滑らかな複素三次超曲面の Poisson 構造の正規形を Lean で形式化するプロジェクト。**

対象は [原論文](paper/cubic_poisson_paper_20261104.pdf) の **定理1.1、第3項**
（Theorem 1.1.3、印刷 pp. 2–3）です。2026-11-13。
**原定理の代数的解釈を証明済みです。** 現在の到達点と実行済みの検証は
[STATUS](docs/STATUS.md) に記載します。

## 最初に読むもの

1. [研究方針](docs/RESEARCH_PLAN.md)：目標、完成条件、次の課題。
2. [Blueprint](blueprint/README.md)：数学的な依存関係、原論文とLeanの対応。
3. [研究ノート](docs/RESEARCH_NOTES.md)：Bertiniを置き換える線形代数の証明など。
4. [ライブラリ調査](docs/LIBRARIES.md)：mathlib / Axiom Stacks の具体的な利用先。
5. [Codexでの開始手順](docs/CODEX.md)：環境の準備と、そのまま使える最初の指示。

## 実行

Linux/macOS で Bash、Python 3.9以降、Git、curl、tar、zstd を用意します。
システムの Python 3.9/3.10 でも `lake build` の整合性検査が動作するよう、
SHA-256 はストリーミング計算を使います（Python 3.11 固有の API は不要）。

```bash
bash scripts/bootstrap.sh  # 必要な場合のみ初回環境準備
lake build
```

`bootstrap.sh` は固定版のLeanを取得・検証し、固定した依存関係を解決し、
必要なmathlibキャッシュを取得してビルドと公理監査を実行します。
既に同じLeanが使える環境ではその実行系を利用します。
Stacks の Git partial clone が `HTTP 400` / `promisor remote` で中断された場合は、
`scripts/resolve_deps.sh` が固定コミットを `HTTP/1.1`・`--no-filter` で取得し直して
Lake の依存解決を一度だけ再試行します。通常の成功時には余分な取得をしません。
全 workspace は `nc-cubic-lean/.lake/packages/` を共有するため、同じ
mathlib・Stacks のソースや `.olean` を重複取得・コンパイルしません。
同じ復旧処理は `integrations/stacks` および `blueprint/verso` の
独立したビルドにも適用されます。いずれも固定済みのlockfileを使い、
失敗時に限り `Stacks` の不完全なpartial cloneを修復します。
未解決の場合は失敗を報告し、既存の checkout を無断で削除しません。
最終定理の完成確認は別のコマンドです。

```bash
bash scripts/check.sh --complete
```

最終ゲートは、全課題の証明・元の幾何学的な最終型・公理監査・独立レビューを検査します。
`lake build` は通常の Lean ビルドに加え、公理監査、Stacks アダプターの検証、Verso HTMLとLuaLaTeX PDFの生成まで要求します。最終定理の確認には上記の完成ゲートも使います。

## 固定した基盤

| 依存 | 固定版 |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| AxiomMath/Stacks（本体のCM/Koszul証明と独立検証） | `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` |

通常の証明ライブラリはmathlibと固定版Stacksの必要モジュールに依存します。
`NcCubic/GradientRegularity.lean` がCohen–Macaulay性・局所正則列・Koszulの局所大域接続を
使い、gradientの低次数syzygy消滅を証明します。大域正則列そのものを別証明したとは扱いません。
[integrations/stacks](integrations/stacks/README.md) の独立したAPI検証先も保持します。
全Stacksを一括importする構成ではありません。

## コードと証明状態

**元の幾何学的定理を証明済みです。**
[`NcCubic/Completion.lean`](NcCubic/Completion.lean) の
`NcCubic.theorem113 : NcCubic.Geometry.GeometricClassificationStatement` が、
実際の非零Poisson双ベクトルの正規形と逆方向を証明します。
任意の双ベクトルの標準表示、元の外積三乗との複素線形同型、Jacobi持上げ、
全開集合上の括弧比較まで接続し、19課題すべてを証明しました。
アフィン分類 `theorem113_affine` も保持しています。

対象は代数的な切断で、Poisson条件は標準的な誘導括弧のJacobi恒等式で定義します。
最終型と実際の証明依存は原論文に対して独立レビュー済みです。
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

日本語の数学的本文を [`blueprint/verso`](blueprint/verso/README.md) に置く。
Blueprint v0.4.0では、全19課題の正確な主張・仮定・証明設計・原典の位置・
実装先候補を整理した。アフィン分類と元の幾何学的定理の完成条件を分け、
条件付きの障害計算と証拠の存在定理も区別する。
`leanprover/verso-blueprint` の固定版で、数式・依存グラフ・進捗表・
証明済みLean宣言へのリンクを生成する。ルートで `bash scripts/build_blueprint.sh` を実行すると、
HTML と LuaLaTeX 製 PDF を同時生成する。PDF のためには MacTeX / TeX Live の
`lualatex`・`kpsewhich`・`luatexja` と Verso が要求する TeX パッケージが必要である。
証明ライブラリとは独立したpackageで、GitHub Actionsによる公開は設定していない。
全体ビルド・HTML・日本語PDF生成の検証は [STATUS](docs/STATUS.md) を参照する。
作業環境のTeX補完手順は [TEX_RUNTIME](docs/TEX_RUNTIME.md) に記載する。

### 単一コマンドのデフォルトビルド（v0.3.0）

Lean 4.35.0 と Lake が利用できる場合、clone したリポジトリの
**ルートで `lake build` を実行するだけ**で、次が順に実行される設定です。

1. `NcCubic` のビルド
2. ソース整合性チェック、プロジェクト全宣言の公理監査
3. `blueprint/tasks.json` と Verso の依存関係照合
4. Axiom Stacks のKoszulアダプターの個別ビルド・公理監査
5. Verso Blueprint のHTMLとLuaLaTeX製PDFの生成、および両出力の存在チェック

依存構成の最適化（2026-11-08）：`integrations/stacks` と `blueprint/verso` の
`packagesDir = "../../.lake/packages"` により、固定したGit checkout・コンパイル済み
Mathlib/Stacks・Verso依存をルートと共有する。各 workspace 固有の `.lake/build`、
HTML・PDF 出力、および検証ターゲットは独立である。
既存の旧キャッシュを捨てずに共通側へ引き継ぐには、実行中のビルド終了後、
`python3 scripts/reuse_legacy_builds.py` で対象を確認し、
`python3 scripts/reuse_legacy_builds.py --apply` で移行できる。
旧ディレクトリは自動削除されない。移行後の正常ビルドを確認してから不要な
旧キャッシュを整理する。共有には同一固定 SHA、root workspace、同一 toolchain が必要。
`python3 scripts/dependency_info.py shared-check` で、ビルド前にも
3 workspace の lockfile・設定・共有 SHA の整合性だけを検査できる。

生成先はHTMLが `blueprint/verso/_out/site/html-multi/index.html`、
PDFが `blueprint/verso/_out/site/pdf/main.pdf`。PDF の元となる生成 TeX は
`blueprint/verso/_out/site/tex/main.tex` に保存される。
PDF は静的な印刷版で、依存グラフの対話操作はHTML版に残る。

実装は `lakefile.lean` のデフォルト `fullProject` ターゲットと
`scripts/full_build.sh`。下位のLakeコマンドには明示的なターゲットを
指定しているので、デフォルトターゲットを再帰起動しません。

開発中にLeanソースだけを速く検証するには `lake build NcCubic`。
完全な数学的最終判定には従来通り `bash scripts/check.sh --complete`。
最初の `lake build` はVersoの追加依存をネットワークから取得する必要があり、
依存の競合・環境制限で失敗する可能性があります。失敗は無視しません。
**2026-11-07、公開済みクラウド環境で全体ビルドとHTML生成が成功しました。**
クリーンな新規cloneでの全依存再取得は未検証です。

リポジトリ名は `uedakazushi/nc-cubic-lean` です。Lean の `NcCubic` 名前空間と Lake の `nc_cubic` package 名は意図的にそのまま保持します。旧リポジトリ名の GitHub URL はリダイレクトされますが、Codex の環境・Git remote には新URLを使用してください。
