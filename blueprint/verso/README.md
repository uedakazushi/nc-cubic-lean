# Verso Blueprint

2026-11-07 / Blueprint v0.4.0。
定理1.1(3)の数学的な設計を、公式
[VersoBlueprint](https://github.com/leanprover/verso-blueprint) の **v4.35.0** で記述する。
Lean 4.35.0を使う独立したLake packageであり、本文の数式、依存グラフ、進捗表、
検証済みLean宣言へのリンクをHTMLに、印刷用の静的版をLuaLaTeXでPDFに生成する。
主ライブラリの依存pinは変更しない。

## 本文

| ファイル | 担当する課題 |
|---|---|
| [Blueprint.lean](NcCubicBlueprint/Blueprint.lean) | 元の定理、二段階の目標、実装順、検証の読み方 |
| [Foundations.lean](NcCubicBlueprint/Chapters/Foundations.lean) | P0–P6b：多項式・Hessian・Jacobi・ブロックの逆構成 |
| [LieTheory.lean](NcCubicBlueprint/Chapters/LieTheory.lean) | L0–L5：非退化形式、support、Lie理論の証拠、三次元分解 |
| [Completion.lean](NcCubicBlueprint/Chapters/Completion.lean) | A・G0–G2・T：アフィン分類、表示・持上げ・降下、幾何学的完成 |

全19課題について、主張・仮定・証明設計・実装先候補を記述する。
未完了課題の証明設計は未形式化の論証である。Leanで検証済みの課題はP0–P5・P6a・P6b・L0–L5・Aの15課題である。

- P1 → `NcCubic.CubicDifferential.hessian_gradient`：微分の次数・Euler・Hessian恒等式と線形性。
- L0 → `NcCubic.NondegenerateForm.exists_nondegenerate`：無限体上の基点自由な対称形式族に非退化元が存在する。
- P4 → `NcCubic.CubicDifferential.hessian_basepoint_free`：孤立gradient条件からの基点自由性。

- P6a → `NcCubic.Jacobian.jacobi`：一ブロックのJacobian括弧。関連する9定理を検証済み。
- L2 → `NcCubic.LieObstruction.no_highest_root_witness`：明示された証拠からの矛盾。
  根基型・最高根型・交差括弧に関する計5定理を検証済み。証拠の存在は含めない。

代表宣言との関連付けだけで課題全体を完了とはしない。
Aは `NcCubic.theorem113_affine` で証明済み。Tは未証明である。
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

生成先はHTMLが `blueprint/verso/_out/site/html-multi/index.html`、
PDFが `blueprint/verso/_out/site/pdf/main.pdf`、生成TeXが
`blueprint/verso/_out/site/tex/main.tex` である。
HTMLには数式のある章、対話的な依存グラフ、進捗表とリンクを生成する。
PDFにはVersoの静的TeXレンダリングを用い、対話的機能は含めない。

PDFのビルドには `lualatex`、`kpsewhich`、`luatexja.sty` と
Versoが要求するTeX Liveパッケージ・Source系フォントパッケージが必要である。
Macでは日本語対応を含むMacTeXを推奨する。`scripts/blueprint_lualatex.sh` は
生成TeXのプリアンブルに `\\usepackage{luatexja}` を一度だけ挿入して
日本語を組版する。原稿ソースやHTML用KaTeXのマクロには変更を加えない。
各章に固有の参照名と英字の出力パスを指定し、日本語見出しからのURL衝突を避ける。
生成前にこのHTMLディレクトリを置換し、改名前の章を残さない。
全体ビルド・公理監査を含めて検証するときはルートで `lake build`。
元の分類定理の完成判定は `bash scripts/check.sh --complete` で別に行う。
現在は4課題が未完了であり、最終ゲートは失敗するのが正しい。

2026-11-07、準備済みクラウド環境で従来の全体ビルドとHTML生成を検証した。
2026-11-08、LuaLaTeXエンジンラッパーを単体テストし、日本語と数式を含む
試験文書がPDFになり、日本語テキストを抽出できることを確認した。
実際のVerso Blueprint全体のPDF生成は未検証である。
初回はVersoBlueprint・Versoと補助依存の取得にネットワーク接続が必要。
この独立した Lake package でも Stacks の Git partial clone が失敗し得るため、
`scripts/build_blueprint.sh` はルート共通の `scripts/resolve_deps.sh` を呼ぶ。
Stacks の HTTP 400 / promisor remote エラー時には、固定SHAのフィルターなしfetchで
一度修復して依存解決を再試行する。手動で復旧する場合はリポジトリルートから
`bash scripts/resolve_deps.sh blueprint/verso` とする。
manifestが存在しない場合は依存の無断更新を避けるため停止する。
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
