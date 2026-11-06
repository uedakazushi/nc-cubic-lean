# 現在の状態

2026-11-07 / v0.1.0。

**元の定理1.1(3)は未形式化。アフィン分類も未証明。**

## 確認済み

| 対象 | 状態 |
|---|---|
| 原典 | 定理1.1第3項、印刷pp.2–3と同定。PDFを同梱しSHA256照合済み |
| アフィン目標 | `AffineClassificationStatement` を定義してコンパイル。仮定、変換方向、縮約の符号を数学的に別レビュー済み |
| 基本ライブラリ | `lake build NcCubic` 成功 |
| 公理監査 | `scripts/Audit.lean` が38宣言を走査。標準3公理以外なし |
| 証明済み補題 | Jacobian括弧9補題、Lie証拠5補題。計14件の宣言が実際にtheoremであることを検査 |
| セットアップ | `scripts/bootstrap.sh` の取得・SHA256検証・依存解決・キャッシュ取得・ビルドを実行。再実行も成功 |
| Axiom Stacks接続 | 正則列→H₁正則性、syzygy→Koszul関係のspanの2補題を実ビルド・厳密公理監査 |
| CM API検証 | `NcCubicStacksCM` の3宣言のimport・型・公理依存を確認。gradientへの適用は未証明 |
| 未完成判定 | `--complete` は未解決の17ノードを列挙して失敗する。これが現在の正しい結果 |
| 検査の拒否動作 | 一時的な独自公理を監査が拒否。proof-hole検査がcodeとコメントを区別することも確認 |

依存はLean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`、
Stacks `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` に固定した。
両packageのmanifestは実際のLakeによる生成物で、共有する依存の版は一致する。

## 証明した範囲

`NcCubic.Jacobian.jacobi` は任意の可換係数環上の任意の多項式に対する完全な
Jacobi恒等式である。座標生成元の確認だけではない。反対称性、Leibniz、potentialの
Casimir性、他の変数の中心性、式(1.2)の座標括弧も証明した。

`NcCubic.LieObstruction` は原論文式(3.2)から、明示された最高ウェイト型・最高根型の
証拠に対する \(H(v,v)=0\) と、基点自由性との矛盾を証明する。
可換な括弧間の双線形形式の消滅も示した。**その証拠の存在は未証明**であり、
根基の消滅や三次元ブロック分類を完了したとは扱わない。

`NcCubicStacks` の2補題は既存Stacks定理をプロジェクト向けに接続する一般補題である。
smooth cubicのgradientが正則列になること、低次数syzygyの消滅はまだ示していない。
これらは原論文の新しい数学的結果としてではなく、形式化の初期資産として扱う。

## 実行コマンドと再現上の制約

通常の再現はREADMEのbootstrap/checkで行う。
Stacks側では `lake build NcCubicStacks NcCubicStacksAudit NcCubicStacksCM` を実行した。
上流の一部にstyle/deprecation warningはあるが、ビルドエラーはない。

初期検証の管理されたLinux実行環境には、数値PIDとprocfsのnamespaceの不一致があった。
この環境ではLean自身の実行ファイルの検出だけに
`scripts/compat/lean_self_path.c` の互換処理を使用した。
公式Lean配布物・証明kernel・依存ライブラリのソースは改変していない。
通常の環境では不要で、原因を確認した環境でのみ
`bash scripts/compat/run.sh bash scripts/check.sh` により再現できる。

## 次の着手点

`python3 scripts/next_task.py` は現在、P1（Hessian対称性）、L0（非退化形式の存在）、
P0（外積・座標変換との比較）を準備済み課題として返す。
研究方針・Blueprint・現在のtask graphは、過去の会話を取得せずに作業を再開できる。
最終目標のTとアフィン分類Aは未完了のままである。

## Verso Blueprint integration (2026-11-07 / v0.2.0)

A separate `blueprint/verso` Lake workspace now contains a VersoBlueprint
v4.35.0 generator, three mathematical chapters, and 19 task labels with
explicit dependency edges. Existing proved representatives are linked to
`NcCubic.Jacobian.jacobi` and
`NcCubic.LieObstruction.no_highest_root_witness`.
The repository also contains `scripts/check_blueprint.py` for deterministic
label/edge checks and `scripts/build_blueprint.sh` for local rendering.
**Verso has not yet been fetched or built in an actual Lean environment.**
Consequently no generated HTML and no resolved subworkspace lockfile are
claimed. The root mathlib and Stacks pins remain unchanged; Codex must perform
the initial dependency resolution, build, and visual check and then commit the
subworkspace manifest. The original theorem remains open.
