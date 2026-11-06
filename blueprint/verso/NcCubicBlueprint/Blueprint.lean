import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import NcCubic
import NcCubicBlueprint.Chapters.Foundations
import NcCubicBlueprint.Chapters.LieTheory
import NcCubicBlueprint.Chapters.Completion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "滑らかな三次超曲面の Poisson 構造：Blueprint" =>
%%%
tag := "nc-cubic-blueprint"
%%%

2026-11-07 / Blueprint v0.4.0。
原典は同梱の `paper/cubic_poisson_paper_20261104.pdf`、対象は
定理1.1第3項（印刷 pp.2–3）と、その証明に必要な §2–3 である。

*分類定理は未証明である。* 現在の19課題のうち、完了しているのは一ブロックの
Jacobian 括弧 P6a と、明示された Lie 理論の証拠から矛盾を導く L2 の二つ。
証拠の存在、アフィン分類 A、幾何学的な最終目標 T は未完了である。
以下は各課題の主張・仮定・証明設計・実装先候補を与える。

# 目標と規約
%%%
tag := "target"
file := "target"
%%%

$`V` を複素 $`N\ge5` 次元空間、$`0\ne F\in\operatorname{Sym}^3V^*`、
$`X=V(F)\subset\mathbf P(V)` を滑らかとする。$`\dim X=N-2\ge3` である。
$`F` を固定して Poisson 切断 $`\pi_X` を定数 trivector $`P` で表示するとき、
非零の $`\pi_X` に対し、ある $`k\ge1`、$`m\ge0` と線形座標が存在して

$$`N=3k+m,\qquad P=\sum_{s=1}^k\partial_{x_{s1}}\wedge\partial_{x_{s2}}\wedge\partial_{x_{s3}},\qquad F=\sum_{s=1}^k f_s(x_s,u)`

となることと、その逆構成を証明する。各 $`f_s` は全次数3、同じ中心変数
$`u=(u_1,\ldots,u_m)` を共有してよい。括弧は

$$`\{x_{s1},x_{s2}\}=\partial_{x_{s3}}f_s,\quad\{x_{s2},x_{s3}\}=\partial_{x_{s1}}f_s,\quad\{x_{s3},x_{s1}\}=\partial_{x_{s2}}f_s`

で、異なる active ブロックの間と $`\{u_\alpha,-\}` は0。
$`m=0`、$`k=1` を排除しない。座標・ブロック順序・中心三次式の配分の一意性は主張しない。
一般階数、退化スキーム、量子化は今回の目標に含めない。

# 実装の道筋
%%%
tag := "roadmap"
file := "roadmap"
%%%

1. 多項式基盤：P0・P1 を実装し、P4 の基点自由性、P2 の低次数 syzygy 消滅、
   P3 の符号を含む Jacobi の線形化へ進む。
2. 独立な線形代数・Lie 理論：L0 の非退化形式の存在、L1 の support 上の構成、
   L3・L4 の証拠の存在、L5 の三次元ブロック分解を順に示す。
3. アフィン分類：P5 で多項式を分解し、P6b の複数ブロックの逆構成と合わせて A を証明する。
4. 幾何への接続：G0 の表示、G1 の Jacobi 持上げ、G2 の比較・降下を証明して T を閉じる。

次の具体的な着手点は P1、L0、P0。P1 の後には P4 が短い独立課題となる。
大きな障害は P2 の大域正則性、L3・L4 の存在定理、G0–G2 の幾何学的基盤である。
既存 API と未確認の適用条件は `docs/LIBRARIES.md` に分けて記録する。
ファイル候補は将来の配置案であり、存在する Lean 宣言の一覧ではない。

# 読み方と検証
%%%
tag := "verification"
file := "verification"
%%%

各ラベルは `blueprint/tasks.json` の19課題と一対一に対応する。
そこに依存関係・受入条件・状態・検証済み宣言を置き、本文の依存辺と照合する。
L群は一般の基点自由な形式族についての補題群で、P3・P4 との結合は A で行う。
未証明の設計には証明完了を表すディレクティブを付けない。
命題の定義や一つの補助定理の検証だけで課題を完了にしない。

ルートの `lake build` は証明ライブラリ、公理監査、Stacks アダプター、依存グラフの照合、
この HTML の生成を実行する。分類定理の完成確認は別の
`bash scripts/check.sh --complete` で行う。現在は17課題が残っているため失敗するのが正しい。

{include 0 NcCubicBlueprint.Chapters.Foundations}
{include 0 NcCubicBlueprint.Chapters.LieTheory}
{include 0 NcCubicBlueprint.Chapters.Completion}

{blueprint_graph}

{blueprint_summary}
