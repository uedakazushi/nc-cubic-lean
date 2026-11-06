import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "アフィン分類から元の幾何学的定理へ" =>
%%%
tag := "completion"
file := "completion"
htmlSplit := .never
%%%

分類する対象は $`X=V(F)\subset\mathbf P(V)` 上の全 Poisson 双ベクトル切断である。
アフィン錐上にあらかじめ与えた $`q=\iota_{dF}P` の分類だけでは元の定理にならない。
原論文 §2 の表示・Jacobi の持上げと、幾何学的な定義の比較をこの章で接続する。
以下の A・G0–G2・T は全て未証明である。

# アフィン核心の正確な完成条件
%%%
tag := "affine-classification"
%%%

:::theorem "A" (uses := "P3, P4, L5, P5, P6b")
$`N\ge5`、$`0\ne F\in\mathbf C[z_1,\ldots,z_N]_3`、
`HasIsolatedGradientZero F`、$`0\ne P\in\Lambda^3\mathbf C^N` の下で、
$`\iota_{dF}P` が全多項式上で Jacobi を満たすことと、
`HasBlockNormalForm F P` が同値である。
最終的な Lean 宣言は
`NcCubic.theorem113_affine : NcCubic.AffineClassificationStatement`。
:::

証明設計：順方向では P3・P4 から $`K(P)` の基点自由性を得て L5 を適用し、P5 で
$`F` を分解する。逆方向は P6b と可逆な座標変換を使う。
基底を伴う存在量化、$`N=3k+m`、全 $`f_s` の三次斉次性、
任意の共変ベクトルに対する $`P` の等式まで `HasBlockNormalForm` に詰める。
`AffineClassificationStatement` は現在は命題の定義であり、これを引数に取る wrapper は
この目標の証明とはしない。ファイル候補は `NcCubic/AffineClassification.lean`。

# 任意の射影双ベクトルを取り込む
%%%
tag := "geometric-bridge"
%%%

:::lemma_ "G0" (uses := "P2, P0")
$`F` が滑らかな射影三次超曲面 $`X` を定めるとき、固定した $`F` に対して線形同型

$$`\Lambda^3V\xrightarrow{\sim}H^0(X,\Lambda^2T_X),\qquad P\longmapsto(\iota_{dF}P)|_X`

を構成する。右辺への写像は斉次二次 bivector の射影化である。
任意の切断がこの形で表されることと、$`P` の一意性の両方を示す。
:::

証明設計は原論文の補題2.2・命題2.3（印刷 pp.4–5）に沿う。

1. $`\mathbf P=\mathbf P(V)` として Euler 列、その外積と twist から
   $`H^0(\mathbf P,\Lambda^2T_{\mathbf P}(-3))=H^1(\mathbf P,\Lambda^2T_{\mathbf P}(-3))=0`
   と $`H^0(\mathbf P,\Lambda^3T_{\mathbf P}(-3))\simeq\Lambda^3V` を示す。
   必要な線束の中間コホモロジー消滅は $`\dim\mathbf P=N-1\ge4` の範囲で供給する。
2. 制限列から切断を周囲へ一意に延長し、二次係数 bivector $`B` で代表させる。
   接性を $`\iota_{dF}B=FA+hE`、$`A` は一次ベクトル場、$`h` は三次式、と書く。
   Euler 場は $`E=\sum_i z_i\partial_{z_i}`。再度縮約すると $`h=-A(F)/3`。
3. $`q=B-\frac13E\wedge A` とすれば $`\iota_{dF}q=0`。
   Koszul の次数部分
   $`S_0\otimes\Lambda^3V\to S_2\otimes\Lambda^2V\to S_4\otimes V`
   の完全性から一意な定数 $`P` を得る。左隣は係数次数が負なので0。
4. 代表の差 $`E\wedge Z` が $`F` を Casimir に持てば
   $`3FZ=Z(F)E`。滑らかさからの $`F` の既約性と整除性を証明し、
   $`Z=(c/3)E`、従って差が0と示す。任意の $`P` から接する切断を作る逆も確認する。

線束の切断の持上げ、sheaf の接性とアフィンの等式、正則列の高次 Koszul 完全性を
それぞれ独立の補題にする。P2 の低次数 syzygy だけを引用して高次完全性まで済ませない。
G0 の証明には、G2 にまとめる最終比較に先立って、smoothness から gradient 条件を得る
補題を用意する。これにより G0 と G2 の循環依存を避ける。
非零性の比較 $`P\ne0\iff\pi_X\ne0` も線形同型から得る。
ファイル候補は `NcCubic/Geometry/Representation.lean`。

:::lemma_ "G1" (uses := "G0, P2")
標準代表 $`q=\iota_{dF}P` の $`X` 上の射影化が Poisson ならば、
アフィン錐上でも $`[q,q]=0`。従って A の全多項式 Jacobi 仮定を満たす。
:::

証明設計：原論文の命題2.4。標準体積形式による divergence $`\delta` を定義し、
交代性と Hessian 対称性から $`\delta q=0` を示す。
Schouten 括弧との符号を含む恒等式、および Casimir 性から、
$`J=[q,q]` は $`\delta J=0`、$`\iota_{dF}J=0` を満たす。
$`X` 上での射影化の消滅を、twist した三重接束の制限列と G0 のコホモロジー計算から

$$`J=FT+E\wedge B_2,\qquad T\in\Lambda^3V,\quad B_2\in S_2\otimes\Lambda^2V`

と表す。恒等式

$$`\delta(FT)=\iota_{dF}T,\qquad \delta(E\wedge B_2)=NB_2-E\wedge\delta B_2`

に $`E` を外積して $`E\wedge B_2=-N^{-1}E\wedge\iota_{dF}T` を得る。
元の式を縮約すると $`(1-3/N)F\iota_{dF}T=0`。
$`N\ge5`、整域性、$`F\ne0` から縮約は0、P2 の定数係数の独立性から $`T=0`、従って $`J=0`。
Schouten 括弧の座標式と A の Jacobiator の関係（係数2を含む）も証明する。
接性や $`\iota_{dF}q=0` だけではこの持上げを結論できない。
ファイル候補は `NcCubic/Geometry/JacobiLift.lean`。

:::lemma_ "G2" (uses := "G0, P0, P6b")
射影的 smoothness と斉次三次式の gradient 条件、幾何学的 Poisson 切断と
座標環上の括弧を比較し、標準代表の射影降下・$`X` への制限・座標変換を接続する。
原論文の切断を正則な切断として扱う場合は、代数的切断との比較も必要である。
:::

証明設計：smoothness と「gradient の零点は原点のみ」の比較は Euler 等式と
射影超曲面の Jacobian criterion により先に独立して証明する。
斉次二次 bivector のスカラー作用への適合性、degree 0 の局所関数上での括弧、
チャート間の貼り合わせを検証する。$`F` の Casimir 性からイデアル $`(F)` が保たれ、
超曲面に降下することを示す。逆構成では P6b を使う。
必要な代数的・正則な大域切断の比較は、この射影的な対象の範囲を明示し、
Schouten 括弧との適合も確認して接続する。未確認の比較を定義に埋め込まない。
ファイル候補は `NcCubic/Geometry/Comparison.lean`。

# 元の定理と終了判定
%%%
tag := "geometric-classification"
%%%

:::theorem "T" (uses := "A, G0, G1, G2")
滑らかな複素射影三次超曲面 $`X=V(F)\subset\mathbf P(V)`、$`\dim X=N-2\ge3` 上の
任意の非零 Poisson 切断 $`\pi_X` は、正規化された三次元 volume trivector の和と
$`F=\sum_s f_s(x_s,u)` により表示される。括弧は各三変数の Jacobian 括弧で、
異なる active ブロックの間と中心変数の括弧は0である。逆にこの正規形は
$`X` 上の Poisson 構造を与える。
最終宣言は `NcCubic.theorem113 : NcCubic.GeometricClassificationStatement` とする。
:::

証明設計：G0 で $`\pi_X` を一意な $`P` に移し、非零性も同型で移す。
G1・G2 で A の仮定を満たして正規形を得て、G2 で幾何学的な結論へ戻す。
逆方向も射影降下まで行う。最終命題の定義はまだ Lean にはない。
原論文の量化対象・全仮定・式(1.1)(1.2)・逆構成を型と照合してから導入する。
ファイル候補は `NcCubic/Completion.lean`。

終了時は全プロダクション宣言の公理監査と、最終型の独立レビューを行う。
`bash scripts/check.sh --complete` が通ることを最終ゲートとする。
一般階数、退化スキーム、moduli、量子化は定理第3項の完成条件には含めない。
