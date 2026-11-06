import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "多項式・Hessian・Jacobi 恒等式" =>
%%%
tag := "foundations"
file := "foundations"
htmlSplit := .never
%%%

この章の体は複素数体、$`V=\mathbf C^N`、$`S=\mathbf C[z_1,\ldots,z_N]` とする。
$`F\in S_3` は斉次三次式、$`P\in\Lambda^3V` は定数の交代テンソルである。
添字は式では $`1,\ldots,N`、Lean では `Fin N` を使う。
原論文の補題2.1・3.1と §3.3 に対応する。未証明の節にある「証明設計」は
実装する論証であって、Lean の証明完了を表すものではない。

# 座標モデルと変換の契約
%%%
tag := "coordinates"
%%%

:::definition "P0" (lean := "NcCubic.basisContractionBracket_covariance")
有限次元双対を通じた同型
$`\Lambda^3V\simeq\operatorname{Alt}^3(V^*,\mathbf C)` を作り、
`NcCubic.Trivector` と外積の対応を証明する。$`P^{ija}=P(dz_i,dz_j,dz_a)` と置き、
縮約の規約を

$$`q^{ij}=\sum_aP^{ija}F_a,\qquad \{f,g\}=\sum_{i,j}q^{ij}(\partial_i f)(\partial_j g)`

とする。これは `contractionCoefficients` と `bracketFromCoefficients` の定義に一致する。
括弧の双線形性・反対称性・両側 Leibniz 則、および $`\{F,g\}=0` を示す。

基底 $`b=(b_j)` に対する代入 $`z_i=\sum_j(b_j)_iy_j` が `polynomialInBasis` である。
この代入が代数同型を定め、微分の連鎖律と括弧の変換則を満たすことを証明する。
`HasBlockTrivector` の行列式による等式は、任意の三つの共変ベクトルに対する等式であり、
volume trivector の和と同値でなければならない。
:::

:::proof "P0"
外積と交代写像の同型、行列式の契約、可逆な基底代入、偏微分の連鎖律、任意Pの括弧の共変性を検証済み。
:::

証明設計：標準基底と双対基底による交代多重線形写像の外延性から始める。
三変数で $`P=e_1\wedge e_2\wedge e_3` のとき
$`\{z_1,z_2\}=F_3`、$`\{z_2,z_3\}=F_1`、$`\{z_3,z_1\}=F_2`
となる符号を先に固定する。$`F` は代入で変換し、$`P` は基底ベクトルの外積で変換する。
両者に同じ座標行列を機械的に掛ける実装にしない。

受入条件：定義のコンパイルに加え、外積との比較、縮約、可逆な基底変換、
括弧の共変性までを定理として検証する。ファイル候補は `NcCubic/Coordinates.lean`。

# 三次式の微分
%%%
tag := "cubic-differential"
%%%

:::lemma_ "P1" (lean := "NcCubic.CubicDifferential.hessian_gradient")
$`F\in S_3` に対して $`F_i\in S_2`、$`F_{ij}\in S_1`、
$`F_{ij}=F_{ji}`、$`\sum_i z_iF_i=3F` が成り立つ。
対称双線形形式

$$`H_p(v,w)=\sum_{i,j}F_{ij}(p)v_iw_j`

を定めると、$`p\mapsto H_p` は線形であり、

$$`H_p(w,w)=2\,dF_w(p)`

が任意の $`p,w\in V` について成り立つ。
:::

:::proof "P1"
`NcCubic/CubicDifferential.lean` で検証済み。二階偏微分が一次式であることを使い、
一次式の評価と二次偏微分へのEuler等式からHessian恒等式を導く。
双線形形式と点に関する線形写像も構成した。
:::

偏微分の交換と斉次次数の公式を使う。
係数2・3は標数0により可逆である。既存 API の入口は
`MvPolynomial.pderiv_comm`、`coeff_pderiv`、
`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`。
零多項式も斉次式であることを許し、偏微分が非零であるとは仮定しない。
ファイル候補は `NcCubic/CubicDifferential.lean`。

:::lemma_ "P2" (uses := "P1") (lean := "NcCubic.GradientRegularity.cubic_linear_syzygy_zero")
$`F` が `HasIsolatedGradientZero` を満たすならば、
gradient列のKoszul複体は大域的に第1ホモロジーが消え、特に

$$`\sum_i a_iF_i=0,\qquad \deg a_i\leq1\quad\Longrightarrow\quad a_i=0\ (\forall i)`

が成り立つ。定数係数の場合も含め、未証明の正則性を追加仮定として残さない。
:::

:::proof "P2"
`NcCubic.GradientRegularity.cubic_linear_syzygy_zero` で検証済み。
零点条件から商環のKrull次元0を得て、局所Cohen–Macaulay正則性を適用し、
KoszulのH₁完全性を局所化から大域へ貼り合わせる。次数比較で結論する。
この証明経路は大域正則列そのものを別途証明する必要がなく、分類目標を弱めない。
:::

原論文の経路：gradient ideal $`I=(F_1,\ldots,F_N)` の零点集合が原点だけなので、
Nullstellensatz から $`\sqrt I=(z_1,\ldots,z_N)`、従って高さ $`N` を得る。
多項式環の Cohen–Macaulay 性と次元を使って正則性を導く。
局所環の定理を使う場合は、局所化から大域の斉次列へ戻す比較も証明する。
Koszul の第1関係は $`F_je_i-F_ie_j` で生成され、その成分は次数2である。
関係式の次数0・1の斉次成分を取り出せば、低次数 syzygy が消える。
生成関係の次数だけを述べて、大域的な関係の生成や斉次成分への射影を省略しない。

`integrations/stacks` の検証済みアダプターは「正則列なら Koszul 関係で生成される」
という条件付きの一般結果である。今回の本体実装はその先の局所CM判定・H₁の貼り合わせ・次数比較まで検証した。
単位イデアルを仮定する定理は $`I` に適用できない。
ファイル候補は `NcCubic/GradientSyzygy.lean`。

# Jacobi の線形化
%%%
tag := "jacobi-hessian"
%%%

:::lemma_ "P3" (uses := "P0, P1, P2") (lean := "NcCubic.CubicJacobi.jacobi_iff_hessians_compatible")
$`\gamma(P(\alpha,\beta))=P(\alpha,\beta,\gamma)` で $`P(\alpha,\beta)\in V` を定め、
$`K(P)\subset\operatorname{Sym}^2 V^*` を次の等式で定義する：

$$`H(P(\alpha,\beta),P(\gamma,\eta))+H(P(\beta,\gamma),P(\alpha,\eta))+H(P(\gamma,\alpha),P(\beta,\eta))=0.`

全ての $`\alpha,\beta,\gamma,\eta\in V^*` についての条件である。
滑らかさの gradient 条件の下で、$`q=\iota_{dF}P` による全多項式上の
Jacobi 恒等式は、$`H_p\in K(P)` が全 $`p\in V` で成り立つことと同値である。
:::

:::proof "P3"
`NcCubic.CubicJacobi.jacobi_iff_hessians_compatible` で検証済み。
全多項式Jacobi、符号付きの座標展開、全共変ベクトルの互換性を、
証明済みP2を使って接続した。追加のsyzygy仮定は残さない。
:::

まず反対称な二重導分の Jacobiator が各引数で導分になることを示す。
従って座標生成元での Jacobi と全多項式上の Jacobi が同値になる。
規約を $`J^{ijk}=\{z_i,\{z_j,z_k\}\}+\mathrm{cyc}` とすると、正確な展開は

$$`J^{ijk}=\sum_aF_aL_a^{ijk},\qquad L_a^{ijk}=\sum_{r,b}(P^{ira}P^{jkb}+P^{jra}P^{kib}+P^{kra}P^{ijb})F_{br}.`

各 $`L_a^{ijk}` は一次斉次式なので P2 により消える。
$`K(P)` の左辺に $`(dz_i,dz_j,dz_k,dz_a)` を入れた値は、
Hessian の対称性と $`P` の交代性によって $`-L_a^{ijk}(p)` に等しい。
多重線形性で任意の共変ベクトルへ拡張する。逆方向では syzygy 消滅を必要としない。
多項式の恒等的消滅と全点での消滅の比較には、複素数体が無限体であることを使う。
ファイル候補は `NcCubic/HessianCompatibility.lean`。

:::lemma_ "P4" (uses := "P1") (lean := "NcCubic.CubicDifferential.hessian_basepoint_free")
$`F` が `HasIsolatedGradientZero` を満たすならば、Hessian の線形系は基点自由である：

$$`w\ne0\quad\Longrightarrow\quad\exists p\in V,\ H_p(w,w)\ne0.`
:::

:::proof "P4"
`NcCubic.CubicDifferential.hessian_basepoint_free` と
`hessian_range_basepoint_free` で検証済み。追加の正則列仮定はない。
:::

全ての $`p` で値が0なら P1 により $`dF_w=0` であり、gradient 条件から
$`w=0`。構成的には非零な偏微分 $`F_i(w)` を一つ選び $`p=e_i` とすればよい。
この課題は P2・Jacobi・Lie 理論を待たずに実装できる。

# 多項式の分解と逆構成
%%%
tag := "polynomial-blocks"
%%%

:::lemma_ "P5" (uses := "P0, P1, P3, L2") (lean := "NcCubic.BlockHessian.hasBlockNormalForm_of_compatible")
$`P` の三次元直和分解に適合する座標を取り、$`k\ge1` とする。
全 Hessian が $`K(P)` に属せば、異なる active ブロック $`s\ne t` に対して
$`\partial_{x_{si}}\partial_{x_{tj}}F=0` となる。従って

$$`F=\sum_{s=1}^k f_s(x_s,u),\qquad f_s\in\mathbf C[x_{s1},x_{s2},x_{s3},u_1,\ldots,u_m]_3.`
:::

:::proof "P5"
`PolynomialBlocks.lean` と `BlockHessian.lean` で検証済み。ブロックtrivectorの等式を明示的な入力とし、その存在はL5をAで適用して得る。従ってこの一般補題自体の証明依存からL5を外した。
:::

証明設計：正規化された各三次元 volume の双対基底から二つずつ共変ベクトルを取り、
$`K(P)` の式に代入する。交差縮約は0なので、異なるブロックの任意の基底ベクトル間の
Hessian 値が0になる。これは L2 の可換因子間の消滅と同じ計算であり、
L5 の出力に Lie イデアルの証拠を残さずに、trivector の等式だけから実装できる。
原論文どおり Lie 括弧を使う場合は、各完全イデアルが括弧の span であることを使って
L2 の条件付き計算をイデアル全体へ拡張する必要がある。

混合二階偏微分が0なら、二つの異なる active ブロックにまたがる単項式の係数は0。
指数の積が標数0で非零であることを確認する。
残った各単項式をその唯一の active ブロックへ、中心変数のみの単項式を block 0 へ割り当てる。
$`k\ge1` は最後の配分に必要で、$`m=0` も許す。配分は一意性を主張しない。
ファイル候補は `NcCubic/PolynomialBlocks.lean`。

:::theorem "P6a" (lean := "NcCubic.Jacobian.jacobi")
任意の可換係数環上で、異なる三変数 $`x_1,x_2,x_3` と任意の potential $`f` に対し、

$$`\{g,h\}_f=f_{x_1}(g_{x_2}h_{x_3}-g_{x_3}h_{x_2})+f_{x_2}(g_{x_3}h_{x_1}-g_{x_1}h_{x_3})+f_{x_3}(g_{x_1}h_{x_2}-g_{x_2}h_{x_1})`

は全多項式について Jacobi を満たす。反対称性、Leibniz 則、potential の Casimir 性、
他の変数の中心性も成立する。potential の斉次性・滑らかさは不要である。
:::

:::proof "P6a"
`NcCubic/Jacobian.lean` で偏微分を展開し、混合偏微分の交換と環の恒等式に帰着して検証済み。
`NcCubic.Jacobian.jacobi` は座標生成元だけでなく全多項式を量化する。
関連する9定理の一覧と検証状態は task register および `docs/STATUS.md` を参照する。
:::

:::lemma_ "P6b" (uses := "P6a, P0") (lean := "NcCubic.normalForm_satisfiesJacobi")
互いに素な active 三変数組と共通の中心変数 $`u` に対し、
$`f_s\in\mathbf C[x_s,u]` の Jacobian 括弧の和は Poisson 括弧である。
P0 の線形座標変換により移した括弧も Jacobi を満たす。
:::

:::proof "P6b"
`JacobianBlocks.lean` と `BlockContraction.lean` で共有中心を許す全多項式Jacobi、縮約係数との一致、可逆な座標変換、正規形からの逆構成を検証済み。
:::

証明設計：各括弧は別ブロックの potential の active 偏微分を0にする。
異なる二ブロックの交差 Jacobiator は、三重導分として座標上で検査すれば0になる。
中心変数を共有するため「変数集合が全て互いに素」とは仮定しない。
和の Jacobi、共通中心の中心性、$`\sum_s f_s` の Casimir 性を示し、
`contractionCoefficients` が与える括弧と一致させる。
ファイル候補は `NcCubic/JacobianBlocks.lean`。
