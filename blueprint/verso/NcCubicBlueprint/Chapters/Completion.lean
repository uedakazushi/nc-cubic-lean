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

原論文の定理1.1(3)を、実際の滑らかな複素射影三次超曲面上の双ベクトル切断について証明した。
アフィン分類Aだけでなく、任意の切断の標準表示G0、Jacobi比較G1、幾何学的比較G2を接続している。
最終型と実際の証明の依存関係は独立レビュー済みである。

# アフィン分類
%%%
tag := "affine-classification"
%%%

:::theorem "A" (uses := "P3, P4, L5, P5, P6b") (lean := "NcCubic.theorem113_affine")
$`N\ge5`、非零三次斉次式 $`F`、孤立gradient零点条件、非零 $`P\in\Lambda^3\mathbf C^N` の下で、
$`\iota_{dF}P` が全多項式上でJacobiを満たすことと、$`F,P` がブロック正規形を持つことは同値である。
:::

:::proof "A"
Hessianのcompatible形式族の基点自由性からL5を適用し、元の $`P` を保持したvolumeブロック分解を得る。
P5で混合偏微分を消して $`F` を分解する。逆方向はP6bと可逆な座標変換による。
基底、$`N=3k+m`、全summandの三次斉次性、任意の共変ベクトルに対する $`P` の等式を含む。
:::

# 任意の射影双ベクトルの表示
%%%
tag := "geometric-bridge"
%%%

:::lemma_ "G0" (uses := "P2, P0") (lean := "NcCubic.Geometry.hypersurfaceExteriorBivectorEquiv_standardRepresentative")
滑らかな複素射影三次超曲面 $`X=V(F)\subset\mathbf P(V)`、$`\dim V\ge5` に対し、
固定した $`F` による複素線形同型
$$`\Lambda^3V\xrightarrow{\sim}H^0(X,\Lambda^2T_X),\qquad P\longmapsto(\iota_{dF}P)|_X`
を構成する。任意の切断は一意な定数trivectorで表される。
:::

:::proof "G0"
実際のEuler列・その外積とtwistのコホモロジー消滅から、任意の切断を周囲へ持ち上げる。
標準twist双対同型によるEuler中央項の同型と、元のEuler商の大域切断上の全射性から二次切断を得る。
site側とnative側の外積は、一般のschemeで証明した標準同型で比較する。

標準Euler写像の比座標への作用を実際に計算し、二次係数から得た括弧と切断の括弧を全開集合上で比較する。
引き戻しの自然性と法線方向の消滅から係数の可除性を得て、Euler補正と高次Koszul完全性から定数 $`P` を構成する。
代表独立性には多項式環での非零積の消去を使い、既約性を追加仮定にしない。

`exists_standardRepresentative` は表示の存在を無条件に証明する。
`hypersurfaceBivectorEquiv` は実際の構成写像の線形性・単射性・全射性から得た同型であり、
`hypersurfaceExteriorBivectorEquiv` は元の外積三乗との比較を合成した同型である。
順写像・逆写像の標準表示と、全開集合上の括弧の式も証明した。
:::

:::lemma_ "G1" (uses := "G0, P2") (lean := "NcCubic.Geometry.polynomialJacobi_iff_hypersurfaceGlobalJacobi")
標準代表 $`q=\iota_{dF}P` の超曲面上の全開集合におけるJacobi恒等式と、
全多項式上のJacobi恒等式は同値である。
:::

:::proof "G1"
実際の構造層上のJacobiから、Euler場と座標Jacobiatorの外積の各係数が $`F` で割り切れることを導く。
斉次商の交代性、divergence消滅、gradient horizontality、Euler恒等式を使ってJacobiatorを消す。
低次数の定数syzygy消滅はP2から供給する。射影Poisson条件からの可除性を入力仮定に残さない。
逆方向は標準括弧の降下による。G0の全開集合上の表示により、任意の実際の双ベクトルにも適用できる。
:::

:::lemma_ "G2" (uses := "G0, P0, P6b") (lean := "NcCubic.Geometry.GeometricConverse.exists_bivector_of_normalForm")
射影的smoothnessと孤立gradient条件、実際の接層外積切断と標準的な誘導双導分を比較する。
標準代表の射影降下、超曲面への制限、座標変換、双ベクトルと誘導括弧の相互回収を接続する。
:::

:::proof "G2"
実際のアフィンpresentationとJacobianの素点被覆から、scheme smoothnessとgradient条件を比較する。
斉次基本開の次数0環、局所化、超曲面商環で括弧を構成し、全開集合へ貼り合わせる。
標準外積双対射の行列式公式を計算し、実際の有限局所自由性から同型性を証明する。
Smooth仮定からこの標準同型を供給し、誘導括弧の回収と単射性を得る。
任意の定数trivectorから実際の双ベクトルを構成し、正規形から非零Poisson切断を得る。

対象は代数的な切断で、Poisson条件は標準の誘導括弧のJacobi恒等式で定義する。
これは標数0でSchouten自己括弧の消滅と同値になる通常の定義の選択である。
別個のSchouten演算やその同値定理、解析的切断・GAGA比較のLean実装は主張しない。
:::

# 元の定理
%%%
tag := "geometric-classification"
%%%

:::theorem "T" (uses := "A, G0, G1, G2") (lean := "NcCubic.theorem113")
滑らかな複素射影三次超曲面 $`X=V(F)\subset\mathbf P(V)`、$`\dim V=N\ge5` 上の任意の非零Poisson双ベクトルは、
正規化された非空の三次元volumeブロックの和に対応する。
適切な基底に対して $`N=3k+m`、$`F=\sum_s f_s(x_s,u)` となり、
各 $`f_s` は三次斉次である。斉次座標のアフィン錐上の表示では、括弧は各active三変数のJacobian括弧となり、異なるactiveブロック間と中心変数との括弧は0である。
逆にこの正規形は実際の非零Poisson双ベクトルを与える。
:::

:::proof "T"
`NcCubic.theorem113 : NcCubic.Geometry.GeometricClassificationStatement`。
任意の実際の双ベクトルにG0を適用し、標準表示からG1・G2でAの仮定を得て正規形へ進む。
逆方向は標準外積双対同型とG2の逆構成による。
最終型は表示・持上げ・同型・比較を追加仮定に含めない。
全開集合上の全切断の括弧の等式を結論し、正方向・逆方向をともに証明した。
:::

最終型と実際の証明依存は、原論文の定理1.1(3)の代数的解釈と独立に照合した。
全production宣言の公理監査と `bash scripts/check.sh --complete` が最終ゲートである。
一般階数、退化スキーム、moduli、量子化は第3項の完成条件に含めない。
