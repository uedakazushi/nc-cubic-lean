import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "対称双線形形式と Lie 理論による分解" =>
%%%
tag := "lie-theory"
file := "lie-theory"
htmlSplit := .never
%%%

原論文の補題3.2（印刷 pp.6–7）を独立した代数命題として実装する。
有限次元複素ベクトル空間 $`V` と $`P\in\Lambda^3V` に対し、
$`K(P)` が基点自由なら $`P` は直和をなす三次元空間の volume trivector の和である。
$`P=0` なら空和、非零なら少なくとも一つのブロックを得る。
この章の L0–L5 は一般の $`P` に対する補題群なので、P3・P4 には直接依存しない。
アフィン分類 A で Hessian の族に適用するときに P3・P4 を使う。

ここでの形式は複素双線形である。Hermitian 形式や `InnerProductSpace ℂ V` で代用しない。
非退化不変形式を持つ Lie 代数にも可解な例があり、その仮定だけで半単純性を結論しない。

# 基点自由性から非退化形式へ
%%%
tag := "nondegenerate-form"
%%%

:::lemma_ "L0" (lean := "NcCubic.NondegenerateForm.exists_nondegenerate")
無限体 $`K` 上の有限次元空間 $`E` と、対称双線形形式の線形部分空間 $`\mathcal H` を考える。
任意の $`v\ne0` に対してある $`H\in\mathcal H` が $`H(v,v)\ne0` を満たすならば、
$`\mathcal H` は非退化形式を含む。
:::

:::proof "L0"
`NcCubic.NondegenerateForm.exists_nondegenerate` で検証済み。
非退化制限の次元を最大化し、直交補空間内の非零ベクトルと
行列式pencilの一次係数による拡張で矛盾を得る。零次元も含む。
:::

数学的な方針：階数最大の $`B\in\mathcal H` を選び、階数を $`r` とする。
退化していれば $`0\ne v\in\operatorname{rad}B` を取り、radical の補空間 $`U` に制限する。
$`A=B|_U` は非退化で $`\dim U=r`。任意の $`H\in\mathcal H` に対し

$$`(B+tH)|_{U\oplus Kv}=\begin{pmatrix}A+tC&tb\\tb^{\mathsf T}&td\end{pmatrix},\qquad d=H(v,v).`

全 $`t\in K` で階数は $`r` 以下なので、この行列式多項式は恒等的に0。
一次係数は $`\det(A)d`、従って $`H(v,v)=0` となり基点自由性に矛盾する。
形式化は、階数の最大元、radical の補空間、制限の階数不等式、
行列式の一次係数、無限体上の多項式恒等式の五補題に分ける。
零次元では零形式が非退化である場合も含める。
一般の Bertini を必須依存にする必要はない。詳しい論証は `docs/RESEARCH_NOTES.md` §1。
ファイル候補は `NcCubic/NondegenerateForm.lean`。

# support 上の Lie 代数
%%%
tag := "support-lie"
%%%

:::lemma_ "L1" (uses := "P0, L0") (lean := "NcCubic.SupportConstruction.exists_support_lie_data")
$`W=\operatorname{span}\{P(\alpha,\beta)\mid\alpha,\beta\in V^*\}` とする。
基点自由な $`K(P)` から、全空間 $`V` と $`W` 上で同時に非退化な対称形式 $`B` を選べる。
$`[x,y]=P(B^\flat x,B^\flat y)` は $`V` のLie括弧を定め、supportに制限できる。
$`W` 上の不変形式 $`B|_W` は非退化で、$`[W,W]=W`、$`Z(W)=0` が成り立つ。
制限形式の族全体が基点自由で、任意の制限形式 $`H` は

$$`H([a,b],[c,d])+H([b,c],[a,d])+H([c,a],[b,d])=0.\tag{K}`

を満たす。supportをannihilateする共変ベクトルを引数に持つ $`P` は0であり、
support上で一致する共変ベクトルの縮約は一致する。
:::

:::proof "L1"
`SupportConstruction.exists_support_lie_data` で検証済み。
L0を全空間と制限形式の像へ適用し、二つの行列式pencilの積が零でない点を選ぶことで
同時非退化性を得る。$`B([x,y],z)` は交代的なので不変性を持ち、
JacobiatorをBで対にすると(K)になる。Bの非退化性によりJacobiが従う。
$`B^\flat` の全射性とsupportの定義から括弧のspanがWとなり、
不変性から中心はWの直交補空間となる。直交直和でWへ制限して完全性と中心零を得る。
全制限形式の互換性・基点自由性も同時に構成している。
:::

元のPの復元には $`B([x,y],z)=P(B^\flat x,B^\flat y,B^\flat z)` と
annihilator比較を用いる。明示的な外積の部分型 `P_W` を構成する必要はない。
`NondegenerateRestriction.lean`、`SupportLie.lean`、`SupportConstruction.lean` が実装を分担する。

# 条件付き障害から証拠の構成へ
%%%
tag := "lie-witnesses"
%%%

:::lemma_ "L2" (lean := "NcCubic.LieObstruction.no_highest_root_witness")
体上の Lie 代数と双線形形式 $`H` が (K) を満たすとする。
次のどちらの証拠も $`H(v,v)=0` を導く：

* 根基型：$`[h,v]=cv`、$`[e,w]=v`、$`[e,v]=[v,w]=0`、$`c\ne0`。
* 最高根型：$`[a,b]=v`、$`[h,v]=cv`、$`[a,v]=[b,v]=0`、$`c\ne0`。

従って全形式が (K) を満たす基点自由な族に対し、非零の $`v` を持つそのような証拠は存在しない。
また $`[b,c]=[c,a]=0` なら $`H([a,b],[c,d])=0`。
これらには $`H` の対称性・非退化性・不変性を仮定しない。
:::

:::proof "L2"
`NcCubic/LieObstruction.lean` で (K) にそれぞれ
$`(h,v,e,w)`、$`(a,b,h,v)` を代入し、$`cH(v,v)=0` を導いて検証済み。
`radical_witness_isotropic`、`highest_root_witness_isotropic` と
基点自由性との矛盾を述べる二定理、および `cross_bracket_pairing_zero` の計5定理である。
存在定理 L3・L4 と、可換な完全イデアル全体への span による拡張は含まない。
:::

:::lemma_ "L3" (uses := "L1, L2") (lean := "NcCubic.LieObstruction.radical_eq_bot_of_compatible_basepointFree")
L1 の有限次元複素 Lie 代数 $`W=[W,W]`、$`Z(W)=0` と、
基点自由な (K) の族に対して、可解根基 $`\mathfrak r` は0である。
具体的には $`\mathfrak r\ne0` から非零の根基型証拠を構成し、L2 と矛盾させる。
:::

:::proof "L3"
`RadicalWitness.lean`・`PrimitiveWitness.lean`・`RadicalElimination.lean`で検証済み。
極小可換イデアルの作用の忠実像を半単純にし、根基底から非零raising作用を選んで
非零固有値・primitive vectorを構成する。像から持ち上げた元でL2の実際の証拠を得る。
元のWの半単純性を仮定しない。
:::

原論文の設計を四段階に分ける。

1. 根基の導来列の最後の非零項から極小非零 $`W`-イデアル $`I` を取る。
   $`I` は可換で既約な $`W`-加群である。
2. 複素有限次元既約表現上では根基がスカラーで作用する。
   $`W=[W,W]` なので全作用素の trace は0。$`\dim I>0` と標数0から根基の作用は0。
   従って $`I` は半単純商 $`W/\mathfrak r` の既約加群になる。
3. $`Z(W)=0` からこの加群は自明でない。最高ウェイトベクトル $`v\ne0` と
   単純根の三つ組 $`e,f,h` を選ぶ。最高ウェイト値 $`c` は非零自然数の複素数への像である。
4. 商からの任意の持上げを取り $`w=c^{-1}[f,v]` と置く。
   根基の作用が0なので $`[e,w]=v`、$`[e,v]=0`、$`[h,v]=cv`、
   可換性から $`[v,w]=0`。L2 を適用する。

2・3の存在定理と作用の比較は、忠実な作用の像を使う実装経路で検証した。
忠実表現にしか適用できない定理をそのまま既約加群 $`I` に使わない。
持上げた元が $`W` 自体で厳密な三つ組の関係を満たすとは仮定しない。
一般の Levi 分解を証明せずに商から持ち上げる経路を優先する。
ファイル候補は `NcCubic/RadicalWitness.lean`。

:::lemma_ "L4" (uses := "L3, L2") (lean := "NcCubic.SimpleFactorDimension.simple_ideal_finrank_eq_three")
$`W` は単純イデアルの直和に分解し、全ての単純因子は三次元、すなわち $`\mathfrak{sl}_2` 型である。
:::

:::proof "L4"
`RootCombinatorics.lean`・`RootWitness.lean`・`RankOneDimension.lean`・
`SimpleFactorDimension.lean`で検証済み。実際の単純代数からCartanと根基底を選び、
最高高さの根の配置を構成して高階数を排除する。階数0を排除し、階数1の根空間分解から
三次元性を得る。任意の単純イデアルへの形式族の制限も証明した。
:::

半単純性から有限個の単純イデアルへの分解を得る。
階数2以上の因子では最高根 $`\theta` を二つの正根 $`\alpha+\beta` に分け、
根空間の括弧の非零性から $`v=[e_\alpha,e_\beta]\ne0` を作る。
最高根の性質から $`[e_\alpha,v]=[e_\beta,v]=0`、
Cartan 部分代数内で $`\theta(h)=c\ne0` となる $`h` を選ぶ。L2 がこれを排除する。
残る階数1では被約根系が $`\{\alpha,-\alpha\}` であることを示し、
二つの根空間の次元1と Cartan の次元1から全次元3を示す。
最高根の存在、分解可能性、根の加法に対応する括弧の非零性をそれぞれ明示する。
Dynkin 型の全分類を前提にする必要はないが、階数1の次元計算を省略しない。
ファイル候補は `NcCubic/SimpleFactors.lean`。

# 元のテンソルの復元
%%%
tag := "trivector-blocks"
%%%

:::theorem "L5" (uses := "L4") (lean := "NcCubic.TrivectorBlocks.has_block_trivector_of_basepoint_free")
基点自由な $`K(P)` に対し、直和をなす三次元部分空間 $`W_s` と
$`0\ne P_s\in\Lambda^3W_s` が存在し、$`P=\sum_sP_s`。
$`P\ne0` なら $`k\ge1`、$`V` 内の補空間の次元を $`m` として $`N=3k+m`。
各 $`W_s` の基底を選び直して、全 volume 係数を1にできる。
:::

:::proof "L5"
`BlockClassification.lean`で検証済み。実際の半単純supportの有限atom分解と三次元基底を構成し、
直交補空間で全空間へ拡張する。Cartan三形式から元のPを任意の共変ベクトル上で復元し、
非零volume係数を基底の一つのスカラー倍で正規化する。
:::

異なる単純イデアルは $`B` に関して直交する。
実際 $`x=[a,b]` と別因子の $`y` に対して $`B(x,y)=B(a,[b,y])=0`。
各因子への $`B` の制限は、全体の非退化性と直交直和から非退化になる。
従って Cartan 三形式 $`B([x,y],z)` は各因子上の三形式の和。
$`B^\flat` で添字を戻し、元の $`P` との等式を任意の共変ベクトルで確認する。
因子の括弧が非零で $`B` の制限も非退化なので各 $`P_s` は非零。
三次元外積の基底に対する係数を $`c_s\ne0` とし、基底ベクトル一つを $`c_s` 倍して正規化する。
複素数の立方根の選択は不要である。
ファイル候補は `NcCubic/TrivectorBlocks.lean`。
