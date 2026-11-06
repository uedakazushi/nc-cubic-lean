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

:::lemma_ "L0"
無限体 $`K` 上の有限次元空間 $`E` と、対称双線形形式の線形部分空間 $`\mathcal H` を考える。
任意の $`v\ne0` に対してある $`H\in\mathcal H` が $`H(v,v)\ne0` を満たすならば、
$`\mathcal H` は非退化形式を含む。
:::

証明設計：階数最大の $`B\in\mathcal H` を選び、階数を $`r` とする。
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

:::lemma_ "L1" (uses := "P0, L0")
$`W=\operatorname{span}\{P(\alpha,\beta)\mid\alpha,\beta\in V^*\}` と置く。
$`P\in\Lambda^3W` と、これが最小の support であることを証明する。
$`K(P)` は基点自由と仮定する。その $`W` への制限の像も基点自由なので、
L0 からその像の中に非退化な対称形式 $`B` を選べる。
$`W` 上で

$$`[x,y]=P_W(B^\flat x,B^\flat y),\qquad B^\flat(x)=B(x,-)`

と置くと Lie 括弧になり、$`B` は不変で、
$`[W,W]=W`、$`Z(W)=0` を満たす。
全ての制限形式 $`H` は次の条件を満たす：

$$`H([a,b],[c,d])+H([b,c],[a,d])+H([c,a],[b,d])=0.\tag{K}`
:::

証明設計：有限次元の双対制限 $`V^*\to W^*` の全射性を使い、support と
trivector の制限を比較する。$`B([x,y],z)` は交代三形式なので不変性を得る。
Jacobiator を任意の $`t` と $`B` で対にすると $`B\in K(P_W)` の式になり、
非退化性から Jacobi を得る。$`B^\flat` は同型であり、support の定義により
括弧の span は $`W` 全体。不変性と非退化性から中心はこの span の直交補空間で、従って0。

選んだ $`B` だけでなく、族 $`\{H|_W:H\in K(P)\}` 全体の基点自由性と (K) を保持する。
この方針では先に $`W` 上で作業し、最後に $`V` 内の補空間を選ぶ。
$`V` 上と $`W` 上で同時に非退化な形式を選ぶ追加の開集合の議論は不要。
ファイル候補は `NcCubic/SupportLie.lean`。

# 検証済みの条件付き障害と、残る存在定理
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

:::lemma_ "L3" (uses := "L1, L2")
L1 の有限次元複素 Lie 代数 $`W=[W,W]`、$`Z(W)=0` と、
基点自由な (K) の族に対して、可解根基 $`\mathfrak r` は0である。
具体的には $`\mathfrak r\ne0` から非零の根基型証拠を構成し、L2 と矛盾させる。
:::

証明設計を四段階に分ける。

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

主な未形式化部分は2・3の存在定理と、商・持上げに関する作用の比較である。
忠実表現にしか適用できない定理をそのまま既約加群 $`I` に使わない。
持上げた元が $`W` 自体で厳密な三つ組の関係を満たすとは仮定しない。
一般の Levi 分解を証明せずに商から持ち上げる経路を優先する。
ファイル候補は `NcCubic/RadicalWitness.lean`。

:::lemma_ "L4" (uses := "L3, L2")
$`W` は単純イデアルの直和に分解し、全ての単純因子は三次元、すなわち $`\mathfrak{sl}_2` 型である。
:::

証明設計：半単純性から有限個の単純イデアルへの分解を得る。
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

:::theorem "L5" (uses := "L4")
基点自由な $`K(P)` に対し、直和をなす三次元部分空間 $`W_s` と
$`0\ne P_s\in\Lambda^3W_s` が存在し、$`P=\sum_sP_s`。
$`P\ne0` なら $`k\ge1`、$`V` 内の補空間の次元を $`m` として $`N=3k+m`。
各 $`W_s` の基底を選び直して、全 volume 係数を1にできる。
:::

証明設計：異なる単純イデアルは $`B` に関して直交する。
実際 $`x=[a,b]` と別因子の $`y` に対して $`B(x,y)=B(a,[b,y])=0`。
各因子への $`B` の制限は、全体の非退化性と直交直和から非退化になる。
従って Cartan 三形式 $`B([x,y],z)` は各因子上の三形式の和。
$`B^\flat` で添字を戻し、元の $`P` との等式を任意の共変ベクトルで確認する。
因子の括弧が非零で $`B` の制限も非退化なので各 $`P_s` は非零。
三次元外積の基底に対する係数を $`c_s\ne0` とし、基底ベクトル一つを $`c_s` 倍して正規化する。
複素数の立方根の選択は不要である。
ファイル候補は `NcCubic/TrivectorBlocks.lean`。
