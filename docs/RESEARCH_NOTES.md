# 研究ノート

2026-11-07 / v0.1.0。現時点で有効な知識を整理する。Lean検証の状態はSTATUSを参照。

## 1. 非退化な対称形式の存在：Bertiniを不要にする証明

**状態：Leanの `NondegenerateForm.lean` で証明済み。新規性は主張しない。**

無限体 \(K\) 上の有限次元空間 \(E\) と、対称双線形形式の線形部分空間 \(L\) を考える。
任意の \(v\ne0\) に対して、ある \(H\in L\) が \(H(v,v)\ne0\) を満たすと仮定する。
このとき \(L\) は非退化形式を含む。

実際、階数が最大の \(B\in L\) を選び、その階数を \(r\) とする。
退化しているなら \(0\ne v\in\operatorname{rad}B\) を選ぶ。
\(\operatorname{rad}B\) の補空間 \(U\) における制限 \(A=B|_U\) は非退化で
\(\dim U=r\) である。任意の \(H\in L\) に対して、\(U\oplus Kv\) 上の行列を

\[
(B+tH)|_{U\oplus Kv}=
\begin{pmatrix} A+tC&tb\\tb^{\mathsf T}&td\end{pmatrix},\qquad d=H(v,v)
\]

と書く。全ての \(t\in K\) で \(B+tH\in L\) の階数は \(r\) 以下なので、この
\((r+1)\) 次行列の行列式は0。無限体であるため行列式多項式は恒等的に0である。
\(t\) の一次係数は \(\det(A)d\) である。最後の行と列の非対角成分を通る置換項は
少なくとも \(t^2\) を含むからである。\(\det(A)\ne0\) より \(H(v,v)=0\)。
全 \(H\in L\) に対して成立し、基点自由性に矛盾する。

必要なLean補題は、(i) bounded Nat値の階数の最大値、(ii) radicalの補空間での
非退化性、(iii) 制限の階数不等式、(iv) 無限体で全点消滅する多項式の零性、
(v) 上記行列式の一次係数である。Bertiniや射影schemeをこの箇所に導入する必要がない。
この証明自体は対称双線形形式について標数2を排除しないが、本研究の応用は複素数体。

### support上で先に作業する

\(W=\operatorname{span}\{P(\alpha,\beta)\}\) に \(P\) がsupportを持つことを示し、
\(K(P)\) を \(W\) に制限する。その像は基点自由なので上の補題を適用できる。
\(W\) 上でLie構造を作り、\([W,W]=W\)、\(Z(W)=0\) を示せばよい。
最後に \(V\) 内の補空間を中心座標に取る。\(V\) と \(W\) で同時に非退化な形式を
選ぶ一般開集合の議論を省ける。ただしsupport・制限・trivectorの比較は形式化する。

## 2. Lie理論の大きな存在定理から切り出す証拠補題

全ての \(a,b,c,d\) に対して
\[
H([a,b],[c,d])+H([b,c],[a,d])+H([c,a],[b,d])=0 \tag{K}
\]
とする。\(H\) の非退化性や不変性は以下の小補題には必要ない。

**根基を排除する証拠。** \(c\ne0\)、\([h,v]=cv\)、\([e,w]=v\)、
\([e,v]=[v,w]=0\) なら、(K)に \((h,v,e,w)\) を代入して \(cH(v,v)=0\)。
従って \(H(v,v)=0\)。\(v\ne0\) なら基点自由な全形式の族に対してこの証拠は存在できない。

**高階数因子を排除する証拠。** \([a,b]=v\)、\([h,v]=cv\)、
\([a,v]=[b,v]=0\)、\(c\ne0\) なら、(K)に \((a,b,h,v)\) を代入して同じ結論を得る。

**可換な因子。** \([b,c]=[c,a]=0\) なら (K) から
\(H([a,b],[c,d])=0\)。完全イデアルが互いに可換なら、括弧の線形spanを取って
その積全体で \(H\) が消える。最後のspanへの拡張は別の補題である。

初期コードの対応箇所は `NcCubic/LieObstruction.lean`。証拠の存在を示すL3/L4は
ここからは従わない。根基では極小可換イデアル・既約表現上の根基の作用・最高ウェイト、
単純因子では最高根の分解とroot-space bracketの非零性が必要である。

## 3. 使うべき微分・係数の経路

\(q^{ij}=\sum_aP^{ija}F_a\) のJacobiを展開し、\(\sum_aF_aL_a^{ijk}\) とまとめる。
\(L_a^{ijk}\) は一次式なので、滑らかな三次式のgradientが持つ低次数syzygyの消滅が
決定的である。「全点で多項式が零」と「多項式が零」の比較も係数体の仮定を明示する。

異なるactiveブロックの \(i,j\) に対する \(\partial_i\partial_jF=0\) は、
両変数を含む単項式がないことを意味する。対応する係数は \(d_i d_j\) 倍され、
標数0では非零係数を保つ。各単項式を一つのブロックへ割り当て、中心だけの単項式は
block 0へ置く。\(k\ge1\) がこの最後の操作に必要である。

Jacobianブロックの逆構成はsmoothnessを必要としない。
任意のpolynomial potentialに対する括弧の反対称性、Leibniz、Casimir、Jacobiを先に証明し、
中心変数を共有する独立activeブロックの和へ拡張する。

## 4. 既存ライブラリを適用する際の本質的な注意

- Stacksの `Koszul.Syzygies` の一部は単位イデアルを仮定する。原点で消えるgradient
  idealにはそのまま適用できない。`Koszul.Regular` → `Koszul.Relations` が適切な入口。
- `StacksFrontier` のLean証明と、元のStacksの文章との型の一致は別に確認する。
- gradient idealを含む素イデアルでの局所正則性と、大域H₁消滅・低次数syzygy消滅は
  `GradientRegularity.lean` で検証済み。全正次数Koszul消滅は `Geometry/GradedKoszul.lean` で追加証明済み。大域正則列そのものの別証明とは区別する。
- 複素対称双線形形式とHermitian内積を区別する。
- 係数モデルの分類、外積の分類、幾何学的sectionの分類を比較定理なしに同一視しない。
- 数値実験やCASによる確認はLean証明ではない。必要なら証明書を生成して検証する。

## 5. 原論文と文献の確認範囲

原論文§2–3の式と証明経路を読んだ範囲では、具体的な反例や表示式の誤りは見つかって
いない。これは背景定理まで含む独立の完全証明、あるいはLean検証を意味しない。

EtingofのMIT講義ノートで、Proposition 16.9（根基のスカラー作用、印刷p.88）、
§19.4（root decomposition）、Theorem 25.17（最高ウェイト）、§32.2（最高根）の
参照位置を確認した。具体的なroot bracket非零性と階数1の三次元性については、
mathlibの型へ合わせる依存関係をさらに詰める。URL等は `references.bib` に記載する。

## 6. 完成した幾何学的接続

`NcCubic.theorem113 : NcCubic.Geometry.GeometricClassificationStatement` を証明した。
実際の非零大域双ベクトルとその全開集合上の誘導括弧を対象とし、標準表示や比較を入力しない。

### 任意の切断から標準表示へ

1. `CubicAmbientLift` は実際のEuler外積列・twistのコホモロジー消滅と制限列から、
   任意の超曲面上の双ベクトルをambientへ一意に持ち上げる。
   その制限は元の引き戻し・押し出し随伴の単位写像である。
2. `CanonicalEulerLiteralData` は標準twist双対同型と実際のbiproductの包含・射影から
   Euler中央項の同型を構成する。`CanonicalDataRatioAction` はこの同型と元のEuler商の
   合成が持つ比座標への作用を計算する。
3. `ExteriorSiteNativeBridge` は一般のschemeでsite側とnative側の直和・外積を比較する。
   `BufferedExteriorSurjectivity` と `BufferedQuadraticLift` は、元のEuler商のΓ全射性から
   実際の二次切断を直接構成する。
4. `QuadraticProjectiveComparison` は、任意の標準チャートの部分開上で二次係数と括弧を比較する。
   比座標の生成元対での一致から、実際の相対双導分の全開集合上の一致を得る。
5. 実際の引き戻し自然性と超曲面の法線方程式の消滅から係数の可除性を導く。
   Euler補正で水平な二次代表を作り、graded Koszulの高次完全性と次数比較から定数trivectorを得る。
   `GeometricRepresentationCore` がこれらを接続し、`GeometricRepresentation` が実際の標準Euler同型を代入する。
6. 構成した標準表示と括弧の単射性から、元の構成写像の全射性を得る。
   `GeometricRepresentationEquiv` は単射性・線形性と合わせ、元の外積三乗と実際の大域切断の複素線形同型を構成する。

### Jacobiと逆方向

実際の超曲面上の標準括弧がJacobiを満たすことと、勾配縮約が全多項式上でJacobiを満たすことを比較した。
Euler場との外積のF可除性を幾何から導き、斉次商の交代性・divergence・gradient horizontality・
Euler恒等式・定数syzygy消滅を使う代替経路で、可除性を仮定に残さない。

標準外積双対射の行列式公式を計算し、有限局所自由性から実際の同型性を証明した。
Smoothからこの標準同型を供給し、任意の定数trivectorから実際の双ベクトルを構成する。
`GeometricCanonicalDirections` は、標準表示からブロック正規形への方向と、
正規形から非零Poisson切断への方向を接続する。`Completion.lean` が元の最終型を証明する。

### Koszulの数学的範囲

P2は孤立gradient条件からgradient商の次元0を示し、局所Cohen–Macaulay性と正則列を使い、
局所化したKoszul完全性を大域へ戻す。大域正則列そのものは主張しない。
表示に使う高次完全性は `GradedKoszul` と `ExteriorKoszul` で別途供給し、
係数次数の射影から定数preimageを得る。低次数syzygy消滅だけで高次完全性を済ませない。

### 層の比較での型指定

`AlgebraicBivector`・`bivectorSheaf`・`tangentSheaf` の引数には `X := ...`・`S := ...` を明示する。
同じ射影scheme・構造射でも、推論で選ばれるAPIの表記が異なると、Kähler微分や外積の内部で
大きな定義的等式の検証が生じる。直和・外積の境界は一般のscheme上で証明した明示的同型を使う。
構造射の表記を変える場合は、まず射の通常の等式を証明し、`BivectorMorphismCongr` で移送する。
`ProjectiveBivectorTransport` と `ProjectiveAmbientReindex` はこの移送と全開集合上の括弧の保存を実装する。
これらは実際の等式・同型による移送であり、幾何学的な比較を新たな仮定にしない。

### Poisson条件の形式化の範囲

原論文印刷p.2は基礎体をℂとし、p.4のEuler/Koszul論では射影schemeと飽和イデアルを用いる。
本文はholomorphic・解析的カテゴリーと明示していない。現在のSchemeによる型はこの代数的読解に忠実である。
Poisson条件は、実際の双ベクトルの標準的な誘導双導分の全開集合上のJacobi恒等式で定義する。
これは標数0でSchouten自己括弧の消滅と同値になる通常の定義選択である。
別個のSchouten演算やその同値定理、解析的切断・GAGAの比較をLeanで証明したとは主張しない。
G2の受入条件とBlueprintはこの範囲にそろえ、最終型と実際の証明依存は独立レビューした。

### 依存生成物

3 workspaceは固定した同一のroot `.lake/packages` を共有する。
TeX実行系の補完はworkspace内に置き、`docs/TEX_RUNTIME.md` に記録する。
最終検証は `lake build` と `bash scripts/check.sh --complete` による。
