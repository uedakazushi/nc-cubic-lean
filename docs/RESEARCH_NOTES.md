# 研究ノート

2026-11-07 / v0.1.0。現時点で有効な知識を整理する。Lean検証の状態はSTATUSを参照。

## 1. 非退化な対称形式の存在：Bertiniを不要にする証明

**状態：通常の数学として証明を検討済み。Leanでは未証明。新規性は主張しない。**

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

## 6. 幾何学的な橋渡しの現在の契約と次の実験

**元のscheme上の任意のPoisson切断の表示G0と双ベクトル・括弧の比較は未完了。**
座標条件を新たにsmoothnessの定義として置き、元の定理を置き換えることはしない。

初期の座標的な入口は次の二つであり、さらに下記の実装を追加した。

- `Geometry/JacobianCondition.lean`：非零同次座標xでF(x)=0ならgradientの一成分が
  非零という条件と、`HasIsolatedGradientZero F` の同値。Eulerの係数3を割る箇所はℂ上。
  pivot座標x_i≠0のchartでは、非pivot偏微分だけの非零性と同値である。
- `Geometry/AffineChart.lean`：変数を `σ ⊕ Unit` とし、右側の一変数を1にする
  `dehomogenize`、正規化された `lift`、その多項式商環 `CoordinateRing` と点評価写像。
  評価・非pivot偏微分がこの代入と交換することを証明した。
  斉次式の零点ではEuler等式によりpivot偏微分も回復し、両方のJacobian条件が一致する。

### G2の実際のschemeとの比較

固定版Stacksの `ProjectiveChart.HypersurfaceChart.chartQuotientEquiv` は、実際の閉埋込み
`i : Z ⟶ Proj ...` と `Proj.idealOfClosedSubscheme ... i = Ideal.span {F}` から、
chartの切断環と `R[Y]/(dehomCoeff R j F)` の環同型を供給する。
そのため幾何学的データはscheme Z・閉埋込みi・その斉次イデアルの等式で持てる。
任意のsectionがtrivectorで表せるという結論を、このデータの仮定に含めない。

`ChartComparison` はpivotの並べ替え、dehomogenizeとの一致、一式presentation、
全素点のfibre次元とJacobian判定を実装し、実際のscheme smoothnessと
`HasIsolatedGradientZero F` の同値を証明した。`CanonicalHypersurface` は標準の
Proj商の定義イデアルが(F)に一致することを飽和性で証明し、同じ同値を適用する。
座標条件をschemeのsmoothnessの定義として採用したものではない。

### G0でまだ必要な切断と接束の構成

`SerreComputation.serreTwistCohomology`（01XU）は線束O(d)の各次数のコホモロジーを
計算し、`ProjectiveSpaceHodgeCohomology`（0FUK）は余接外積Ω^pのHodgeコホモロジーを
計算する。後者の正twist消滅はq>0の結論であり、H⁰(Λ²T(-3))=0を直接与えない。
原論文補題2.2に必要な双対Euler列、接束の外積・twistと短完全列の具体的な射、
H⁰(Λ³T(-3))≃Λ³Vの同型を構成して、既存の線束計算を適用する必要がある。
実際の双対Euler列、有限局所自由な加群の超曲面制限列は検証済み。制限列の最後の射は
元の閉埋込みのpullback-pushforward随伴の単位写像そのものである。
コホモロジー消滅の適用と、実際の切断から接性の係数式を得る比較を接続中。
G0が使う高次のgraded Koszul完全性は、今回 `Geometry/GradedKoszul.lean` と
`ExteriorKoszul.lean` で証明した。配列から定数Pへの一意な表示は
`PolynomialRepresentation.lean`、勾配縮約そのものによる線形同値は
`RepresentationLinearEquiv.lean` にある。実際の切断から配列を取得する段階は未完了。

### P2の数学的な型の確認

`cubic_linear_syzygy_zero` は代数閉体K、N個の変数、N個のgradient成分についての定理。
CM切断判定に渡す商次元は0、列の長さと多項式環の次元はいずれもNなので、必要な
次元等式は実際の型から成立する。idealを含まない素イデアルでは単元生成元を使い、
idealを含む場合だけ局所正則列を使う。gradient ideal全体を単位イデアルとは仮定しない。
次数比較は全次数≤1の非斉次係数も扱い、Jacobiatorの一次斉次係数を特に含む。
結論を仮定するtypeclassや未知の正則性を引数に持たず、ℂ上の元のアフィン仮定へ適用できる。
これは元の射影smoothnessとの比較を証明したことにはならない。

### 接性・一意性の現在の実装経路

`TangentRepresentative.lean` は、実際の二次skew配列Bと接性の係数式
ΣᵢBⁱʲFᵢ=FAʲ+hXʲから、q=B−(1/3)E∧Aを構成し、厳密なgradient水平性と二次斉次性を得る。
この係数式自体をschemeの接性から得る比較は別途必要である。
`RepresentativeUniqueness.lean` では3FZ=Z(F)Eの成分を交差乗算し、非零3Fを消去してE∧Z=0を得る。
したがって原論文の代表独立性に使われたFの既約性は、この証明経路では不要である。

`ChartPresentation.lean` は一式の実際のAlgebra.Presentationと1×1 Jacobianを構成した。
`JacobianIdeal.lean` はdehomogenized equationと偏微分の単位イデアル生成、商環の全素点での
偏微分被覆を証明した。これらを実際のAlgebra.IsSmoothAtへ接続し、その後Scheme.Smoothと比較する。

`ConeBracket.lean` は実際のS/(F)に括弧とJacobiを降下する。
`LocalChartHamiltonian.lean` は局所化環の比座標の導分と次数0射影チャート環の括弧係数を構成し、
両者の値が一致することを証明した。全次数0環の安定性は `ProjectiveBracketDescent.lean` で追加証明した。
`LocalizedBracket.lean` は局所化環の全要素での実際の括弧とJacobiを構成する。
異なるpivot間の貼り合わせと実際のΛ²T切断との同定は引き続き必要である。

### この準備環境での依存生成物の共有

rootとVersoのmathlib/Stacksのgitコミット一致を確認し、無視対象の.lake/package checkoutを
同一固定版のcheckoutへsymlinkして生成物を共有した。manifestや証明kernelの設定は変更しない。
元のVerso cacheは無視対象work/cache-backupに退避しており、これは環境内の再生成可能なcache処理である。
新規cloneでは通常通り固定manifestから取得する。

### 構造層上の括弧への接続

`PoissonSheaf`は各開集合の実際の構造層切断環上の演算・制限適合性・
交代性・Leibniz則・Jacobiを明示する。`PoissonGluing`は被覆の全ての部分開集合上の
局所演算と重なりでの一致から、構造層の一意な貼り合わせで大域演算を構成する。
基底定数は実際のscheme射からの引き戻しで定義し、相対性も局所判定する。
この一般貼り合わせは、まだ射影チャートの演算が全ての部分開集合へ延長されたことや、
接束外積の切断と比較されたことの代替ではない。

### Jacobi持上げの代替代数経路

`EulerJacobiLift`と`HomogeneousDivision`は、三次Jacobiator Jについて、
Euler場との外積の全係数がFで割り切れることからJ=0を導く。
四重配列Qを一次斉次部分へ射影してE∧J=FQを保ち、Fの非零性から縮約に必要なQの最初の2添字の反対称性を回収する。
閉性・水平性とEuler公式よりδ(E∧J)=N J、i_dF(E∧J)=3FJなのでi_dF Q=3J。
δと勾配縮約の反交換、定数gradient syzygy消滅によりδQ=0、従って(N−3)J=0となる。
この経路はJ=FT+E∧Bの構成を必要としない。`RatioJacobi` は比座標のJacobiator分子を
Euler∧Jと比較し、`ChartJacobiDivisibility` と `LocalizedPrincipalIdeal` は実際の商環での
消滅から局所化の分母を消去する。異なる二つの変数の冪を消去する
`PrincipalSaturation.dvd_of_two_mul`により、既約性なしに大域可除性へ戻す。
`HypersurfaceStandardComparison.polynomialJacobi_iff_hypersurfaceGlobalJacobi` は、
標準代表から構成された全開集合上の括弧について双方向を接続済み。
任意の幾何学的双ベクトルとこの標準括弧の一致は別の未完了の比較であり、G1は未完了とする。

### 最終の幾何学的な型

`Geometry.GeometricClassificationStatement` は未証明の命題定義である。
入力は実際の滑らかな射影三次超曲面の閉埋込みと、相対余接層の双対の二重外積の
非零大域切断であり、表示定理・持上げ・比較定理を仮定に含めない。
結論は実際の全開集合上の括弧の標準表示と `HasBlockNormalForm`、逆方向は
各正規形からの実際の非零双ベクトルの存在である。原論文§1.1・定理1.1(3)との
独立の型レビューで、代数的な分類目標としての忠実性を確認した。

Poisson条件は標準的な標数0の特徴付け、すなわち実際の双ベクトルから誘導される
括弧のJacobi恒等式で記述する。別個のSchouten演算や解析的なカテゴリーの機構を
実装したとは主張しない。実際の双ベクトルと括弧の行列式評価の一致・単射性を
証明してから、この目標を完成した定理として扱う。

### 次に接続する未完了部分

1. 検証済みのEuler外積完全列・twist完全性・負の線束コホモロジーから、
   Λ²T(-3)の実際のH⁰/H¹消滅と、元のEuler商写像の大域切断上の全射性を導く。
   これにより `AmbientBivectorLift` の明示的な消滅仮定を外し、任意の切断を
   `ProjectiveQuadraticSections` の係数表示へ移す。
2. 実際のtwist乗法のcurryとしてO(1)→O(-1)の双対への同型を構成し、局所評価を比較する。
   双対biconeの元の包含・射影を保ったまま、Euler商による切断の括弧と
   `QuadraticRepresentative` の多項式括弧の一致を示す。
   閉埋込みの接性からnormal方向の括弧の消滅を得て、既存の可除性・Euler補正・
   Koszul表示を適用し、任意の幾何学的切断からPを得る。ここはまだ未証明である。
3. `ExteriorRawDual` の標準precomposition写像の同型性と、外積接層からraw determinant
   dualへの標準射を構成し、有限局所自由な場合の検証済みstalk双対性と比較する。
   さらに余接外積の双対からcotangent-to-tangent内部Homへの標準縮約を構成して、
   既存の `bivectorContraction` と一致させる。これが双導分から実際の双ベクトルへの
   逆構成、および双ベクトルから括弧への単射性の残件である。
4. 以上を、実際の標準括弧のJacobiと全多項式Jacobiの同値、証明済みアフィン分類、
   非零性の比較に接続する。`GeometricClassificationStatement` は独立レビュー済みの
   未証明の命題定義であり、`NcCubic.theorem113` はまだ証明されていない。
