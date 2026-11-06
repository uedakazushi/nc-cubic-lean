# ライブラリ調査

2026-11-07 / v0.1.0。以下は固定版のソースで確認した利用先である。実際のビルド状態は STATUS.md と integrations/stacks/README.md を参照する。

## 1. 推奨する固定版

| 対象 | 固定する値 | 確認根拠 |
|---|---|---|
| Lean | `leanprover/lean4:v4.35.0` | mathlib と Stacks 双方の固定コミットの `lean-toolchain` を読んだ |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | mathlib の `v4.35.0` tag の ref と Stacks の manifest が一致 |
| AxiomMath/Stacks | `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` | 2026-11-06 の main。コミット名は version bump to v4.35.0 |

固定版の一次資料:

- https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679
- https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/lean-toolchain
- https://github.com/AxiomMath/Stacks/tree/5ed82d14634e8d9576bb844c7bd4e3da66d450e7
- https://raw.githubusercontent.com/AxiomMath/Stacks/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/lean-toolchain
- https://raw.githubusercontent.com/AxiomMath/Stacks/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/lake-manifest.json

注意: Stacks の README はまだ v4.34.0-rc2 と書くが、実際の `lean-toolchain` と `lakefile.toml` は v4.35.0。README の記述でバージョンを選ばない。調査時点の mathlib master は v4.36.0-rc2 であり、この Stacks pin と一致しない。

## 2. 基本方針

証明本体は上記mathlibと固定版Stacksに依存する。StacksはP2の低次数gradient syzygy消滅を実証明するため、必要なCM・Koszulモジュールだけを導入した。独立したAPI検証用package `integrations/stacks` も保持し、同一pinを使う。Versoは引き続き独立した文書packageである。

`import Stacks` または `import StacksFrontier` を基礎ファイルに置かない。公式 README は約 63,000 モジュールの全ビルドに大きな時間・メモリが必要と記し、コンパイル済み Stacks のキャッシュは計画段階としている。`lake exe cache get` で取得するのは Mathlib のキャッシュである。少数のモジュールでも推移的依存は大きくなりうるため、実際の時間・メモリを測ってから通常の検証経路に入れる。

ユーザーの「使えるものは何でも」は数学的基盤の再開発を避ける方針として反映する。利用予定・取得済み・import 成功・対象定理への適用済みを別の状態として管理する。

## 3. mathlib で実際に確認した API

以下は上記固定コミットのソースで宣言と仮定を確認したもの。現在のオンライン docs は master に追随するため、コードの根拠は固定コミットを優先する。

| 目的 | モジュール / API | この論文での用途 |
|---|---|---|
| 多変数偏微分 | `Mathlib.Algebra.MvPolynomial.PDeriv`; `MvPolynomial.pderiv`, `pderiv_mul`, `coeff_pderiv`, `pderiv_comm`, `pderiv_rename`, `pderiv_eq_zero_of_notMem_vars` | q の係数、Jacobiator、混合偏微分消滅、ブロック独立性 |
| 斉次多項式 | `Mathlib.RingTheory.MvPolynomial.Homogeneous`; `MvPolynomial.IsHomogeneous`, `homogeneousComponent`, `IsHomogeneous.coeff_eq_zero` | 三次・二次・一次を区別し、次数の比較を行う |
| Euler 等式 | `Mathlib.RingTheory.MvPolynomial.EulerIdentity`; `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv` | `3F = Σ zᵢFᵢ`、アフィン gradient の唯一の零点 |
| 外積 | `Mathlib.LinearAlgebra.ExteriorPower.Basic`, `.Basis`; `exteriorPower.ιMulti`, `exteriorPower.map` | P、基底変換、直和の各三次元 volume |
| 縮約 | `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction`; `CliffordAlgebra.contractLeft`, `contractLeft_contractLeft`, `contractLeft_comm` | 二次形式 Q=0 で ExteriorAlgebra の縮約として使う。固定次数へ制限する橋渡しは要作成 |
| 正則列 | `Mathlib.RingTheory.Regular.RegularSequence`; `RingTheory.Sequence.IsRegular` と `IsWeaklyRegular` | 局所gradient正則列の受け口。StacksのCM判定・Koszul局所大域接続に実際に適用済み |
| 零点とイデアル | `Mathlib.RingTheory.Nullstellensatz` | smoothness の座標条件から gradient ideal の情報へ |
| Lie 基礎 | `Mathlib.Algebra.Lie.Semisimple.Basic`; `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals` | 補題3.2の根基排除 |
| 不変双線形形式 | `Mathlib.Algebra.Lie.InvariantForm`; `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate` | 非退化不変形式と非零可換イデアルの排除から半単純性 |
| Cartan 判定 | `Mathlib.Algebra.Lie.CartanCriterion`; `LieAlgebra.hasTrivialRadical_iff_isKilling` | 半単純性から Killing form / root theory への橋渡し |
| 既約表現 | `Mathlib.Algebra.Lie.Semisimple.Lemmas`; `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`, `hasTrivialRadical_of_isIrreducible_of_isFaithful` | 根基が既約表現でスカラーに作用する論証の参考。忠実性などの追加仮定を必ず確認する |
| sl₂ 三つ組 | `Mathlib.Algebra.Lie.Sl2`; `IsSl2Triple`, `IsSl2Triple.HasPrimitiveVectorWith`, `HasPrimitiveVectorWith.exists_nat`, `lie_e_pow_succ_toEnd_f` | 補題3.2で H(v,v)=0 を導くベクトルの構成 |
| 根系 | `Mathlib.Algebra.Lie.Weights.RootSystem`; `LieAlgebra.IsKilling.rootSystem`, `exists_mem_rootSpace_lie_ne_zero`, `rootSpace_two_smul` | 階数≥2 の単純因子から最高根の共通零点を作る |
| 単純性と根系 | `Mathlib.Algebra.Lie.Weights.IsSimple`; `LieAlgebra.IsKilling.isSimple_iff_isIrreducible` | 単純 Lie 因子と既約根系を対応させる |

固定ソース URL の形は `https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/` に上記モジュール名の `.` を `/` にしたパスと `.lean` を付ける。

## 4. Stacks の利用先

### 4.1 実装済み：低次数gradient syzygyの消滅

`NcCubic/GradientRegularity.lean` は次の固定版モジュールを直接importする。

| モジュール | 適用した主なAPIと役割 |
|---|---|
| `CohenMacaulay.MvPolynomial` | `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial`：多項式環の各局所化のCM性（tags 0AAI・00ND） |
| `CohenMacaulay.Equidimensional` | `Module.IsMaximalCohenMacaulay.ringKrullDim_quotient_add_length_eq_and_isRegular`：正しい余次元で切る列の局所正則性（tag 00R9。内部で02JNを使用） |
| `Koszul.Regular` | `Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular`：局所正則列からKoszul消滅 |
| `Koszul.Localization` | `Koszul.isH1Regular_of_forall_localization_prime`：局所のH₁消滅を大域へ接続 |
| `Koszul.Relations` | `Koszul.isH1Regular_iff_forall`：syzygyがKoszul関係のspanに入ること |

パスの接頭辞はいずれも `StacksFrontier.RingTheory.`。
実装した論証は次の通りである。

1. `GradientRadical.lean`：孤立gradient零点とNullstellensatzから、gradient idealのradicalが原点の極大イデアルであることを示す。
2. `GradientDimension.lean`：上にある素イデアルがその極大イデアルだけであることから、商のKrull次元0を得る。
3. 多項式環のCM性と00R9を使い、gradient idealを含む各素イデアルで局所正則列を得る。
4. idealを含まない素イデアルでは、生成元の一つが局所化で単元となる。明示的な逆元によるKoszul関係の式でH₁消滅を示す。
5. 局所大域接続で大域H₁消滅を得る。`GradientSyzygy.lean` の次数比較により、次数2の生成元に対する係数全次数≤1のsyzygyは0になる。

結果は `NcCubic.GradientRegularity.cubic_linear_syzygy_zero`。
仮定は三次斉次性と孤立gradient零点であり、gradientの正則性を追加仮定に残さない。
大域正則列そのものや全高次Koszulホモロジーの消滅を別途証明したとは扱わない。
後者を必要とする射影表示G0には追加の議論が残る。
`lake build NcCubic.GradientRegularity` を実行し、主要定理の公理依存が標準3公理のみであることを確認した。

`Koszul.Syzygies` の単位イデアル仮定を、原点を共通零点に持つgradient ideal全体へ誤用しない。
単元の議論は零点集合の外側の局所化でのみ使っている。

### 4.2 射影的な表示・smoothness比較：正確な受け口と未接続部分

以下は固定版ソースの型を確認した段階であり、本プロジェクトへのimport・適用を
検証済みとする一覧ではない。実装済みの座標比較は `NcCubic/Geometry/` に分けている。

- `AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation`
  - `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d` は
    `SerreTwistCohomology R m d` を構成する（tag 01XU）。
  - 射影次元は `m+1`。`degreeZero`、`degreeTop` はそれぞれH⁰・最高次の線形同型。
    `vanishing q` は `q+1 ≠ m+1` のときのH^(q+1)消滅である。
- `AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`
  - `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_twistedHodgeCohomology`
    は `k>0`、`q>0` のときのH^q(Ω^p(k))消滅（tag 0FUK）。
  - `isZero_cohomologySheaf_twistingSheaf` は `-n≤d<0` の線束の全次数消滅を供給する。
  - H⁰(Λ²T(-3))=0とH⁰(Λ³T(-3))≃Λ³Vを、そのまま与える型ではない。
    余接Euler列の双対、外積、twist、必要な射の同定と短完全列の接続が残る。
- `AlgebraicGeometry.ProjectiveChart.HypersurfaceChart`
  - `Stacks.ProjectiveChart.chartQuotientEquiv` の入力は実際の閉埋込み
    `i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)`、
    斉次式 `F`、および `Proj.idealOfClosedSubscheme ... i = Ideal.span {F}`。
  - 結果は `R[Y₁,…,Yₙ]/(dehomCoeff R j F) ≃+* Γ(Z, subschemeChart i j)`。
    `chartPresentation_C` が係数Rとの適合を別に示す。
- `RingTheory.Smooth.JacobianCriterion`
  - `Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem`（tag 00TE）の入力は
    実際の `P : Algebra.Presentation R S ι σ` と、全素イデアルpに対する
    `Nontrivial (p.Fiber S) → ringKrullDim (p.Fiber S) + Nat.card σ = Nat.card ι`。
  - 結果は素イデアルqでの `Algebra.IsSmoothAt R q` と、relations→variablesの埋込みで
    選ぶJacobian minorがqに入らないことの同値。
    射影三次式のsmoothnessとgradient零点条件を直接同一視できるAPIではない。

現在の `Geometry/JacobianCondition.lean` は、三次式の同次座標Jacobian条件と
`HasIsolatedGradientZero` の同値を証明する。これはscheme smoothnessの定義ではない。
`Geometry/AffineChart.lean` は、変数を `σ ⊕ Unit` とした実際のdehomogenization、
評価・偏微分の比較、対応する多項式商環と点評価を構成する。
次はこのdehomogenizationを `dehomCoeff` と比較し、一式関係の具体的presentationと
上の全fibre次元条件を供給する。その後にschemeのsmoothnessと貼り合わせる。
詳しい現在の契約と次の実験は `RESEARCH_NOTES.md` §6 に記載する。

### 4.3 Bertini

`StacksFrontier/AlgebraicGeometry/Variety/Bertini/` と `Morphisms/Fibres/Bertini*` に実コードがある。`BertiniSmooth` の `smooth_specializedDivisor_forGeneral` は非空 open と smooth-locus 条件を仮定する。これだけを引用して「基点自由な任意の二次形式線形系に非退化元がある」が証明済みとしない。

本プロジェクトではこの箇所を最大階数の行列式の議論で置き換え、Bertiniを必須依存にしない。詳細は RESEARCH_NOTES.md §1 を参照。

## 5. Stacks の信頼性・ライセンス・実行状態

公式サイト https://stacks.axiommath.ai/ と README は `StacksCore` を人手で原典との対応まで確認した層、`StacksFrontier` をまだその人手レビューを通過していない層として区別する。両層の証明が kernel-check され、標準公理 `propext`, `Classical.choice`, `Quot.sound` のみを使うというのが提供元の説明である。本調査ではその全ビルドや全宣言の公理監査を独立再実行していない。

このメモで上げた高度な CM/Koszul/射影幾何の候補は主として Frontier。利用を禁止する理由ではないが、使う定理について原典 tag、Lean の実際の型、仮定の不足や結論の弱化がないことを調べ、対象 package でビルドし、`#print axioms` を確認する。

Mathlib と Stacks の Lean コードは Apache-2.0。原典 Stacks Project の本文は GNU FDL。import による依存を優先し、コードを移植する場合には upstream の著作権・ライセンスヘッダーと出典コミットを維持する。原典本文を無断で大量同梱する必要はない。

## 6. 調査で見つからなかった完成品

GitHub code search で mathlib の `PoissonAlgebra` と `Schouten` は該当なし、Stacks の `Poisson` も該当なしだった。検索は不存在の証明ではないが、本件の代数的 Poisson 構造と Schouten 括弧を既製品として import できるとは確認できていない。mathlib の `Poisson` というファイル名には調和解析・確率論が含まれ、本件とは別物である。

補題3.2の「K(P) が基点自由なら P が三次元 volume の直和になる」という結論、必要な最高ウェイトベクトルの選択、階数1単純因子の三次元性を一つで供給するライブラリも確認できなかった。Mathlib の Lie/root/sl₂ API を組み合わせるべきで、外部定理の名を `axiom` として置くべきではない。

他の Lean ライブラリについても検索したが、本件で mathlib + Stacks より直接的な実コードを追加する根拠は得られなかった。検索だけの段階で PhysLean・SciLean 等を依存へ加えることは推奨しない。

## 7. 検証と導入の実務

1. 固定 mathlib で小さい polynomial kernel を動かす。
2. Stacks を固定 hash で取得する別 package / 検証 target を用意する。
3. 最初の Stacks smoke test は `Koszul.Relations` 等一つの必要モジュールと `#check` を含む短いファイルにする。
4. full `import Stacks` を避け、必要なモジュールごとに実際の推移的依存と計算費用を測る。
5. 既知定理を対象の定義へ接続する adapter を `NcCubic/External/Stacks/` 等に置き、upstream 側の語彙を本体へ広げすぎない。
6. 最終定理について `#print axioms` だけでなく、宣言の型が原論文の主張を正しく表すことをレビューする。条件付き wrapper のみで完成扱いしない。
