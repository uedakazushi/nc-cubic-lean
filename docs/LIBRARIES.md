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

初期の必須依存は上記 mathlib とする。係数による Poisson/Jacobi の定義、偏微分、Euler 等式、ブロック型の十分性はそれだけで着手できる。Stacks の固定版を追加できる独立した検証用 package / import target を設け、個々の必要モジュールを導入する。

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
| 正則列 | `Mathlib.RingTheory.Regular.RegularSequence`; `RingTheory.Sequence.IsRegular` と `IsWeaklyRegular` | gradient の正則性の受け口。Cohen–Macaulay/Koszul の適切な結論への接続は Stacks 候補 |
| 零点とイデアル | `Mathlib.RingTheory.Nullstellensatz` | smoothness の座標条件から gradient ideal の情報へ |
| Lie 基礎 | `Mathlib.Algebra.Lie.Semisimple.Basic`; `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals` | 補題3.2の根基排除 |
| 不変双線形形式 | `Mathlib.Algebra.Lie.InvariantForm`; `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate` | 非退化不変形式と非零可換イデアルの排除から半単純性 |
| Cartan 判定 | `Mathlib.Algebra.Lie.CartanCriterion`; `LieAlgebra.hasTrivialRadical_iff_isKilling` | 半単純性から Killing form / root theory への橋渡し |
| 既約表現 | `Mathlib.Algebra.Lie.Semisimple.Lemmas`; `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`, `hasTrivialRadical_of_isIrreducible_of_isFaithful` | 根基が既約表現でスカラーに作用する論証の参考。忠実性などの追加仮定を必ず確認する |
| sl₂ 三つ組 | `Mathlib.Algebra.Lie.Sl2`; `IsSl2Triple`, `IsSl2Triple.HasPrimitiveVectorWith`, `HasPrimitiveVectorWith.exists_nat`, `lie_e_pow_succ_toEnd_f` | 補題3.2で H(v,v)=0 を導くベクトルの構成 |
| 根系 | `Mathlib.Algebra.Lie.Weights.RootSystem`; `LieAlgebra.IsKilling.rootSystem`, `exists_mem_rootSpace_lie_ne_zero`, `rootSpace_two_smul` | 階数≥2 の単純因子から最高根の共通零点を作る |
| 単純性と根系 | `Mathlib.Algebra.Lie.Weights.IsSimple`; `LieAlgebra.IsKilling.isSimple_iff_isIrreducible` | 単純 Lie 因子と既約根系を対応させる |

固定ソース URL の形は `https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/` に上記モジュール名の `.` を `/` にしたパスと `.lean` を付ける。

## 4. Stacks の具体的な利用候補

### 4.1 gradient の正則列と Koszul 関係

これは本プロジェクトで最も直接的な Stacks の利用先である。

1. `StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial`
   - `Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange`
   - `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial`
   - 原典の Stacks tags: `0AAI`, `00ND`。
   - 多項式環とその局所化の Cohen–Macaulay 性。体から出発する特殊化が必要。

2. `StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion`
   - `Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim`
   - 原典 tag `02JN`。
   - Noetherian local CM ring で、極大イデアル内の列が長さだけ次元を下げることと正則性を結ぶ。
   - 論文の大域多項式環へそのまま使えるわけではない。局所化と斉次性のアダプターを証明する。

3. `StacksFrontier.RingTheory.Koszul.Regular`
   - `Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular`
   - mathlib の正則列から Koszul complex の正次数 exactness へ進める。

4. `StacksFrontier.RingTheory.Koszul.Relations`
   - `Koszul.isH1Regular_iff_forall`, `Koszul.isH1Regular_iff_ker_le_relSpan`
   - first syzygy が Koszul relations の span に入ることを得る。
   - 次に `Fᵢ` の次数2と、係数の次数0/1から消滅を結論する部分を自作する。

`Koszul.Syzygies` という名前だけで選ばない。同ファイルの主要定理は生成元が単位イデアルを生成するという仮定を持ち、本件の原点を零点に持つ gradient ideal にそのまま当てはまらない。

### 4.2 射影的な表示と延長

次の個別ソースを確認した。

- `StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness`
  - 名前空間 `Stacks.AlgebraicGeometry.ProjEulerSequence`
  - `shortExact_eulerSequence`, `exists_shortExact_eulerSequence` がある。
  - 定数係数環上の射影空間の相対余接 Euler 列。双対化、外積、twist、H⁰ 計算への接続は別途必要。
- `StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic`
  - `Stacks.ProjectiveCohomology.isIso_cechCohomologyToCohomology_chart`
  - `isZero_Hgroup_of_lt` は射影空間の次元より上の消滅。
  - 論文補題2.2に必要な特定 twist の全コホモロジー消滅とは異なる。
- 同ディレクトリに `CechVanishing`, `TwistSections`, `TwistWeights` があることは確認したが、必要な Bott 型計算が完備しているかまでは未確認。

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
