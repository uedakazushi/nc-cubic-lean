# 現在の状態

2026-11-07。**アフィン分類Aは証明済み。元の幾何学的定理1.1(3)は未証明。**

`NcCubic.theorem113_affine : NcCubic.AffineClassificationStatement` を証明した。
元からある契約の仮定・量化・結論を変更せず、正方向と逆方向を接続している。
L5と最終アフィン型は独立レビュー済み。

## Leanで検証した範囲

19課題中15課題（P0–P5・P6a・P6b・L0–L5・A）が完了した。
未完了はG0・G1・G2・Tの4課題である。

- P0：外積と交代写像の同型、縮約の符号、Leibniz・反対称性・Casimir性、
  可逆な基底代入・連鎖律・任意Pの括弧の共変性。
- P1・P4：微分の斉次次数、Euler等式、Hessianの対称双線形性・点に関する線形性、
  Hess_F(p)(w,w)=2dF_w(p)、実際のgradient条件からの基点自由性。
- P2：孤立gradient零点からradicalと商環次元0を得て、局所CM正則列、
  Koszulの局所大域接続、次数比較により次数0/1のsyzygyを消去。
  大域正則列そのものや高次Koszul消滅を証明したとはしない。
- P3：全多項式Jacobiと座標条件、符号付き展開、全共変ベクトルのHessian互換性の同値。
  未証明のsyzygy仮定は残さない。
- P5：ブロックtrivectorを明示入力として混合偏微分を消去し、斉次f_sを構成。
  ブロックtrivectorの存在はL5をAで接続する課題である。
- P6a・P6b：中心変数を共有する独立ブロックの全多項式Jacobiと、
  実際のHasBlockNormalFormから縮約括弧がPoissonになる逆方向。
- L0：無限体上の基点自由な対称形式族に非退化元が存在すること。
  非退化制限の次元最大化・行列式pencilで証明し、Bertiniは使わない。
- L1：K(P)から全空間とsupport上で同時非退化なBを選び、実際のLie構造、
  不変性、完全性、中心零、全制限形式族の互換性・基点自由性を構成。
  元のPの復元にはambient Cartan pairingとannihilator比較を使う。
- L2–L4：根基型・最高根型の証拠の実際の存在と障害、可解根基の排除、
  高階数単純因子の排除、階数1の三次元性、有限単純イデアル分解。
- L5：基点自由なK(P)だけから元のPの三次元volume正規形を構成。
  半単純性・分解・非退化性や正規形そのものを追加仮定にしない。
- A：三次斉次性・孤立gradient零点・P非零の元の契約をそのまま証明。

G1の代数部分も `Divergence.lean` で検証した。実際の縮約括弧に対し、
Jacobiatorのdivergence消滅・gradient horizontality・Euler恒等式を示し、
幾何学的分解J=FT+E∧B₂があれば全多項式Jacobiを結論する。
分解の存在そのものは仮定として明示し、G1全体の完成とはしない。

## 幾何学的接続の実装済み補助結果

G0–G2の完成状態は未完了のまま、次を実際の定義に対して追加した。

- `PolynomialRepresentation`・`RepresentationLinearEquiv`：水平な二次双ベクトルと定数trivectorの
  勾配縮約による線形同値。高次Koszul完全性と次数射影により存在・一意性を証明した。
- `TangentRepresentative`・`RepresentativeUniqueness`：接性の係数式からEuler補正を行い、
  代表の独立性を証明。既約性を使わず、多項式環で非零積を消去する。
- `GradedKoszul`・`ExteriorKoszul`：実際のgradientについて全正次数のKoszulホモロジー消滅と
  必要なgraded strandの一意な定数preimage。配列・外積・元のPの係数も符号込みで比較した。
- `ChartCoordinates`・`ChartNormalization`・`ChartPresentation`・`JacobianIdeal`：
  pivotの並べ替え、比座標、実際の一式presentationとJacobian、商環の全素点での偏微分被覆。
- `ConeBracket`・`LocalChartHamiltonian`：実際の商環S/(F)と局所化環の演算、
  比座標Hamiltonianと実際の次数0射影チャート環の括弧係数の一致、次数0環全体の保存。
- `AffineSmoothness`：実際の滑らかなscheme射から、アフィン開集合の切断環の滑らかさを比較。
- `LocalizedBracket`：実際の多項式局所化上の全要素についての括弧、Leibniz・Jacobi・自然性。
- `ProjectivePoisson`・`ProjectiveHypersurfacePoisson`・`ProjectiveOverlap`：
  実際の次数0環と超曲面商環の全要素に対するPoisson括弧、斉次局所化の重なりでの一致。
- `PoissonSheaf`・`PoissonGluing`：実際の構造層上の括弧とHamiltonian導分、
  被覆上の整合する局所Poisson演算の一意な貼り合わせ。
- `KahlerBracket`：双導分から実際の余接外積の双対への標準写像。
  余接加群が有限自由なら実際の接加群外積へ移し、微分の外積上の評価を比較。
- `ChartSmoothness`・`HypersurfacePresentation`・`AffineSmoothnessCover`：
  実際の一式超曲面のfibre次元と全素点でのJacobian判定、孤立gradient条件と
  各チャート代数のSmoothの同値、実際のアフィン開被覆からのscheme Smoothの復元。
- `TangentSheaf`・`ProjectiveBivector`・`TangentNaturality`：実際の相対余接層の双対、
  接層外積の大域切断、開集合上の導分作用と全制限写像との適合性。
- `PolynomialTangent`：係数配列を実際の多項式接加群外積に移し、
  微分の外積上の評価が元の括弧と一致することと配列の一意性を証明。

- `HomogeneousBasicBracket`・`HomogeneousSectionBracket`・`BasisPoissonGluing`・
  `AmbientProjectivePoisson`・`AmbientProjectiveRelative`：全正次数斉次基本開での演算から、
  実際の射影構造層全体へ括弧を一意に貼り合わせ、実際の構造射に対する相対性まで検証。
- `EulerLocalization`・`ProjectiveRepresentative`：Euler場が次数0関数を零に送り、
  Euler場との外積で代表を変えても全ての実際の開集合上で括弧が一致する。
- `EulerJacobiLift`・`HomogeneousDivision`：Euler∧Jacobiatorの各係数がFで割り切れれば、
  商の斉次性・必要な反対称性を回収し、divergenceと勾配独立性から全多項式Jacobiを導く。
  実際の超曲面構造層上のJacobiから可除性を導出し、全多項式Jacobiとの同値まで接続済み。
  双ベクトルから誘導される括弧との比較は別途未完了。符号・N−3の係数・代数補題の範囲は独立レビュー済み。
- `PrincipalSaturation`：異なる二変数から主斉次イデアルの飽和性を証明。
- `LineExteriorEuler`・`PolynomialKahlerBasis`：階数1部分束の外積完全列の標準商写像と、
  実際の多項式代数同型からのKähler基底。射影接束への適用は実装中。
- `BivectorContraction`・`BivectorSheafMap`・`BivectorSheafDesc`：実際の接層上の局所交代縮約と制限適合性、
  外積層全体から接縮約層への標準射、実際の双ベクトル切断から全開集合上の括弧への写像を構成。
  その単射性・逆写像と標準多項式代表との一致は引き続き構成中。

- `ChartComparison`・`CanonicalHypersurface`：実際の閉埋込みの定義イデアルが(F)である場合、
  および標準的なProj商で、scheme Smoothと孤立gradient条件の同値を証明。
- `HypersurfaceGlobalPoisson`・`HypersurfaceGlobalRelative`・`HypersurfaceStandardComparison`：
  超曲面の全開集合上に実際の相対Poisson括弧を構成し、そのJacobiと全多項式Jacobiの同値を証明。
- `ProjectiveCotangentRank`・`ProjectiveTangent`・`ImmersionFaithfulness`：
  実際の射影余接束の有限局所自由性、双対Euler列、滑らかな閉埋込みから誘導される
  双ベクトル大域切断写像の単射性を証明。
- `TwistSumSections`・`EulerTangentAction`：標準biproduct成分によるtwist切断と斉次多項式の同値、
  実際の接束Euler商写像の局所関数への作用を比較。任意の双ベクトルの係数表示は引き続き構成中。
- `AffineCotangentSections`・`AffineLocalHom`・`AffineTangent`：アフィン開上でのみ、実際の
  微分層・内部Homの切断を切断環の微分・Homと比較し、標準の接切断導分写像との一致を証明。

- `HypersurfaceRestrictionSequence`・`HypersurfaceRestrictionSections`・`AmbientBivectorLift`：
  実際の随伴の単位写像を最後の射とする制限完全列から、負twistのH⁰/H¹消滅を仮定した
  一意な大域持上げを構成。滑らかな閉埋込みでは実際の双ベクトルからの持上げの単射性も証明。
  接束外積に対する必要な消滅の適用は引き続き接続中。
- `ProjectiveCohomology`・`TangentEulerResolution`・`ProjectiveTwistDual`：
  負の線束twistと有限直和の全次数コホモロジー消滅、実際の接束Euler外積完全列、
  双対Euler列の中央項とO(1)直和の同型を検証。
- `SheafExteriorFrame`・`ProjectiveExteriorFrame`・`ProjectiveQuadraticSections`：
  元の包含・射影とtwist乗法から標準の二次係数表示を構成し、実際の大域切断と
  二次斉次多項式係数族の線形同値、および明示的な和による再構成を証明。
- `ExteriorUnitGenerators`・`BivectorLocalDescent`・`BivectorEvaluation`：
  実際の外積の生成元と層化の単位写像を比較し、局所的な外積の括弧が導分の行列式になること、
  大域双ベクトルの括弧がその実際の制限切断の評価であることを証明。
- `StructureSheafBiderivation`・`SheafBiderivationPairing`・`SheafBiderivationExterior`：
  相対双導分から実際の余接外積の双対の大域切断を構成。微分層の切断と切断環の微分の
  比較はアフィン開上だけで行い、任意の開集合へは層として貼り合わせる。
- `RepresentativeFaithfulness`・`HypersurfaceBracketFaithfulness`・`StandardPoissonConverse`：
  実際の標準括弧の零性とPの零性の同値、および正規形から非零相対Poisson演算を構成。
  構成した演算を実際の双ベクトルとして復元する比較は引き続き構成中。

`SheafKahler`は各開集合の切断環のKähler微分上の形式を構成する。
任意の開集合で微分層の切断と切断環の微分を同一視したとは主張しない。

実際の射影切断からの係数代表の取得と、接束外積の切断から標準括弧への比較は未完了である。未完了の比較は次節以下に明示する。

## 依存と検証

Lean 4.35.0、mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679、
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7を保持。
P2の実証明に必要なCM/Koszulの個別モジュールだけを主ライブラリへ導入した。
Lakeで再解決したroot/Versoのmanifestには同じ固定Stacksを追加し、既存依存のrevisionは変更しない。

主な検証コマンドはルートの `lake build`。証明ライブラリ、全NcCubic宣言の公理監査、
課題宣言のtheorem確認、Stacksアダプター、Blueprint整合性とHTML生成を要求する。
分類定理の完成判定は `bash scripts/check.sh --complete`。未完了課題がある現在は失敗する。
許容する公理はpropext・Classical.choice・Quot.soundのみで、独自公理や証明穴は使わない。
今回の全体 `lake build` は成功した。189モジュールをビルドし、2410宣言の推移的公理監査、
117件の課題定理の実在・theorem確認、既存Stacksアダプターの監査まで通過した。
Verso検査は `ok: true`・エラー0件。19ノード・34依存辺・15課題の証明済み状態を照合した。
HTML11ページのローカルファイルと全ノードanchorに欠落はなく、181種類の数式をKaTeXで検査した。
上流依存のlinter warningは残る。新規cloneの全依存再取得は未検証である。

HTML生成先は `blueprint/verso/_out/site/html-multi/index.html`。
作業環境では `source scripts/env.sh` と `export XDG_CACHE_HOME=/workspace/.cache` を使う。
procfs互換処理は現在は不要。原論文はpaper/source.jsonのSHA256で照合する。

## 実装中の課題：元の射影幾何への接続

アフィン分類の完成だけでは、任意の幾何学的Poisson切断に適用できない。
G0–G2には次の実際のscheme/sheaf構成が残っている。

1. dehomogenized cubicの一式presentation・fibre次元条件を整え、
   実際の射影超曲面のSmoothと検証済み座標Jacobian条件を比較する。
2. 余接Euler列から接束外積・twistを同定し、コホモロジーと制限列から
   任意の双ベクトル切断の一意なtrivector表示、および消えるJacobiatorの分解を導く。
3. Poisson/Schoutenの幾何学的な定義・射影降下・正則切断と代数的切断の比較を接続する。

Stacksの既存Serre/Hodge計算・HypersurfaceChart・JacobianCriterionは調査済みだが、
これらの比較写像を自動的に供給する定理ではない。座標条件をscheme smoothnessの代替定義にしたり、
未証明の表示を公理にしてTを閉じることはしない。実際の型と次の具体的実験は
RESEARCH_NOTES §6、LIBRARIES §4.2に記載した。最終幾何学的命題の型レビューも未完了。
