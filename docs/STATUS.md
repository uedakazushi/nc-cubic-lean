# 現在の状態

2026-11-13。**原論文の定理1.1(3)の代数的解釈を証明済み。**

`NcCubic.theorem113 : NcCubic.Geometry.GeometricClassificationStatement`
を [Completion.lean](../NcCubic/Completion.lean) で証明した。
滑らかな複素射影三次超曲面上の任意の非零Poisson双ベクトルを対象とし、
ブロック正規形と逆方向をともに結論する。表示・同型・持上げ・比較を追加仮定にしない。
最終型と実際の証明依存は、原論文に対する独立レビューを通過した。

## 証明した範囲

19課題（P0–P5・P6a・P6b・L0–L5・A・G0–G2・T）すべてが完了した。

- 多項式・Lie理論：gradientのKoszul完全性、JacobiとHessian互換性、
  基点自由な形式族からの非退化形式、supportの半単純Lie分解、元のtrivectorの正規化、
  三次式のブロック分解、逆方向のJacobiを証明した。
- アフィン分類：`theorem113_affine : AffineClassificationStatement`。
  Bertiniの代わりに最大階数・行列式pencilを使う。gradientの大域正則列そのものを主張せず、
  局所Cohen–Macaulay性とKoszulの局所大域接続を使う。
- G0：実際のEuler列・twistのコホモロジー消滅からambientへ持ち上げ、
  元のEuler商の大域切断上の全射性から二次切断を得る。
  全開集合上の括弧比較と法線方向の消滅、Euler補正・高次Koszul完全性から定数trivectorを得る。
  `exists_standardRepresentative` は任意の双ベクトルの標準表示の存在を証明する。
- G0の線形同型：`hypersurfaceBivectorEquiv` と
  `hypersurfaceExteriorBivectorEquiv` を構成した。後者の始域は元の外積三乗であり、
  終域は実際の大域双ベクトル切断をその複素係数作用で見た加群である。
  順写像・逆写像の標準表示と全開集合上の括弧の式を証明した。
- G1：超曲面の全開集合上のJacobiからEuler∧Jacobiatorの係数可除性を導き、
  斉次商・divergence・Euler恒等式・定数syzygy消滅から全多項式Jacobiを得る。
  実際の標準括弧について両方向の同値を証明した。
- G2：scheme smoothnessと孤立gradient条件を比較し、次数0チャート環・局所化・超曲面商環の
  括弧を全構造層へ降下した。標準外積双対射の行列式公式と同型性、
  実際の双ベクトルと誘導括弧の相互回収・単射性を証明した。
- T：任意の切断を標準表示し、Jacobi比較からアフィン分類へ適用する。
  逆方向では標準同型を使い、正規形から実際の非零Poisson双ベクトルを構成する。

site側とnative側の直和・外積の比較は、一般のschemeで証明した標準同型を使う。
構造射の表記を変える移送は実際の射の等式による線形移送であり、全開集合上の括弧を保存する。
未証明の表示や比較を隠したtypeclass・oracleは使わない。

## 形式化の範囲

対象は代数的なscheme上の接層外積の大域切断で、Poisson条件は標準的な誘導双導分の
全開集合上のJacobi恒等式で定義する。これは標数0でSchouten自己括弧の消滅と同値になる
通常の定義選択であり、原定理の代数的な分類対象は変更しない。
別個のSchouten演算やその同値定理、解析的切断・GAGA比較のLean実装は主張しない。
量子化・一般階数・退化スキーム・moduliも定理第3項の完成範囲に含めない。

## 検証

最終定理と無条件の標準表示定理は、カーネル検証と推移的公理監査を通過した。
全production宣言の許可公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
`sorry`・独自公理・unsafeな証明手段は使わない。

全体 `lake build` と `bash scripts/check.sh --complete` はともに成功した。
299モジュール・3242宣言の公理監査・127課題宣言チェックを通過した。
Stacksアダプター2宣言の監査、Blueprintの19ノード・34辺・全19証明済み表示、
日本語HTMLとLuaLaTeX PDF（20ページ）の生成も確認した。
再現手順は以下の通り。
固定依存は3 workspaceで同じroot `.lake/packages` を共有する。
作業環境のTeX設定は [TEX_RUNTIME.md](TEX_RUNTIME.md) を参照する。

```bash
source scripts/env.sh
export XDG_CACHE_HOME=/workspace/.cache
lake build
bash scripts/check.sh --complete
```

`lake build` はライブラリ・全宣言監査・課題宣言・固定依存・Stacksアダプター・
BlueprintのHTMLとLuaLaTeX PDFを検証する。
生成先は `blueprint/verso/_out/site/html-multi/index.html` と
`blueprint/verso/_out/site/pdf/main.pdf`。
新規cloneからの全依存再取得は独立には検証していない。
