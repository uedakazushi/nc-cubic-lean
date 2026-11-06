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

## 依存と検証

Lean 4.35.0、mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679、
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7を保持。
P2の実証明に必要なCM/Koszulの個別モジュールだけを主ライブラリへ導入した。
Lakeで再解決したroot/Versoのmanifestには同じ固定Stacksを追加し、既存依存のrevisionは変更しない。

主な検証コマンドはルートの `lake build`。証明ライブラリ、全NcCubic宣言の公理監査、
課題宣言のtheorem確認、Stacksアダプター、Blueprint整合性とHTML生成を要求する。
分類定理の完成判定は `bash scripts/check.sh --complete`。未完了課題がある現在は失敗する。
許容する公理はpropext・Classical.choice・Quot.soundのみで、独自公理や証明穴は使わない。
今回の全体 `lake build` は成功した。46モジュールをビルドし、517宣言の推移的公理監査、
117件の課題定理の実在・theorem確認、既存Stacksアダプターの監査まで通過した。
Verso検査は `ok: true`・エラー0件。19ノード・34依存辺・15課題の証明済み状態を照合した。
HTML11ページのローカルファイルと全ノードanchorに欠落はなく、181種類の数式をKaTeXで検査した。
上流依存のlinter warningは残る。新規cloneの全依存再取得は未検証である。

HTML生成先は `blueprint/verso/_out/site/html-multi/index.html`。
作業環境では `source scripts/env.sh` と `export XDG_CACHE_HOME=/workspace/.cache` を使う。
procfs互換処理は現在は不要。原論文はpaper/source.jsonのSHA256で照合する。

## 深刻な未解決点：元の射影幾何への接続

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
