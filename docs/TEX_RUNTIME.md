# この環境の LuaLaTeX 日本語ランタイム

2026-11-12 の用意済み環境は LuaHBTeX 1.18.0 / LaTeX 2024-11-01 を持つが、LuaTeX-ja・日本語フォント・Lua 用パッケージが不足していた。システム領域と HOME は変更せず、この checkout の `work/texmf-user` に公式配布アーカイブを展開した。

実行時:

```sh
export TEXMFHOME=/workspace/nc-cubic-lean/work/texmf-user
export TEXMFVAR=/workspace/nc-cubic-lean/work/texmf-var
export TEXMFCONFIG=/workspace/nc-cubic-lean/work/texmf-config
```

LuaTeX-ja は `https://ftp.math.utah.edu/pub/tex/historic/systems/texlive/2024/tlnet-final/archive/luatexja.tar.xz` の2025年2月版。2026年最新版では古い LaTeX の未宣言 socket エラーとなるため、この互換版を用いる。

その他のアーカイブは `https://mirrors.mit.edu/CTAN/systems/texlive/tlnet/archive/` から取得: `haranoaji`, `luatexbase`, `luaotfload`, `lualibs`, `lua-uni-algos`, `lua-alt-getopt`, `ctablestack`。`work/tex-downloads/` に取得済みファイルを保存。展開時は先頭 `texmf-dist/` を取り除き、`tlpkg/` は省略した。展開スクリプトは `work/extract_tex_archives.py`。

確認済み:

```sh
kpsewhich luatexja.sty
lualatex -interaction=nonstopmode -halt-on-error -output-directory=work work/japanese-smoke.tex
pdftotext work/japanese-smoke.pdf -
```

1ページPDFが生成され、HaranoAjiMincho-Regular.otf を埋め込み、日本語が正しくテキスト抽出された。これはランタイム修復であり、正式な Blueprint 全体のPDFビルド成功を代替するものではない。

Blueprint 全体の直接コンパイルで追加した依存は `sourcecodepro` と `ulem`（上記の現行 CTAN）および `sourcesanspro`・`sourceserifpro`（上記 Utah TL2024-final。現行配布ではパッケージ名が変わり旧名 URL は404）。`memoir` クラスと互換にするため、ワークスペース内の旧版 `luatexja-compat.sty` の `\newcommand\printglossary...` 一行を、現行公式 LuaTeX-ja と同じ `\ifdefined\printglossary\else...\fi` ガードで囲んだ。

2026-11-12 23:07 UTC に生成済み Blueprint TeX を元の wrapper で直接コンパイルし、21ページ・333975バイトの `blueprint/verso/_out/site/pdf/main.pdf` が得られた。日本語のタイトルと本文は抽出可能、HaranoAji と Source Sans フォントを埋め込み。プレーンテキストの Unicode `₁`（2箇所）・`ℂ`（1箇所）の未収録グリフ警告は親エージェントへ報告済み。同じ環境変数で正式な統合 `lake build` も成功し、ライブラリ・監査・HTML・PDFの全段階を通過した。
