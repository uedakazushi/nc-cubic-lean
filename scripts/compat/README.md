# この初期検証環境に固有のprocfs互換処理

通常のLinux/macOS環境ではこの処理は不要であり、bootstrapは自動で有効化しない。

初期検証に使った管理された実行環境では、`getpid()` の番号とprocfsの数値PIDが
同じnamespaceを指さなかった。公式Lean 4.35.0の `src/runtime/io.cpp` にある
`lean_io_app_path` は `/proc/<getpid()>/exe` を使うため、`failed to locate application`
となる。一方、`/proc/self/exe` はその実行プロセスを正しく指していた。

このソースは、**実行中の自分の数値PIDに一致するexeパスだけ**を `/proc/self/exe` へ
読み替える。その他のreadlink、アクセス制御、ネットワーク、Lean本体や証明kernelを
変更しない。公式配布物のSHA256はdependencies.jsonで検証した。

同じ症状と原因を確認したLinux環境でのみ、次を利用できる。

```bash
bash scripts/compat/run.sh bash scripts/bootstrap.sh
bash scripts/compat/run.sh bash scripts/check.sh
```

Cコンパイラとlibdlを必要とし、生成する共有ライブラリは無視対象の `.tools/compat/`
に置く。標準の環境でこのエラーが出た場合は、まず配布物とパスの破損を調べる。
任意のダウンロード失敗・権限エラーに対する回避策として使わない。

初期版の検証はこの自己パスの互換処理を有効にして行ったことをSTATUSに記載する。
