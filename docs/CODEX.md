# Codexでの開始・継続

2026-11-07 / v0.1.0。

## 1. 環境を用意する

Codex Cloudの環境作成で `uedakazushi/nc-cubic-lean` を選択する。
環境のセットアップに次を実行させる。

```bash
bash scripts/bootstrap.sh
```

Stacks の大きな Git partial clone が `HTTP 400` で中断された場合は、
固定 SHA に対する `--refetch --no-filter` を使って自動的に一度復旧を試みる。
依存解決以外の失敗はそのまま報告し、プロキシ・認証・TLS設定は変更しない。

準備済み環境を使う通常の作業では次を実行する。

```bash
source scripts/env.sh
bash scripts/check.sh
python3 scripts/next_task.py
```

このリポジトリは環境で実行するファイルを提供する。リポジトリへの保存だけでは
Cloud環境の作成・公開や将来のタスク起動は行われない。
現行の公式手順では、環境を作成し、準備結果を確認してPublish後、その環境で新しい
タスクを開始する。既存の環境設定がある場合はそれを再利用してよい。

公式資料:
- https://learn.chatgpt.com/docs/environments/cloud-environments
- https://learn.chatgpt.com/docs/agent-configuration/agents-md

## 2. 最初の指示

以下を通常のタスクの指示として送る。

> AGENTS.mdとdocs/RESEARCH_PLAN.mdを読み、docs/STATUS.mdとblueprint/tasks.jsonを確認して、
> 定理1.1(3)の形式化を進めてください。まずscripts/check.shで現在の基盤を検証し、
> 依存関係が整った未完了の課題を選んで、定理・証明・検証まで実装してください。
> mathlibとAxiom Stacksの固定版を必要に応じて調べ、独立した課題は並列に進めてください。
> 小さな補題を一つ終えただけで停止せず、実行可能な間は次の課題へ進んでください。
> 原定理の意味を変えず、証明穴や独自公理を導入しないでください。
> 検証済みの区切りでmainへ保存し、現在の方針・未解決箇所・次の着手方法を更新してください。

継続時は「研究方針を読み、現在の未完了課題から続けてください」でよい。
モデル名や実行時間は環境で利用できるものに従う。APIキーや外部の定理証明サービスを
必須にしない。GitHub ActionsやPRを起動する必要もない。

## 3. 制限付きネットワークの候補

実際に使う宛先を環境設定で許可する。GitHubの認証は環境側の接続を使い、tokenを
ソースやログに入れない。初期取得・依存解決で使う主なホストは次のとおり。

| 用途 | ホスト |
|---|---|
| Leanの公式配布入口 | `releases.lean-lang.org` |
| Gitとreleaseへのredirect | `github.com` |
| release asset本体 | `release-assets.githubusercontent.com` |
| API、固定ソース、tarball | `api.github.com`, `raw.githubusercontent.com`, `codeload.github.com` |
| mathlibのキャッシュ | `cache.mathlib.org`, `lakecache.blob.core.windows.net` |
| 数学・ライブラリ調査 | `leanprover-community.github.io`, `stacks.axiommath.ai`, `stacks.math.columbia.edu`, `ocw.mit.edu` |

キャッシュ配布先は固定版の `Cache/Infra.lean` 等と実際の通信先を確認する。
`releases.lean-lang.org` のみ許可しても、redirect先が許可されていなければ取得は失敗する。
403が出たら、失敗した正確なホストを調べ、環境設定を修正・再公開する。
proxyを外す、TLS検証を無効にする、別の経路で制限を回避するといった修復はしない。

## 4. Stacksを使う作業

[独立したStacks package](../integrations/stacks/README.md) を読む。
基本ライブラリのビルドとStacks全体のビルドを結び付けない。
まず正則列からKoszul関係式を得る小さい検証先を使い、実際のgradientへの適用は別に証明する。
importしたというだけで対象定理の証明済み範囲を広げない。

## 5. 終了前の操作

`scripts/check.sh` を実行し、現行STATUSとtask graphを更新する。
未実行の検証を成功扱いしない。通常のfast-forwardでcommit/pushし、変更内容・検証内容・
残る数学的課題を報告する。mainへ新しい変更が来ていた場合は内容を読んで統合する。
force push、履歴破棄、無断の外部通知は行わない。
