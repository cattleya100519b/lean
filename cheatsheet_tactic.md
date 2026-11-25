# Lean 4 tactic チートシート

Lean 4 の基本 tactic と Mathlib の主要 tactic を、指定された5列で整理する。

特に「理論」については、単に数学のどの分野で使うかではなく、Lean の証明システムのどの層に属し、どの論理・数学的理論を背景としているかを記載する。

まず、分類の前提を押さえておく。

## 1. tactic の位置づけ

Lean の証明は、大きく次の構造になっている。

① Tactic 層

人間が証明手順を記述するための言語

`intro`, `apply`, `rw`, `simp`, `omega` など

証明項を構築

② Term / Proof 層

命題に対応する型と、その型を満たす証明項

`Eq.refl`, `And.intro`, `Nat.rec`, `Exists.intro` など

型検査

③ Kernel 層

証明項が命題の型を満たすか検証

依存型理論・Calculus of Inductive Constructions 系の型理論

ここで重要なのは、tactic 自体が数学的な証明を保証しているわけではないこと。

tactic は証明項を組み立てるためのプログラムであり、最終的な証明の正当性は Kernel が型検査する。

また、tactic の分類には次のような違いがある。

| 分類      | 意味                   |
| ------- | -------------------- |
| 基本論理操作  | 命題の構造に従って証明を構築       |
| 等式操作    | 等式の対称性・推移性・置換などを利用   |
| 簡約・書き換え | 定義展開や等式によって式を変形      |
| 決定手続き   | 特定の論理・数学領域の問題を機械的に判定 |
| 自動証明探索  | 登録された規則などを利用して証明を探索  |

以下では、この分類を踏まえて整理する。

## 2. 基本 tactic（Lean 4 Core）

Mathlib を使わなくても利用できる、証明構築の基本的な tactic。

### 2.1 証明の導入・構築

| tactic        | 由来             | 実行内容                        | 使用例                       | 理論                    |
| ------------- | -------------- | --------------------------- | ------------------------- | --------------------- |
| `intro`       | introduction   | `∀` や `→` の仮定を導入する          | `intro h`                 | 自然演繹。含意導入則・全称導入則      |
| `intros`      | introductions  | 複数の仮定をまとめて導入する              | `intros x h`              | 自然演繹                  |
| `exact`       | exact          | ゴールと型が一致する証明項を与える           | `exact h`                 | Curry–Howard対応。型付け規則  |
| `apply`       | apply          | 定理や仮定を適用し、その前提を新しいゴールにする    | `apply Nat.add_comm`      | 自然演繹。含意除去則            |
| `refine`      | refine         | 未完成部分をプレースホルダーにした証明項を構築する   | `refine ⟨?_, ?_⟩`         | 依存型理論。項構成・型推論         |
| `assumption`  | assumption     | コンテキスト内にゴールと一致する仮定がないか探す    | `assumption`              | 仮定規則（Hypothesis rule） |
| `constructor` | constructor    | 帰納型のコンストラクタを使ってゴールを分解する     | `constructor`             | 帰納型・論理結合子の導入則         |
| `left`        | 左側の選択          | `P ∨ Q` の左側を証明する            | `left`                    | 選言導入則                 |
| `right`       | 右側の選択          | `P ∨ Q` の右側を証明する            | `right`                   | 選言導入則                 |
| `use`         | use（使用する）      | 存在命題の証人を指定する                | `use 5`                   | 存在量化の導入則              |
| `have`        | have（持つ）       | 中間命題を導入し、その証明を構築する          | `have h : P := by ...`    | 自然演繹。補題導入             |
| `let`         | let（定義する）      | ローカルな定義・変数を導入する             | `let x := 5`              | 依存型理論。局所定義            |
| `suffices`    | suffice（十分である） | まず十分条件を証明し、それを使って元のゴールを証明する | `suffices h : P from ...` | 自然演繹。推論の逆向き構成         |
| `show`        | show（示す）       | 現在のゴールを指定した型として明示する         | `show P`                  | 型検査・型の定義的等価性          |

### 2.2 仮定・場合分け・帰納法

| tactic          | 由来                      | 実行内容                   | 使用例                    | 理論                      |
| --------------- | ----------------------- | ---------------------- | ---------------------- | ----------------------- |
| `cases`         | cases（場合分け）             | 帰納型のコンストラクタごとに場合分けする   | `cases h`              | 帰納型の除去規則                |
| `rcases`        | rcases（recursive cases） | 仮定を再帰的に分解する            | `rcases h with ⟨a, b⟩` | 帰納型の除去規則・パターンマッチ        |
| `obtain`        | obtain（得る）              | 仮定から必要な要素を取り出す         | `obtain ⟨x, hx⟩ := h`  | 存在量化・帰納型の除去規則           |
| `induction`     | induction（帰納法）          | 帰納法の基底ケースと帰納ステップに分解する  | `induction n with`     | Peano 算術・帰納型の帰納原理       |
| `by_cases`      | by cases（場合分けによって）      | 命題 `P` と `¬ P` に場合分けする | `by_cases h : n = 0`   | 排中律・古典論理                |
| `by_contra`     | by contradiction        | ゴールの否定を仮定して矛盾を導く       | `by_contra h`          | 背理法・古典論理                |
| `contradiction` | contradiction（矛盾）       | コンテキスト内の矛盾を探してゴールを解決する | `contradiction`        | 矛盾律・爆発律                 |
| `exfalso`       | ex falso（偽から）           | ゴールを `False` に変更する     | `exfalso`              | 爆発律（Ex falso quodlibet） |
| `subst`         | substitute              | 等式を使って変数を置換する          | `subst x`              | 等号の置換・等式推論              |
| `revert`        | revert（元に戻す）            | ローカル変数・仮定をゴール側に戻す      | `revert h`             | 量化子・含意導入                |
| `clear`         | clear（取り除く）             | 不要な仮定をコンテキストから削除する     | `clear h`              | 証明状態の操作                 |

### 2.3 等式・書き換え・簡約

| tactic   | 由来                          | 実行内容                         | 使用例                             | 理論                        |
| -------- | --------------------------- | ---------------------------- | ------------------------------- | ------------------------- |
| `rfl`    | reflexivity                 | 定義的に等しいことを証明する               | `rfl`                           | 等号の反射律・定義的等価性             |
| `rw`     | rewrite                     | 等式や同値関係を使って式を書き換える           | `rw [h]`                        | 等号の置換規則（Leibniz equality） |
| `simp`   | simplification              | 登録された簡約規則を再帰的に適用する           | `simp`                          | 項書き換え系・簡約理論               |
| `dsimp`  | definitional simplification | 主に定義展開や簡約可能な式を簡約する           | `dsimp [f]`                     | 定義的等価性・β/ι/ζ 簡約           |
| `change` | change（変更する）                | 定義的に等価な型・式にゴールを変更する          | `change x + 0 = x`              | 定義的等価性・変換規則               |
| `calc`   | calculation                 | 複数の等式・不等式を連鎖させる              | `calc a = b := h₁; _ = c := h₂` | 等式推論・推移律                  |
| `congr`  | congruence                  | 等式の両辺に共通する関数・演算を考慮してゴールを分解する | `congr 1`                       | 合同関係・等式の合同性               |
| `funext` | function extensionality     | 関数の入出力ごとの等しさから関数の等しさを証明する    | `funext x`                      | 関数外延性                     |
| `ext`    | extensionality              | 外延性を使って構造体や関数などの等式を分解する      | `ext x`                         | 外延性原理                     |
| `symm`   | symmetry                    | 等式・同値関係の向きを反転する              | `symm`                          | 対称律                       |
| `trans`  | transitivity                | 等式・関係を推移的に接続する               | `trans b`                       | 推移律                       |
| `calc`   | calculation                 | 論理的な推論を段階的に記述する              | `calc a ≤ b := h₁; _ ≤ c := h₂` | 関係の推移律                    |

`rfl` と `rw` と `simp` は特に重要。

- `rfl`：定義を展開すると左右が一致する。
- `rw`：指定した等式を使って一度書き換える。
- `simp`：登録済みの簡約規則を繰り返し適用する。

なお、`rw` は単なる文字列置換ではない。型理論における等号の置換規則に基づいている。

## 3. Mathlib の主要 tactic

ここからは `import Mathlib` などによって利用できる Mathlib の tactic。

Core の基本操作に対して、数学的な特定領域の計算や証明探索を自動化するものが多い。

### 3.1 算術・数値計算

| tactic       | 由来                     | 実行内容                    | 使用例          | 理論                                       |
| ------------ | ---------------------- | ----------------------- | ------------ | ---------------------------------------- |
| `omega`      | Omega（算術決定手続きの名称）      | 自然数・整数などの線形算術を自動的に解く    | `omega`      | Presburger arithmetic（加法を中心とする算術の決定可能理論） |
| `norm_num`   | normalize numbers      | 数値式を計算・正規化して命題を解く       | `norm_num`   | 数値計算・決定手続き                               |
| `norm_cast`  | normalize casts        | 型変換（cast）を正規化する         | `norm_cast`  | 型変換の正規化・等式書き換え                           |
| `positivity` | positivity             | 式が正・非負であることを自動的に証明する    | `positivity` | 順序構造・半環・順序体                              |
| `linarith`   | linear arithmetic      | 仮定に含まれる線形等式・不等式からゴールを導く | `linarith`   | 線形不等式・Fourier–Motzkin 消去法系               |
| `nlinarith`  | nonlinear arithmetic   | 多項式の等式・不等式を利用して証明する     | `nlinarith`  | 実閉体の算術・多項式不等式                            |
| `ring`       | ring（環）                | 可換環などの多項式恒等式を証明する       | `ring`       | 抽象代数学・環論                                 |
| `ring_nf`    | ring normal form       | 多項式を正規形に変換する            | `ring_nf`    | 環論・多項式の正規化                               |
| `field_simp` | field simplification   | 分母を払って有理式を扱いやすくする       | `field_simp` | 体論・分数式の代数的変形                             |
| `norm_cast`  | normalize casts        | 整数・有理数などの型変換を整理する       | `norm_cast`  | 代数構造間の準同型・型変換                            |
| `gcongr`     | generalized congruence | 単調性などを利用して不等式を分解する      | `gcongr`     | 順序理論・単調写像・合同性                            |

特に `omega`、`linarith`、`nlinarith`、`ring` は役割が違う。

| tactic      | 得意な問題                 |
| ----------- | --------------------- |
| `omega`     | 整数・自然数の線形算術。大小関係や整数条件 |
| `linarith`  | 線形等式・不等式の組み合わせ        |
| `nlinarith` | 乗算を含む多項式の等式・不等式       |
| `ring`      | 多項式の恒等式               |

例えば、

```
example (a b : ℤ) (h₁ : a < b) (h₂ : b < a) : False := by
  linarith
```

これは線形不等式の矛盾を自動的に導く。

一方、

```
example (x y : ℤ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring
```

こちらは環の演算規則に従って多項式を正規化する。

### 3.2 論理・命題変形

| tactic          | 由来                             | 実行内容                           | 使用例             | 理論               |
| --------------- | ------------------------------ | ------------------------------ | --------------- | ---------------- |
| `push_neg`      | push negation                  | 否定記号を命題の内部に移動する                | `push_neg`      | 古典論理・量化子の否定      |
| `by_contra`     | by contradiction               | 否定を仮定して矛盾を導く                   | `by_contra h`   | 背理法・古典論理         |
| `contrapose`    | contraposition                 | 命題を対偶に変換する                     | `contrapose h`  | 対偶律              |
| `tauto`         | tautology                      | 命題論理の恒真式を自動的に証明する              | `tauto`         | 命題論理・真理値表        |
| `aesop`         | Aesop（ギリシャの寓話作家 Aesop に由来する名称） | 登録された規則を使って証明を探索する             | `aesop`         | 自然演繹・証明探索・探索戦略   |
| `decide`        | decide（決定する）                   | 計算可能な命題を評価して証明する               | `decide`        | 計算可能性・命題の決定可能性   |
| `native_decide` | native + decide                | ネイティブコードによる計算を利用して決定可能な命題を証明する | `native_decide` | 計算可能性・反射法        |
| `trivial`       | trivial（自明な）                   | 単純な証明を自動的に解決する                 | `trivial`       | 基本的な論理規則・簡単な証明探索 |

`tauto` と `aesop` は混同しやすい。

- `tauto`：命題論理の真理値構造を扱う。
- `aesop`：登録された証明規則を利用して、より一般的な証明探索を行う。

例えば、`P → P` のような命題は `tauto` で解決できる。一方、仮定や帰納型の構造をたどるような証明では `aesop` が役立つ。

### 3.3 構造・集合・代数的操作

| tactic           | 由来                                            | 実行内容                      | 使用例                | 理論                |
| ---------------- | --------------------------------------------- | ------------------------- | ------------------ | ----------------- |
| `ext`            | extensionality                                | 外延性によって等式を要素ごとの命題に分解する    | `ext x`            | 集合論・関数外延性・構造体の外延性 |
| `ac_rfl`         | associativity and commutativity + reflexivity | 結合律・交換律による違いを正規化して等式を証明する | `ac_rfl`           | 代数学・可換モノイド        |
| `fin_cases`      | finite cases                                  | 有限型の全ケースを列挙する             | `fin_cases n`      | 有限集合・有限型の列挙       |
| `interval_cases` | interval cases                                | 整数などの有限区間にある値を列挙する        | `interval_cases n` | 順序理論・有限探索         |
| `injection`      | injection                                     | コンストラクタの単射性を利用して等式を分解する   | `injection h`      | 帰納型の単射性           |
| `cases`          | cases                                         | データ型の構造に従って分解する           | `cases n`          | 帰納型の除去規則          |

### 3.4 書き換え・補助操作

| tactic       | 由来                       | 実行内容                  | 使用例                | 理論         |
| ------------ | ------------------------ | --------------------- | ------------------ | ---------- |
| `simp_rw`    | simplification + rewrite | 指定した順番で簡約・書き換えを繰り返す   | `simp_rw [h₁, h₂]` | 項書き換え系     |
| `simpa`      | simplify + assumption    | 簡約した結果が仮定などと一致するか確認する | `simpa using h`    | 項書き換え系・型検査 |
| `convert`    | convert（変換する）            | 与えた証明とゴールの差を等式として解決する | `convert h`        | 等式推論・型の変換  |
| `subst_vars` | substitute variables     | 等式で決まる変数を置換する         | `subst_vars`       | 等式推論       |
| `unfold`     | unfold（展開する）             | 定義を展開する               | `unfold f`         | 定義展開・δ簡約   |
| `norm_num1`  | normalize numbers        | 数値式の正規化を行う            | `norm_num1`        | 数値計算・正規化   |

## 4. tactic の由来についての補足

略称・名称について、特に覚えておくとよいものを整理する。

| 表記           | 元の言葉                                         | 意味                  |
| ------------ | -------------------------------------------- | ------------------- |
| `simp`       | simplification                               | 簡約                  |
| `rw`         | rewrite                                      | 書き換え                |
| `rfl`        | reflexivity                                  | 反射律                 |
| `dsimp`      | definitional simplification                  | 定義的簡約               |
| `norm_num`   | normalize numbers                            | 数値の正規化              |
| `norm_cast`  | normalize casts                              | 型変換の正規化             |
| `linarith`   | linear arithmetic                            | 線形算術                |
| `nlinarith`  | nonlinear arithmetic                         | 非線形算術               |
| `ring_nf`    | ring normal form                             | 環の正規形               |
| `field_simp` | field simplification                         | 体における簡約             |
| `tauto`      | tautology                                    | 恒真式                 |
| `ext`        | extensionality                               | 外延性                 |
| `ac_rfl`     | associativity and commutativity, reflexivity | 結合律・交換律による反射        |
| `gcongr`     | generalized congruence                       | 一般化された合同性           |
| `aesop`      | Aesop                                        | ギリシャの寓話作家イソップの名前に由来 |
| `omega`      | Omega                                        | 算術決定手続きの名称          |
| `nlinarith`  | nonlinear arithmetic                         | 非線形算術               |

`exact`、`apply`、`intro`、`cases` などは一般英語の動詞をそのまま使った名称であり、略称ではない。

## 5. 理論上の分類をもう少し詳しく

今回の「理論」は、実は3つの異なる階層を区別すると理解しやすい。

### A. 数理論理・証明論

命題をどのように組み立て、証明するかという理論。

| 理論                      | 関連 tactic                                | 内容                |
| ----------------------- | ---------------------------------------- | ----------------- |
| 自然演繹（Natural Deduction） | `intro`, `apply`, `constructor`, `cases` | 命題の導入・除去規則による証明   |
| Curry–Howard対応          | `exact`, `apply`, `refine`               | 命題を型、証明を項として対応させる |
| 直観主義論理                  | `intro`, `constructor`, `left`, `right`  | 排中律を前提としない論理      |
| 古典論理                    | `by_contra`, `by_cases`, `push_neg`      | 排中律・背理法などを利用する論理  |
| 帰納法                     | `induction`, `cases`                     | 帰納型の構造に基づく証明      |
| 等式論理                    | `rfl`, `rw`, `symm`, `trans`             | 等号の反射律・対称律・推移律・置換 |

### B. 数学的理論・決定手続き

特定の数学的構造や理論に特化した tactic。

| 理論                    | 関連 tactic              | 内容              |
| --------------------- | ---------------------- | --------------- |
| Presburger arithmetic | `omega`                | 加法・大小関係を中心とした算術 |
| 線形算術                  | `linarith`             | 線形等式・不等式        |
| 非線形算術                 | `nlinarith`            | 多項式の等式・不等式      |
| 環論                    | `ring`, `ring_nf`      | 環の演算規則と多項式      |
| 体論                    | `field_simp`           | 分数式・逆元          |
| 順序理論                  | `positivity`, `gcongr` | 順序関係・単調性        |
| 命題論理                  | `tauto`                | 命題の真理値構造        |
| 集合論・外延性               | `ext`                  | 要素ごとの一致による等しさ   |

### C. Lean の実装・メタプログラミング

これは数学的理論とは少し違う分類。

| レイヤー            | 関連要素         | 内容                         |
| --------------- | ------------ | -------------------------- |
| Syntax          | tactic の構文   | `by`, `rw`, `simp` などの記述形式 |
| Elaborator      | tactic の実行   | 記述された構文を解釈する               |
| MetaM / TacticM | tactic の実装基盤 | ゴール・ローカル仮定・メタ変数などを操作する     |
| Proof Term      | 証明項          | tactic が構築する実際の証明          |
| Kernel          | 型検査          | 証明項が正しいか検証する               |

この区別は重要。

例えば `ring` は環論に基づく数学的な証明を自動化する tactic だが、その実装は Lean のメタプログラミング機構を利用している。

そして最終的には、環論に基づいて構築された証明項を Kernel が検証する。

つまり、数学的な理論と Lean の実装レイヤーは別の分類軸ということ。

## 6. 最初に覚えるならこの一覧

実際に Lean で証明を書く際の優先順位としては、以下を推奨する。

| 優先度 | tactic        | 覚えるべき役割   |
| --- | ------------- | --------- |
| 高   | `intro`       | 仮定を導入     |
| 高   | `exact`       | 証明を与える    |
| 高   | `apply`       | 定理を適用     |
| 高   | `constructor` | 命題を分解     |
| 高   | `cases`       | 場合分け      |
| 高   | `induction`   | 帰納法       |
| 高   | `rw`          | 書き換え      |
| 高   | `rfl`         | 定義的な等式    |
| 高   | `simp`        | 簡約        |
| 高   | `have`        | 中間命題      |
| 中   | `rcases`      | 仮定の分解     |
| 中   | `use`         | 存在命題の証人   |
| 中   | `by_contra`   | 背理法       |
| 中   | `subst`       | 等式による置換   |
| 中   | `simpa`       | 簡約して証明    |
| 中   | `omega`       | 自然数・整数の算術 |
| 中   | `norm_num`    | 数値計算      |
| 中   | `linarith`    | 線形不等式     |
| 中   | `ring`        | 多項式恒等式    |
| 低   | `aesop`       | 証明探索      |
| 低   | `ext`         | 外延性       |
| 低   | `nlinarith`   | 非線形算術     |
| 低   | `field_simp`  | 分数式の整理    |

## 参考資料

より正確な定義や実装を調べる際には、以下が役立つ。

1. [The Lean 4 Language Reference – Tactic Proofs](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/?utm_source=chatgpt.com) — tactic の仕組み、証明状態、証明項と Kernel の関係。
2. [Mathlib4 Tactics Reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html?utm_source=chatgpt.com) — Mathlib の tactic 一覧と個々の仕様。
3. [Metaprogramming in Lean 4 – Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html?utm_source=chatgpt.com) — tactic の実装、TacticM などの内部構造。

個人的には、今の段階では 基本論理操作 → 等式操作 → 算術の自動化 の順番で理解するのがよいと思う。

特に `exact`、`apply`、`constructor`、`rw` の4つは、Curry–Howard対応と自然演繹を Lean の操作に結びつけるうえで重要。自動化 tactic は、その後に「何を自動化しているのか」を理解すれば十分。

※この表は Lean 4 / Mathlib 4 の主要 tactic を対象とした学習用の整理であり、網羅的な API リファレンスではない。また、由来が公式に定義されていない名称については、一般的な名称の解釈を記載している。