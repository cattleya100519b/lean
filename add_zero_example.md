
## 任意の自然数 \(n\) に対して、\(n+0=n\) が成立する

$$
\forall n\in\mathbb{N},\quad n+0=n
$$

### Lean

```lean
theorem add_zero_example (n : Nat) : n + 0 = n := by
  rfl
```

### 意味

|記述|意味|
|---|---|
|theorem|定理を宣言する|
|add_zero_example|定理の名前|
|(n : Nat)|nは自然数|
|n + 0 = n|証明したい命題|
|by|ここから証明を書く|
|rfl|両辺が定義上等しいことを示す (reflexivity 反射律)|

### 内容

1. 命題の提示：\(n+0=n\) という等式を証明目標として与える。
1. 定義による簡約：自然数の加算の定義に従って左辺を簡約する。
1. 等式の検証：左右が定義的に等しいことを確認する。
1. 証明の構築：反射律（Eq.refl）によって等式の証明を完成させる。

---

## 0 + n = n (1)

### Lean

```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.zero_add]
```

### 意味
- induction：数学的帰納法による証明
- zero：帰納法の基底
- succ：帰納法のステップ
- ih：帰納法の仮定 (induction hypothesis（帰納法の仮定）)
- rw：既知の等式を使った書き換え

### tactic

|Tactic|役割|
|---|---|
|rfl|定義的に等しいことを証明|
|intro|含意や全称命題の仮定を導入|
|induction|帰納法を適用|
|rw|等式による書き換え|
|exact|既にある証明を使って目標を解決|
|constructor|命題の構造に応じて目標を分解|

---

## 0 + n = n (2)

### Lean

```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.add_succ]
      rw [ih]
```

### 過程

```
https://ja.wikipedia.org/wiki/ペアノの公理

加法
自然数の加法は次のように再帰的に定義される。
n + 0 = n
n + S(m) = S(n + m)
S(n) を n の後者（英: successor）[注釈 3] ，Sをsuccessor functionと云う。
```

$$
\begin{aligned}
&0+S(n)\\
={}&S(0+n) && \text{Nat.add\_succ}\\
={}&S(n) && \text{帰納法の仮定 } ih\\
={}&n+1
\end{aligned}
$$

