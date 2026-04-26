# Theorem 3.6.12 证明详解：`nat_infinite`

## 原文证明

```lean
theorem SetTheory.Set.nat_infinite : infinite nat := by
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all
```

---

## 逐步解析

### 第 1 步：`by_contra this`

**目的**：反证法。

假设 `nat` 是**有限的**，即 `¬infinite nat`。根据 `infinite` 的定义：
```lean
infinite X ↔ ¬ finite X
finite X ↔ ∃ n, X ≈ Fin n
```

所以 `¬infinite nat` 等价于 `∃ n, nat ≈ Fin n`。

---

### 第 2 步：`choose n hn using this`

从 `∃ n, nat ≈ Fin n` 中提取出一个具体的 `n : ℕ` 和双射 `hn : nat ≈ Fin n`。

经过 `simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn` 后，`hn` 变成：
```lean
hn : ∃ f : nat → Fin n, Function.Bijective f
```

---

### 第 3 步：`choose f hf using hn`

从 `hn` 中提取双射 `f : nat → Fin n` 和它的证明 `hf : Bijective f`。

---

### 第 4 步：`choose M hM using bounded_on_finite f`

**关键引理**：`bounded_on_finite f` 说，如果 `f : Fin n → nat`，那么存在一个界 `M` 使得所有函数值都不超过 `M`。

```lean
bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M
```

所以我们得到：
- `M : ℕ` — 上界
- `hM : ∀ i, (f i : ℕ) ≤ M` — 对所有 `i`，函数值都 ≤ M

**核心洞察**：因为 `Fin n` 只有 `n` 个有限个元素，任何从它到 `nat` 的双射都会被有界地限制。

---

### 第 5 步：`replace hf := hf.surjective ↑(M+1)`

**这是证明中最关键的一步！**

- `↑(M+1)` 把 `M+1 : ℕ` 提升为 `Fin n` 的元素（`Fin n` 的元素就是 `< n` 的自然数）
- `hf.surjective ↑(M+1)` 试图说 `M+1` 在 `f` 的像中

但根据 `bounded_on_finite`，`f` 的所有值都 `≤ M`，所以 `M+1` **不可能在 `f` 的像里**！

这与 `f` 是满射（surjective）矛盾。

`replace hf := hf.surjective ↑(M+1)` 把 `hf` 重新定义为 `¬Surjective f`，引入了矛盾。

---

### 第 6 步：`contrapose! hf`

对 `hf` 进行逆否命题变换，把 `¬Surjective f` 暴露出来。

---

### 第 7 步：`peel hM with hi`

**`peel` tactic 是关键！**

`hM : ∀ i, (f i : ℕ) ≤ M` 是一个全称量化的命题。

`peel hM with hi` 从这个全称命题中**提取出一个具体的实例**：
```lean
hi : (f ? : ℕ) ≤ M
```
其中 `?` 是某个具体的 `i : Fin n`。

---

### 第 8 步：`contrapose! hi`

再次使用逆否命题，得到：
```lean
hi : ¬((f ? : ℕ) ≤ M)
```
即：
```lean
hi : (f ? : ℕ) > M
```

---

### 第 9 步：矛盾！

同时我们有：
- `(f ? : ℕ) ≤ M` — 从 `hM` 通过 `peel` 得到
- `(f ? : ℕ) > M` — 从 `contrapose! hi` 得到

**矛盾！**

---

### 第 10 步：`apply_fun nat_equiv.symm at hi; simp_all`

清理矛盾，完成证明。

---

## 核心思路总结

```
1. 反证法：假设 nat 是有限的
           ↓
2. 如果 nat ≈ Fin n 存在双射 f
           ↓
3. 因为 Fin n 只有 n 个元素，f 的值必须有界（被 M 限制）
           ↓
4. 但 f 是满射，M+1 作为 nat 的元素必须在像里
           ↓
5. 矛盾！M+1 不可能既 ≤ M 又 > M
```

---

## `peel` tactic 的作用

`peel` 是 Mathlib 中用于处理全称量词的 tactic。它的作用是：

- **输入**：`h : ∀ i, P i`（全称命题）
- **输出**：`peel h with hi` 产生 `hi : P ?`（具体的实例）

这相当于数学证明中"令 `i` 为某个具体值"的操作。

没有 `peel`，Lean 无法从全称量词 `∀ i` 中"打开"出一个具体的不等式来构造矛盾。

---

## 关键引理：`bounded_on_finite`

```lean
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M
```

这个引理说明了：有限定义域上的函数，其值域是有界的。

**直观理解**：如果一个函数只在 `n` 个点上有定义，每个函数值都是某个自然数，那么这些自然数中一定有一个最大的，它就是上界。

---

## 哲学意义

这个证明揭示了**无穷的本质**：

- **每个自然数 `n` 是有限的**：`n` 作为集合（`Fin n`）确实可以和自身一一对应
- **但 `nat`（所有自然数的集合）是无限的**：不存在任何 `n` 使得 `nat ≈ Fin n`

**无穷不是"一个很大的数"**，而是集合的一种拓扑/序结构性质。无界性是有穷和无穷的本质区别。