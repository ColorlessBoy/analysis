# 自然数的范畴性 (Categoricity of Natural Numbers)

> 对应习题：Exercise 3.5.13 — `SetTheory.Set.nat_unique`

## 什么是范畴性？

一个理论称为**范畴的 (categorical)**，如果它的所有模型都互相同构——也就是说，任何两个满足该理论的结构本质上"长一样"，只差一个重命名。

`nat_unique` 定理正是在陈述这个事实：

> 任何满足 Peano 公理的集合 `(nat', zero, succ)` 都与 `(ℕ, 0, S)` 唯一双射等价。

用范畴性的语言说：**二阶 Peano 公理是范畴的。**

## 为什么这很深刻？——二阶 vs 一阶的关键区别

**二阶 Peano 公理**（`nat_unique` 使用的版本）的归纳公理是：

> 对**所有**性质 P：P(zero) ∧ (∀n, P(n) → P(succ(n))) → ∀n, P(n)

这里的 P 量程覆盖了**所有子集**，这是一个二阶量词。正因为如此：

- **二阶 PA 是范畴的**：任何两个模型必然同构，因为归纳法强制每个元素都必须从 zero 出发经有限步 succ 可达，不留任何"多余的"元素。

- **一阶 PA 不是范畴的**：一阶逻辑的归纳公理只能是一个**公理模式**，对每个一阶公式 φ 单独陈述，无法覆盖所有子集。这导致：
  - 由**紧致性定理 (Compactness)**，存在**非标准模型**——模型中有元素不属于 0, S(0), S(S(0)), ... 这条链
  - 由 **Löwenheim-Skolem 定理**，存在不可数基数的一阶 PA 模型
  - 这些模型与 ℕ 不同构，但满足完全相同的一阶语句

这就是范畴性最惊人的对比：**同一个公理系统，二阶版本唯一确定了自然数，一阶版本却有无数个互不同构的模型。**

## 历史背景：Dedekind 的先驱性工作

这个结果最早可追溯到 **Dedekind 1888 年的著作** *"Was sind und was sollen die Zahlen"*（《数是什么，数应该是什么》）。Dedekind 证明了：

1. 任何两个"简单无穷系统"（即满足 Peano 公理的结构）必然同构
2. 同构映射是唯一的

`nat_unique` 定理正是 Dedekind 定理的形式化版本。Dedekind 的证明思路与代码中的一致：

- 用递归定义构造同构映射 f（`recursion` 调用）
- 用归纳法证明 f 是单射（`Injective`）
- 用归纳法证明 f 是满射（`Surjective`）

## 范畴性的进一步意义

### 语义完备性

范畴的理论自动语义完备——任何语句 φ 或 ¬φ 在（唯一的同构类）模型中为真。这似乎与 Gödel 不完备定理矛盾，但实际上不矛盾：Gödel 限制的是**一阶**可公理化的系统，而二阶 PA 虽然范畴，却没有有效的证明系统（二阶逻辑不可递归公理化）。

### 内部范畴性 (Internal Categoricity)

Väänänen 和 Wang (2015) 提出了更强的概念——不仅在"全模型"中范畴，而且在**所有 Henkin 模型**中也可证地范畴。这避免了依赖特定语义的选择。

> **Theorem 16 (Väänänen & Wang 2015):** 刻画结构 (ℕ, <) 和 (ℝ, <, +, ·, 0, 1) 的二阶语句是内部范畴的。

### Carnap 猜想

Carnap 提出每个数学结构都由其二阶理论确定到同构。Ajtai (1979) 证明这对可数模型是**独立于 ZFC** 的——既相容也不相容。

## 非标准模型的直觉

一阶 PA 的非标准模型长什么样？

想象一个结构：标准的自然数 0, 1, 2, ... 后面，"接上"了一整条无穷链：

```
0, 1, 2, 3, ... , ω, ω+1, ω+2, ... , ω·2, ω·2+1, ...
```

这些"超大"元素 ω, ω+1, ... 满足所有一阶 PA 的公理（每个一阶语句都无法区分它们与标准自然数），但从二阶视角看，它们违反了归纳法——性质"从 0 出发经有限步 succ 可达"包含了标准部分，但不包含 ω，然而归纳法要求**所有**性质都必须满足。

## 推荐阅读

| 文献 | 说明 |
|------|------|
| Dedekind (1888), *Was sind und was sollen die Zahlen* | 原始结果，有英译本 *The Nature and Meaning of Numbers* |
| Shapiro (1991), *Foundations without Foundationalism* | 为二阶逻辑辩护，深入讨论范畴性 |
| SEP: [Higher-Order Logic](https://plato.stanford.edu/entries/logic-higher-order/) | 第 10 节专门讨论范畴性 |
| Väänänen & Wang (2015), *Internal Categoricity in Mathematics* | 内部范畴性的现代发展 |
| Kaye (1991), *Models of Peano Arithmetic* | 非标准模型的系统介绍 |
