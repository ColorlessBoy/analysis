# Section 7.1 学习指南：有限和 (Finite Series) 与 Finset

> 对应 Lean 文件：`analysis/Section_7_1.lean`（Tao《Analysis I》§7.1 的翻译）
> 本文档是学习指南；Lean 文件里的 docstring 只保留"翻译字典"（定理 ↔ Mathlib 对应）。

## 1. 本文件的定位（先读）

**重要**：这一章大多数 Finset 定理（`sum_insert`, `sum_union` 等）**来自 Mathlib**，
不在这里重新证明。本文件演示如何**使用**这些定理。

Tao 的 §7.1 本意是从零定义"有限和"（Def 7.1.1 递归定义、Def 7.1.6 枚举定义）并推导
全部性质——但这个工程 Mathlib 已经做完了（`Finset.sum` 的实现加几百条定理）。所以本
文件**不是**"Finset 的定义处"，而是一个三层定位的文件：

1. **字典层**：把 Tao 的每个定义/定理翻译成 Mathlib 的表述。每个定理注释里的
   "**使用的 Mathlib 定理**"就是字典条目，下面的"分工表"是总索引。
   做题时"不知道这个在 Mathlib 里叫什么"是常态——查表、猜名字、验证即可。
2. **原创证明层**：只有少数定理的证明真正"从 Tao 的证明翻译"、值得精读：
   - `finite_series_of_rearrange`（Prop 7.1.8，全文件最核心的证明）
   - `finite_series_of_finite_series`（Lemma 7.1.13，有限 Fubini 的归纳证明）
   - `concat_finite_series`、`shift_finite_series`（Lemma 7.1.4(a)(b)，区间操作）
   其余定理都是一行 `simp` 包装，看它们的证明 = 学 API，不是学数学。
3. **方法论层**：示范"做题时如何找到并验证 Mathlib 定理"（见下文"发现工具箱"）。

还有一个贯穿全书的翻译模式值得记住：**Tao 的定义 → Lean 里的定理**。
Mathlib 的 `Finset.sum s f` 定义为"把 s 底层 Multiset 的元素逐个累加"，天然与枚举顺序
无关（这就是 `finite_series_of_rearrange` 几乎不用证明的原因）。Tao 的枚举定义（选双射
g : Icc (1:ℤ) n → X 求和，Def 7.1.6）在 Lean 里无法直接作为定义（它不可计算），所以变成了
定理 `finite_series_eq`。读懂这个映射，后续章节（无穷和、积分等）的翻译套路完全相同。

## 2. 核心概念：List → Multiset → Finset

### 为什么是 List → Multiset → Finset？

先问一个基本问题：**有限和 `∑` 需要对"有限集合"做什么？** 答案是"把每个元素恰好枚举一次"。
这个需求决定了类型设计：Lean 的 `Set`（即 `α → Prop`）是**谓词**，只能"测试元素在不在"，
它可以是无限的，也**没有**"把元素一个个拿出来"的操作——所以有限和需要的"有限集合"
**不是**从直觉的 `Set` 概念扩展出来的，而是从"能枚举的数据"这个方向长出来的：

```
List（有顺序、可重复）→ 商掉置换 → Multiset（无顺序、可重复）→ 加上 Nodup → Finset（无顺序、无重复）
```

每一层删掉有限和用不到的东西：顺序删掉（和与顺序无关，Prop 7.1.8 在 Lean 里因此几乎
免费），重复删掉（每个元素恰好出现一次）。剩下的"恰好能枚举一次"的极小结构就是 `Finset`。
Tao 书里的"集合"一词同时指谓词和有限集合；Lean 把它们分成了 `Set` 与 `Finset` 两个类型，
翻译时看到书里的"集合"，先判断是哪个。

### Multiset：通过 Quotient 实现无序

`Multiset α = Quotient (List.Perm)` —— 列表在"置换等价"下的商

- **`List [1,2,3]`** 和 **`[2,1,3]`** 在数学上是同一个多重集（顺序不重要）
- **关键**：`Multiset.prod = foldr (· * ·) 1` 用 `Quot.liftOn` 将 `List.foldr` 提升到 Quotient
- **置换不变性**保证结果与代表元无关

### Finset：多重集 + 无重复

`Finset ι = {s : Multiset ι // Nodup s}` —— 无重复的多重集 = 有限集合

```
Finset ℤ:  {1, 2, 3}   ✓
Finset ℤ:  {1, 1, 2}   ✗ (违反 Nodup)
```

### 桥梁：Set ↔ Finset（`Mathlib.Data.Fintype.Sets`）

上面说"Finset 不是从 Set 扩展来的"，但 Mathlib 里确实有一座桥：`Mathlib.Data.Fintype.Sets`。
它的前提是 **`Fintype α`（整个类型有限）**——此时所有子集都是有限的，`Finset` 和 `Set`
是同一件事的两种视角，`Fintype.finsetEquivSet : Finset α ≃ Set α` 给出明确等价。桥的两端：

- **Finset → Set（免费）**：内建 coercion `↑s : Set α`。这就是"Finset 能用 Set 的 API"
  的原因：每个 Finset 都被看成它的"谓词版本"，所以 `s ⊆ t`、`Disjoint`、`s ∩ t` 这些
  Set 世界的陈述对 Finset 同样成立。本文件 `finite_series_of_disjoint_union` 的
  `Disjoint X Y`（X Y 是 Finset）就是借 `Finset.disjoint_coe` 与 Set 版互通的。
- **Set → Finset（要付 `Fintype` 的账）**：`Set.toFinset : Set α → Finset α`，需要
  `[Fintype s]`（该集合自身有限）。实现是 `(Finset.univ : Finset s).map (Embedding.subtype _)`：
  把子类型 `s` 的全部成员枚举出来。把"谓词"变成"数据"必须事先知道所有成员——这正是
  `[Fintype s]` 假设的存在理由。配套一整套 `toFinset_*` 定理（`mem_toFinset`、
  `toFinset_inter`、`toFinset_union`、`toFinset_subset_toFinset`、`disjoint_toFinset`……），
  把集合论陈述逐条翻译成 Finset 陈述。
- **成员的类型层面**：`Finset.Subtype.fintype` 给 `{x // x ∈ s}` 提供 `Fintype` 实例，
  `FinsetCoe.fintype` 给 `(↑s : Set α)` 提供实例——所以 `∑ x : X, f x` 这种"对 Fintype
  求和"的写法也能作用于 Finset 的成员。本文件 `finite_series_of_fintype` 用的
  `Finset.sum_coe_sort`，底层就是这个实例。

**什么时候这座桥不成立？** 类型无限时没有 `finsetEquivSet`：`Set ℤ` 里有无限集
（如 `{x | 0 < x}`），没有对应的 Finset。所以看到 `toFinset` 就提醒自己：
"有限性"已经以 `Fintype` 的形式躺在某处了。

一句话总结方向性：**coercion 把数据看成谓词（免费），`toFinset` 把谓词变成数据（要付
`Fintype` 的账）**。桥不是"Finset 扩展了 Set"，而是"有限世界里两者合一"。

## 3. 最常用的 3 个定理

| 定理 | 用法 | 位置 |
|-----|------|------|
| `Finset.sum_insert` | 如果 `a ∉ s`，则 `∑ i ∈ insert a s, f i = f a + ∑ i ∈ s, f i` | 见 `sum_of_nonempty` |
| `Finset.sum_union` | 如果 `Disjoint s₁ s₂`，则 `∑ i ∈ s₁ ∪ s₂, f i = (∑ ... s₁) + (∑ ... s₂)` | 见 `concat_finite_series` |
| `Finset.sum_add_distrib` | `∑ i ∈ s, (f i + g i) = (∑ ... f i) + (∑ ... g i)` | 见 `finite_series_add` |

## 4. 分工表：本文件 vs Mathlib（按出现顺序）

| 本文件定理 | Tao 出处 | Mathlib 对应物 | 角色 |
|---|---|---|---|
| `sum_of_empty` | Def 7.1.1 | `Finset.sum_eq_zero` + `mem_Icc` | 包装 |
| `sum_of_nonempty` | Def 7.1.1 | `Finset.sum_insert`（ℕ 版是 `sum_Icc_succ_top`） | 包装 |
| `concat_finite_series` | Lemma 7.1.4(a) | `Finset.sum_union` + 区间并集等式（手写） | 半原创 |
| `shift_finite_series` | Lemma 7.1.4(b) | 无直接对应（`sum_Icc_shift` 族不存在），用 `Finset.sum_bij` | ★原创 |
| `finite_series_add` | Lemma 7.1.4(d) | `Finset.sum_add_distrib` | 包装 |
| `finite_series_const_mul` | Lemma 7.1.4(e) | `Finset.mul_sum` | 包装 |
| `abs_finite_series_le` | Lemma 7.1.4(e) | `Finset.abs_sum_le_sum_abs` | 直接调用 |
| `finite_series_of_le` | Lemma 7.1.4(f) | `Finset.sum_le_sum` | 包装 |
| `finite_series_of_rearrange` | Prop 7.1.8 | 无对应；本质是 fold 的置换不变性 | ★原创证明 |
| `exist_bijection` | Def 7.1.6 前置 | `Finset.equivOfCardEq` | 包装 |
| `finite_series_eq` | Def 7.1.6 | `Finset.sum_bij` | 半原创（Tao 定义 → 定理） |
| `finite_series_of_empty` | Prop 7.1.11(a) | `Finset.sum_empty` | 包装 |
| `finite_series_of_singleton` | Prop 7.1.11(b) | `Finset.sum_singleton` | 包装 |
| `finite_series_of_fintype` | — | `Finset.sum_coe_sort` | 包装 |
| `map_finite_series` | Prop 7.1.11(c) | `Finset.sum_equiv` | 包装 |
| `finite_series_of_disjoint_union` | Prop 7.1.11(e) | `Finset.sum_union` | 包装 |
| `finite_series_of_add` | Prop 7.1.11(f) | `Finset.sum_add_distrib` | 包装 |
| `finite_series_of_const_mul` | Prop 7.1.11(g) | `Finset.mul_sum` | 包装 |
| `finite_series_of_le'` | Prop 7.1.11(h) | `Finset.sum_le_sum` | 包装 |
| `abs_finite_series_le'` | Prop 7.1.11(i) | `Finset.abs_sum_le_sum_abs` | 直接调用 |
| `finite_series_of_finite_series` | Lemma 7.1.13 | 组合多个 sum 定理（归纳骨架原创） | ★原创证明 |
| `finite_series_refl` / `finite_series_comm` | Cor 7.1.14 | `map_finite_series` + product 交换 | 半原创 |
| `binomial_theorem` | Ex 7.1.4 | `add_pow` + `Nat.cast_choose` | 半原创 |
| `lim_of_finite_series` | Ex 7.1.5 | `tendsto_finset_sum` | 包装 |
| `sum_union_disjoint` | Ex 7.1.6 | `Finset.sum_biUnion` | 包装 |
| `sum_finite_col_row_counts` | Ex 7.1.7 | `Fin.card_Iio` + `Finset.sum_comm` + `card_filter` | 包装 |

## 5. 如何在 Mathlib 中发现定理？（发现工具箱）

**核心心法：Mathlib 定理名 = 地图。** 名字本身就是结构化索引，猜名字是合法操作：

- **命名规律**：对 `∑` 的运算，先想 `Finset.sum_` 前缀，再加直觉后缀：
  `insert`（加一项）、`union`（并集）、`congr`（逐项相等）、`bij`（双射换标）、
  `comm`（换序）、`product`（乘积集）、`add_distrib`（分配律）、`mul_sum`/`sum_mul`、
  `sum_le_sum`（单调）、`abs_sum_le_sum_abs`（三角不等式）、`eq_zero`（零和）。
  `mem_Icc`/`mem_union`/`mem_product`/`mem_erase` 是各构造的"成员资格 ↔ 逻辑公式"。
- **猜完就验**：在临时文件里写 `#check Finset.sum_insert`，LSP 立刻显示签名；
  错了就改后缀再猜，几秒钟一轮。
- **`#find "关键词"`**：按名字片段搜整个环境（`import Mathlib` 后即可用）。
- **`simp?` / `exact?`**：在目标处让 Lean 自己找定理——把光标停在 `simp?` 上，
  Lean 会建议 `simp only [...]`，其中列出的名字就是你需要的定理。
- **官方文档**：https://docs.mathlib4.org/ 搜 `Finset.sum`，每个定理都有名字和签名。
- **跳转**：VS Code 里 Cmd/Ctrl-click 任意定理名，直接看它的定义和证明。
- **源码**：`lake env grep "theorem sum_insert" .` 或
  `lake env grep "sum_biUnion" Mathlib/Algebra/BigOperators`。
- **关键模块**：`Mathlib.Algebra.BigOperators.Group.Finset.Basic`（sum/prod 大本营）、
  `Mathlib.Data.Finset.*`（集合构造本身）、`Mathlib.Topology.Algebra.Monoid`
  （有限和的极限 `tendsto_finset_sum`，见 `lim_of_finite_series`）。

## 6. ∑ 记号的语法糖（都是 `Finset.sum` 的不同写法）

- `∑ x ∈ s, f x` ≡ `Finset.sum s f`（`s : Finset α`，定义上 rfl 相等）。
- `∑ x, f x`（`α` 有 `Fintype`）≡ `Finset.sum Finset.univ f`（对全类型求和）。
- `∑ x ∈ s with h : p x, f x h` ≡ `Finset.sum s (fun x ↦ if h : p x then f x h else 0)`。
  这正是 `finite_series_of_rearrange` / `finite_series_eq` 里
  `if hi : i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0` 的来历：
  Tao 的枚举定义要求"把 f 限制在 Icc (1:ℤ) n 上"，Lean 里用 `if hi : i ∈ s` 把带证明的
  成员资格 `hi` 交给 `g` 构造 `g ⟨i, hi⟩`；`else 0` 表示枚举范围之外贡献为零。
- 定义层面：`Finset.sum s f = (s.1.map f).sum`，即把 s 底层 Multiset 的元素逐个
  累加（`Multiset.sum` 是 `foldr (+) 0` 在置换商上的提升）。所以和与枚举顺序无关——
  这就是 7.1.8 重排定理在 Lean 里近乎免费的原因。

## 7. 常见错误

**问题**：`sum_insert` 报错 `a ∉ s` 无法推导
**解决**：确保有 `a ∉ s` 的证明，或用 `by simp` 让 Lean 推导（见 `sum_of_nonempty` 中的用法）

**问题**：`sum_union` 需要 `Disjoint` 但代码中没写
**解决**：先证明不相交条件，通常用 `Finset.disjoint_iff_inter_eq_empty` 或 `by simp`
（见 `concat_finite_series` 中的 `h_disjoint` 构造）
