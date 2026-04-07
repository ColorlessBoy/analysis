# singleton_iProd_equiv 证明详解

## 1. 背景：什么是 iProd？

### 1.1 依赖乘积 (Dependent Product)

在类型论和集合论中，**依赖乘积**（Dependent Product）是一个重要的构造。

给定：
- 一个索引集合 `I : Set`
- 一个依赖族 `X : I → Set`（即对每个索引 `i : I`，有一个集合 `X i`）

`iProd X` 表示所有"依赖元组"的集合，即选择函数 `x : ∀ i : I, X i`。

### 1.2 具体定义

在代码中，`iProd` 定义如下：

```lean
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)
```

这个定义可能看起来复杂，但核心思想是：
- `tuple x` 将一个依赖函数 `x : ∀ i, X i` 编码为一个对象
- `iProd X` 是所有这样的 `tuple x` 组成的集合

### 1.3 关键定理

```lean
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x
```

这个定理说明：`t` 是 `iProd X` 的元素，当且仅当 `t` 等于某个 `tuple x`。

---

## 2. singleton_iProd_equiv 的含义

### 2.1 定理陈述

```lean
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X
```

这说的是：**在单点集 `{i}` 上的依赖乘积，同构于 `X` 本身**。

### 2.2 为什么这是对的？

直观理解：
- 索引集 `{i}` 只有一个元素 `i`
- 依赖族 `fun _:({i}:Set) ↦ X` 对每个索引都返回 `X`（常值函数）
- 所以 `∀ j : {i}, X j` 本质上就是 `X`（只需要选择一个元素）
- 因此 `iProd (fun _:({i}:Set) ↦ X) ≃ X`

---

## 3. 证明详解

### 3.1 toFun：从 iProd 到 X

```lean
toFun t := ((mem_iProd _).mp t.property).choose ⟨i, by simp⟩
```

**步骤分解：**

1. `t : iProd (fun _:({i}:Set) ↦ X)` 是一个依赖元组
2. `t.property` 是证明 `t.val ∈ iProd _`
3. `(mem_iProd _).mp t.property` 得到 `∃ x : ∀ j : {i}, X j, t.val = tuple x`
4. `.choose` 选出一个具体的函数 `x : ∀ j : {i}, X j`
5. `⟨i, by simp⟩ : {i}` 是单点集中唯一的元素（`i` 带上它属于 `{i}` 的证明）
6. `x ⟨i, by simp⟩ : X` 取出这个函数在唯一索引处的值

**直观理解：** 既然索引集只有一个元素，元组实际上就只有一个分量，直接取出即可。

### 3.2 invFun：从 X 到 iProd

```lean
invFun x := ⟨tuple (fun j : ({i}:Set) ↦ x), by apply tuple_mem_iProd⟩
```

**步骤分解：**

1. `x : X` 是一个元素
2. `fun j : ({i}:Set) ↦ x` 是常值函数，对任意索引都返回 `x`
3. `tuple (fun j ↦ x)` 将这个函数编码为一个对象
4. `tuple_mem_iProd` 证明这个对象属于 `iProd`
5. 最终得到 `iProd (fun _:({i}:Set) ↦ X)` 的一个元素

**直观理解：** 给定 `x : X`，创建一个"元组"，它在唯一的索引处取值 `x`。

### 3.3 left_inv：证明 toFun ∘ invFun = id

```lean
left_inv := by
  intro t
  ext
  have h := (mem_iProd _).mp t.property
  rw [h.choose_spec, tuple_inj]
  ext j
  have hj : j = ⟨i, by simp⟩ := by
    apply Subtype.ext
    exact (mem_singleton j.val i).mp j.property
  rw [hj]
```

**详细解释：**

1. **目标**：证明 `invFun (toFun t) = t`

2. `have h := (mem_iProd _).mp t.property`：
   - 得到 `∃ x : ∀ j : {i}, X j, t.val = tuple x`
   - `h.choose` 是选出的函数
   - `h.choose_spec` 是证明 `t.val = tuple h.choose`

3. `rw [h.choose_spec, tuple_inj]`：
   - 将目标变为证明 `fun j ↦ h.choose ⟨i, by simp⟩ = h.choose`
   - 这里用到了 `tuple_inj`：`tuple x = tuple y ↔ x = y`

4. `ext j`：函数外延性，需要证明对任意 `j : {i}`，两边相等

5. `have hj : j = ⟨i, by simp⟩`：
   - **关键步骤**：证明 `{i}` 中任意元素 `j` 都等于 `⟨i, by simp⟩`
   - 使用 `Subtype.ext`：子类型的外延性
   - 使用 `(mem_singleton j.val i).mp j.property`：
     - `j.property : j.val ∈ {i}`
     - `mem_singleton j.val i : j.val ∈ {i} ↔ j.val = i`
     - 得到 `j.val = i`

6. `rw [hj]`：将 `j` 替换为 `⟨i, by simp⟩`，两边就相等了

**直观理解：** 因为 `{i}` 只有一个元素，所以 `fun j ↦ h.choose ⟨i, by simp⟩` 和 `h.choose` 在所有 `j` 处都取相同的值。

### 3.4 right_inv：证明 invFun ∘ toFun = id

```lean
right_inv := by
  intro x
  simp only
  have h := (mem_iProd _).mp (tuple_mem_iProd (fun j : ({i}:Set) ↦ x))
  have hspec := h.choose_spec
  rw [tuple_inj] at hspec
  have : h.choose = fun j : ({i}:Set) ↦ x := hspec.symm
  rw [this]
```

**详细解释：**

1. **目标**：证明 `toFun (invFun x) = x`

2. `have h := (mem_iProd _).mp (tuple_mem_iProd (fun j ↦ x))`：
   - `invFun x` 创建了 `tuple (fun j ↦ x)`
   - `tuple_mem_iProd` 证明它属于 `iProd`
   - `mem_iProd` 给出 `∃ z, tuple (fun j ↦ x) = tuple z`
   - `h.choose` 是选出的函数 `z`

3. `have hspec := h.choose_spec`：
   - 得到 `tuple (fun j ↦ x) = tuple h.choose`

4. `rw [tuple_inj] at hspec`：
   - 得到 `fun j ↦ x = h.choose`

5. `have : h.choose = fun j ↦ x := hspec.symm`：
   - 反过来写

6. `rw [this]`：
   - 将 `h.choose` 替换为 `fun j ↦ x`
   - 然后 `h.choose ⟨i, by simp⟩ = (fun j ↦ x) ⟨i, by simp⟩ = x`

**直观理解：** `toFun` 取出元组的唯一分量，`invFun` 用这个分量创建常值元组。因为元组只有一个分量，所以往返操作回到原点。

---

## 4. 关键概念总结

### 4.1 单点集的性质

单点集 `{i}` 有特殊性质：
- 只有一个元素：`⟨i, by simp⟩`
- 任意 `j : {i}` 都满足 `j = ⟨i, by simp⟩`
- 证明使用 `mem_singleton : x ∈ {a} ↔ x = a`

### 4.2 tuple 和 tuple_inj

- `tuple x` 将依赖函数 `x : ∀ i, X i` 编码为对象
- `tuple_inj`：`tuple x = tuple y ↔ x = y`（编码是单射）

### 4.3 选择函数 .choose

当有存在性命题 `∃ x, P x` 时：
- `.choose` 选出一个满足条件的 `x`
- `.choose_spec` 给出 `P x` 的证明

---

## 5. 图示

```
iProd (fun _:({i}:Set) ↦ X)          X
        |                              |
        | toFun                        | id
        v                              v
        X  ──────────────────────►  X
              invFun
              
        X                              X
        |                              |
        | invFun                       | id
        v                              v
iProd (fun _:({i}:Set) ↦ X) ───► iProd (fun _:({i}:Set) ↦ X)
              toFun
```

两个三角形交换，证明了 `toFun` 和 `invFun` 互为逆映射。

---

## 6. 类比

可以把这个同构类比于：

- **有限维向量空间**：一维向量空间同构于其基域
- **笛卡尔积**：`X × Y × Z` 是三维的，`X` 是一维的
- **函数空间**：从单点集到 `X` 的函数空间同构于 `X` 本身

这个定理是依赖乘积理论的一个基础事实，说明单点索引集上的依赖乘积退化为单个集合。
