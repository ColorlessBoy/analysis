# `OfNat` 与 `NatCast` 的区别

> 对应 `Section_4_1.lean:115-138` 的疑问：为什么 `Int.instOfNat` 和 `Int.instNatCast` 看起来都做同一件事，却需要两个？为什么 `Int.ofNat_inj` 和 `Int.natCast_inj` 感觉重复？

## 一句话总结

**`OfNat` 处理数字字面量（`0`, `1`, `42` 等编译期已知的数），`NatCast` 处理从 `ℕ` 类型的表达式/变量的统一转换（`(n : Int)` 其中 `n : ℕ`）。两者服务于不同的语法机制，不能互相替代。**

---

## 详细解释

### `OfNat` — 字面量的类型类

```lean4
instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0
```

- `OfNat` 是**按具体数字索引**的类型类：`OfNat α n` 表示类型 `α` 可以理解数字字面量 `n`。
- 当写 `(0 : Int)`、`(1 : Int)`、`(42 : Int)` 时，Lean 分别查找 `OfNat Int 0`、`OfNat Int 1`、`OfNat Int 42`。
- `{n:ℕ}` 是一个**参数化实例**（parametric instance），它对每个具体的 `n` 生成一个 `OfNat Int n` 实例，从而使**任何自然数字面量**都可以直接作为 `Int` 使用。
- 这本质上是一个编译器在解析语法时的机制：**每个 numeral 都是一个独立的 `OfNat` 实例**。

### `NatCast` — 类型的统一转换

```lean4
instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0
```

- `NatCast` 是**单参数类型类**：`NatCast α` 表示存在一个从 `ℕ` 到 `α` 的规范嵌入。
- 当 `n : ℕ` 是一个**变量或表达式**，写 `(n : Int)` 时，Lean 将其脱糖为 `Nat.cast n`，查找 `NatCast Int` 实例。
- 这不是按具体数字索引的，而是针对整个 `ℕ` 类型的。

### 关键区别

| 方面 | `OfNat` | `NatCast` |
|------|---------|-----------|
| 索引方式 | 按具体数字 `n : ℕ` | 按目标类型 `α` |
| 用途 | 字面量语法 `0`, `1`, `42` | 类型转换语法 `(n : Int)` |
| 实例形式 | `OfNat Int n` （每数字一个） | `NatCast Int` （一个就够了） |
| 触发场景 | 解析器遇到数字 token | 遇到 `(expr : Type)` 且有 `Nat` 子表达式 |

### 为什么两个 `inj` 定理

- `Int.ofNat_inj` 覆盖 **`ofNat` 语法路径**：`(ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m)`
- `Int.natCast_inj` 覆盖 **`NatCast` 语法路径**：`(n : Int) = (m : Int) ↔ n = m`

两者在数学上等价（说的都是 ℕ → ℤ 是单射），但分别对应两种不同的句法写法。在后续的证明中，用户可能会遇到任意一种写法，两种定理都提供可以避免反复 `simp` 转换。

---

## 历史背景

Lean 4 早期主要依赖 `OfNat` 处理所有涉及 ℕ 的转换。后来社区引入了 `NatCast` / `IntCast` / `RatCast` 这套统一的 cast 类型类族，以分离 "字面量解析" 和 "类型转换" 两个关注点。

在现代 Mathlib 中，标准做法是：
- `NatCast` 负责实际的转换逻辑
- `OfNat` 实例由 `NatCast` **派生**（所以用户通常只需要定义 `NatCast`）

但由于本教材是自建 ℤ 类型（没有继承 Mathlib 的标准实例），所以两者都需要显式提供。

---

## 在教材中是否可以简化？

如果可以依赖 Mathlib 的标准 `NatCast` 派生机制，可以只保留 `NatCast` 并用 `simp` 自动处理 `OfNat`。但在教材的自建类型上，保持两者是清晰且安全的做法——`Int.ofNat_inj` 和 `Int.natCast_inj` 虽然看起来重复，但能确保在任何语法路径下都有对应的引理可用。
