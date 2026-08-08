# 第 9 课 · 实战 BOSS：加法结合律

> 《证明也是程序》系列 · 语言教材式第 9 课 · 机器验证版
> 全部代码可在 [Lean Web](https://lean.math.hhu.de/) 零安装运行

---

## 学完这课，你能…

- 独立完成一个多步定理（任务书模式，无课文）
- 组合使用：归纳 + 归纳假设 + 算术（omega）
- 说出"把大问题拆成小步骤"在证明里的样子

## 热身（复习旧词）

用第 8 课的技能，展开计算 `double 4`：

<details>
<summary>答案：</summary>

```lean
example : double 4 = 8 := rfl
```

</details>

（不会也没关系——这就是 BOSS 课的预热：前八课的技能全部要上场。）

## 任务书（没有课文，只有任务）

> **BOSS 任务：证明加法结合律**
>
> 对任意自然数 m、n、k：
> $$(m + n) + k = m + (n + k)$$
>
> 这是真实教材里的正式习题——有一本叫《实分析》的书，第 2 章就是它。你的武器库：
> - `induction`（第 7 课）——对哪个变量归纳？
> - `ih`（第 7 课）——归纳假设怎么用？
> - `omega`（第 7 课）——算术计算器
> - `calc`（第 7 课）——长链证明
>
> 提示（先自己试 15 分钟，再展开）：

<details>
<summary>提示 1：对哪个变量归纳？</summary>

对 m。因为 + 的定义是"按第一个参数递归"的（第 8 课的 myAdd：match m）——跟着定义走，归纳才顺。
</details>

<details>
<summary>提示 2：骨架长什么样？</summary>

```lean
example : ∀ m n k : ℕ, (m + n) + k = m + (n + k) := by
  intro m n k
  induction m with
  | zero => ?base
  | succ m ih => ?step
```

基例：m = 0 时，两边都是 n + k（`omega` 一句过）。
递推步：假设 (m+n)+k = m+(n+k)，证明 ((m+1)+n)+k = (m+1)+(n+k)。
</details>

<details>
<summary>完整答案：</summary>

```lean
example : ∀ m n k : ℕ, (m + n) + k = m + (n + k) := by
  intro m n k
  induction m with
  | zero => omega
  | succ m ih =>
      have hstep : ((m + 1) + n) + k = (m + (n + k)) + 1 := by omega
      calc
        ((m + 1) + n) + k = (m + (n + k)) + 1 := hstep
        _ = (m + 1) + (n + k) := by omega
```

</details>

## 解剖答案（证完再看）

```lean
  | zero => omega
```

**基例**：m = 0，左边 (0+n)+k = n+k，右边 0+(n+k) = n+k——两边一样，`omega` 确认。

```lean
  | succ m ih =>
      have hstep : ((m + 1) + n) + k = (m + (n + k)) + 1 := by omega
```

**递推步的核心**：`hstep` 为什么成立？——展开 (m+1)+n = (m+n)+1（第 8 课：加法按第一个参数递归），然后 **`ih` 上场**：把 (m+n)+k 换成 m+(n+k)。omega 自动使用归纳假设完成了这一步。

> **这就是归纳假设的用法：它不是装饰，是递推步里唯一"有内容"的那一步。**把中间的算术交给 omega（工具），把结构掌握在自己手里（归纳）——工程师的数学。

```lean
      calc
        ((m + 1) + n) + k = (m + (n + k)) + 1 := hstep
        _ = (m + 1) + (n + k) := by omega
```

**收尾**：(m+(n+k))+1 = (m+1)+(n+k)——加法的交换性在这里只用到"外层"（+1 挪进去），omega 处理。

## BOSS 课的真正内容

你刚完成的，是一个**两段式的证明**：先找一个"中间状态"（hstep），把左边一步步挪到右边。这是数学证明的基本功——**不会一步到位，就拆成中间站**。而"中间状态"从哪来？看目标：左边 (m+1)+n+k 和右边 (m+1)+(n+k) 只差"括号位置"，所以中间站就是"把 m+1 这个括号先拆开、再把 ih 用在里面"。

**证明 = 找中间站。**这一句，是十课以来所有技能的总纲。

## 练习

**练习 1 · 翻译**：把"加法交换律"（m + n = n + m）的陈述写成 Lean 命题（**只写陈述，不证明**——它是下一课的预告题，比结合律更难，需要两次归纳）：

<details>
<summary>答案：</summary>

```lean
example : ∀ m n : ℕ, m + n = n + m := by
  sorry
```

（`sorry` 是"我承诺会证明"的占位符。交换律需要先证两个辅助引理（0 + n = n 和 n + 0 = n），再两次归纳——比结合律难一个档次，留给想挑战的人。）
</details>

**练习 2 · 仿写**：把 BOSS 证明改成对 **k** 归纳（而不是 m）。提示：跟着定义走——k 在 (m+n)+k 里是第二个参数，加法按第一个参数递归，所以对 k 归纳会卡住。试试看卡在哪：

<details>
<summary>答案：</summary>

对 k 归纳会卡在递推步：ih 给的是 (m+n)+k 的性质，但递推步需要操作 (m+n)+(k+1) = ...，而 + 不按第二个参数展开——**没有定义的支持，归纳寸步难行**。这个失败练习的意义：**归纳必须跟着类型的构造走**（第 7 课的语法点，现在你亲手验证了）。
</details>

**练习 3 · 改错**：下面这段要证明结合律，会报错。为什么？

```lean
example : ∀ m n k : ℕ, (m + n) + k = m + (n + k) := by
  intro m n k
  induction m with
  | zero => omega
```

<details>
<summary>答案：</summary>

错误信息："Alternative `succ` has not been provided"——只有基例，没有递推步。
这是第 7 课练习 3 的同一道改错题。现在你应该能自己解释了：**缺了递推步，多米诺只倒了第一块。**
</details>

## 总结

- BOSS 公式：induction 跟着定义走 + ih 是递推步的核心 + omega 做算术
- 证明 = 找中间站（hstep），拆成可验证的小步
- 归纳必须顺着类型的构造方向——方向错了，寸步难行

**下一课预告（毕业课）**：把十课的全部词汇，用在真正的实分析上——**"对任意实数 x，存在自然数 n 比 x 大"**（阿基米德性质）。你第 2 课学的 ∀、第 3 课学的 ∃，将在第一个实分析定理里汇合。然后，你就能打开《实分析》教材了。
