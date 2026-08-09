---
name: classics-crossref
description: Cross-reference library for math notes — maps every concept/theorem in a section note to how the classic texts treat it (Halmos '50, Folland '99, Rudin '87, Stein-Shakarchi '05, Tao '11, Royden '10). Use when a deep-math-notes writer must compare treatments, when user asks 另一本书怎么讲 / 各家教材对比 / 翻译成别的教材的术语, or when a claim needs checking against standard conventions. Supplements (never replaces) deep-math-notes.
---

# Classics Crossref（跨教材对照库）

> 一份笔记如果不写明"各家怎么定义、谁先证明、哪里叫法不同"，就不是教材级笔记。

## 0. 目的

每节笔记中，对**每个核心定义/定理**给出：
- 本课（Tao 书）的叫法与编号；
- 2~4 本经典教材里对应的名字/编号/风格差异；
- 若有历史（谁提出、哪年），一两句。

不是堆引用，是为了"三件套"：名字（做了什么）、编号（去哪查）、差异（术语障碍在哪）。

## 1. 测度论核心书目（本库）

| 简称 | 书 | 特点（使用建议） |
|------|----|------------------|
| Tao | Tao, _An Introduction to Measure Theory_ (2011) | 本仓库形式化的主线。先 Jordan/Riemann 再到 Lebesgue；大量动机、习题驱动 |
| Halmos | Halmos, _Measure Theory_ (1950, Springer GTM) | 经典又免俗：抽象测度、extension 定理、符号最现代；零闲聊，直给定义+定理 |
| Folland | Folland, _Real Analysis: Modern Techniques…_ (2nd ed, 1999) | 研究生标准：Lebesgue 测度 → 抽象测度 → Lp；以 Carathéodory 扩展为支点；后面还有调和方法 |
| Rudin | Rudin, _Real and Complex Analysis_ (3rd ed, 1987) | 只含前两章（测度/积分的抽象版）；以 Riesz 表示定理为顶点；书很薄，手法老练 |
| Stein- Shakarchi | Stein & Shakarchi, _Real Analysis_ (Princeton Lectures in Analysis, 2005) | 一作 [StSk2005]，Tao 书明确说受其启发（先 Lebesgue 后抽象）；更像"讲故事的教材" |
| Royden | Royden & Fitzpatrick, _Real Analysis_ (4th ed, 2010) | Thomas 派的传统选择：全套证明、问题多；适合对照"为什么我们不能 …" |

## 2. 每节必做"对照三行"

不管写哪一节，笔记里都放一个小节 `## 教材对照`，用下面模板：

```
| 概念/定理 | Tao § | Halmos | Folland | Rudin | S&S | 关键差异 |
|-----------|-------|--------|---------|-------|-----|----------|
```

每行差异写一句人话（不是页码）：例如
"Halmos 用 σ-ring；Rudin 从跟 Riesz 表示走；Tao 反其道先在 R^d 上建外测度。"

再在下面补一段"为什么这差异重要"（2-4 句）：不同的构造次序决定读者先看到什么、先信什么。

## 3. 提示：对照时怎么找

1. 先按**定理名**干活（单调收敛、Carathéodory 扩展、Vitali 覆盖……），拿名字去记忆。
2. 找不到编号时，**只写名字 + 大致位置**（如"Rudin ch.1, second theorem about ..."），
   并写明"编号待核"，绝不编造章节号。
3. 同一概念叫法不同时**并排**给出（如 outer measure vs exterior measure vs outer content）。
4. 只谈自己真正见过的教材（书架上的）。不要假装读过 Halmos 而没读过——查不到就写
   "Halmos 我有，此处用 Folland 的讲法对照"。

## 4. 反规则（不许做）

- 不许对同一教材的两个不同年份/版本编号混用（Rudin 2nd vs 3rd 编号不同！）；
- 不许编造}引文——找不到具体段落不能"据说"；
- 不许为了"省事"只对照一本教材：Tao + 至少 1 本（优先 Folland 或 S&S）起步；
- 不许把"我教材没这么讲"当成"这么讲是错的"——差异并列，不裁判高下（除 Tacit 错误外）。