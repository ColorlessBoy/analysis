---
name: social-listening
argument-hint: "[topic/segment + platforms + decision it informs]"
description: "Structured market research from social media — X, YouTube, Bilibili, Douyin, Weibo. Use when you need to understand user pain points, unmet needs, competitor weaknesses, or topic demand from public content and comments without interviews."
intent: >-
  Run a social media listening pass across X, YouTube, Bilibili, Douyin, and Weibo: per-platform source
  map, search plan, verbatim evidence capture, signal classification, and confidence-labeled output.
  Every claim is a hypothesis to validate, never a verdict. Adapted from the Market Intelligence
  Suite OSINT discipline; adds China-platform specifics (danmaku, water-army signals, platform
  demographic skew).
type: workflow
best_for:
  - "Finding what users actually complain about and wish for in a topic area"
  - "Estimating demand/topic heat from video titles, play counts, and comment volume"
  - "Arming discovery interviews and JTBD canvases with evidence-backed hypotheses"
scenarios:
  - "调研'自学数学分析'人群的痛点，用 B站/抖音/微博"
  - "X 和 YouTube 上英语世界的数学学习产品在讨论什么"
  - "竞品在社媒上被骂得最多的是什么"
estimated_time: "60-90 min per run"
---

# Social Media Market Listening (自媒体市场调研)

## Purpose

Turn X / YouTube / Bilibili / Douyin / Weibo into a market research instrument:
**source map → search plan → verbatim capture → signal classification → confidence-labeled output.**
Bridges discovery and competitive intelligence. Output feeds JTBD canvases, proto-personas,
opportunity trees, and battle cards — as hypotheses to validate, not verdicts.

## Input

- **Topic/segment**: e.g. "自学数学分析的痛点", "数学学习 AI 工具", "Lean 定理证明"
- **Platforms**: which of X / YouTube / Bilibili / Douyin / Weibo (default: all five)
- **Decision**: what the research informs (positioning? pricing? feature?)
- **Competitors** (optional): whose weaknesses to hunt

## Per-Platform Source Map

| Platform | Best reveals | Key signal surfaces |
|----------|--------------|---------------------|
| X | 实时讨论、KOL 观点、英文世界趋势 | 搜索语法（`from:` `since:` `lang:`）、转/赞/评比、话题时间线、创作者发帖（发帖主题变化 = 定位转向信号） |
| YouTube | 长内容痛点、搜索意图 | 视频标题=需求关键词（标题即搜索意图）、评论区深度讨论、播放/观看量、频道画像（订阅者=受众池） |
| Bilibili | 教育类需求热度、即时情绪 | **弹幕=瞬时情绪反馈**、视频标题/播放量=需求热度、评论+弹幕双重语料、一键三连率、课程/科普区生态 |
| Douyin | 大众化需求、消费行为信号 | 话题标签（`#数学分析`）、评论区高互动、直播切片、收藏/加购=行为信号（比点赞更接近付费意愿） |
| Weibo | 情绪爆发点、社区规模、事件发酵 | 热搜/超话、超话粉丝数=社区规模、大V转发层级、时间线追踪话题从萌芽到爆发的节奏 |

## Workflow

1. **定焦**（3 问）: 这个调研支持什么决策？时限？我们已经知道什么？
2. **搜索计划**: 每平台 2-5 个查询词组合 = 主题词 × 场景词 × 情绪词
   - 例: `数学分析 自学 太难`、`数分 证明 看不懂`、`b站 数学课 推荐`、`real analysis self-study struggle`
3. **采集**: 每条证据记 平台 + 链接 + **引用原文（verbatim，逐字）** + 日期 + 互动数据（播放/点赞/评论数）
4. **归类**: 需求信号 / 痛点信号 / 竞品弱点 / 替代方案（题解书、视频课、AI tutor、Copilot 类工具）
5. **聚类**: 主题 + 强度 = 证据条数 × 来源多样性 × 互动量（单平台刷屏 ≠ 跨平台趋势）
6. **标注**: 每条发现标 Fact（可核实数据/原文）/ Inference（推断）/ Assumption（假设）
7. **输出**: 发现清单 + 置信度 + 下一步验证动作（访谈、问卷、pol-probe）

## Output Schema

```text
主题 | 证据(原文引用+链接+互动量) | 强度(高/中/低) | 置信度 | 下一步验证
```

## 反虚假信号（中国平台特有）

- **水军/刷量**: 互动量异常高但内容质量差、账号注册时间集中、评论措辞模板化
- **幸存者偏差**: 发声者多为极端体验者；沉默的大多数看不到
- **平台人口差异**: 抖音用户 ≠ B站用户 ≠ 微博用户 — 分平台画像，禁止合并统计
- **情绪 ≠ 需求**: 吐槽多 ≠ 付费意愿强 — 用行为信号（收藏/加购/进群/购买）佐证
- **爆款 ≠ 趋势**: 单条爆款可能是巧合，需 ≥3 条独立证据才算一个主题
- **合规**: 引用原文注意篇幅，标注来源；不做用户画像溯源

## Common Pitfalls

- 只收集不归类 — 证据不进入输出框架等于白做
- 把"评论区骂声"直接当需求写进 PRD — 先过访谈验证
- 忽略各平台用户结构差异，得出"全平台一致"的错误结论
- 用社媒情绪替代真实访谈 — 本 skill 产出的是假设清单，最后一站永远是真人对话

## References

- Related: `voice-of-customer-miner`（应用商店/论坛）、`intel-discipline-advisor`（先三问定焦）、`jobs-to-be-done`、`proto-persona`
- Adapted from the Market Intelligence Suite OSINT discipline (deanpeters/Product-Manager-Skills, CC BY-NC-SA 4.0)
