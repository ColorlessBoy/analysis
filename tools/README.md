# Lean 国内环境一键配置（试水版 v0.1）

`lean-china-setup.sh` 用于在国内网络下快速配置 Lean 4 + Mathlib：

```bash
bash tools/lean-china-setup.sh            # 安装 elan + 工具链 + 拉取缓存
GH_PROXY=https://gh-proxy.com bash tools/lean-china-setup.sh   # 自定义加速前缀
bash tools/lean-china-setup.sh new myproj # 顺手创建带 Mathlib 的项目
```

原理：

1. elan / Lean 工具链二进制 → GitHub 加速前缀（ghfast.top 等，可用环境变量切换）
2. Mathlib / Lean4 git 仓库 → `git insteadOf` 仅改写 lean 两个 org 的 https 拉取
3. Mathlib olean 缓存 → 官方源直拉 + 重试；失败时给出人工指引

## 它同时是市场调研（这是试水的目的）

**假设**：国内存在一批被环境配置劝退的 Lean 用户/学习者，数量未知。
**验证方式**（脚本本身的传播数据 = 需求信号）：

| 指标 | 判断 |
|------|------|
| 脚本被 fork/star 次数 | 需求规模下限 |
| issue 里"装到哪一步挂了" | 真实痛点分布（配置痛点 vs 使用痛点） |
| 交流群进群人数（脚本输出里引导） | 活跃度，后续社区种子 |
| B 站/知乎教程引用此脚本 | 内容漏斗联动 |

**判定线**：发布后 2-4 周内 star > 50 或 群人数 > 30 → 值得做阶段 2（完整镜像）；
否则说明痛点不够痛或人群太小，把精力还给内容系列（数学学习者主线）。

## 联动

- 内容系列（B 站"5 分钟配好 Lean 环境"）引用此脚本 → 双向导流
- 云端验证产品线（远期）：脚本服务的是"本地 Lean 用户"，他们是云端验证 API 的第一批客户
  （云上验证 = 免本地编译，价值主张直接）
