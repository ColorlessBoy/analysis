#!/usr/bin/env bash
# =============================================================
# Lean 4 国内环境一键配置脚本 (MVP v0.1 试水版)
#
# 目的：绕过国内访问 GitHub 不稳定的问题，快速配好 Lean 4 + Mathlib。
# 策略：
#   1. elan / 工具链二进制 → GitHub 加速前缀（ghproxy 类）
#   2. Mathlib / Lean4 git 仓库 → git insteadOf 改写为加速前缀
#   3. Mathlib olean 缓存 → 直接拉官方（Azure/GitHub），失败则给出指引
#
# 用法：
#   bash tools/lean-china-setup.sh            # 安装 elan + 当前项目工具链
#   GH_PROXY=https://gh-proxy.com bash tools/lean-china-setup.sh   # 自定义加速前缀
#
# 注意：v0.1 是试水版，某些分支需要真机验证。见文件末尾 TODO。
# =============================================================
set -euo pipefail

# ---------- 镜像配置（可被环境变量覆盖） ----------
# GitHub 加速前缀：github.com 上的资源 URL 前面拼上这个前缀
# 常见可用前缀（按稳定性自己换）：
#   https://ghfast.top    https://gh-proxy.com    https://ghproxy.net
GH_PROXY="${GH_PROXY:-https://ghfast.top}"

# elan 版本管理器（rustup 的 Lean fork）
ELAN_BASE="https://github.com/leanprover/elan"

# ---------- 工具函数 ----------
say()  { printf "\033[1;34m[lean-setup]\033[0m %s\n" "$*"; }
warn() { printf "\033[1;33m[lean-setup]\033[0m %s\n" "$*"; }
die()  { printf "\033[1;31m[lean-setup]\033[0m %s\n" "$*" >&2; exit 1; }

detect_os_arch() {
  case "$(uname -s)" in
    Darwin) OS="apple-darwin" ;;
    Linux)  OS="unknown-linux-gnu" ;;
    *) die "不支持的系统: $(uname -s)" ;;
  esac
  case "$(uname -m)" in
    x86_64|amd64) ARCH="x86_64" ;;
    arm64|aarch64) ARCH="aarch64" ;;
    *) die "不支持的架构: $(uname -m)" ;;
  esac
  say "系统: $OS / $ARCH"
}

read_toolchain() {
  if [ -f lean-toolchain ]; then
    TOOLCHAIN="$(cat lean-toolchain)"
  else
    warn "未找到 lean-toolchain 文件，使用稳定版"
    TOOLCHAIN="leanprover/lean4:stable"
  fi
  say "目标工具链: $TOOLCHAIN"
}

install_elan() {
  if command -v elan >/dev/null 2>&1 || [ -f "$HOME/.elan/bin/elan" ]; then
    say "elan 已存在: $($HOME/.elan/bin/elan --version 2>/dev/null || elan --version)"
    return 0
  fi
  say "安装 elan（走加速前缀 $GH_PROXY）..."
  local tarball="elan-init-${ARCH}-${OS}.tar.gz"
  local url="$GH_PROXY/$ELAN_BASE/releases/latest/download/$tarball"
  curl -fsSL --connect-timeout 15 "$url" -o "/tmp/$tarball" \
    || die "下载 elan 失败: $url （可换 GH_PROXY 再试）"
  local tmpdir
  tmpdir="$(mktemp -d)"
  tar -xzf "/tmp/$tarball" -C "$tmpdir"
  # 压缩包内是 elan-init 安装器
  sh "$tmpdir/elan-init" -y --no-modify-path >/dev/null 2>&1 \
    || die "elan-init 执行失败（$tmpdir/elan-init 是否存在？）"
  rm -rf "$tmpdir"
  say "elan 安装完成"
}

proxy_github_orgs() {
  # 只把 lean 相关 org 的 https 拉取改写为加速前缀，不动其他仓库
  local cfg="$HOME/.gitconfig"
  say "写入 git insteadOf（仅 leanprover/leanprover-community 两个 org）"
  git config --global url."$GH_PROXY/https://github.com/leanprover/".insteadOf "https://github.com/leanprover/"
  git config --global url."$GH_PROXY/https://github.com/leanprover-community/".insteadOf "https://github.com/leanprover-community/"
  git config --global url."$GH_PROXY/https://raw.githubusercontent.com/leanprover-community/".insteadOf "https://raw.githubusercontent.com/leanprover-community/"
}

install_toolchain() {
  if elan default 2>/dev/null | grep -q "$TOOLCHAIN"; then
    say "工具链已就绪"
    return 0
  fi
  say "安装工具链 $TOOLCHAIN（首次约 200MB，走加速前缀）..."
  # 优先用 elan 直接装（若 elan 支持自定义分发源，则经代理）
  if ELAN_DIST_SERVER="$GH_PROXY/https://github.com/leanprover/lean4/releases/download" \
       elan toolchain install "$TOOLCHAIN" >/dev/null 2>&1; then
    elan default "$TOOLCHAIN"
    say "工具链安装完成（经 ELAN_DIST_SERVER 代理）"
    return 0
  fi
  warn "elan 直连代理失败，尝试手动下载工具链 tarball 并 toolchain link ..."
  # 手动方案：下载 release 压缩包 → 解压 → elan toolchain link
  local ver tag
  ver="$(echo "$TOOLCHAIN" | sed 's|.*:||')"
  tag="v${ver%%-*}"
  # Lean 4 release 资产名形如 lean-<ver>-<os>-<arch>.tar.gz 或 lean-<ver>-<os>.tar.gz，需按实际调整
  for name in "lean-${ver%%-*}-${OS}-${ARCH}" "lean-${ver%%-*}-${OS}"; do
    local u="$GH_PROXY/https://github.com/leanprover/lean4/releases/download/$tag/$name.tar.gz"
    if curl -fsSL --connect-timeout 15 "$u" -o "/tmp/lean-tc.tar.gz" 2>/dev/null; then
      local d="$HOME/.elan/toolchains/local-$ver"
      mkdir -p "$d"
      tar -xzf /tmp/lean-tc.tar.gz -C "$d" --strip-components=1 2>/dev/null \
        || tar -xzf /tmp/lean-tc.tar.gz -C "$d"
      elan toolchain link "local-$ver" "$d"
      elan default "local-$ver"
      say "工具链手动安装完成"
      return 0
    fi
  done
  die "工具链安装失败。请手动安装后重试： https://leanprover-community.github.io/install/"
}

setup_cache() {
  say "拉取 Mathlib 编译缓存（此步最耗时，失败可重试）..."
  for i in 1 2 3; do
    if lake exe cache get 2>/dev/null; then
      say "缓存就绪"
      return 0
    fi
    warn "缓存拉取失败（第 $i/3 次），网络不稳请重试，或稍后手动执行: lake exe cache get"
    sleep 3
  done
  warn "缓存未拉取成功。备选方案："
  warn "  1. 重试: lake exe cache get"
  warn "  2. 若你有网盘/OSS 的 cache 打包（见 README），解压到 .lake/packages/mathlib/Mathlib 同级"
}

new_project() {
  say "创建 Lean 项目 $1 并接入 Mathlib ..."
  lake new "$1" math >/dev/null 2>&1 || lake new "$1" >/dev/null 2>&1
  cd "$1"
  lake update >/dev/null 2>&1 || warn "lake update 失败（可能需重试）"
  say "项目创建完成，下一步:"
  say "  cd $1 && lake build"
}

# ---------- 主流程 ----------
main() {
  detect_os_arch
  read_toolchain
  install_elan
  proxy_github_orgs
  export PATH="$HOME/.elan/bin:$PATH"
  install_toolchain
  if [ "${1:-}" = "new" ]; then
    [ -n "${2:-}" ] || die "用法: $0 new <项目名>"
    new_project "$2"
  elif [ -f lakefile.lean ] || [ -f lakefile.toml ]; then
    setup_cache
  fi
  say "完成！当前环境:"
  "$HOME/.elan/bin/lean" --version
  say ""
  say "踩坑了？欢迎提 issue 或进交流群（见仓库 README）——你的反馈就是在帮国内 Lean 社区排雷。"
}

main "$@"
# ---------- TODO (v0.1 需要真机验证的项) ----------
# 1. elan-init 压缩包内二进制名（macOS/Linux 各平台）是否都是 elan-init
# 2. ELAN_DIST_SERVER 是否被 elan 支持；不支持时手动 toolchain link 的
#    资产命名（lean-<ver>-<os>-<arch>.tar.gz）是否与官方 release 一致
# 3. git insteadOf 对 push 的影响（本脚本只改写 https 拉取，push 走 ssh 不受影响）
# 4. cache 失败时的网盘/OSS 分发方案（阶段 2）
