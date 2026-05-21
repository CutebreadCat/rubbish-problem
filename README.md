# rubbish-problem

Erdős Problem 361 的证明工作仓库

## 问题描述

对于固定的 c > 0 和大整数 n，求集合 A ⊆ {1,...,⌊cn⌋} 的最大大小，使得 n 不是 A 的子集和。

## 已证明的结果

### c ≥ 1 的精确公式 ✅
F_c(n) = ⌊cn⌋ - ⌈n/2⌉

### k=1 的特殊情况 ✅
区间 [(n+1)/2, n-1] 是 admissible 的

### 一般情况 k ≥ 1 的关键洞见 ✅
对于区间 I = [n/(k+1), n/k]，没有子集和等于 n

## 项目结构

```
rubbish-problem/
├── README.md
├── CONCLUSION.md
├── proof-log-summary.md
├── problem-361/
│   ├── materials/
│   │   ├── source-summary.md
│   │   ├── research-directions.md
│   │   └── problem-361.lean
│   └── proof-log/
│       ├── iteration-001.lean
│       ├── ...
│       └── iteration-013.lean
└── skills/
    └── claude-proof-loop/
```

## 自动化流程

使用以下脚本进行自动化证明迭代：

```bash
# 基础迭代
./auto-iterate.sh 14

# 使用 Claude CLI
./auto-iterate-claude.sh 14 "Prove the general k case"
```

## 下一步

1. 设置 Lake 项目（需要 Mathlib）
2. 完善一般情况的 Lean 形式化
3. 探索 c < 1 的情况

## 参考文献

- [Erdős Problem 361](https://www.erdosproblems.com/361)
- [Formal Conjectures](https://github.com/formal-conjectures/formal-conjectures)
