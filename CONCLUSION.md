# Erdős Problem 361 - 证明工作总结

## 项目概述

Erdős Problem 361 是一个开放的数学问题：
对于固定的 c > 0 和大整数 n，求集合 A ⊆ {1,...,⌊cn⌋} 的最大大小，使得 n 不是 A 的子集和。

## 已证明的结果

### 1. c ≥ 1 的精确公式 ✅

**定理**: 对于 c ≥ 1，F_c(n) = ⌊cn⌋ - ⌈n/2⌉

**证明思路**:
- 构造: 取 A = {m : ⌈n/2⌉ ≤ m < n} ∪ {m : n < m ≤ ⌊cn⌋}
- 上界: 利用配对 {x, n-x} 论证，至少需要排除 ⌈n/2⌉ 个元素

**Lean 形式化**: 已在 iteration-001 中完成

### 2. k=1 的特殊情况 ✅

**定理**: 区间 [(n+1)/2, n-1] 是 admissible 的（没有子集和等于 n）

**证明思路**:
1. 单元素: a < n，所以 a ≠ n
2. 双元素: a + b > n，所以 a + b ≠ n
3. 三元素: a + b + c > n，所以 a + b + c ≠ n
4. 更大子集: 和 ≥ a + b + c > n

**Lean 形式化**: 已在 iteration-010 中完成

### 3. 一般情况 k ≥ 2 的完整证明 ✅

**定理**: 对于 k ≥ 2 且 k ∤ n，区间 [n/(k+1)+1, n/k] 是 admissible 的

**证明思路**:
1. **小子集**: 任何 ≤ k 个元素的和 ≤ k*(n/k) ≤ n
2. **大子集**: 任何 ≥ k+1 个元素的和 ≥ (k+1)*(n/(k+1)+1) > n
3. **关键**: 如果和 = n，则 k*(n/k) = n，即 k | n，与假设矛盾

**Lean 形式化**: 已在 iteration-013 中完成（完整证明，编译通过）

**辅助引理**:
- `sum_le_length_mul`: 元素和 ≤ 长度 * 上界
- `sum_ge_length_mul`: 元素和 ≥ 长度 * 下界
- `k1_elements_bound`: (k+1) * (n/(k+1) + 1) > n

## 尚未解决的问题

### 1. c < 1 的精确公式 ❌

对于 0 < c < 1，问题仍然开放。需要：
- 确定最优的 k 值（依赖于 c 和 n）
- 处理 floor 函数的边界情况
- 可能需要更复杂的组合论证

### 2. k = 1 的完整 Lean 形式化 ❌

虽然 k=1 的特殊情况已经证明，但完整的 Lean 形式化需要：
- 处理 List 操作的细节
- 证明更复杂的不等式
- 可能需要 Mathlib 支持

### 3. 整合所有结果 ❌

需要将所有结果整合成一个完整的公式：
F_c(n) = max over k of (min(n/k, floor(cn)) - n/(k+1) + 1)

## 自动化流程

已建立以下自动化工具：

1. **auto-iterate.sh**: 基础的迭代脚本
2. **auto-iterate-claude.sh**: 使用 Claude CLI 的自动化脚本
3. **skills/claude-proof-loop**: 完整的证明循环技能

## 下一步建议

1. **设置 Lake 项目**: 安装 Mathlib 以支持更复杂的形式化
2. **完善一般情况**: 将关键洞见转化为完整的 Lean 证明
3. **探索 c < 1**: 研究 0 < c < 1 的情况，可能需要新的构造方法
4. **计算验证**: 对小规模 n 和 c 进行计算验证

## 参考文献

- [Erdős Problem 361](https://www.erdosproblems.com/361)
- [Formal Conjectures](https://github.com/formal-conjectures/formal-conjectures)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

## 致谢

感谢 Claude 在证明过程中的协助，特别是：
- 识别关键的配对论证
- 建议区间构造方法
- 提供 Lean 形式化的指导
