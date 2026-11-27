# Alon–Jaeger–Tarsi at 79 · Walk audit

[![Verification](https://github.com/CarbonKryptonide/ajt79-walk-audit/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/CarbonKryptonide/ajt79-walk-audit/actions/workflows/ci.yml)

**The all-dimension Alon–Jaeger–Tarsi conjecture at $p=79$ remains open and is unproved here.** This independent research audit verifies two narrower results in Lean 4. A two-coordinate walk has an expected low-state fraction of $59/197>21/100$ at both phases of every cycle, exposing the value-dependent holding obstruction in the inference from the embedded Markov chain in Nagy–Pach–Tomon’s unpublished Appendix C. An exact dyadic reset walk has stationary law $\pi_p$ satisfying $2H(\pi_p)<\log p$ for $`p\in\{59,61,79\}`$. The Lean sources total 221 lines, with zero `sorry`, zero custom axioms, and no `native_decide`.

## Kernel-verified statements

```lean
namespace Holding

theorem holding_obstruction (n : ℕ) :
    lowFraction (cycles n) = 59/197 ∧
    lowFraction (advance false (cycles n)) = 59/197 ∧
    (21/100 : ℚ) < 59/197

end Holding

namespace Reset

theorem reset_walk_audit (p m : ℕ) [NeZero p]
    (field_period : (p = 59 ∧ m = 29) ∨ (p = 61 ∧ m = 30) ∨ (p = 79 ∧ m = 39)) :
    (0 < denominator m ∧ (∀ a, 0 < weight p m a) ∧ ∑ a, weight p m a = denominator m) ∧
    (∀ b, incoming (weight p m) b = 2 * weight p m b) ∧
    2 * entropy (weight p m) (denominator m) < Real.log p

end Reset
```

Exact `#print axioms` output from `lake env lean WalkAudit.lean`:

```text
'Holding.field_midpoints' depends on axioms: [propext, Quot.sound]
'Holding.holding_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reset.reset_walk_audit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The mathematical report establishes barriers to independent reset coupling, uniform $\operatorname{poly}(n)77^n$ overlap bounds for fixed nine-point alphabets, and character-by-character group-ring lifting. The accompanying Python stress tests include all 41,904 invertible $2\times2$ matrices over $\mathbb F_5,\mathbb F_7,\mathbb F_{11},\mathbb F_{13}$. [Audit report](AUDIT_REPORT.md) · [Stress tests](computations/test_routes.py)

## Repository layout

| File | Contents |
| --- | --- |
| [AUDIT_REPORT.md](AUDIT_REPORT.md) | Mathematical arguments and limits of the three proof routes |
| [WalkAudit.lean](WalkAudit.lean) | Lean entry point and axiom checks |
| [WalkAudit/Holding.lean](WalkAudit/Holding.lean) | Common-sign walk and exact two-phase holding obstruction |
| [WalkAudit/Reset.lean](WalkAudit/Reset.lean) | Stationary reset laws and kernel-checked entropy bounds |
| [computations/verify_stationarity.py](computations/verify_stationarity.py) | Independent exact checks of the holding and reset laws |
| [computations/test_routes.py](computations/test_routes.py) | Exact stress tests for the three proof routes |
| [computations/enumerate_midpoints.py](computations/enumerate_midpoints.py) | Enumeration of minimum midpoint sets and their affine orbits |

## Reproduce

With [elan](https://github.com/leanprover/elan#installation) installed, run from the repository root. The project pins Lean 4.19.0 and Mathlib 4.19.0.

```sh
lake exe cache get && lake build
```

The Python checks use the standard library.

```sh
python computations/verify_stationarity.py && python computations/test_routes.py
```

## Sources

- János Nagy and Péter Pál Pach. *The Alon–Jaeger–Tarsi conjecture via group ring identities*. Journal of the European Mathematical Society. [Journal article](https://doi.org/10.4171/JEMS/1640) · [arXiv:2107.03956](https://arxiv.org/abs/2107.03956)
- János Nagy, Péter Pál Pach, and István Tomon. *Irredundant hyperplane covers*. The original preprint contains Appendix C. The withdrawal notice identifies an error in Claim 4.5. [Original preprint](https://arxiv.org/abs/2205.03389v1) · [Withdrawal notice](https://arxiv.org/abs/2205.03389)
- János Nagy and Péter Pál Pach. *On a group ring identity related to the Alon–Jaeger–Tarsi conjecture*. [arXiv:2604.26320](https://arxiv.org/abs/2604.26320)

## Research disclosure

This independent audit used AI assistance for multi-agent exploration of the proof routes and for the Lean 4 formalization. The Lean kernel verifies the stated theorems. The mathematical arguments and computational checks are available for independent review. Released under the [MIT License](LICENSE).

## 中文摘要

$p=79$ 时任意维数的 Alon–Jaeger–Tarsi 猜想仍是公开问题，本仓库未给出证明。Lean 4 内核验证了原预印本附录 C 中依赖状态的停留机制反例（低状态期望比例为 $59/197>21/100$），以及 $p=59,61,79$ 上重置随机游走的平稳分布熵界 $2H(\pi_p)<\log p$。审计报告给出独立耦合、固定字母表重叠计数和逐特征标群环提升的具体障碍，Python 脚本可独立复核有限计算。本项目在独立研究审计中使用了 AI 多代理探索和 Lean 4 形式化辅助。
