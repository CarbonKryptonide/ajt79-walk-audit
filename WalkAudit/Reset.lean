import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Reset

/-- Shannon entropy in nats of a law with positive integer masses w and
total mass D. -/
noncomputable def entropy {α : Type} [Fintype α] (w : α → ℕ) (D : ℕ) : ℝ :=
  (∑ a, (w a : ℝ) * Real.log ((D : ℝ) / w a)) / D

/-- A finite integer certificate bounds the logarithmic information
of each state and the weighted mean of the depth. -/
theorem entropy_bound {α : Type} [Fintype α] (w c : α → ℕ) (D p : ℕ)
    (hD : 0 < D) (hw : ∀ a, 0 < w a) (hs : ∑ a, w a = D)
    (hc : ∀ a, D ≤ 3 * 2 ^ c a * w a)
    (hmean : 3 * (∑ a, w a * c a) ≤ 4 * D)
    (hp : 3 ^ 6 * 2 ^ 8 < p ^ 3) : 2 * entropy w D < Real.log p := by
  have dpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpoint (a : α) :
      Real.log ((D : ℝ) / w a) ≤ Real.log 3 + (c a : ℝ) * Real.log 2 := by
    have wp : 0 < (w a : ℝ) := by exact_mod_cast hw a
    have h : (D : ℝ) / w a ≤ 3 * (2 : ℝ) ^ c a := by
      apply (div_le_iff₀ wp).2
      exact_mod_cast hc a
    calc
      _ ≤ Real.log (3 * (2 : ℝ) ^ c a) := Real.log_le_log (div_pos dpos wp) h
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hs' : ∑ a, (w a : ℝ) = D := by exact_mod_cast hs
  have hm' : 3 * (∑ a, (w a : ℝ) * c a) ≤ 4 * D := by exact_mod_cast hmean
  have hsum :
      (∑ a, (w a : ℝ) * Real.log ((D : ℝ) / w a)) ≤
        (D : ℝ) * Real.log 3 + (∑ a, (w a : ℝ) * c a) * Real.log 2 := by
    calc
      _ ≤ ∑ a, (w a : ℝ) * (Real.log 3 + (c a : ℝ) * Real.log 2) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (by positivity))
      _ = _ := by simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib,
          ← Finset.sum_mul, hs']
  have he : entropy w D ≤ Real.log 3 + (4 / 3 : ℝ) * Real.log 2 := by
    apply (div_le_iff₀ dpos).2
    nlinarith [mul_le_mul_of_nonneg_right hm' l2]
  have comparison : (3 : ℝ)^6 * 2^8 < (p : ℝ)^3 := by exact_mod_cast hp
  have logs := Real.log_lt_log (by norm_num : 0 < (3 : ℝ)^6 * 2^8) comparison
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at logs
  norm_num at logs
  linarith only [logs, he]

/-- At zero take ±1. At every other residue take zero or its double. -/
def endpoints {p : ℕ} (a : ZMod p) : ZMod p × ZMod p :=
  if a = 0 then (1, -1) else (0, 2 * a)

/-- Twice the mass arriving at b in one fair step. -/
def incoming {p : ℕ} [NeZero p] (w : ZMod p → ℕ) (b : ZMod p) : ℕ :=
  ∑ a : ZMod p, ((if (endpoints a).1 = b then w a else 0) +
    (if (endpoints a).2 = b then w a else 0))

/-- m is the period up to sign. Depth k≥1 denotes ±2^(k−1). -/
def depth (p m : ℕ) (a : ZMod p) : ℕ :=
  if a = 0 then 0 else 1 + ((List.range m).find? (fun i =>
    let r := 2 ^ i % p
    a.val == r || a.val == p - r)).getD m

def weight (p m : ℕ) (a : ZMod p) : ℕ :=
  if a = 0 then 2 ^ m - 1 else 2 ^ (m - depth p m a)

def denominator (m : ℕ) := 3 * (2 ^ m - 1)

structure Certificate (p m : ℕ) [NeZero p] : Prop where
  total_pos : 0 < denominator m
  positive : ∀ a, 0 < weight p m a
  total : ∑ a, weight p m a = denominator m
  stationary : ∀ b, incoming (weight p m) b = 2 * weight p m b
  dyadic : ∀ a, denominator m ≤ 3 * 2 ^ depth p m a * weight p m a
  mean_depth : 3 * (∑ a, weight p m a * depth p m a) ≤ 4 * denominator m
  threshold : 3 ^ 6 * 2 ^ 8 < p ^ 3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem certificates : Certificate 59 29 ∧ Certificate 61 30 ∧ Certificate 79 39 := by
  constructor
  · constructor <;> decide
  constructor <;> constructor <;> decide

/-- Positive normalized masses, exact reset stationarity and the actual
Shannon-entropy inequality for each of the three fields. -/
theorem reset_walk_audit (p m : ℕ) [NeZero p]
    (field_period : (p = 59 ∧ m = 29) ∨ (p = 61 ∧ m = 30) ∨ (p = 79 ∧ m = 39)) :
    (0 < denominator m ∧ (∀ a, 0 < weight p m a) ∧ ∑ a, weight p m a = denominator m) ∧
    (∀ b, incoming (weight p m) b = 2 * weight p m b) ∧
    2 * entropy (weight p m) (denominator m) < Real.log p := by
  have cert : Certificate p m := by
    rcases field_period with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact certificates.1
    · exact certificates.2.1
    · exact certificates.2.2
  exact ⟨⟨cert.total_pos, cert.positive, cert.total⟩, cert.stationary,
    entropy_bound _ _ _ _ cert.total_pos cert.positive cert.total
      cert.dyadic cert.mean_depth cert.threshold⟩

end Reset
