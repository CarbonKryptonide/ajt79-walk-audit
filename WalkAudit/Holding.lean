import Mathlib.Data.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A common fair sign drives both coordinates. The first coordinate is
forced on even turns, the second on odd turns. On its optional turn a
coordinate holds exactly at residues 0, 1 and 2. -/
namespace Holding

abbrev Site := Fin 9
abbrev Pair := Site × Site
abbrev Law (S : Type) := (S → ℚ) → ℚ

def residue : Site → ZMod 79 := ![0, 1, 2, 3, 7, 14, 44, 63, 78]
def left : Site → Site := ![8, 8, 1, 8, 0, 7, 4, 6, 7]
def right : Site → Site := ![1, 3, 3, 4, 5, 6, 2, 3, 5]

theorem field_midpoints : ∀ i, residue (left i) ≠ residue i ∧
    residue (right i) - residue i = -(residue (left i) - residue i) := by decide

def move (optional positive : Bool) (i : Site) : Site :=
  if optional && decide (i.val < 3) then i else if positive then right i else left i

def observable (optional : Bool) (f : Site → ℚ) (i : Site) : ℚ :=
  (f (move optional false i) + f (move optional true i)) / 2

def mean (weights : Site → ℚ) (f : Site → ℚ) : ℚ :=
  (∑ i, weights i * f i) / 197

def before : Site → ℚ := ![23, 23, 23, 10, 30, 22, 22, 26, 18]
def after : Site → ℚ := ![15, 23, 11, 36, 16, 24, 24, 20, 28]

theorem probability_weights :
    (∀ i, 0 < before i ∧ 0 < after i) ∧
    (∑ i, before i) = 197 ∧ (∑ i, after i) = 197 := by
  exact ⟨by decide, by norm_num [before, Fin.sum_univ_succ],
    by norm_num [after, Fin.sum_univ_succ]⟩

theorem forced_step (f : Site → ℚ) :
    mean before (observable false f) = mean after f := by
  norm_num [mean, before, after, observable, move, left, right, Fin.sum_univ_succ]
  ring!

theorem optional_step (f : Site → ℚ) :
    mean after (observable true f) = mean before f := by
  norm_num [mean, before, after, observable, move, left, right, Fin.sum_univ_succ]
  ring!

/-- The same sign in both components is essential. -/
def jointMove (swapped positive : Bool) (z : Pair) : Pair :=
  (move swapped positive z.1, move (!swapped) positive z.2)

def advance (swapped : Bool) (law : Law Pair) : Law Pair :=
  fun f => law (fun z => (f (jointMove swapped false z) + f (jointMove swapped true z)) / 2)

def initial : Law Pair :=
  fun f => mean before (fun i => mean after (fun j => f (i, j)))

def cycles : ℕ → Law Pair
  | 0 => initial
  | n+1 => advance true (advance false (cycles n))

private theorem before_const (c : ℚ) : mean before (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, probability_weights.2.1]

private theorem after_const (c : ℚ) : mean after (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, probability_weights.2.2]

theorem cycle_marginals (n : ℕ) :
    (∀ f, cycles n (fun z => f z.1) = mean before f) ∧
    (∀ f, cycles n (fun z => f z.2) = mean after f) := by
  induction n with
  | zero =>
    exact ⟨fun f => by simp [cycles, initial, after_const],
           fun f => by simp [cycles, initial, before_const]⟩
  | succ n ih =>
    constructor
    · intro f
      change cycles n (fun z => observable false (observable true f) z.1) = _
      rw [ih.1, forced_step, optional_step]
    · intro f
      change cycles n (fun z => observable true (observable false f) z.2) = _
      rw [ih.2, optional_step, forced_step]

def low (i : Site) : ℚ := if i.val < 3 then 1 else 0

/-- The expected fraction in the three low residues, at either phase
of every cycle. This is the mean of the two marginal probabilities. -/
def lowFraction (law : Law Pair) : ℚ :=
  (law (fun z => low z.1) + law (fun z => low z.2)) / 2

theorem holding_obstruction (n : ℕ) :
    lowFraction (cycles n) = 59/197 ∧
    lowFraction (advance false (cycles n)) = 59/197 ∧
    (21/100 : ℚ) < 59/197 := by
  obtain ⟨h₁, h₂⟩ := cycle_marginals n
  have hbefore : mean before low = 69/197 := by
    norm_num [mean, before, low, Fin.sum_univ_succ]
  have hafter : mean after low = 49/197 := by
    norm_num [mean, after, low, Fin.sum_univ_succ]
  constructor
  · rw [lowFraction, h₁, h₂, hbefore, hafter]
    norm_num
  constructor
  · change (cycles n (fun z => observable false low z.1) +
        cycles n (fun z => observable true low z.2)) / 2 = _
    rw [h₁, h₂, forced_step, optional_step, hbefore, hafter]
    norm_num
  · norm_num

end Holding
