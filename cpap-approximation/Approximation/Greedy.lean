module

public import Approximation.Loads

/-!
Algorithm 1, the greedy cycle-path assignment: each cycle, in order, receives a
path of minimum load-sum with respect to the paths chosen before it. `GreedyRun`
describes every run of the algorithm (any tie-breaking); `greedy` is the run
that breaks ties by position.
-/

@[expose] public section
namespace STACS2027

/-- The first option minimizing `f` (an arbitrary element of `argmin`, with ties broken by
position); `[]` on an empty option list. -/
def chooseMin (f : List Edge → Nat) : List (List Edge) → List Edge
  | [] => []
  | [p] => p
  | p :: q :: rest => if f p ≤ f (chooseMin f (q :: rest)) then p else chooseMin f (q :: rest)

/-- Algorithm 1 continued after the paths `acc` have been chosen: the paths of the remaining
cycles, each a path of minimum load-sum under the loads of all paths chosen before it. -/
def greedyFrom (acc : List (List Edge)) : List (List (List Edge)) → List (List Edge)
  | [] => []
  | opts :: rest =>
    chooseMin (pathLoad acc) opts :: greedyFrom (acc ++ [chooseMin (pathLoad acc) opts]) rest

/-- Algorithm 1 on the option lists of the cycles (the greedy cycle-path assignment). -/
def greedy (options : List (List (List Edge))) : List (List Edge) :=
  greedyFrom [] options

/-- `GreedyRun acc options chosen`: `chosen` is a possible output of Algorithm 1 on the cycles
with option lists `options`, started with the paths `acc` already chosen: each path is an option
of its cycle of minimum load-sum with respect to the paths chosen before it (ties broken
arbitrarily). -/
def GreedyRun : List (List Edge) → List (List (List Edge)) → List (List Edge) → Prop
  | _, [], [] => True
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False
  | acc, opts :: rest, p :: ps =>
    p ∈ opts ∧ (∀ q ∈ opts, pathLoad acc p ≤ pathLoad acc q) ∧ GreedyRun (acc ++ [p]) rest ps

theorem chooseMin_mem (f : List Edge → Nat) {opts : List (List Edge)} (h : opts ≠ []) :
    chooseMin f opts ∈ opts := by
  induction opts with
  | nil => exact absurd rfl h
  | cons p rest ih =>
    cases rest with
    | nil => simp [chooseMin]
    | cons q rest =>
      simp only [chooseMin]
      split
      · simp
      · exact List.mem_cons_of_mem p (ih (by simp))

theorem chooseMin_le (f : List Edge → Nat) (opts : List (List Edge)) :
    ∀ q ∈ opts, f (chooseMin f opts) ≤ f q := by
  induction opts with
  | nil => simp
  | cons p rest ih =>
    cases rest with
    | nil => simp [chooseMin]
    | cons q' rest =>
      intro q hq
      simp only [chooseMin]
      split
      · rename_i hle
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Nat.le_refl _
        · exact Nat.le_trans hle (ih q hq)
      · rename_i hlt
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Nat.le_of_lt (Nat.lt_of_not_le hlt)
        · exact ih q hq

/-- `greedy` is a run of Algorithm 1 whenever every cycle has an option. -/
theorem greedyFrom_run (acc : List (List Edge)) (options : List (List (List Edge)))
    (h : ∀ opts ∈ options, opts ≠ []) : GreedyRun acc options (greedyFrom acc options) := by
  induction options generalizing acc with
  | nil => trivial
  | cons opts rest ih =>
    show _ ∈ opts ∧ (∀ q ∈ opts, _ ≤ _) ∧ GreedyRun _ rest _
    exact ⟨chooseMin_mem _ (h opts (by simp)), chooseMin_le _ opts,
      ih _ (fun o ho => h o (by simp [ho]))⟩

theorem greedy_run (options : List (List (List Edge))) (h : ∀ opts ∈ options, opts ≠ []) :
    GreedyRun [] options (greedy options) :=
  greedyFrom_run [] options h

/-- A run of Algorithm 1 chooses an option for every cycle. -/
theorem GreedyRun.valid {acc : List (List Edge)} {options : List (List (List Edge))}
    {chosen : List (List Edge)} (h : GreedyRun acc options chosen) :
    ValidChoices options chosen := by
  induction options generalizing acc chosen with
  | nil =>
    cases chosen with
    | nil => trivial
    | cons _ _ => exact False.elim h
  | cons opts rest ih =>
    cases chosen with
    | nil => exact False.elim h
    | cons p ps => exact ⟨h.1, ih h.2.2⟩

/-- The greedy inequality: the cost of a greedy run is at most the sum, over the cycles, of the
load-sum under the final greedy loads of the path any other assignment gives that cycle (each
greedy step costs at most the current, hence at most the final, load-sum of the competitor's
path). -/
theorem GreedyRun.cost_le {acc : List (List Edge)} {options : List (List (List Edge))}
    {chosen qs : List (List Edge)} (h : GreedyRun acc options chosen)
    (hq : ValidChoices options qs) :
    cost (acc ++ chosen) ≤ cost acc + (qs.map (pathLoad (acc ++ chosen))).sum := by
  induction options generalizing acc chosen qs with
  | nil =>
    cases chosen with
    | nil =>
      cases qs with
      | nil => simp
      | cons _ _ => exact False.elim hq
    | cons _ _ => exact False.elim h
  | cons opts rest ih =>
    cases chosen with
    | nil => exact False.elim h
    | cons p ps =>
      cases qs with
      | nil => exact False.elim hq
      | cons q qs =>
        obtain ⟨_, hmin, hrun⟩ := h
        obtain ⟨hqo, hqs⟩ := hq
        have hstep := ih hrun hqs
        rw [List.append_assoc, List.singleton_append] at hstep
        have hsnoc := cost_snoc_pathLoad acc p
        have hpq : pathLoad acc p ≤ pathLoad (acc ++ p :: ps) q :=
          Nat.le_trans (hmin q hqo) (pathLoad_le_pathLoad_append acc (p :: ps) q)
        simp only [List.map_cons, List.sum_cons]
        omega

end STACS2027
