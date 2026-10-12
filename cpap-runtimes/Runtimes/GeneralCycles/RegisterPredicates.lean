module

public import Runtimes.GeneralCycles.RegTests
public import Runtimes.GeneralCycles.Output
import Mathlib.Tactic

/-! Fixed-size equality, lexicographic and cycle-edge-set tests.
All labels are compared as register values. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def regValues (c : Config) (rs : List ℕ) : List ℕ := rs.map c.reg

def equalTest : List ℕ → List ℕ → RegTest
  | [], [] => .truth true
  | a :: as, b :: bs => .both (.equal a b) (equalTest as bs)
  | _, _ => .truth false

def lexTest : List ℕ → List ℕ → RegTest
  | [], [] => .truth false
  | [], _ :: _ => .truth true
  | _ :: _, [] => .truth false
  | a :: as, b :: bs => .either (.less a b) (.both (.equal a b) (lexTest as bs))

def allTest : List RegTest → RegTest
  | [] => .truth true
  | p :: ps => .both p (allTest ps)

def anyTest : List RegTest → RegTest
  | [] => .truth false
  | p :: ps => .either p (anyTest ps)

def adjacentRegs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: adjacentRegs (b :: rest)

def cyclicRegs (rs : List ℕ) : List (ℕ × ℕ) := adjacentRegs (rs ++ rs.take 1)

def edgeTest (p q : ℕ × ℕ) : RegTest :=
  .either (.both (.equal p.1 q.1) (.equal p.2 q.2))
    (.both (.equal p.1 q.2) (.equal p.2 q.1))

def subsetTest (ps qs : List (ℕ × ℕ)) : RegTest :=
  allTest (ps.map fun p => anyTest (qs.map fun q => edgeTest p q))

def sameCycleTest (rs ss : List ℕ) : RegTest :=
  .both (subsetTest (cyclicRegs rs) (cyclicRegs ss))
    (subsetTest (cyclicRegs ss) (cyclicRegs rs))

def earlierTest (outerIndices outerValues innerIndices innerValues : List ℕ) : RegTest :=
  .either (lexTest innerValues outerValues)
    (.both (equalTest innerValues outerValues) (lexTest innerIndices outerIndices))

@[simp] theorem equalTest_eval (rs ss : List ℕ) (c : Config) :
    (equalTest rs ss).eval c = decide (regValues c rs = regValues c ss) := by
  induction rs generalizing ss with
  | nil => cases ss <;> simp [equalTest, RegTest.eval, regValues]
  | cons a as ih =>
    cases ss with
    | nil => simp [equalTest, RegTest.eval, regValues]
    | cons b bs =>
      simp [equalTest, RegTest.eval, regValues, ih]
      rfl

@[simp] theorem lexTest_eval (rs ss : List ℕ) (c : Config) :
    (lexTest rs ss).eval c = decide (regValues c rs < regValues c ss) := by
  induction rs generalizing ss with
  | nil => cases ss <;> simp [lexTest, RegTest.eval, regValues]
  | cons a as ih =>
    cases ss with
    | nil => simp [lexTest, RegTest.eval, regValues]
    | cons b bs =>
      simp [lexTest, RegTest.eval, regValues, ih, List.cons_lt_cons_iff]
      rfl

@[simp] theorem allTest_eval (ps : List RegTest) (c : Config) :
    (allTest ps).eval c = decide (∀ p ∈ ps, p.eval c = true) := by
  induction ps with
  | nil => simp [allTest, RegTest.eval]
  | cons p ps ih =>
    simp [allTest, RegTest.eval, ih]

@[simp] theorem anyTest_eval (ps : List RegTest) (c : Config) :
    (anyTest ps).eval c = decide (∃ p ∈ ps, p.eval c = true) := by
  induction ps with
  | nil => simp [anyTest, RegTest.eval]
  | cons p ps ih =>
    simp [anyTest, RegTest.eval, ih]

@[simp] theorem edgeTest_eval (p q : ℕ × ℕ) (c : Config) :
    (edgeTest p q).eval c = decide (edge (c.reg p.1) (c.reg p.2) =
      edge (c.reg q.1) (c.reg q.2)) := by
  simp [edgeTest, RegTest.eval, edge_eq_iff]

theorem adjacentRegs_map (rs : List ℕ) (c : Config) :
    (adjacentRegs rs).map (fun p => edge (c.reg p.1) (c.reg p.2)) =
      pathEdges (regValues c rs) := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    cases rs with
    | nil => rfl
    | cons b rest =>
      simpa [adjacentRegs, regValues, pathEdges] using
        (congrArg (edge (c.reg a) (c.reg b) :: ·) ih)

theorem cyclicRegs_map (rs : List ℕ) (c : Config) :
    (cyclicRegs rs).map (fun p => edge (c.reg p.1) (c.reg p.2)) =
      cycleEdges (regValues c rs) := by
  rw [cyclicRegs, adjacentRegs_map]
  simp [regValues, cycleEdges, List.map_take]

theorem subsetTest_eval (ps qs : List (ℕ × ℕ)) (c : Config) :
    (subsetTest ps qs).eval c = decide (∀ p ∈ ps,
      edge (c.reg p.1) (c.reg p.2) ∈
        qs.map (fun q => edge (c.reg q.1) (c.reg q.2))) := by
  apply Bool.eq_iff_iff.mpr
  rw [subsetTest, allTest_eval]
  simp only [decide_eq_true_eq]
  rw [List.forall_mem_map]
  simp only [anyTest_eval, decide_eq_true_eq]
  constructor
  · intro h p hp
    obtain ⟨test, ht, he⟩ := h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    have heq : edge (c.reg p.1) (c.reg p.2) = edge (c.reg q.1) (c.reg q.2) := by
      simpa only [edgeTest_eval, decide_eq_true_eq] using he
    exact List.mem_map.mpr ⟨q, hq, heq.symm⟩
  · intro h p hp
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp (h p hp)
    exact ⟨edgeTest p q, List.mem_map.mpr ⟨q, hq, rfl⟩,
      by simpa only [edgeTest_eval, decide_eq_true_eq] using heq.symm⟩

@[simp] theorem sameCycleTest_eval (rs ss : List ℕ) (c : Config) :
    (sameCycleTest rs ss).eval c = decide (SameCycle (regValues c rs) (regValues c ss)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sameCycleTest, RegTest.eval, Bool.and_eq_true, subsetTest_eval,
    decide_eq_true_eq]
  unfold SameCycle
  rw [← cyclicRegs_map rs c, ← cyclicRegs_map ss c]
  simp only [List.forall_mem_map]

@[simp] theorem earlierTest_eval (oi ov ii iv : List ℕ) (c : Config) :
    (earlierTest oi ov ii iv).eval c = decide (regValues c iv < regValues c ov ∨
      (regValues c iv = regValues c ov ∧ regValues c ii < regValues c oi)) := by
  simp [earlierTest, RegTest.eval]

theorem equalTest_safe (rs ss : List ℕ) (hr : rT ∉ rs) (hs : rT ∉ ss) :
    rT ∉ (equalTest rs ss).sources := by
  induction rs generalizing ss with
  | nil => cases ss <;> simp [equalTest, RegTest.sources]
  | cons a as ih =>
    cases ss with
    | nil => simp [equalTest, RegTest.sources]
    | cons b bs =>
      simp only [List.mem_cons, not_or] at hr hs
      simp [equalTest, RegTest.sources, hr.1, hs.1, ih _ hr.2 hs.2]

theorem lexTest_safe (rs ss : List ℕ) (hr : rT ∉ rs) (hs : rT ∉ ss) :
    rT ∉ (lexTest rs ss).sources := by
  induction rs generalizing ss with
  | nil => cases ss <;> simp [lexTest, RegTest.sources]
  | cons a as ih =>
    cases ss with
    | nil => simp [lexTest, RegTest.sources]
    | cons b bs =>
      simp only [List.mem_cons, not_or] at hr hs
      simp [lexTest, RegTest.sources, hr.1, hs.1, ih _ hr.2 hs.2]

theorem allTest_safe (ps : List RegTest) (h : ∀ p ∈ ps, rT ∉ p.sources) :
    rT ∉ (allTest ps).sources := by
  induction ps with
  | nil => simp [allTest, RegTest.sources]
  | cons p ps ih =>
    simp [allTest, RegTest.sources, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem anyTest_safe (ps : List RegTest) (h : ∀ p ∈ ps, rT ∉ p.sources) :
    rT ∉ (anyTest ps).sources := by
  induction ps with
  | nil => simp [anyTest, RegTest.sources]
  | cons p ps ih =>
    simp [anyTest, RegTest.sources, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem adjacentRegs_safe (rs : List ℕ) (h : rT ∉ rs) :
    ∀ p ∈ adjacentRegs rs, p.1 ≠ rT ∧ p.2 ≠ rT := by
  induction rs with
  | nil => simp [adjacentRegs]
  | cons a rs ih =>
    cases rs with
    | nil => simp [adjacentRegs]
    | cons b rest =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [List.mem_cons, not_or] at h
        exact ⟨Ne.symm h.1, Ne.symm h.2.1⟩
      · exact ih (fun hm => h (List.mem_cons_of_mem a hm)) p hp

theorem cyclicRegs_safe (rs : List ℕ) (h : rT ∉ rs) :
    ∀ p ∈ cyclicRegs rs, p.1 ≠ rT ∧ p.2 ≠ rT := by
  apply adjacentRegs_safe
  simp only [List.mem_append, not_or]
  exact ⟨h, fun hm => h (List.mem_of_mem_take hm)⟩

theorem subsetTest_safe (ps qs : List (ℕ × ℕ))
    (hp : ∀ p ∈ ps, p.1 ≠ rT ∧ p.2 ≠ rT)
    (hq : ∀ q ∈ qs, q.1 ≠ rT ∧ q.2 ≠ rT) :
    rT ∉ (subsetTest ps qs).sources := by
  apply allTest_safe
  intro ptest hptest
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hptest
  apply anyTest_safe
  intro qtest hqtest
  obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hqtest
  have hpp := hp p hpm
  have hqq := hq q hqm
  simp [edgeTest, RegTest.sources, hpp.1, hpp.2, hqq.1, hqq.2, eq_comm]

theorem sameCycleTest_safe (rs ss : List ℕ) (hr : rT ∉ rs) (hs : rT ∉ ss) :
    rT ∉ (sameCycleTest rs ss).sources := by
  simp only [sameCycleTest, RegTest.sources, List.mem_append, not_or]
  exact ⟨subsetTest_safe _ _ (cyclicRegs_safe rs hr) (cyclicRegs_safe ss hs),
    subsetTest_safe _ _ (cyclicRegs_safe ss hs) (cyclicRegs_safe rs hr)⟩

theorem earlierTest_safe (oi ov ii iv : List ℕ)
    (hoi : rT ∉ oi) (hov : rT ∉ ov) (hii : rT ∉ ii) (hiv : rT ∉ iv) :
    rT ∉ (earlierTest oi ov ii iv).sources := by
  simp [earlierTest, RegTest.sources, lexTest_safe _ _ hiv hov,
    equalTest_safe _ _ hiv hov, lexTest_safe _ _ hii hoi]


def distinctTest : List ℕ → RegTest
  | [] => .truth true
  | a :: as => .both (allTest (as.map fun b => .neg (.equal a b))) (distinctTest as)

@[simp] theorem distinctTest_eval (rs : List ℕ) (c : Config) :
    (distinctTest rs).eval c = decide (regValues c rs).Nodup := by
  induction rs with
  | nil => simp [distinctTest, RegTest.eval, regValues]
  | cons a as ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [distinctTest, RegTest.eval, Bool.and_eq_true, allTest_eval,
      decide_eq_true_eq, ih]
    rw [List.forall_mem_map]
    simp [RegTest.eval, regValues, List.mem_map]
    intro hn
    constructor
    · intro hall j hj
      exact Ne.symm (hall j hj)
    · intro hall j hj
      exact Ne.symm (hall j hj)

 theorem allTest_sources (ps : List RegTest) (r : ℕ)
    (h : r ∈ (allTest ps).sources) : ∃ p ∈ ps, r ∈ p.sources := by
  induction ps with
  | nil => simp [allTest, RegTest.sources] at h
  | cons p ps ih =>
    simp only [allTest, RegTest.sources, List.mem_append] at h
    rcases h with h | h
    · exact ⟨p, by simp, h⟩
    · obtain ⟨q, hq, hr⟩ := ih h
      exact ⟨q, by simp [hq], hr⟩

theorem distinctTest_sources (rs : List ℕ) (r : ℕ)
    (h : r ∈ (distinctTest rs).sources) : r ∈ rs := by
  induction rs with
  | nil => simp [distinctTest, RegTest.sources] at h
  | cons a as ih =>
    simp only [distinctTest, RegTest.sources, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨p, hp, hr⟩ := allTest_sources _ _ h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
      simp only [RegTest.sources, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp
      · exact List.mem_cons_of_mem _ hb
    · exact List.mem_cons_of_mem _ (ih h)

theorem distinctTest_safe (rs : List ℕ) (hr : rT ∉ rs) :
    rT ∉ (distinctTest rs).sources := fun h => hr (distinctTest_sources _ _ h)

theorem adjacentRegs_mem (rs : List ℕ) :
    ∀ p ∈ adjacentRegs rs, p.1 ∈ rs ∧ p.2 ∈ rs := by
  induction rs with
  | nil => simp [adjacentRegs]
  | cons a rs ih =>
    cases rs with
    | nil => simp [adjacentRegs]
    | cons b rest =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · obtain ⟨h1, h2⟩ := ih p hp
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem cyclicRegs_mem (rs : List ℕ) :
    ∀ p ∈ cyclicRegs rs, p.1 ∈ rs ∧ p.2 ∈ rs := by
  intro p hp
  obtain ⟨h1, h2⟩ := adjacentRegs_mem _ p hp
  constructor
  · rcases List.mem_append.mp h1 with h1 | h1
    · exact h1
    · exact List.mem_of_mem_take h1
  · rcases List.mem_append.mp h2 with h2 | h2
    · exact h2
    · exact List.mem_of_mem_take h2

end STACS2027.Runtimes.GeneralCycles
