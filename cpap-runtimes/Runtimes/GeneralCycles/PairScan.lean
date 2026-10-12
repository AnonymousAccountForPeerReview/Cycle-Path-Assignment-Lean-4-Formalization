module

public import Runtimes.GeneralCycles.EdgeScan
public import Runtimes.GeneralCycles.RegisterPredicates
import Mathlib.Tactic

/-! Sequential edge tests for a fixed register walk. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def Held (rs : List ℕ) (values : ℕ → ℕ) (c : Config) : Prop :=
  ∀ r ∈ rs, c.reg r = values r

def allPairs (g : Graph) (values : ℕ → ℕ) (pairs : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ pairs, edge (values p.1) (values p.2) ∈ g

instance (g : Graph) (values : ℕ → ℕ) (pairs : List (ℕ × ℕ)) :
    Decidable (allPairs g values pairs) := by unfold allPairs; infer_instance

def andFlag (d : ℕ) : Stmt := .ifz edgeFound (.const d 0) .skip

def scanPairs : List (ℕ × ℕ) → ℕ → Stmt
  | [], _ => .skip
  | p :: ps, d => .seq (scanEdge p.1 p.2) (.seq (andFlag d) (scanPairs ps d))

theorem held_indep {rs : List ℕ} {values : ℕ → ℕ} {W : List ℕ}
    (h : ∀ r ∈ rs, r ∉ W) : Indep W (Held rs values) := by
  intro c c' hag hh r hr
  exact (hag.reg r (h r hr)).trans (hh r hr)

theorem andFlag_spec {S d : ℕ} {P : Config → Prop} (b q : Bool)
    (hP : Indep [d] P) :
    HTB S (andFlag d)
      (fun c => P c ∧ c.reg d = (if b then 1 else 0) ∧
        c.reg edgeFound = (if q then 1 else 0))
      (fun c => P c ∧ c.reg d = (if b && q then 1 else 0)) 3 := by
  refine HTB.run_le (by simp [andFlag, LoopFree]) (by simp [andFlag, size]) ?_
  intro c ⟨hp, hd, hq⟩
  refine ⟨AddrOK.of_memFree rfl, ?_⟩
  have hpc : P (c.setReg d 0) := hP.setReg (by simp) 0 hp
  cases b <;> cases q <;> simp_all [andFlag]

theorem edgeBody_size_le (a b : ℕ) : size (edgeBody a b) ≤ 200 := by
  simp [edgeBody, readEdge, markEdge, inputEdgeTest, RegTest.branch, size, addc, ifLt, ifEq]

theorem scanPairs_spec {g : Graph} {memory : ℕ → ℕ} {P : Config → Prop}
    {rs : List ℕ} {values : ℕ → ℕ} {S d : ℕ}
    (pairs : List (ℕ × ℕ)) (b : Bool)
    (hregs : ∀ r ∈ rs, 100 ≤ r) (hd : 40 ≤ d) (hd' : d < 50)
    (hpairs : ∀ p ∈ pairs, p.1 ∈ rs ∧ p.2 ∈ rs)
    (hP : Indep (d :: edgeScratch) P) (hmem : GraphMemory g memory)
    (hS : 2 * g.length + 1 ≤ S) :
    HTB S (scanPairs pairs d)
      (fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧
        Held rs values c ∧ c.reg d = (if b then 1 else 0))
      (fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧
        Held rs values c ∧ c.reg d = (if b && decide (allPairs g values pairs) then 1 else 0))
      (pairs.length * (208 * (g.length + 1) + 3) + 1) := by
  induction pairs generalizing b with
  | nil =>
    simpa [scanPairs, allPairs] using
      (HTB.skip : HTB S .skip _ _ 1)
  | cons p ps ih =>
    have hpair := hpairs p (by simp)
    have hpa : 50 ≤ p.1 := by have := hregs p.1 hpair.1; omega
    have hpb : 50 ≤ p.2 := by have := hregs p.2 hpair.2; omega
    let Base := fun c => P c ∧ c.reg edgeCount = g.length ∧ c.mem = memory ∧ Held rs values c
    have hBase : Indep (d :: edgeScratch) Base := by
      intro c c' hag ⟨hp, hn, hm, hh⟩
      have hcount : edgeCount ∉ d :: edgeScratch := by
        simp [edgeCount, edgeScratch, rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound]
        omega
      have hheld : Indep (d :: edgeScratch) (Held rs values) := held_indep (by
        intro r hr
        have h := hregs r hr
        simp [edgeScratch, rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound]
        omega)
      exact ⟨hP _ _ hag hp, (hag.reg _ hcount).trans hn, hag.mem.trans hm,
        hheld _ _ hag hh⟩
    have hQ : Indep edgeScratch (fun c => Base c ∧ c.reg d = (if b then 1 else 0)) := by
      intro c c' hag ⟨hc, hf⟩
      have hwide := hag.mono (show ∀ r ∈ edgeScratch, r ∈ d :: edgeScratch by
        intro r hr; exact List.mem_cons_of_mem d hr)
      have hnd : d ∉ edgeScratch := by
        simp [edgeScratch, rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound]
        omega
      exact ⟨hBase _ _ hwide hc, (hag.reg _ hnd).trans hf⟩
    have hs := scanEdge_spec (x := values p.1) (y := values p.2)
      (P := fun c => Base c ∧ c.reg d = (if b then 1 else 0))
      hpa hpb hQ hmem hS
    have hscan : HTB S (scanEdge p.1 p.2)
        (fun c => Base c ∧ c.reg d = (if b then 1 else 0))
        (fun c => Base c ∧ c.reg d = (if b then 1 else 0) ∧
          c.reg edgeFound = (if decide (edge (values p.1) (values p.2) ∈ g) then 1 else 0))
        (208 * (g.length + 1)) := hs.mono (by
          rintro c ⟨hc, hf⟩
          exact ⟨⟨hc, hf⟩, hc.2.1, hc.2.2.1, hc.2.2.2 p.1 hpair.1,
            hc.2.2.2 p.2 hpair.2⟩) (by
          rintro c ⟨⟨hc, hf⟩, _, _, _, _, he⟩
          exact ⟨hc, hf, by simpa using he⟩) (by
          have := edgeBody_size_le p.1 p.2
          nlinarith [Nat.zero_le g.length])
    have hupdate := andFlag_spec (S := S) (P := Base) (d := d) b
      (decide (edge (values p.1) (values p.2) ∈ g))
      (hBase.mono (by
        intro r hr
        exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))
    have hrec := ih (b && decide (edge (values p.1) (values p.2) ∈ g))
      (fun p hp => hpairs p (by simp [hp]))
    have hrec' := hrec.pre (P' := fun c => Base c ∧
      c.reg d = (if b && decide (edge (values p.1) (values p.2) ∈ g) then 1 else 0)) (by
      rintro c ⟨⟨hp, hn, hm, hh⟩, hf⟩
      exact ⟨hp, hn, hm, hh, hf⟩)
    refine (hscan.seq (hupdate.seq hrec')).mono ?_ ?_ ?_
    · rintro c ⟨hp, hn, hm, hh, hf⟩
      exact ⟨⟨hp, hn, hm, hh⟩, hf⟩
    · rintro c ⟨hp, hn, hm, hh, hf⟩
      refine ⟨hp, hn, hm, hh, ?_⟩
      have hall : decide (allPairs g values (p :: ps)) =
          (decide (edge (values p.1) (values p.2) ∈ g) && decide (allPairs g values ps)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Bool.and_eq_true]
        constructor
        · intro h
          exact ⟨h p (by simp), fun q hq => h q (List.mem_cons_of_mem p hq)⟩
        · rintro ⟨hhead, htail⟩ q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hhead
          · exact htail q hq
      rw [hall]
      simpa [Bool.and_assoc] using hf
    · simp only [List.length_cons]
      rw [Nat.add_mul]
      omega

end STACS2027.Runtimes.GeneralCycles
