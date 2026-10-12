module

public import Runtimes.Sort.EnumeratedFront
public import Runtimes.Flow.SortedConstruction
public import Runtimes.NamedHoles
import Mathlib.Tactic

/-!
# Sorting construction for any four-cycle enumeration

This construction uses the same stable sorting algorithm and output phases as the
canonical construction, with the front end now proved for arbitrary supplied cycle lists.
The network and assignment positions retain the supplied order. The only cited algorithm
in the final pipeline is the minimum-cost flow solver interface.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- The sorted network construction accepts cycles in their supplied order. -/
def buildEnumeratedSorted : Stmt := .seq ZeroCost.stepInit (.seq EnumeratedSort.front out4)

/-- The end of the label-independent workspace. -/
def enumeratedBuildSpace (g : Graph) (cs : List Cycle) : ℕ :=
  EnumeratedSort.fEnd g cs 4 (bD g cs 4)

/-- A uniform construction-time constant. -/
def enumeratedBuildConstant : ℕ := 4 * EnumeratedSort.CF + 200

/-- The front end supplies the precise data read by the four-cycle output phases. -/
theorem ob_of_enumeratedFront {g : Graph} {cs : List Cycle} {k F : ℕ} {c : Config}
    (h : EnumeratedSort.FrontPost g cs k F c) :
    OB cs k (EnumeratedSort.fEID g cs k F) (EnumeratedSort.fCNT g cs k F) c :=
  ⟨h.ga.rt, h.rne, h.reid, h.rcnt, h.meid, h.mcnt⟩

/-- The sorted RAM construction for any list of simple four-cycles. -/
theorem enumeratedBuild_spec {g : Graph} {cs : List Cycle}
    (hcs : ∀ c ∈ cs, IsCycle g 4 c) {S : ℕ} (hS : enumeratedBuildSpace g cs ≤ S) :
    HTB S buildEnumeratedSorted (fun c => c = initial (flowInput g cs 4))
      (fun c => c.out = netEnc4 cs)
      (enumeratedBuildConstant * ((cs.length + 1) * (Nat.clog 2 (4 * cs.length) + 1))) := by
  have hf := EnumeratedSort.ffits g cs 4 hcs (bD g cs 4) hS
  have hd : bD g cs 4 ≤ S := by
    have := hf.1
    omega
  have h₁ := stepInit_spec hcs hd
  have h₂ : HTB S EnumeratedSort.front (InitPost g cs 4)
      (fun c => OB cs 4 (EnumeratedSort.fEID g cs 4 (bD g cs 4))
        (EnumeratedSort.fCNT g cs 4 (bD g cs 4)) c ∧ c.out = [])
      (EnumeratedSort.CF * (EnumeratedSort.fL g cs 4 *
        (Nat.clog 2 (EnumeratedSort.fL g cs 4) + 1) + 1)) :=
    HTB.of_forall fun c₀ hI =>
      (EnumeratedSort.front_spec g cs 4 hcs c₀
        (EnumeratedSort.frontIn_of_initPost hcs hI)
        (by rw [hI.rfree]; exact hS)).post fun c ⟨hP, _, ho⟩ => by
          rw [hI.rfree] at hP
          exact ⟨ob_of_enumeratedFront hP, by rw [ho, hI.rout]⟩
  have h₃ := out4_specA hcs (S := S) hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  refine ((h₁.seq (h₂.seq h₃)).pre fun c hc => hc).weaken ?_
  change 5 * cs.length + 16 + (EnumeratedSort.CF *
    (4 * cs.length * (Nat.clog 2 (4 * cs.length) + 1) + 1) +
      (130 * cs.length + 30)) ≤ enumeratedBuildConstant *
        ((cs.length + 1) * (Nat.clog 2 (4 * cs.length) + 1))
  unfold enumeratedBuildConstant
  have hlog : 1 ≤ Nat.clog 2 (4 * cs.length) + 1 := by omega
  nlinarith [Nat.zero_le EnumeratedSort.CF]

/-- The construction workspace is linear in the input size and cycle count. -/
theorem enumeratedBuild_memory {g : Graph} {cs : List Cycle}
    (hcs : ∀ c ∈ cs, IsCycle g 4 c) :
    enumeratedBuildSpace g cs ≤ 2 * g.length + 64 * cs.length + 4 := by
  have := EnumeratedSort.fEnd_le g cs 4 hcs (bD g cs 4)
  have hD : bD g cs 4 = 2 * g.length + 3 + 4 * cs.length := rfl
  have hL : EnumeratedSort.fL g cs 4 = 4 * cs.length := rfl
  unfold enumeratedBuildSpace
  omega

/-- The full sorting-network claim, including arbitrary cycle permutations, follows from
the proved sorting construction, the proved extraction, and the cited flow-solver interface. -/
theorem sortedNetworkConstruction : SortedNetworkConstruction := by
  intro F T hF
  refine ⟨buildEnumeratedSorted, extract4, 4 * enumeratedBuildConstant + 64, fun g cs hperm => ?_⟩
  have hcs := isCycle_of_perm hperm
  obtain ⟨t₁, ht₁, h₁⟩ := HTB.computesIn (enumeratedBuild_spec hcs le_rfl)
  obtain ⟨out, pos, _, t₂, t₃, _, _, h₂, ht₂, h₃, ht₃, _, hl, hp, hv, ho⟩ :=
    cpap4_flow_core hF hperm
  have hm := enumeratedBuild_memory hcs
  have hn : n4 cs ≤ 6 * cs.length + 2 := by
    have := length_eList4 hcs
    simp only [n4]
    omega
  refine ⟨netEnc4 cs, out, pos, t₁, t₂, t₃, h₁.mono ?_, ?_,
    ⟨num4 cs, n4 cs, net4 cs, goodNet4 hcs, rfl, length_net4 hcs, hn,
      net4_hasAssignment_iff hperm⟩, h₂, ht₂, h₃.mono ?_, ?_, hl, hp, hv, ho⟩
  · refine hm.trans ?_
    calc
      2 * g.length + 64 * cs.length + 4 ≤ 64 * (cs.length + g.length + 1) := by omega
      _ ≤ (4 * enumeratedBuildConstant + 64) * (cs.length + g.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
  · have hlog := sortedBuild_logarithm cs.length
    calc
      t₁ ≤ enumeratedBuildConstant * ((cs.length + 1) *
          (Nat.clog 2 (4 * cs.length) + 1)) := ht₁
      _ ≤ enumeratedBuildConstant * ((cs.length + 1) *
          (4 * (Nat.log 2 (cs.length + 1) + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlog)
      _ = 4 * enumeratedBuildConstant * ((cs.length + 1) *
          (Nat.log 2 (cs.length + 1) + 1)) := by ring
      _ ≤ (4 * enumeratedBuildConstant + 64) * ((cs.length + g.length + 1) *
          (Nat.log 2 (cs.length + 1) + 1)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
  · have hD : bD g cs 4 = 2 * g.length + 3 + 4 * cs.length := rfl
    calc
      bD g cs 4 + 6 * cs.length + 1 ≤ 64 * (cs.length + g.length + 1) := by omega
      _ ≤ (4 * enumeratedBuildConstant + 64) * (cs.length + g.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
  · calc
      t₃ ≤ 18 * cs.length + 20 := ht₃
      _ ≤ 64 * (cs.length + g.length + 1) := by omega
      _ ≤ (4 * enumeratedBuildConstant + 64) * (cs.length + g.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)

end STACS2027.Runtimes.Flow
