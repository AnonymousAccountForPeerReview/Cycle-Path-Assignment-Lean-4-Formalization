module

public import ApproximationHardness.Embed.RotationRAM
import Lean.Elab.Tactic.Omega

/-! # The bounded linear RAM scan that writes the rotation list -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing
  STACS2027.PlanarAssembly

def readoutRegisters : List Nat := [1,60,61,65,127,128,129,130]

structure ReadoutFrame (start c : Config) : Prop where
  mem : c.mem = start.mem
  reg : ∀ r ∈ readoutRegisters, c.reg r = start.reg r

theorem ReadoutFrame.refl (c : Config) : ReadoutFrame c c :=
  ⟨rfl, fun _ _ => rfl⟩

theorem ReadoutFrame.step {start c : Config} (h : ReadoutFrame start c) :
    ReadoutFrame start (run rotationStep c) := by
  refine ⟨(rotationStep_mem c).trans h.mem, ?_⟩
  intro r hr
  rw [rotationStep_reg c r (by
    simp only [readoutRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
  exact h.reg r hr

theorem rotationValue_frame {start c : Config} (h : ReadoutFrame start c)
    (o : Nat → Bool) (d : Nat) : rotationValue c o d = rotationValue start o d := by
  simp only [rotationValue, h.mem, h.reg 60 (by simp [readoutRegisters]),
    h.reg 61 (by simp [readoutRegisters]), h.reg 65 (by simp [readoutRegisters]),
    h.reg 127 (by simp [readoutRegisters]), h.reg 128 (by simp [readoutRegisters]),
    h.reg 129 (by simp [readoutRegisters])]

/-- Address and orientation conditions for all darts in the scan. -/
structure ReadoutReady (S N : Nat) (c : Config) (o : Nat → Bool) : Prop where
  one : c.reg 1 = 1
  rep : ∀ d, d < N → c.reg 127 + d < S
  info : ∀ d, d < N → c.reg 60 + c.mem (c.reg 127 + d) < S
  index : ∀ d, d < N → c.reg 61 + c.mem (c.reg 127 + d) < S
  group : ∀ d, d < N → c.reg 65 + c.mem (c.reg 127 + d) < S
  indexOrientation : ∀ d, d < N →
    c.reg 130 + c.mem (c.reg 61 + c.mem (c.reg 127 + d)) < S
  groupOrientation : ∀ d, d < N →
    c.reg 130 + c.mem (c.reg 65 + c.mem (c.reg 127 + d)) < S
  next : ∀ d, d < N → c.reg 128 + d < S
  previous : ∀ d, d < N → c.reg 129 + d < S
  indexValue : ∀ d, d < N →
    c.mem (c.reg 130 + c.mem (c.reg 61 + c.mem (c.reg 127 + d))) =
      boolWord (o (c.mem (c.reg 61 + c.mem (c.reg 127 + d))))
  groupValue : ∀ d, d < N →
    c.mem (c.reg 130 + c.mem (c.reg 65 + c.mem (c.reg 127 + d))) =
      boolWord (o (c.mem (c.reg 65 + c.mem (c.reg 127 + d))))

theorem ReadoutReady.frame {S N : Nat} {start c : Config} {o : Nat → Bool}
    (h : ReadoutReady S N start o) (hf : ReadoutFrame start c) :
    ReadoutReady S N c o := by
  have h₁ := hf.reg 1 (by simp [readoutRegisters])
  have h₆₀ := hf.reg 60 (by simp [readoutRegisters])
  have h₆₁ := hf.reg 61 (by simp [readoutRegisters])
  have h₆₅ := hf.reg 65 (by simp [readoutRegisters])
  have h₁₂₇ := hf.reg 127 (by simp [readoutRegisters])
  have h₁₂₈ := hf.reg 128 (by simp [readoutRegisters])
  have h₁₂₉ := hf.reg 129 (by simp [readoutRegisters])
  have h₁₃₀ := hf.reg 130 (by simp [readoutRegisters])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact h₁.trans h.one
  all_goals simpa only [hf.mem,h₆₀,h₆₁,h₆₅,h₁₂₇,h₁₂₈,h₁₂₉,h₁₃₀] using
    (by first | exact h.rep | exact h.info | exact h.index | exact h.group |
      exact h.indexOrientation | exact h.groupOrientation | exact h.next |
      exact h.previous | exact h.indexValue | exact h.groupValue)

theorem rotationStep_ready {S N : Nat} {c : Config} {o : Nat → Bool}
    (h : ReadoutReady S N c o) (hd : c.reg 126 < N) :
    AddrOK S rotationStep c ∧
      (run rotationStep c).out = c.out ++ [rotationValue c o (c.reg 126)] := by
  exact ⟨rotationStep_addrOK c (h.rep _ hd) (h.info _ hd) (h.index _ hd)
    (h.group _ hd) (h.indexOrientation _ hd) (h.groupOrientation _ hd)
    (h.next _ hd) (h.previous _ hd), rotationStep_out c o
    (h.indexValue _ hd) (h.groupValue _ hd)⟩

/-- A fixed program writes every selected rotation entry in increasing dart order. -/
theorem rotationLoop_spec {S N : Nat} (start : Config) (o : Nat → Bool)
    (hR : ReadoutReady S N start o) :
    ∀ (n d : Nat) (c : Config), ReadoutFrame start c →
      c.reg 125 = n → c.reg 126 = d → d + n ≤ N →
      ∃ t c', ExecB S rotationLoop c t c' ∧
        t ≤ (size rotationStep + 1) * n + 1 ∧ ReadoutFrame start c' ∧
        c'.out = c.out ++ (List.range' d n).map (rotationValue start o) := by
  intro n
  induction n with
  | zero =>
    intro d c hf hc _ _
    exact ⟨1,c,.loopDone hc,by simp,hf,by simp⟩
  | succ n ih =>
    intro d c hf hc hi hb
    have hd : c.reg 126 < N := by omega
    have hr := hR.frame hf
    obtain ⟨hA,hout⟩ := rotationStep_ready hr hd
    have hE := execB_run rotationStep rotationStep_loopFree c hA
    have ht := cost_le_size rotationStep c
    have hpos := rotationStep_advance c hr.one
    obtain ⟨t,c',he,hbound,hfinal,hout'⟩ := ih (d+1) (run rotationStep c) hf.step
      (by have := hpos.2; omega) (by have := hpos.1; omega) (by omega)
    refine ⟨RAM.cost rotationStep c+t+1,c',.loopNext (by omega) hE he,
      ?_,hfinal,?_⟩
    · rw [Nat.mul_succ]; omega
    · rw [hout',hout,rotationValue_frame hf,hi]
      simp [List.range'_succ, List.append_assoc]

theorem rotationValue_correct {F : ForestData} (hF : F.Valid) (c : Config)
    (o β : Nat → Bool) {d : Nat} (hd : d < 2 * F.E)
    (hrep : c.mem (c.reg 127 + d) = F.rep d)
    (hbit : encodedBit (c.mem (c.reg 60 + F.rep d))
      (c.mem (c.reg 61 + F.rep d)) (c.mem (c.reg 65 + F.rep d)) o = β (F.rep d))
    (hn : c.mem (c.reg 128 + d) = ForestData.rotN hF (fun _ => false) d)
    (hp : c.mem (c.reg 129 + d) = ForestData.rotInvN hF (fun _ => false) d) :
    rotationValue c o d = ForestData.rotInvN hF β d := by
  unfold rotationValue
  rw [hrep]
  dsimp only
  rw [hbit,hn,hp]
  exact (ForestData.rotInvN_choice hF β hd).symm

/-- The final scan emits the exact planar rotation, once the computed tables are installed. -/
theorem rotationLoop_planar {f : CNF} (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f))
    {S : Nat} (c : Config) (o : Nat → Bool)
    (hR : ReadoutReady S (2 * f.flatten.length) c o)
    (hc : c.reg 125 = 2 * f.flatten.length) (hi : c.reg 126 = 0) (hout : c.out = [])
    (hv : ∀ d, d < 2 * f.flatten.length →
      rotationValue c o d = ForestData.rotInvN (incF_valid hf) (incBits hf o) d)
    (ho : ((incF f).sol (incF_valid hf)).Consistent o) :
    ∃ t c', ExecB S rotationLoop c t c' ∧
      t ≤ (size rotationStep + 1) * (2 * f.flatten.length) + 1 ∧
      c'.out = rotOut hf o ∧ IsPlanarRotation f c'.out := by
  obtain ⟨t,c',ht,hb,_,he⟩ := rotationLoop_spec c o hR (2*f.flatten.length) 0 c
    (.refl c) hc hi (by omega)
  have hm : (List.range (2*f.flatten.length)).map (rotationValue c o) = rotOut hf o := by
    unfold rotOut
    apply List.map_congr_left
    intro d hd
    exact hv d (List.mem_range.mp hd)
  have he' : c'.out = rotOut hf o := by
    simpa only [hout,List.nil_append,← List.range_eq_range',hm] using he
  exact ⟨t,c',ht,hb,he',he' ▸ rotOut_planar hf hp ho⟩

end STACS2027.Embed.RAMSolver
