module

public import ApproximationHardness.Sim.Parse
public import ApproximationHardness.RAM.Decode.Program
import Lean.Elab.Tactic.Omega

/-!
# Reading the code of a list of paths

The code of a list of paths `ps` is `encodePaths ps`: the list of paths, each a list of edges, each
edge its two endpoints, all numbers in unary (the registered foundation's list format).
`parsePaths` reads it bit by bit and appends `pathsCode ps` to the even memory cells
(`xok_parsePaths`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity.SAT

/-- The code of an edge: its two endpoints in unary. -/
def encodeEdge (e : Edge) : List Bool := writeNat e.1 ++ writeNat e.2

/-- The code of a path: the list of its edges. -/
def encodePath (p : List Edge) : List Bool := writeList encodeEdge p

/-- The code of a list of paths. -/
def encodePaths (ps : List (List Edge)) : List Bool := writeList encodePath ps

theorem encodeEdge_length (e : Edge) : (encodeEdge e).length = e.1 + e.2 + 2 := by
  simp [encodeEdge]; omega

theorem encodePath_length_pos (p : List Edge) : 1 ≤ (encodePath p).length := by
  simp [encodePath, writeList]; omega

def parseEdge : XStmt := xseqs [.sub pCL pCL pONE, readNat pV, putNum pV, readNat pV, putNum pV]

theorem xok_parseEdge (e : Edge) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodeEdge e ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parseEdge c c' (11 * (encodeEdge e).length) ∧ c'.inp = rest ∧ c'.mem = memOf (L ++ RAM.edgeCode e) ∧
      c'.reg pP = 2 * (L ++ RAM.edgeCode e).length ∧ c'.reg pCL = c.reg pCL - 1 ∧ c'.out = c.out ∧
      ∀ i, i ≠ pCL → i ≠ pV → i ≠ pB → i ≠ pT → i ≠ pFL → i ≠ pP → c'.reg i = c.reg i := by
  have s1 := xok_sub pCL pCL pONE c
  generalize hc1 : c.setReg pCL (c.reg pCL - c.reg pONE) = c1 at s1
  have c1r : ∀ i, i ≠ pCL → c1.reg i = c.reg i := by intro i hi; rw [← hc1]; simp [XConfig.setReg, hi]
  have c1CL : c1.reg pCL = c.reg pCL - 1 := by rw [← hc1]; simp [XConfig.setReg, hone]
  obtain ⟨c2, s2, v2, i2, m2, o2, r2⟩ := xok_readNat pV (by decide) (by decide) (by decide) (by decide) c1 e.1
    (writeNat e.2 ++ rest) (by rw [← hc1]; simp [XConfig.setReg, hin, encodeEdge])
    (by rw [c1r pONE (by decide), hone])
  obtain ⟨c3, s3, m3, p3, i3, o3, r3⟩ := xok_putNum pV (by decide) c2 L
    (by rw [r2 pP (by decide) (by decide) (by decide) (by decide), c1r pP (by decide), hP])
    (by rw [m2, ← hc1]; exact hm)
    (by rw [r2 pTWO (by decide) (by decide) (by decide) (by decide), c1r pTWO (by decide), htwo])
  obtain ⟨c4, s4, v4, i4, m4, o4, r4⟩ := xok_readNat pV (by decide) (by decide) (by decide) (by decide) c3 e.2 rest
    (by rw [i3, i2])
    (by rw [r3 pONE (by decide), r2 pONE (by decide) (by decide) (by decide) (by decide), c1r pONE (by decide), hone])
  obtain ⟨c5, s5, m5, p5, i5, o5, r5⟩ := xok_putNum pV (by decide) c4 (L ++ [c2.reg pV])
    (by rw [r4 pP (by decide) (by decide) (by decide) (by decide), p3]) (by rw [m4, m3])
    (by rw [r4 pTWO (by decide) (by decide) (by decide) (by decide), r3 pTWO (by decide),
      r2 pTWO (by decide) (by decide) (by decide) (by decide), c1r pTWO (by decide), htwo])
  rw [v2, v4] at m5 p5
  refine ⟨c5, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (xok_skip _)))))).mono ?_, by rw [i5, i4], ?_, ?_, ?_,
    by rw [o5, o4, o3, o2, ← hc1]; rfl, ?_⟩
  · rw [encodeEdge_length]; omega
  · rw [m5]; simp [RAM.edgeCode]
  · rw [p5]; simp [RAM.edgeCode]
  · rw [r5 pCL (by decide), r4 pCL (by decide) (by decide) (by decide) (by decide), r3 pCL (by decide),
      r2 pCL (by decide) (by decide) (by decide) (by decide), c1CL]
  · intro i a1 a2 a3 a4 a5 a6
    rw [r5 i a6, r4 i a2 a3 a4 a5, r3 i a6, r2 i a2 a3 a4 a5, c1r i a1]

def parsePath : XStmt := xseqs [.sub pCNT pCNT pONE, readNat pCL, putNum pCL, .loop pCL parseEdge]

theorem xok_parsePath (p : List Edge) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodePath p ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parsePath c c' (13 * (encodePath p).length) ∧ c'.inp = rest ∧
      c'.mem = memOf (L ++ RAM.pathCode p) ∧ c'.reg pP = 2 * (L ++ RAM.pathCode p).length ∧
      c'.reg pCNT = c.reg pCNT - 1 ∧ c'.out = c.out ∧ ∀ i, ParseFree i → c'.reg i = c.reg i := by
  have s1 := xok_sub pCNT pCNT pONE c
  obtain ⟨c2, s2, v2, i2, m2, o2, r2⟩ := xok_readNat pCL (by decide) (by decide) (by decide) (by decide)
    (c.setReg pCNT (c.reg pCNT - c.reg pONE)) p.length (writeValues encodeEdge p ++ rest)
    (by simp [XConfig.setReg, hin, encodePath, writeList])
    (by simp [XConfig.setReg, hone])
  have hP2 : c2.reg pP = 2 * L.length := by
    rw [r2 pP (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, hP]
  obtain ⟨c3, s3, m3, p3, i3, o3, r3⟩ := xok_putNum pCL (by decide) c2 L hP2 (by rw [m2]; exact hm)
    (by rw [r2 pTWO (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, htwo])
  rw [v2] at m3 p3
  let I : List Edge → XConfig → Prop := fun pre d =>
    d.inp = writeValues encodeEdge (p.drop pre.length) ++ rest ∧
      d.mem = memOf (L ++ [p.length] ++ pre.flatMap RAM.edgeCode) ∧
      d.reg pP = 2 * (L ++ [p.length] ++ pre.flatMap RAM.edgeCode).length ∧ d.reg pCL = p.length - pre.length ∧
      d.out = c.out ∧ ∀ i, i ≠ pCL → i ≠ pV → i ≠ pB → i ≠ pT → i ≠ pFL → i ≠ pP → d.reg i = c3.reg i
  have hI0 : I [] c3 := ⟨by rw [i3, i2]; rfl, by rw [m3]; simp, by rw [p3]; simp,
    by rw [r3 pCL (by decide), v2]; simp, by rw [o3, o2]; rfl, fun _ _ _ _ _ _ _ => rfl⟩
  have hone3 : c3.reg pONE = 1 := by
    rw [r3 pONE (by decide), r2 pONE (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, hone]
  have htwo3 : c3.reg pTWO = 2 := by
    rw [r3 pTWO (by decide), r2 pTWO (by decide) (by decide) (by decide) (by decide)]; simp [XConfig.setReg, htwo]
  obtain ⟨c4, s4, hI4⟩ := xok_listLoop (a := pCL) (body := parseEdge) p I (fun e => 11 * (encodeEdge e).length)
    (by
      intro pre e suf d hp ⟨d1, d2, d3, d4, d5, d6⟩
      have hl : pre.length < p.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      rw [writeValues_drop encodeEdge hp] at d1
      obtain ⟨d', s', i', m', p', cl', o', r'⟩ := xok_parseEdge e (writeValues encodeEdge suf ++ rest) d _
        (by rw [d1, List.append_assoc]) d3 d2
        (by rw [d6 pONE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hone3])
        (by rw [d6 pTWO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), htwo3])
      refine ⟨d', s', ?_, ?_, ?_, ?_, by rw [o', d5], fun i a1 a2 a3 a4 a5 a6 => by
        rw [r' i a1 a2 a3 a4 a5 a6, d6 i a1 a2 a3 a4 a5 a6]⟩
      · rw [i']; simp only [List.length_append, List.length_singleton]
        rw [show p.drop (pre.length + 1) = suf by subst hp; simp]
      · rw [m']; simp
      · rw [p']; simp
      · rw [cl', d4]; simp; omega)
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c3 hI0
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := hI4
  have hlen : (encodePath p).length = p.length + 1 + (writeValues encodeEdge p).length := by
    simp [encodePath, writeList]
  have hsum := sum_cost_le encodeEdge (fun e => by rw [encodeEdge_length]; omega) 11 p
  refine ⟨c4, (s1.seq (s2.seq (s3.seq (s4.seq (xok_skip _))))).mono ?_, ?_, ?_, ?_, ?_, by rw [e5], ?_⟩
  · rw [hlen]; omega
  · rw [e1, List.drop_eq_nil_of_le (Nat.le_refl _)]; rfl
  · rw [e2]; simp [RAM.pathCode]
  · rw [e3]; simp [RAM.pathCode]
  · rw [e6 pCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r3 pCNT (by decide), r2 pCNT (by decide) (by decide) (by decide) (by decide)]
    simp [XConfig.setReg, hone]
  · intro i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    rw [e6 i a6 a8 a1 a3 a2 a4, r3 i a4, r2 i a6 a1 a3 a2]; simp [XConfig.setReg, a5]

def parsePaths : XStmt := xseqs [readNat pCNT, putNum pCNT, .loop pCNT parsePath]

theorem xok_parsePaths (ps : List (List Edge)) (rest : List Bool) (c : XConfig) (L : List Nat)
    (hin : c.inp = encodePaths ps ++ rest) (hP : c.reg pP = 2 * L.length) (hm : c.mem = memOf L)
    (hone : c.reg pONE = 1) (htwo : c.reg pTWO = 2) :
    ∃ c', XOk parsePaths c c' (14 * ((encodePaths ps).length + 1)) ∧ c'.inp = rest ∧
      c'.mem = memOf (L ++ RAM.pathsCode ps) ∧ c'.out = c.out ∧ ∀ i, ParseFree i → c'.reg i = c.reg i := by
  obtain ⟨c1, s1, v1, i1, m1, o1, r1⟩ := xok_readNat pCNT (by decide) (by decide) (by decide) (by decide) c ps.length
    (writeValues encodePath ps ++ rest) (by rw [hin]; simp [encodePaths, writeList]) hone
  obtain ⟨c2, s2, m2, p2, i2, o2, r2⟩ := xok_putNum pCNT (by decide) c1 L
    (by rw [r1 pP (by decide) (by decide) (by decide) (by decide), hP]) (by rw [m1, hm])
    (by rw [r1 pTWO (by decide) (by decide) (by decide) (by decide), htwo])
  rw [v1] at m2 p2
  have hone2 : c2.reg pONE = 1 := by rw [r2 pONE (by decide), r1 pONE (by decide) (by decide) (by decide) (by decide), hone]
  have htwo2 : c2.reg pTWO = 2 := by rw [r2 pTWO (by decide), r1 pTWO (by decide) (by decide) (by decide) (by decide), htwo]
  let I : List (List Edge) → XConfig → Prop := fun pre d =>
    d.inp = writeValues encodePath (ps.drop pre.length) ++ rest ∧
      d.mem = memOf (L ++ [ps.length] ++ pre.flatMap RAM.pathCode) ∧
      d.reg pP = 2 * (L ++ [ps.length] ++ pre.flatMap RAM.pathCode).length ∧ d.reg pCNT = ps.length - pre.length ∧
      d.reg pONE = 1 ∧ d.reg pTWO = 2 ∧ d.out = c.out ∧ ∀ i, ParseFree i → d.reg i = c.reg i
  have hI0 : I [] c2 := ⟨by rw [i2, i1]; rfl, by rw [m2]; simp, by rw [p2]; simp,
    by rw [r2 pCNT (by decide), v1]; simp, hone2, htwo2, by rw [o2, o1], fun i ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ => by
      rw [r2 i a4, r1 i a5 a1 a3 a2]⟩
  obtain ⟨c3, s3, hI3⟩ := xok_listLoop (a := pCNT) (body := parsePath) ps I (fun p => 13 * (encodePath p).length)
    (by
      intro pre p suf d hp ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩
      have hl : pre.length < ps.length := by have := congrArg List.length hp; simp at this; omega
      refine ⟨by rw [d4]; omega, ?_⟩
      rw [writeValues_drop encodePath hp] at d1
      obtain ⟨d', s', i', m', p', n', o', r'⟩ := xok_parsePath p (writeValues encodePath suf ++ rest) d _
        (by rw [d1, List.append_assoc]) d3 d2 d5 d6
      refine ⟨d', s', ?_, ?_, ?_, ?_, ?_, ?_, by rw [o', d7], fun i hi => by rw [r' i hi, d8 i hi]⟩
      · rw [i', show ps.drop (pre ++ [p]).length = suf by subst hp; simp]
      · rw [m']; simp
      · rw [p']; simp
      · rw [n', d4]; simp; omega
      · rw [r' pONE (by decide), d5]
      · rw [r' pTWO (by decide), d6])
    (by intro d ⟨_, _, _, d4, _⟩; rw [d4]; simp)
    c2 hI0
  obtain ⟨e1, e2, -, -, -, -, e7, e8⟩ := hI3
  have hlen : (encodePaths ps).length = ps.length + 1 + (writeValues encodePath ps).length := by
    simp [encodePaths, writeList]
  have hsum := sum_cost_le encodePath encodePath_length_pos 13 ps
  refine ⟨c3, (s1.seq (s2.seq (s3.seq (xok_skip _)))).mono ?_, ?_, ?_, e7, e8⟩
  · rw [hlen]; omega
  · rw [e1, List.drop_eq_nil_of_le (Nat.le_refl _)]; rfl
  · rw [e2]; simp [RAM.pathsCode]

end STACS2027.Sim
