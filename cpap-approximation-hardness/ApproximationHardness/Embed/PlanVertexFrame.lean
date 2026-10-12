module

public import ApproximationHardness.Embed.PlanVertexLoop
public import ApproximationHardness.Embed.PlanOrdinaryBounds
public import ApproximationHardness.Embed.PlanDistinguishedValues
import Lean.Elab.Tactic.Omega

/-! Representative dispatch and finite memory frames for the vertex-plan compiler. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem vertexFrame_run_skip (c : Config) : run .skip c=c := rfl

/-- The representative branch follows the fixed initialization header. -/
def vertexFinish : Stmt := .ifz test (seqs [ordinaryParts,topParts]) .skip

theorem run_vertexTableStep (c : Config) :
    run vertexTableStep c=run vertexFinish (run vertexHeader (run distinguishedProgram c)) := by
  simp only [vertexTableStep,vertexFinish,vertexHeader,storeVertexGroups,vertexLookup,
    seqs,run_seq,vertexFrame_run_skip]

/-- The full initialization header dispatches exactly the representative indices. -/
theorem vertexHeader_test {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {r : Nat} (hr : r<2*G.E) (hv : c.reg vertex=r) :
    (run vertexHeader c).reg test=0 ↔ G.rep r=r := by
  generalize he₁ : run storeVertexGroups c=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc.storeVertexGroups
  have hv₁ : c₁.reg vertex=r := by rw [←he₁]; exact (storeVertexGroups_reg c vertex (by decide)).trans hv
  generalize he₂ : run (clearParts vertex) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ clearParts_context hc₁ vertex (by decide)
  have hv₂ : c₂.reg vertex=r := by rw [←he₂,clearParts_reg _ _ _ (by decide),hv₁]
  generalize he₃ : run (clearParts topVertex) c₂=c₃
  have hc₃ : Context L G s c₃ := he₃ ▸ clearParts_context hc₂ topVertex (by decide)
  have hv₃ : c₃.reg vertex=r := by rw [←he₃,clearParts_reg _ _ _ (by decide),hv₂]
  simp only [vertexHeader,seqs,run_seq,vertexFrame_run_skip,he₁,he₂,he₃]
  exact vertexLookup_test hc₃ hr hv₃

/-- Invalid representative indices have empty ordinary and synthetic plan nodes. -/
theorem parts_nonrepresentative {G : DG} {s : DS} {r : Nat}
    (hr : r<2*G.E) (hn : G.rep r≠r) :
    (G.fd s).parts r=[] ∧ (G.fd s).parts (2*G.E+r)=[] := by
  have hv : ¬(G.fd s).IsVertex r := by intro h; exact hn h.2
  have ht : ¬(G.fd s).IsTop r := by intro h; have := h.1; change 2*G.E≤r at this; omega
  have hvtop : ¬(G.fd s).IsVertex (2*G.E+r) := by intro h;have := h.1; change 2*G.E+r<2*G.E at this;omega
  have httop : ¬(G.fd s).IsTop (2*G.E+r) := by
    intro h
    have hv' : (G.fd s).IsVertex r := by simpa [DG.fd] using h.2.1
    exact hv hv'
  exact ⟨ForestData.parts_other hv ht,ForestData.parts_other hvtop httop⟩

/-- A one-vertex instruction may change only its distinguished cache and two node entries. -/
def VertexMemFrame (L : DFSRAM.Layout) (G : DG) (r : Nat) (m n : Nat → Nat) : Prop :=
  ∀a,a≠(solverLayout L).limit+r →
    (∀j,j∈[15,16,17,18,19,20] →
      a≠(solverLayout L).cell j r ∧ a≠(solverLayout L).cell j (2*G.E+r)) → m a=n a

/-- Later vertex instructions protect every completed earlier cache and node entry. -/
theorem VertexEntry.frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c d : Config}
    {r q : Nat} (hr : r<2*G.E) (hq : q<r) (hw : 4*G.E≤L.width)
    (h : VertexEntry L (G.fd s) c q) (hf : VertexMemFrame L G r d.mem c.mem) :
    VertexEntry L (G.fd s) d q := by
  have hqlo : q<(solverLayout L).width := by dsimp [solverLayout];omega
  have hrlo : r<(solverLayout L).width := by dsimp [solverLayout];omega
  have hqtop : 2*G.E+q<(solverLayout L).width := by dsimp [solverLayout];omega
  have hrtop : 2*G.E+r<(solverLayout L).width := by dsimp [solverLayout];omega
  have hcache : d.mem ((solverLayout L).limit+q)=c.mem ((solverLayout L).limit+q) := by
    apply hf _ (by omega)
    intro j hj
    have hjb : j<22 := by simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hj;omega
    have h₁ := (solverLayout L).cell_lt hjb hrlo
    have h₂ := (solverLayout L).cell_lt hjb hrtop
    constructor <;> omega
  have hcell (j : Nat) (hj : j<22) (i : Nat) (hi : i=q ∨ i=2*G.E+q) :
      d.mem ((solverLayout L).cell j i)=c.mem ((solverLayout L).cell j i) := by
    have hil : i<(solverLayout L).width := by rcases hi with hi | hi <;> subst i <;> assumption
    have hl := (solverLayout L).cell_lt hj hil
    apply hf _ (by omega)
    intro k hk
    constructor
    · intro he; have hinj := (solverLayout L).cell_injective hil hrlo he
      rcases hi with hi | hi <;> omega
    · intro he; have hinj := (solverLayout L).cell_injective hil hrtop he
      rcases hi with hi | hi <;> omega
  refine ⟨hcache.trans h.cache,?_,?_,?_,?_,?_,?_⟩
  · exact (hcell 15 (by decide) q (Or.inl rfl)).trans h.ordinaryGroup
  · exact (hcell 16 (by decide) q (Or.inl rfl)).trans h.ordinaryCount
  · simpa only [PartSlots,hcell 17 (by decide) q (Or.inl rfl),hcell 18 (by decide) q (Or.inl rfl),
      hcell 19 (by decide) q (Or.inl rfl),hcell 20 (by decide) q (Or.inl rfl)] using h.ordinarySlots
  · exact (hcell 15 (by decide) (2*G.E+q) (Or.inr rfl)).trans h.topGroup
  · exact (hcell 16 (by decide) (2*G.E+q) (Or.inr rfl)).trans h.topCount
  · change PartSlots (solverLayout L) d.mem (2*G.E+q) ((G.fd s).parts (2*G.E+q))
    have hs : PartSlots (solverLayout L) c.mem (2*G.E+q) ((G.fd s).parts (2*G.E+q)) := h.topSlots
    simpa only [PartSlots,hcell 17 (by decide) (2*G.E+q) (Or.inr rfl),
      hcell 18 (by decide) (2*G.E+q) (Or.inr rfl),hcell 19 (by decide) (2*G.E+q) (Or.inr rfl),
      hcell 20 (by decide) (2*G.E+q) (Or.inr rfl)] using hs

end STACS2027.Embed.PlanRAM
