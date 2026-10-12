module

public import Outerplanar.TriangleFamily
public import Outerplanar.PlanarMinor
import Mathlib.Tactic

/-! The finite canonical contraction graph retains the actual registered planar embedding. -/

@[expose] public section
namespace STACS2027.TriangleMatching
open STACS2027.OuterplanarMinor

theorem identifyEdges_planar {E : Finset Edge} {u v : Nat}
    (hp : Complexity.PlanarGraph E.toList) (huv : u<v) (hmem : edge u v∈E) :
    Complexity.PlanarGraph (identifyEdges u v E).toList := by
  have he : edge u v=(u,v) := by
    simp only [edge,min_eq_left huv.le,max_eq_right huv.le]
  have hc := hp.contract (Nat.ne_of_lt huv) (Finset.mem_toList.mpr (he ▸ hmem))
  apply hc.canonical.subperm
  apply (Finset.nodup_toList _).subperm
  intro e he'
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp he')
  have ha' : a∈E.toList.erase (u,v) := by
    apply E.nodup_toList.mem_erase_iff.mpr
    have H := Finset.mem_erase.mp ha
    exact ⟨by simpa only [he] using H.1,Finset.mem_toList.mpr H.2⟩
  simp only [List.mem_map]
  exact ⟨(renameTo u v a.1,renameTo u v a.2),⟨a,ha',rfl⟩,rfl⟩

theorem identifyEdges_proper {E : Finset Edge} {u v : Nat}
    (hE : ∀ e∈E,e.1<e.2) (_huv : u≠v) : ∀e∈identifyEdges u v E,e.1<e.2 := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  have hEa := hE a (Finset.mem_erase.mp ha).2
  have hneq := (Finset.mem_erase.mp ha).1
  have hn : identifyVertex u v a.1≠identifyVertex u v a.2 := by
    intro hn
    unfold identifyVertex at hn
    split_ifs at hn with hleft hright
    · omega
    · apply hneq
      apply Prod.ext <;> dsimp [edge] <;> omega
    · apply hneq
      apply Prod.ext <;> dsimp [edge] <;> omega
    · omega
  dsimp [edge]
  omega

end STACS2027.TriangleMatching
