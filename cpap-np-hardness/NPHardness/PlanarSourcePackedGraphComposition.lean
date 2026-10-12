module

public import NPHardness.PlanarSourcePackedGraphLists

/-! Source-order block identities used by the compiled graph phases. These
identities retain the actual forward dense clause tags inside reverse loops. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid
open Complexity.StackTableauEmitter

theorem copyGraphAt_column (flips : EndpointChoices) (k n cb lb W j : Nat) (odd : Bool)
    (bits : Nat→Nat→Bool×Bool) :
    copyGraphAt flips k n cb lb (column W j odd bits) =
      copyGraphAt flips k n cb lb (startG W j) ++
      ((List.range W).reverse.flatMap fun idx =>
        copyGraphAt flips k n (cb+2+(W-1-idx)*20) (lb+4+(W-1-idx)*48)
          (cellCNF W j idx odd (bits j (row W odd idx)))) ++
      copyGraphAt flips k n (cb+2+W*20) (lb+4+W*48) (endG W j) := by
  let F := fun idx => cellCNF W j idx odd (bits j (row W odd idx))
  have hc (i : Nat) : (F i).length=20 := Index.cell_size false W j i odd (bits j (row W odd i))
  have hl (i : Nat) : (F i).flatten.length=48 := Index.cell_size true W j i odd (bits j (row W odd i))
  have hcs : ((List.range W).reverse.flatMap F).length=W*20 := by
    have h := Index.size_flatMap_const false (List.range W).reverse F 20 (fun i _ => hc i)
    simpa only [Index.size,Bool.false_eq_true,↓reduceIte,List.length_reverse,List.length_range] using h
  have hls : ((List.range W).reverse.flatMap F).flatten.length=W*48 := by
    have h := Index.size_flatMap_const true (List.range W).reverse F 48 (fun i _ => hl i)
    simpa only [Index.size,↓reduceIte,List.length_reverse,List.length_range] using h
  change copyGraphAt flips k n cb lb (startG W j ++ (List.range W).reverse.flatMap F ++ endG W j)=_
  rw [copyGraphAt_append,copyGraphAt_append]
  have hstartc : (startG W j).length=2 := rfl
  have hstartl : (startG W j).flatten.length=4 := rfl
  rw [hstartc,hstartl,copyGraphAt_reverse_blocks flips k n (cb+2) (lb+4) 20 48 W F
    (fun i _ => hc i) (fun i _ => hl i)]
  simp only [List.length_append,List.flatten_append,List.length_append,hstartc,hstartl,hcs,hls,Nat.add_assoc]
  rfl

theorem copyGraphAt_rainbowRow (flips : EndpointChoices) (k n cb lb W j : Nat) (odd : Bool) :
    copyGraphAt flips k n cb lb ((List.range W).reverse.flatMap
      (if odd then rbOdd W j else rbEven W j)) =
      (List.range W).reverse.flatMap (fun v => copyGraphAt flips k n
        (cb+(W-1-v)*2) (lb+(W-1-v)*4)
        (if odd then rbOdd W j v else rbEven W j v)) := by
  cases odd <;>
    exact copyGraphAt_reverse_blocks flips k n cb lb 2 4 W _ (fun i _ => rfl) (fun i _ => rfl)

end STACS2027.PlanarSource.Packed
