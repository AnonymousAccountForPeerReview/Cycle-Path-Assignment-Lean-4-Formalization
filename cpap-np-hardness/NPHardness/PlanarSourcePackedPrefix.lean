module

public import NPHardness.PlanarSourcePackedIndex

/-! Exact block prefixes, retaining the registered grid's clause order. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed.Index
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid

def BlockAt (f g : CNF) (start : Bool → Nat) : Prop :=
  ∃ before after, f = before ++ g ++ after ∧ ∀ b, size b before = start b

theorem BlockAt.append_left {f g : CNF} {start : Bool → Nat}
    (h : BlockAt f g start) (pre : CNF) :
    BlockAt (pre++f) g (fun b => size b pre+start b) := by
  obtain ⟨a,z,he,hs⟩ := h
  exact ⟨pre++a,z,by rw [he]; simp [List.append_assoc],fun b => by rw [size_append,hs]⟩

theorem BlockAt.append_right {f g : CNF} {start : Bool → Nat}
    (h : BlockAt f g start) (post : CNF) : BlockAt (f++post) g start := by
  obtain ⟨a,z,he,hs⟩ := h
  exact ⟨a,z++post,by rw [he]; simp [List.append_assoc],hs⟩

theorem BlockAt.trans {f g h : CNF} {a b : Bool → Nat}
    (hf : BlockAt f g a) (hg : BlockAt g h b) : BlockAt f h (fun t => a t+b t) := by
  obtain ⟨p,q,he,hs⟩ := hf
  obtain ⟨r,s,he',hs'⟩ := hg
  exact ⟨p++r,s++q,by rw [he,he']; simp [List.append_assoc],fun t => by rw [size_append,hs,hs']⟩

theorem reverse_range_split (n k : Nat) (hk : k<n) :
    (List.range n).reverse =
      (List.range' (k+1) (n-(k+1))).reverse ++ [k] ++ (List.range k).reverse := by
  have h := List.range_add (n := k+1) (m := n-(k+1))
  rw [show k+1+(n-(k+1))=n by omega,← List.range'_eq_map_range] at h
  rw [h,List.range_succ,List.reverse_append,List.reverse_append]
  simp [List.append_assoc]

theorem reverse_range_block (n k : Nat) (hk : k<n) (f : Nat → CNF) (c : Bool → Nat)
    (hs : ∀ b i, i<n → size b (f i)=c b) :
    BlockAt ((List.range n).reverse.flatMap f) (f k) (fun b => (n-1-k)*c b) := by
  refine ⟨(List.range' (k+1) (n-(k+1))).reverse.flatMap f,
    (List.range k).reverse.flatMap f,?_,?_⟩
  · rw [reverse_range_split n k hk]
    simp [List.flatMap_append,List.append_assoc]
  · intro b
    rw [size_flatMap_const b _ _ (c b)]
    · simp only [List.length_reverse,List.length_range']
      congr 1
      omega
    · intro i hi
      have hh := List.mem_range'.mp (List.mem_reverse.mp hi)
      exact hs b i (by omega)

theorem column_cell_block (W j idx : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hi : idx<W) :
    BlockAt (column W j odd bits) (cellCNF W j idx odd (bits j (row W odd idx)))
      (fun b => (if b then 4 else 2)+(W-1-idx)*(if b then 48 else 20)) := by
  have h := reverse_range_block W idx hi
    (fun i => cellCNF W j i odd (bits j (row W odd i)))
    (fun b => if b then 48 else 20) (fun b i _ => cell_size b W j i odd _)
  have hh := (h.append_left (startG W j)).append_right (endG W j)
  simpa only [column,start_size] using hh

theorem column_start_block (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool) :
    BlockAt (column W j odd bits) (startG W j) (fun _ => 0) := by
  exact ⟨[],(List.range W).reverse.flatMap (fun i => cellCNF W j i odd (bits j (row W odd i))) ++ endG W j,
    by simp [column,List.append_assoc],fun b => size_nil b⟩

theorem column_end_block (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool) :
    BlockAt (column W j odd bits) (endG W j)
      (fun b => (if b then 4 else 2)+W*(if b then 48 else 20)) := by
  refine ⟨startG W j ++ (List.range W).reverse.flatMap
    (fun i => cellCNF W j i odd (bits j (row W odd i))),[],by simp [column],?_⟩
  intro b
  rw [size_append,start_size,size_flatMap_const b _ _ (if b then 48 else 20)
    (fun i _ => cell_size b W j i odd _)]
  simp

theorem BlockAt.getElem? {f g : CNF} {start : Bool → Nat}
    (h : BlockAt f g start) (j : Nat) (hj : j<g.length) : f[start false+j]? = g[j]? := by
  obtain ⟨a,z,he,hs⟩ := h
  have ha : a.length=start false := hs false
  rw [he,← ha,List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

theorem BlockAt.index_lt {f g : CNF} {start : Bool → Nat}
    (h : BlockAt f g start) (j : Nat) (hj : j<g.length) : start false+j<f.length := by
  obtain ⟨a,z,he,hs⟩ := h
  have ha : a.length=start false := hs false
  rw [he,List.length_append,List.length_append]
  omega

theorem BlockAt.off_add {f g : CNF} {start : Bool → Nat}
    (h : BlockAt f g start) (j : Nat) (hj : j≤g.length) :
    Comb.off f (start false+j) = start true+Comb.off g j := by
  obtain ⟨a,z,he,hs⟩ := h
  have ha : a.length=start false := hs false
  have hl : a.flatten.length=start true := hs true
  have ht : f.take (a.length+j) = a ++ g.take j := by
    rw [he,List.append_assoc,List.take_length_add_append,List.take_append_of_le_length hj]
  have hoff (f : CNF) (j : Nat) : Comb.off f j = (f.take j).flatten.length := by
    simp only [Comb.off,Comb.lens,length_flatten',List.map_take]
  rw [← ha,hoff,ht,List.flatten_append,List.length_append,hl,hoff]

theorem BlockAt.off {f g : CNF} {start : Bool → Nat} (h : BlockAt f g start) :
    Comb.off f (start false) = start true := by
  simpa [Comb.off,Comb.lens] using h.off_add 0 (Nat.zero_le _)

def columnBase (W m q k : Nat) (odd b : Bool) : Nat :=
  if odd then q*columnSize b W+(m-q-1-k)*columnSize b W
  else (q-1-k)*columnSize b W

def rainbowBase (W m q k v : Nat) (odd b : Bool) : Nat :=
  m*columnSize b W +
    (if odd then (m-q)*(W*(if b then 4 else 2))+(q-2-k)*(W*(if b then 4 else 2))
     else (m-q-1-k)*(W*(if b then 4 else 2))) +
    (W-1-v)*(if b then 4 else 2)

theorem grid_column_block (W m q k : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (hk : 2*k+(if odd then 2 else 1) ≤ m) :
    BlockAt (gridCNF W m bits) (column W (2*k+(if odd then 1 else 0)) odd bits)
      (columnBase W m q k odd) := by
  change BlockAt _ _ (fun b => columnBase W m q k odd b)
  rw [grid_blocks W m q bits hq]
  cases odd with
  | false =>
    have hk' : k<q := by simp only [Bool.false_eq_true,↓reduceIte] at hk; omega
    have h := reverse_range_block q k hk' (fun j => column W (2*j) false bits)
      (fun b => columnSize b W) (fun b j _ => column_size b W (2*j) false bits)
    simpa only [Bool.false_eq_true,↓reduceIte,Nat.add_zero,columnBase] using
      ((h.append_right _).append_right _).append_right _
  | true =>
    have hk' : k<m-q := by simp only [↓reduceIte] at hk; omega
    have h := reverse_range_block (m-q) k hk' (fun j => column W (2*j+1) true bits)
      (fun b => columnSize b W) (fun b j _ => column_size b W (2*j+1) true bits)
    have hh := ((h.append_left ((List.range q).reverse.flatMap
      (fun j => column W (2*j) false bits))).append_right
      ((List.range (m-q)).reverse.flatMap (fun j => (List.range W).reverse.flatMap (rbEven W (2*j))))).append_right
      ((List.range (q-1)).reverse.flatMap (fun j => (List.range W).reverse.flatMap (rbOdd W (2*j+1))))
    have he (b : Bool) : size b ((List.range q).reverse.flatMap (fun j => column W (2*j) false bits)) =
        q*columnSize b W := by
      rw [size_flatMap_const b _ _ (columnSize b W) (fun b' _ => column_size b W (2*b') false bits)]
      simp
    simpa only [↓reduceIte,columnBase,he] using hh

theorem grid_rainbow_block (W m q k v : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (hk : 2*k+(if odd then 3 else 2) ≤ m) (hv : v<W) :
    BlockAt (gridCNF W m bits)
      ((if odd then rbOdd else rbEven) W (2*k+(if odd then 1 else 0)) v)
      (fun b => rainbowBase W m q k v odd b) := by
  let ec := (List.range q).reverse.flatMap (fun j => column W (2*j) false bits)
  let oc := (List.range (m-q)).reverse.flatMap (fun j => column W (2*j+1) true bits)
  let er := (List.range (m-q)).reverse.flatMap (fun j => (List.range W).reverse.flatMap (rbEven W (2*j)))
  let ro := (List.range (q-1)).reverse.flatMap (fun j => (List.range W).reverse.flatMap (rbOdd W (2*j+1)))
  have hc (b : Bool) : size b (ec++oc)=m*columnSize b W := by
    simp only [ec,oc,size_append]
    rw [size_flatMap_const b _ _ (columnSize b W) (fun _ _ => column_size _ _ _ _ _),
      size_flatMap_const b _ _ (columnSize b W) (fun _ _ => column_size _ _ _ _ _)]
    simp only [List.length_reverse,List.length_range,← Nat.add_mul]
    congr 1
    omega
  have hr (b : Bool) : size b er=(m-q)*(W*(if b then 4 else 2)) := by
    apply (size_flatMap_const b _ _ (W*(if b then 4 else 2)) ?_).trans
    · simp
    · intro j _
      simpa using rainbow_row_size b W (2*j) false
  have he : gridCNF W m bits=(ec++oc)++er++ro := by
    exact grid_blocks W m q bits hq
  rw [he]
  cases odd with
  | false =>
    have hk' : k<m-q := by simp only [Bool.false_eq_true,↓reduceIte] at hk; omega
    have h1 := reverse_range_block (m-q) k hk'
      (fun j => (List.range W).reverse.flatMap (rbEven W (2*j)))
      (fun b => W*(if b then 4 else 2))
      (fun b j _ => by simpa using rainbow_row_size b W (2*j) false)
    have h2 := reverse_range_block W v hv (rbEven W (2*k))
      (fun b => if b then 4 else 2) (fun b j _ => evenRainbow_size b W (2*k) j)
    have h := ((h1.trans h2).append_left (ec++oc)).append_right ro
    simpa only [rainbowBase,Bool.false_eq_true,↓reduceIte,Nat.add_zero,hc,Nat.add_assoc] using h
  | true =>
    have hk' : k<q-1 := by simp only [↓reduceIte] at hk; omega
    have h1 := reverse_range_block (q-1) k hk'
      (fun j => (List.range W).reverse.flatMap (rbOdd W (2*j+1)))
      (fun b => W*(if b then 4 else 2))
      (fun b j _ => by simpa using rainbow_row_size b W (2*j+1) true)
    have h2 := reverse_range_block W v hv (rbOdd W (2*k+1))
      (fun b => if b then 4 else 2) (fun b j _ => oddRainbow_size b W (2*k+1) j)
    have h := ((h1.trans h2).append_left er).append_left (ec++oc)
    have heq : q-1-1=q-2 := by omega
    simpa only [rainbowBase,↓reduceIte,hc,hr,heq,Nat.add_assoc,List.append_assoc] using h

theorem grid_cell_block (W m q k idx : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (hk : 2*k+(if odd then 2 else 1) ≤ m) (hi : idx<W) :
    BlockAt (gridCNF W m bits)
      (cellCNF W (2*k+(if odd then 1 else 0)) idx odd
        (bits (2*k+(if odd then 1 else 0)) (row W odd idx)))
      (fun b => columnBase W m q k odd b+(if b then 4 else 2)+(W-1-idx)*(if b then 48 else 20)) := by
  have h := (grid_column_block W m q k odd bits hq hk).trans
    (column_cell_block W _ idx odd bits hi)
  simpa only [Nat.add_assoc] using h

theorem grid_start_block (W m q k : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (hk : 2*k+(if odd then 2 else 1) ≤ m) :
    BlockAt (gridCNF W m bits) (startG W (2*k+(if odd then 1 else 0)))
      (fun b => columnBase W m q k odd b) := by
  have h := (grid_column_block W m q k odd bits hq hk).trans (column_start_block W _ odd bits)
  simpa only [Nat.add_zero] using h

theorem grid_end_block (W m q k : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (hk : 2*k+(if odd then 2 else 1) ≤ m) :
    BlockAt (gridCNF W m bits) (endG W (2*k+(if odd then 1 else 0)))
      (fun b => columnBase W m q k odd b+(if b then 4 else 2)+W*(if b then 48 else 20)) := by
  have h := (grid_column_block W m q k odd bits hq hk).trans (column_end_block W _ odd bits)
  simpa only [Nat.add_assoc] using h

end STACS2027.PlanarSource.Packed.Index
