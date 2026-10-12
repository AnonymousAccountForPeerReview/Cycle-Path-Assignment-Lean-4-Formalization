module

public import NPHardness.PlanarAssemblyPortReflection

/-! The cyclic order induced by first hits on a finite common face. The
construction uses actual face iterates and records the absence of intervening
selected ports. For two or three ports the only possible orders differ by
reflection. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- The next selected dart, starting just after one selected dart. -/
def NextSelected {n m : Nat} (p : Fin n → Fin n) (port : Fin m → Fin n)
    (i j : Fin m) : Prop :=
  ∃ k, 0<k ∧ iterate p k (port i) = port j ∧
    ∀ r, 0<r → r<k → ∀ t, iterate p r (port i) ≠ port t

theorem nextSelected_exists {n m : Nat} (p : Fin n → Fin n)
    (hp : ∀ a b, p a=p b → a=b) (port : Fin m → Fin n) (i : Fin m) :
    ∃ j, NextSelected p port i j := by
  obtain ⟨T,hT,_,he⟩ := period hp (port i)
  obtain ⟨k,⟨hk,j,hj⟩,hmin⟩ := exists_least
    (P := fun k => 0<k ∧ ∃ j, iterate p k (port i) = port j) ⟨T,hT,i,he⟩
  exact ⟨j,k,hk,hj,fun r hr hrk t h => hmin r hrk ⟨hr,t,h⟩⟩

noncomputable def nextSelected {n m : Nat} (p : Fin n → Fin n)
    (hp : ∀ a b, p a=p b → a=b) (port : Fin m → Fin n) (i : Fin m) : Fin m :=
  Classical.choose (nextSelected_exists p hp port i)

theorem nextSelected_spec {n m : Nat} (p : Fin n → Fin n)
    (hp : ∀ a b, p a=p b → a=b) (port : Fin m → Fin n) (i : Fin m) :
    NextSelected p port i (nextSelected p hp port i) :=
  Classical.choose_spec (nextSelected_exists p hp port i)

/-- Two first-hit walks with the same destination have the same source. -/
theorem NextSelected.source_unique {n m : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a=p b → a=b) {port : Fin m → Fin n}
    (hinj : ∀ i j, port i=port j → i=j) {i j t : Fin m}
    (hi : NextSelected p port i t) (hj : NextSelected p port j t) : i=j := by
  obtain ⟨a,ha,hea,hna⟩ := hi
  obtain ⟨b,hb,heb,hnb⟩ := hj
  have hab : a=b := by
    by_cases hab : a<b
    · have he : iterate p a (port i) = iterate p a (iterate p (b-a) (port j)) := by
        rw [← iterate_add, show b-a+a=b by omega, hea, heb]
      have hstart := iterate_inj hp a he
      exact False.elim (hnb (b-a) (by omega) (by omega) i hstart.symm)
    · by_cases hba : b<a
      · have he : iterate p b (port j) = iterate p b (iterate p (a-b) (port i)) := by
          rw [← iterate_add, show a-b+b=a by omega, hea, heb]
        have hstart := iterate_inj hp b he
        exact False.elim (hna (a-b) (by omega) (by omega) j hstart.symm)
      · omega
  apply hinj
  apply iterate_inj hp a
  rw [hea, hab, heb]

theorem nextSelected_injective {n m : Nat} (p : Fin n → Fin n)
    (hp : ∀ a b, p a=p b → a=b) (port : Fin m → Fin n)
    (hinj : ∀ i j, port i=port j → i=j) :
    ∀ i j, nextSelected p hp port i = nextSelected p hp port j → i=j := by
  intro i j he
  have hi := nextSelected_spec p hp port i
  rw [he] at hi
  exact hi.source_unique hp hinj (nextSelected_spec p hp port j)

/-- An arbitrary return period reduces every iterate to an earlier one. -/
theorem iterate_mod_return {n : Nat} (p : Fin n → Fin n) (x : Fin n)
    {T : Nat} (hT : iterate p T x=x) (r : Nat) :
    iterate p r x = iterate p (r%T) x := by
  have he : r = (r/T)*T+r%T := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod r T).symm
  conv => lhs; rw [he, iterate_add, iterate_period_mul x T hT]

/-- A selected dart cannot be its own next port when another selected dart is
on its face orbit. -/
theorem NextSelected.ne_self {n m : Nat} {p : Fin n → Fin n}
    {port : Fin m → Fin n} (hinj : ∀ i j, port i=port j → i=j)
    {i j : Fin m} (hij : i≠j) (hreach : ∃ r, iterate p r (port i)=port j) :
    ¬ NextSelected p port i i := by
  rintro ⟨T,hT,hret,hn⟩
  obtain ⟨r,hr⟩ := hreach
  have hm : iterate p (r%T) (port i)=port j := (iterate_mod_return p (port i) hret r).symm.trans hr
  have hr0 : 0<r%T := by
    by_cases he : r%T=0
    · rw [he] at hm
      exact False.elim (hij (hinj i j hm))
    · omega
  exact hn (r%T) hr0 (Nat.mod_lt r hT) j hm

theorem nextSelected_ne_self {n m : Nat} (p : Fin n → Fin n)
    (hp : ∀ a b, p a=p b → a=b) (port : Fin m → Fin n)
    (hinj : ∀ i j, port i=port j → i=j)
    (hface : ∀ i j, ∃ r, iterate p r (port i)=port j) (hm : 2≤m) (i : Fin m) :
    nextSelected p hp port i ≠ i := by
  have hj : ∃ j : Fin m, i≠j := by
    by_cases h0 : i.val=0
    · exact ⟨⟨1,by omega⟩,fun h => by have := congrArg Fin.val h; simp only at this; omega⟩
    · exact ⟨⟨0,by omega⟩,fun h => h0 (congrArg Fin.val h)⟩
  obtain ⟨j,hij⟩ := hj
  intro he
  have hi := nextSelected_spec p hp port i
  rw [he] at hi
  exact NextSelected.ne_self hinj hij (hface i j) hi

/-- Reflection reverses a local first-hit walk independently of any matching
with ports from other gadgets. -/
theorem NextSelected.mirror {n m : Nat} {G : Hypermap n}
    (he : ∀ d, G.edge (G.edge d)=d) {port : Fin m → Fin n} {i j : Fin m}
    (h : NextSelected G.face port i j) :
    NextSelected (Reflection.mirror G he).face (fun t => G.edge (port t)) j i := by
  obtain ⟨k,hk,hend,hinside⟩ := h
  refine ⟨k,hk,?_,?_⟩
  · have hr := Reflection.mirror_face_reverse G he k (port i)
    rw [hend] at hr
    exact hr
  · intro r hr hrk t ht
    have hstep : iterate (Reflection.mirror G he).face r (G.edge (port j)) =
        G.edge (iterate G.face (k-r) (port i)) := by
      have hrev := Reflection.mirror_face_reverse G he r (iterate G.face (k-r) (port i))
      rw [← iterate_add,show k-r+r=k by omega,hend] at hrev
      exact hrev
    rw [hstep] at ht
    exact hinside (k-r) (by omega) (by omega) t (hm_edge_inj G _ _ ht)

theorem cyclic_order_no_fixed {m : Nat} (q : Fin m → Fin m)
    (hq : ∀ i j, Reaches q i j) (hm : 2≤m) (i : Fin m) : q i≠i := by
  let j : Fin m := if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hji : j≠i := by
    intro h
    have hv := congrArg Fin.val h
    unfold j at hv
    split at hv <;> dsimp only at hv <;> omega
  intro hi
  have hs : ∀ k, iterate q k i=i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate,hi,ih]
  obtain ⟨k,hk⟩ := hq i j
  exact hji (hk.symm.trans (hs k))

/-- At most three cofacial selected darts admit either orientation of every
cyclic order. Empty and singleton selections need no special matching. -/
theorem nextSelected_small_order_or_mirror {n m : Nat} (G : Hypermap n)
    (he : ∀ d, G.edge (G.edge d)=d) (port : Fin m → Fin n)
    (hinj : ∀ i j, port i=port j → i=j)
    (hface : ∀ i j, Reaches G.face (port i) (port j))
    (hm : m≤3) (q : Fin m → Fin m) (hqi : ∀ i j, q i=q j → i=j)
    (hqc : ∀ i j, Reaches q i j) :
    (∀ i, NextSelected G.face port i (q i)) ∨
      (∀ i, NextSelected (Reflection.mirror G he).face (fun t => G.edge (port t)) i (q i)) := by
  let s := nextSelected G.face (hm_face_inj G) port
  have hs := nextSelected_spec G.face (hm_face_inj G) port
  have hsi := nextSelected_injective G.face (hm_face_inj G) port hinj
  have hm' : m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by omega
  rcases hm' with rfl | rfl | rfl | rfl
  · exact Or.inl (fun i => Fin.elim0 i)
  · left
    intro i
    have hsq : s i=q i := Fin.ext (by have := (s i).isLt; have := (q i).isLt; omega)
    exact hsq ▸ hs i
  · have hsf := nextSelected_ne_self G.face (hm_face_inj G) port hinj hface (by decide)
    have hqf := cyclic_order_no_fixed q hqc (by decide)
    have hsq := two_port_orders s q hsf hqf
    exact Or.inl (fun i => hsq i ▸ hs i)
  · have hsf := nextSelected_ne_self G.face (hm_face_inj G) port hinj hface (by decide)
    have hqf := cyclic_order_no_fixed q hqc (by decide)
    rcases three_port_orders s q hsi hqi hsf hqf with hsq | hsq
    · exact Or.inl (fun i => hsq i ▸ hs i)
    · right
      intro i
      have hh := (hs (q i)).mirror he
      have hi : s (q i)=i := (hsq (q i)).trans (three_port_order_cube q hqi hqf i)
      change nextSelected G.face (hm_face_inj G) port (q i)=i at hi
      rw [hi] at hh
      exact hh

/-- Preserve choices for all local ports while ordering only the used subset.
Unused variable ports therefore never become marked global attachment darts. -/
theorem spherical_cofacial_subset_ordered {g ports : Graph} (hp : ports.Nodup)
    (h : HasSphericalCofacialPorts g ports) {m : Nat}
    (use : Fin m → Fin ports.length) (huse : ∀ i j, use i=use j → i=j) (hm : m≤3)
    (q : Fin m → Fin m) (hqi : ∀ i j, q i=q j → i=j) (hqc : ∀ i j, Reaches q i j) :
    ∃ G : Hypermap (2*g.length), IsGraphEmbedding g G ∧
      2*G.componentCount+2*g.length≤G.eulerRhs ∧
      ∃ port : Fin ports.length → Fin (2*g.length),
        (∀ i j, port i=port j → i=j) ∧
        (∀ i, g[(port i).val/2]?=some ports[i.val]) ∧
        (∀ i, NextSelected G.face (fun t => port (use t)) i (q i)) := by
  classical
  obtain ⟨G,hG,hEuler,root,hports⟩ := h
  have hex : ∀ i : Fin ports.length, ∃ d : Fin (2*g.length),
      Reaches G.face root d ∧ g[d.val/2]?=some ports[i.val] := by
    intro i
    obtain ⟨d,k,hk,hd⟩ := hports ports[i.val] (List.getElem_mem i.isLt)
    exact ⟨d,⟨k,hk⟩,hd⟩
  let port := fun i => Classical.choose (hex i)
  have hspec := fun i => Classical.choose_spec (hex i)
  have hinj : ∀ i j, port i=port j → i=j := by
    intro i j hij
    have hi := (hspec i).2
    have hj := (hspec j).2
    change g[(port i).val/2]?=some ports[i.val] at hi
    change g[(port j).val/2]?=some ports[j.val] at hj
    rw [hij] at hi
    exact Fin.ext ((hp.getElem_inj (hi := i.isLt) (hj := j.isLt)).mp (Option.some.inj (hi.symm.trans hj)))
  have hused : ∀ i j, port (use i)=port (use j) → i=j :=
    fun i j hij => huse i j (hinj _ _ hij)
  have hface : ∀ i j, Reaches G.face (port (use i)) (port (use j)) :=
    common_face_reaches G root (fun i => port (use i)) (fun i => (hspec (use i)).1)
  have he := Reflection.embedding_edge_twice hG
  rcases nextSelected_small_order_or_mirror G he (fun i => port (use i)) hused hface hm q hqi hqc
      with horder | horder
  · exact ⟨G,hG,hEuler,port,hinj,fun i => (hspec i).2,horder⟩
  · refine ⟨Reflection.mirror G he,Reflection.mirror_embedding hG he,
      Reflection.mirror_spherical G he hEuler,fun i => G.edge (port i),?_,?_,horder⟩
    · intro i j hij
      exact hinj i j (hm_edge_inj G _ _ hij)
    · intro i
      dsimp only
      have heq : G.edge (port i)=graphEdge (port i) := Fin.ext (hG.1 (port i))
      rw [heq,graphEdge_div (fun _ => rfl)]
      exact (hspec i).2

/-- Convert a local first-hit witness into the exact routing predicate. The
coverage condition is only on this local face orbit, not on other gadgets. -/
theorem NextSelected.to_nextPort {n m : Nat} {G : Hypermap n} {P : PortPairing G}
    {port : Fin m → Fin n} (hm : ∀ i, P.marked (port i)=true)
    (hcover : ∀ i r, P.marked (iterate G.face r (port i))=true →
      ∃ j, port j=iterate G.face r (port i))
    {i j : Fin m} (h : NextSelected G.face port i j) :
    NextPort P port (G.face (port i)) j := by
  obtain ⟨k,hk,he,hn⟩ := h
  have hk2 : 2≤k := by
    by_cases hk1 : k=1
    · have hf := P.face_separated (port i) (hm i)
      rw [hk1] at he
      change G.face (port i)=port j at he
      rw [he,hm] at hf
      contradiction
    · omega
  refine ⟨k-1,by omega,?_,?_⟩
  · have hke : k=(k-1)+1 := by omega
    rw [hke] at he
    exact he
  · intro r hr
    cases hb : P.marked (iterate G.face r (G.face (port i)))
    · rfl
    · obtain ⟨t,ht⟩ := hcover i (r+1) hb
      exact False.elim (hn (r+1) (by omega) (by omega) t ht.symm)

end STACS2027.PlanarAssembly
