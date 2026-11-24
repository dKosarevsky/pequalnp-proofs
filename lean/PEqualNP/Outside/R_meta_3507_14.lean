import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3507_14
  (branches :
  let edges : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
  let F := fun z : Fin 9 → Bool => edges.any (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10)))
  let solves := fun (p q : Fin 9) (C : Circuit) => ∀ z : Fin 9 → Bool,
    C.eval (List.ofFn z ++ [z 0 || z 4, z p || z q]) = F z
  let neg := fun g : Gate => !(g.op.eval [true])
  let uses := fun C : Circuit => C.gates.flatMap (fun g => if neg g then g.inputs.take 1 else g.inputs)
  let watched := fun p q : Fin 9 => ([0,4,p.val,q.val,9,10] : List ℕ)
  ∀ p q : Fin 9, p.val*10+q.val ∈ ([12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] : List ℕ) →
    ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → solves p q C →
    (∀ D : Circuit, FanInTwo D → solves p q D → C.size ≤ D.size) →
    10 + C.size ≤ (uses C).toFinset.card ∧
      ∃ R : Finset ℕ, (if p.val*10+q.val ∈ ([16,61,57,75] : List ℕ) then 3 else 2) ≤ R.card ∧
        ∀ i ∈ R, i ∉ watched p q ∧ 2 ≤ (uses C).count i)
  (oneNeg :
  let edges : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
  let F := fun z : Fin 9 → Bool => edges.any (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10)))
  let solves := fun (p q : Fin 9) (C : Circuit) => ∀ z : Fin 9 → Bool,
    C.eval (List.ofFn z ++ [z 0 || z 4, z p || z q]) = F z
  let neg := fun g : Gate => !(g.op.eval [true])
  let uses := fun C : Circuit => C.gates.flatMap (fun g => if neg g then g.inputs.take 1 else g.inputs)
  let watched := fun p q : Fin 9 => ([0,4,p.val,q.val,9,10] : List ℕ)
  ∀ p q : Fin 9, p.val*10+q.val ∈ ([12,21,23,32,27,72,38,83,68,86,58,85] : List ℕ) →
    ∀ C : Circuit, FanInTwo C → C.size = 13 → C.gates.countP neg = 1 →
    (∀ i ∈ watched p q, (uses C).count i ≤ 1) → ¬solves p q C)
  (monotone : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size) :
∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∈ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by

  intro p q C _ _ _ _ _ pair hc hsize spec
  let edges : List ℕ := [1,12,23,34,40,5,16,27,38,57,68,85]
  let F := fun z : Fin 9 → Bool => edges.any (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10)))
  let solves := fun (p q : Fin 9) (C : Circuit) => ∀ z : Fin 9 → Bool,
    C.eval (List.ofFn z ++ [z 0 || z 4, z p || z q]) = F z
  let neg := fun g : Gate => !(g.op.eval [true])
  let uses := fun C : Circuit => C.gates.flatMap (fun g => if neg g then g.inputs.take 1 else g.inputs)
  let watched := fun p q : Fin 9 => ([0,4,p.val,q.val,9,10] : List ℕ)
  let good := fun D : Circuit => FanInTwo D ∧ solves p q D
  have orig : good C := by
    refine ⟨hc, ?_⟩
    intro z
    rw [spec z]
    simp [F, edges, List.any, Bool.or_assoc, Fin.ofNat]
  classical
  let P := fun s : ℕ => ∃ D : Circuit, good D ∧ D.size = s
  have hex : ∃ s, P s := ⟨C.size,C,orig,rfl⟩
  obtain ⟨D,⟨hfan,hs⟩,hD⟩ := Nat.find_spec hex
  have least (A : Circuit) (ha : FanInTwo A) (hh : solves p q A) : D.size ≤ A.size := by
    rw [hD]
    exact Nat.find_min' hex (show P A.size from ⟨A,⟨ha,hh⟩,rfl⟩)
  have h13 := (least C orig.1 orig.2).trans hsize
  obtain ⟨distinct, R, cardR, heavy⟩ := branches p q pair D hfan h13 hs least
  change 10 + D.size ≤ (uses D).toFinset.card at distinct
  change (if p.val*10+q.val ∈ ([16,61,57,75] : List ℕ) then 3 else 2) ≤ R.card at cardR
  change ∀ i ∈ R, i ∉ watched p q ∧ 2 ≤ (uses D).count i at heavy
  have account (xs : List ℕ) (T : Finset ℕ) (hm : ∀ i ∈ T, 2 ≤ xs.count i) :
      T.card + xs.toFinset.card ≤ xs.length := by
    let U := xs.toFinset
    have sub : T ⊆ U := fun i hi => List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := hm i hi; omega))
    have a : (∑ i ∈ U, if i ∈ T then (1 : ℕ) else 0) = T.card := by
      have b : (∑ i ∈ U, if i ∈ T then (1 : ℕ) else 0) =
          ∑ i ∈ T, if i ∈ T then (1 : ℕ) else 0 := by
        symm
        exact Finset.sum_subset sub (fun i _ hn => by simp [hn])
      rw [b]
      calc
        _ = ∑ _i ∈ T, (1 : ℕ) := Finset.sum_congr rfl (fun i hi => if_pos hi)
        _ = T.card := by simp
    have total : (∑ i ∈ U, ((if i ∈ T then (1 : ℕ) else 0) + 1)) ≤
        ∑ i ∈ U, xs.count i := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ht : i ∈ T
      · simpa [ht] using hm i ht
      · have hi' : i ∈ xs := List.mem_toFinset.mp hi
        simpa [ht] using List.count_pos_iff.mpr hi'
    rw [Finset.sum_add_distrib, a] at total
    simpa [U, List.sum_toFinset_count_eq_length] using total
  have slots (gs : List Gate) (legal : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap (fun g => if neg g then g.inputs.take 1 else g.inputs)).length +
        gs.countP neg ≤ 2*gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have tail := ih (fun a ha => legal a (by simp [ha]))
      have hlen := legal g (by simp)
      simp only [List.flatMap_cons,List.length_append,List.countP_cons,List.length_cons]
      cases h : neg g <;> simp only [h, Bool.false_eq_true, if_false, if_true, List.length_take] <;> omega
  have hslots := slots D.gates (fun g hg => (hfan g hg).2)
  change (uses D).length + D.gates.countP neg ≤ 2*D.size at hslots
  have base := account (uses D) R (fun i hi => (heavy i hi).2)
  have hR : 2 ≤ R.card := by split at cardR <;> omega
  by_cases noNot : D.gates.countP neg = 0
  · have mono : Monotone2 D := by
      intro g hg
      obtain ⟨op,fan⟩ := hfan g hg
      refine ⟨?_,fan⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
      rcases op with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hp : neg g = true := by simp [neg,h,GateOp.eval]
        have pos : 0 < D.gates.countP neg := List.countP_pos_iff.mpr ⟨g,hg,hp⟩
        omega
    let gate : Gate := ⟨.or,[p.val,q.val]⟩
    let B : Circuit := ⟨gate::D.gates,D.output⟩
    have newMono : Monotone2 B := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | ht
      · simp [gate]
      · exact mono g ht
    have comp (z : Fin 9 → Bool) :
        B.eval (List.ofFn z ++ [z 0 || z 4]) = F z := by
      have read (i : Fin 9) : (List.ofFn z ++ [z 0 || z 4]).getD i.val false = z i := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt : i.val < (List.ofFn z).length),
          List.getElem?_ofFn, dif_pos i.isLt] <;> rfl
      have val : gate.op.eval
          (gate.inputs.map fun w => (List.ofFn z ++ [z 0 || z 4]).getD w false) = (z p || z q) := by
        change ((List.ofFn z ++ [z 0 || z 4]).getD p.val false ||
          ((List.ofFn z ++ [z 0 || z 4]).getD q.val false || false)) = _
        rw [read p,read q,Bool.or_false]
      change (D.gates.foldl _ ((_ ++ [z 0 || z 4]) ++ [_])).getD D.output false = _
      rw [val,List.append_assoc]
      exact hs z
    have lower := monotone B newMono (by
      intro m hm
      apply (comp (fun i : Fin 9 => m.testBit i.val)).trans
      exact (by decide +kernel : ∀ n ∈ ([3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402] : List ℕ),
        F (fun i : Fin 9 => n.testBit i.val) =
        decide (n ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ))) m hm)
    change 15 ≤ D.gates.length + 1 at lower
    change D.gates.length ≤ 13 at h13
    omega
  · have one : D.gates.countP neg = 1 := by omega
    have full : D.size = 13 := by omega
    have excluded : p.val*10+q.val ∉ ([16,61,57,75] : List ℕ) := by
      intro h
      rw [if_pos h] at cardR
      omega
    have rem : p.val*10+q.val ∈ ([12,21,23,32,27,72,38,83,68,86,58,85] : List ℕ) := by
      exact (by decide +kernel : ∀ n ∈ ([12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] : List ℕ),
        n ∉ ([16,61,57,75] : List ℕ) → n ∈ ([12,21,23,32,27,72,38,83,68,86,58,85] : List ℕ)) _ pair excluded
    refine oneNeg p q rem D hfan full one ?_ hs
    intro i hi
    change i ∈ watched p q at hi
    change (uses D).count i ≤ 1
    by_contra! large
    have outside : i ∉ R := fun h => (heavy i h).1 hi
    have more := account (uses D) (insert i R) (by
      intro a h
      rcases Finset.mem_insert.mp h with rfl | h
      · omega
      · exact (heavy a h).2)
    rw [Finset.card_insert_of_notMem outside] at more
    omega
