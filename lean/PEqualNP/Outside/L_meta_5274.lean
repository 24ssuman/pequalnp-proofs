import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5274

private def dGate : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩

private def step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem list_len2 (l : List ℕ) (hl : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  cases l with
  | nil => simp at hl
  | cons x xs =>
    cases xs with
    | nil => simp at hl
    | cons y ys =>
      cases ys with
      | nil => rfl
      | cons z zs => simp at hl

private theorem wires_len (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) :
    (gs.foldl step u).length = u.length + gs.length := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private theorem wires_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ)
    (hi : i < u.length) : (gs.foldl step u).getD i false = u.getD i false := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · dsimp only [step]; rw [List.getD_append _ _ _ _ hi]
    · simp [step]; omega

private theorem wires_take (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool)
    (i : ℕ) (hi : i < u.length + (gs.take n).length) :
    ((gs.take n).foldl step u).getD i false = (gs.foldl step u).getD i false := by
  conv_rhs =>
    rw [← List.take_append_drop n gs, List.foldl_append,
      wires_prefix _ _ _ (by rw [wires_len]; exact hi)]

private theorem wires_gate (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C) (u : List Bool) (j : ℕ)
    (hu : u.length = 26) (hj : j < C.gates.length) :
    (C.wires u).getD (26 + j) false =
      (C.gates.getD j dGate).op.eval
        ((C.gates.getD j dGate).inputs.map fun i => (C.wires u).getD i false) := by
  have hRB' : ∀ k < C.gates.length, ∀ i ∈ (C.gates.getD k dGate).inputs, i < 26 + k := hAO.2.1
  have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
    rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
  have hpreLen : ((C.gates.take j).foldl step u).length = 26 + j := by
    rw [wires_len, hu, List.length_take]; omega
  have hstepLen : (step ((C.gates.take j).foldl step u) (C.gates.getD j dGate)).length = 26 + j + 1 := by
    dsimp only [step]; rw [List.length_append, List.length_singleton, hpreLen]
  change (C.gates.foldl step u).getD (26 + j) false = _
  conv_lhs =>
    rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons,
      wires_prefix _ _ _ (by rw [hstepLen]; omega)]
  dsimp only [step]
  rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
  have hval : ∀ v : Bool, ([v] : List Bool).getD 0 false = v := fun _ => rfl
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hwlt : w < 26 + j := hRB' j hj w hw
  exact wires_take j C.gates u w (by rw [hu, List.length_take]; omega)

private theorem gateEval (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C) (u : List Bool) (j : ℕ)
    (hu : u.length = 26) (hj : j < C.gates.length) :
    let g := C.gates.getD j dGate
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (C.wires u).getD (26 + j) false = ((C.wires u).getD a false && (C.wires u).getD b false)) ∧
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (C.wires u).getD (26 + j) false = ((C.wires u).getD a false || (C.wires u).getD b false)) := by
  have hLen2 := hAO.2.2
  have hmem : C.gates.getD j dGate ∈ C.gates := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  have hlen : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hmem
  have heq := list_len2 _ hlen
  have hwg := wires_gate C hAO u j hu hj
  constructor
  · intro hand
    rw [hwg, hand, heq]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · intro hor
    rw [hwg, hor, heq]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

private theorem mono_wires (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C) (u v : List Bool)
    (hu : u.length = 26) (hv : v.length = 26)
    (huv : ∀ i < 26, u.getD i false = true → v.getD i false = true) :
    ∀ w, (C.wires u).getD w false = true → (C.wires v).getD w false = true := by
  have hOps := hAO.1
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j dGate).inputs, i < 26 + j := hAO.2.1
  have hLen2 := hAO.2.2
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hw26 : w < 26
    · change (C.gates.foldl step u).getD w false = true at hw
      change (C.gates.foldl step v).getD w false = true
      rw [wires_prefix _ _ _ (by rw [hu]; exact hw26)] at hw
      rw [wires_prefix _ _ _ (by rw [hv]; exact hw26)]
      exact huv w hw26 hw
    · by_cases hwEnd : w < 26 + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
        have hj : j < C.gates.length := by omega
        have hmem : C.gates.getD j dGate ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have hlen : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hmem
        have heq := list_len2 _ hlen
        have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
          hRB' j hj _ (by rw [heq]; exact List.mem_cons_self)
        have hbLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
          hRB' j hj _ (by rw [heq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        have hevu := gateEval C hAO u j hu hj
        have hevv := gateEval C hAO v j hv hj
        rcases hOps _ hmem with hand | hor
        · rw [hevu.1 hand, Bool.and_eq_true] at hw
          rw [hevv.1 hand, Bool.and_eq_true]
          exact ⟨ih _ haLt hw.1, ih _ hbLt hw.2⟩
        · rw [hevu.2 hor, Bool.or_eq_true] at hw
          rw [hevv.2 hor, Bool.or_eq_true]
          rcases hw with ha | hb
          · exact Or.inl (ih _ haLt ha)
          · exact Or.inr (ih _ hbLt hb)
      · change (C.gates.foldl step u).getD w false = true at hw
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len, hu]; omega)] at hw
        cases hw

private theorem mono_eval (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C) (u v : List Bool)
    (hu : u.length = 26) (hv : v.length = 26)
    (huv : ∀ i < 26, u.getD i false = true → v.getD i false = true) :
    C.eval u = true → C.eval v = true :=
  fun hc => mono_wires C hAO u v hu hv huv C.output hc

private def incIn (p l : Fin 13) : List Bool :=
  (List.ofFn fun k : Fin 13 => decide (k = p)) ++
  (List.ofFn fun k : Fin 13 => decide (k = l))

private theorem incIn_len (p l : Fin 13) : (incIn p l).length = 26 := by
  simp [incIn]

private theorem incIn_getD (p l : Fin 13) (i : ℕ) (hi : i < 26)
    (hbit : (incIn p l).getD i false = true) : i = p.val ∨ i = 13 + l.val := by
  dsimp only [incIn] at hbit
  by_cases h13 : i < 13
  · rw [List.getD_append _ _ _ _ (by simp [h13])] at hbit
    rw [List.getD_eq_getElem _ _ (by simp [h13]), List.getElem_ofFn] at hbit
    simp only [decide_eq_true_eq] at hbit
    left; exact congrArg Fin.val hbit
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hbit
    simp only [List.length_ofFn] at hbit
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn] at hbit
    simp only [decide_eq_true_eq] at hbit
    right; have := congrArg Fin.val hbit; dsimp only at this; omega

private def quadIn (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun k : Fin 13 => decide (k ∈ Q)) ++
  (List.ofFn fun k : Fin 13 => decide (k ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))

private theorem quadIn_len (Q : Finset (Fin 13)) : (quadIn Q).length = 26 := by
  simp [quadIn]

private theorem quadIn_getD_left (Q : Finset (Fin 13)) (p : Fin 13) (hp : p ∈ Q) :
    (quadIn Q).getD p.val false = true := by
  dsimp only [quadIn]
  rw [List.getD_append _ _ _ _ (by simp [p.isLt])]
  rw [List.getD_eq_getElem _ _ (by simp [p.isLt]), List.getElem_ofFn]
  simp [hp]

private theorem quadIn_getD_right (Q : Finset (Fin 13)) (l : Fin 13)
    (hl : l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) :
    (quadIn Q).getD (13 + l.val) false = true := by
  dsimp only [quadIn]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp [l.isLt]), List.getElem_ofFn]
  simp [hl]

private def inc (p l : ℕ) : Bool :=
  let d := (p + 13 - l) % 13
  d == 0 || d == 1 || d == 3 || d == 9

private def mem4 (x : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : Bool :=
  x == t.1 || x == t.2.1 || x == t.2.2.1 || x == t.2.2.2

private def reps : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0,1,2,5), (0,1,2,6), (0,1,2,7), (0,1,2,11), (0,1,4,6),
   (0,1,4,8), (0,1,4,11), (0,1,5,10), (0,1,5,11), (0,1,6,7)]

private def r13 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12]

private theorem hR13Mem (n : ℕ) (hn : n < 13) : n ∈ r13 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [r13]

private theorem hR13Lt (n : ℕ) (hn : n ∈ r13) : n < 13 := by
  simp only [r13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

private theorem hRepsLen : reps.length = 10 := by decide

private theorem hRepsNodup : reps.Nodup := by decide

private theorem hQuadB : reps.all (fun t =>
    t.1 < t.2.1 && t.2.1 < t.2.2.1 && t.2.2.1 < t.2.2.2 && t.2.2.2 < 13 &&
    r13.all (fun l =>
      (if inc t.1 l then 1 else 0) + (if inc t.2.1 l then 1 else 0) +
      (if inc t.2.2.1 l then 1 else 0) + (if inc t.2.2.2 l then 1 else 0) ≤ 2)) = true := by
  decide

private theorem hCovB : reps.all (fun t =>
    r13.all (fun p =>
      mem4 p t || r13.any (fun l =>
        inc p l && !inc t.1 l && !inc t.2.1 l && !inc t.2.2.1 l && !inc t.2.2.2 l))) = true := by
  decide

private theorem hDisjB : reps.all (fun t1 =>
    reps.all (fun t2 =>
      r13.all (fun k =>
        (t1 == t2 && k == 0) ||
        !(mem4 ((t1.1 + k) % 13) t2 && mem4 ((t1.2.1 + k) % 13) t2 &&
          mem4 ((t1.2.2.1 + k) % 13) t2 && mem4 ((t1.2.2.2 + k) % 13) t2)))) = true := by
  decide

private theorem hMemS3 (p l : Fin 13) :
    p ∈ PEqualNP.HeptadCover.singerLines3 l ↔ inc p.val l.val = true := by
  dsimp only [PEqualNP.HeptadCover.singerLines3, inc]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq, or_assoc]

private theorem hShiftInc (p l k : ℕ) (hp : p < 13) (hl : l < 13) (_hk : k < 13) :
    inc ((p + k) % 13) ((l + k) % 13) = inc p l := by
  dsimp only [inc]
  have hm : ((p + k) % 13 + 13 - (l + k) % 13) % 13 = (p + 13 - l) % 13 := by omega
  rw [hm]

private def toF (t : ℕ × ℕ × ℕ × ℕ) (k : Fin 13) : Finset (Fin 13) :=
  {⟨(t.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
   ⟨(t.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
   ⟨(t.2.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
   ⟨(t.2.2.2 + k.val) % 13, Nat.mod_lt _ (by omega)⟩}

private theorem hRepsOrd (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ reps) :
    t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2 ∧ t.2.2.2 < 13 := by
  have hq := List.all_eq_true.mp hQuadB t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  rcases hq with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩
  exact ⟨h1, h2, h3, h4⟩

private theorem hToF_mem (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ reps) (k p : Fin 13) :
    p ∈ toF t k ↔ mem4 ((p.val + (13 - k.val)) % 13) t = true := by
  have hkLt : k.val < 13 := k.isLt
  have hpLt : p.val < 13 := p.isLt
  have hOrd := hRepsOrd t ht
  dsimp only [toF, mem4]
  simp only [Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq, Fin.ext_iff,
    or_assoc]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · rintro (h | h | h | h)
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem hToF_card (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ reps) (k : Fin 13) :
    (toF t k).card = 4 := by
  have hkLt : k.val < 13 := k.isLt
  have hOrd := hRepsOrd t ht
  dsimp only [toF]
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; rintro (h | h | h) <;> omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; rintro (h | h) <;> omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton, Fin.ext_iff]; intro h; omega),
      Finset.card_singleton]

private theorem hToF_quad (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ reps) (k : Fin 13) :
    toF t k ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 := by
  have hkLt : k.val < 13 := k.isLt
  have hOrd := hRepsOrd t ht
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hToF_card t ht k⟩, ?_⟩
  intro l
  have hlLt : l.val < 13 := l.isLt
  let l' : ℕ := (l.val + (13 - k.val)) % 13
  have hl'Lt : l' < 13 := Nat.mod_lt _ (by omega)
  have hq := List.all_eq_true.mp hQuadB t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have hSum := List.all_eq_true.mp hq.2 l' (hR13Mem l' hl'Lt)
  simp only [decide_eq_true_eq] at hSum
  have hInterStep : ∀ (A : Finset (Fin 13)) (x : Fin 13) (S : Finset (Fin 13)),
      (insert x A ∩ S).card ≤ (A ∩ S).card + if x ∈ S then 1 else 0 := by
    intro A x S
    by_cases hx : x ∈ S
    · have heq : insert x A ∩ S = insert x (A ∩ S) := by ext y; simp [hx]
      rw [heq, ite_eq_left hx]
      exact Finset.card_insert_le _ _
    · have heq : insert x A ∩ S = A ∩ S := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert, and_congr_left_iff]
        intro hy; constructor
        · rintro (rfl | ha); exact absurd hy hx; exact ha
        · exact Or.inr
      rw [heq, ite_eq_right hx, Nat.add_zero]
  have hSingStep : ∀ (x : Fin 13) (S : Finset (Fin 13)),
      ({x} ∩ S).card ≤ if x ∈ S then 1 else 0 := by
    intro x S
    by_cases hx : x ∈ S
    · have heq : ({x} ∩ S : Finset (Fin 13)) = {x} := by ext y; simp [hx]
      rw [heq, Finset.card_singleton, ite_eq_left hx]
    · have heq : ({x} ∩ S : Finset (Fin 13)) = ∅ := by
        ext y; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hy⟩; exact hx hy
      rw [heq, Finset.card_empty, ite_eq_right hx]
  have hIncShiftPt : ∀ x : ℕ, x < 13 →
      (⟨(x + k.val) % 13, Nat.mod_lt _ (by omega)⟩ ∈ PEqualNP.HeptadCover.singerLines3 l ↔ inc x l' = true) := by
    intro x hx
    rw [hMemS3]
    have hL : (l' + k.val) % 13 = l.val := by dsimp only [l']; omega
    rw [← hL, hShiftInc x l' k.val hx hl'Lt hkLt]
  dsimp only [toF]
  have h1 := hInterStep {⟨(t.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
      ⟨(t.2.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
      ⟨(t.2.2.2 + k.val) % 13, Nat.mod_lt _ (by omega)⟩}
    ⟨(t.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩ (PEqualNP.HeptadCover.singerLines3 l)
  have h2 := hInterStep {⟨(t.2.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩,
      ⟨(t.2.2.2 + k.val) % 13, Nat.mod_lt _ (by omega)⟩}
    ⟨(t.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩ (PEqualNP.HeptadCover.singerLines3 l)
  have h3 := hInterStep {⟨(t.2.2.2 + k.val) % 13, Nat.mod_lt _ (by omega)⟩}
    ⟨(t.2.2.1 + k.val) % 13, Nat.mod_lt _ (by omega)⟩ (PEqualNP.HeptadCover.singerLines3 l)
  have h4 := hSingStep ⟨(t.2.2.2 + k.val) % 13, Nat.mod_lt _ (by omega)⟩
    (PEqualNP.HeptadCover.singerLines3 l)
  simp only [hIncShiftPt t.1 (by omega), hIncShiftPt t.2.1 (by omega),
    hIncShiftPt t.2.2.1 (by omega), hIncShiftPt t.2.2.2 (by omega)] at h1 h2 h3 h4
  omega

private theorem hToF_cov (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ reps) (k p : Fin 13)
    (hpNot : p ∉ toF t k) :
    ∃ l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 (toF t k),
      p ∈ PEqualNP.HeptadCover.singerLines3 l := by
  have hkLt : k.val < 13 := k.isLt
  have hpLt : p.val < 13 := p.isLt
  have hOrd := hRepsOrd t ht
  let p' : ℕ := (p.val + (13 - k.val)) % 13
  have hp'Lt : p' < 13 := Nat.mod_lt _ (by omega)
  have hMem4F : mem4 p' t = false := by
    by_contra hT
    exact hpNot ((hToF_mem t ht k p).mpr (Bool.eq_true_of_not_eq_false hT))
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hCovB t ht) p' (hR13Mem p' hp'Lt)
  rw [Bool.or_eq_true, hMem4F, Bool.false_eq_true, false_or, List.any_eq_true] at hc
  rcases hc with ⟨l', hl'Mem, hl'Props⟩
  have hl'Lt : l' < 13 := hR13Lt l' hl'Mem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hl'Props
  rcases hl'Props with ⟨⟨⟨⟨hpL', h1⟩, h2⟩, h3⟩, h4⟩
  let l : Fin 13 := ⟨(l' + k.val) % 13, Nat.mod_lt _ (by omega)⟩
  have hpL : p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    rw [hMemS3]
    have hpBack : (p' + k.val) % 13 = p.val := by dsimp only [p']; omega
    rw [← hpBack, hShiftInc p' l' k.val hp'Lt hl'Lt hkLt]
    exact hpL'
  refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩, hpL⟩
  intro q hqL hqQ
  have hqLt : q.val < 13 := q.isLt
  have hqInc : inc ((q.val + (13 - k.val)) % 13) l' = true := by
    rw [hMemS3] at hqL
    have hqBack : ((q.val + (13 - k.val)) % 13 + k.val) % 13 = q.val := by omega
    have hBack : l.val = (l' + k.val) % 13 := rfl
    rw [hBack, ← hqBack, hShiftInc _ _ _ (Nat.mod_lt _ (by omega)) hl'Lt hkLt] at hqL
    exact hqL
  have hm4 := (hToF_mem t ht k q).mp hqQ
  dsimp only [mem4] at hm4
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hm4
  rcases hm4 with h | h | h | h
  · rw [h, h1] at hqInc; cases hqInc
  · rw [h, h2] at hqInc; cases hqInc
  · rw [h, h3] at hqInc; cases hqInc
  · rw [h, h4] at hqInc; cases hqInc

private theorem hToF_inj (i1 i2 : Fin reps.length) (k1 k2 : Fin 13)
    (hEq : toF reps[i1] k1 = toF reps[i2] k2) : i1 = i2 ∧ k1 = k2 := by
  have hk1Lt : k1.val < 13 := k1.isLt
  have hk2Lt : k2.val < 13 := k2.isLt
  have ht1 : reps[i1] ∈ reps := List.getElem_mem i1.isLt
  have ht2 : reps[i2] ∈ reps := List.getElem_mem i2.isLt
  have hOrd1 := hRepsOrd _ ht1
  let d : ℕ := (k1.val + (13 - k2.val)) % 13
  have hdLt : d < 13 := Nat.mod_lt _ (by omega)
  have hMemShift : ∀ x : ℕ, x = reps[i1].1 ∨ x = reps[i1].2.1 ∨ x = reps[i1].2.2.1 ∨ x = reps[i1].2.2.2 →
      mem4 ((x + d) % 13) reps[i2] = true := by
    intro x hx
    have hxLt : x < 13 := by
      rcases hx with h | h | h | h <;> rw [h] <;> omega
    let p : Fin 13 := ⟨(x + k1.val) % 13, Nat.mod_lt _ (by omega)⟩
    have hp1 : p ∈ toF reps[i1] k1 := by
      dsimp only [toF, p]
      rcases hx with h | h | h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    rw [hEq] at hp1
    have hp2 := (hToF_mem _ ht2 k2 p).mp hp1
    have hShiftMod : (p.val + (13 - k2.val)) % 13 = (x + d) % 13 := by
      dsimp only [p, d]; omega
    rwa [← hShiftMod]
  have h1 := hMemShift reps[i1].1 (Or.inl rfl)
  have h2 := hMemShift reps[i1].2.1 (Or.inr (Or.inl rfl))
  have h3 := hMemShift reps[i1].2.2.1 (Or.inr (Or.inr (Or.inl rfl)))
  have h4 := hMemShift reps[i1].2.2.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hd := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hDisjB _ ht1) _ ht2) d (hR13Mem d hdLt)
  rw [h1, h2, h3, h4] at hd
  simp only [Bool.and_self, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at hd
  exact ⟨Fin.ext (hRepsNodup.getElem_inj_iff.mp hd.1), Fin.ext (by omega)⟩

private theorem and_lower_bound (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C)
    (hInc : ∀ (x3 x4 : Fin 13), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = x3)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = x4)) = true)
    (hQuad : ∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 ∈ x4)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = false) :
    8 ≤ PEqualNP.ReadTwo.nAnd C := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hOps := hAO.1
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j dGate).inputs, i < 26 + j := hAO.2.1
  have hLen2 := hAO.2.2
  let andIdxs : List ℕ :=
    (List.range C.gates.length).filter fun j =>
      decide ((C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hAndCount : andIdxs.length = PEqualNP.ReadTwo.nAnd C := by
    dsimp only [andIdxs, PEqualNP.ReadTwo.nAnd]
    have hGen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p : PEqualNP.CircuitLowerBounds.Gate → Bool),
        ((List.range gs.length).filter fun j => p (gs.getD j dGate)).length = (gs.filter p).length := by
      intro gs p
      induction gs with
      | nil => simp
      | cons g gs ih =>
        rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons]
        have hMap : ((List.range gs.length).map Nat.succ).filter
            (fun j => p ((g :: gs).getD j dGate)) =
            ((List.range gs.length).filter fun j => p (gs.getD j dGate)).map Nat.succ := by
          rw [List.filter_map]; rfl
        have h0 : (g :: gs).getD 0 dGate = g := rfl
        rw [h0, hMap]
        cases hp : p g
        · simp only [Bool.false_eq_true, ite_false, List.length_map, ih]
        · simp only [ite_true, List.length_cons, List.length_map, ih]
    exact hGen C.gates (fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.and))
  let sig : Fin reps.length × Fin 13 → Fin andIdxs.length → Bool := fun p k =>
    let j := andIdxs[k.val]
    let a := (C.gates.getD j dGate).inputs.getD 0 0
    (C.wires (quadIn (toF reps[p.1] p.2))).getD a false
  have hSigInj : Function.Injective sig := by
    rintro ⟨i1, k1⟩ ⟨i2, k2⟩ hSig
    by_contra hNe
    let Q1 := toF reps[i1] k1
    let Q2 := toF reps[i2] k2
    have hQ1 : Q1 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 :=
      hToF_quad reps[i1] (List.getElem_mem i1.isLt) k1
    have hQ2 : Q2 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 :=
      hToF_quad reps[i2] (List.getElem_mem i2.isLt) k2
    have hNe' : Q1 ≠ Q2 := fun h => hNe (Prod.ext (hToF_inj i1 i2 k1 k2 h).1 (hToF_inj i1 i2 k1 k2 h).2)
    have hC1 : Q1.card = 4 := hToF_card reps[i1] (List.getElem_mem i1.isLt) k1
    have hC2 : Q2.card = 4 := hToF_card reps[i2] (List.getElem_mem i2.isLt) k2
    have hSub : ¬ Q2 ⊆ Q1 := fun hs => hNe' (Finset.eq_of_subset_of_card_le hs (by omega)).symm
    rw [Finset.not_subset] at hSub
    obtain ⟨p, hp2, hp1⟩ := hSub
    obtain ⟨l, hlMiss, hpInL⟩ := hToF_cov reps[i1] (List.getElem_mem i1.isLt) k1 p hp1
    let uQ : List Bool := List.zipWith (· || ·) (quadIn Q1) (quadIn Q2)
    have huQLen : uQ.length = 26 := by simp [uQ, quadIn_len]
    have hUnion : ∀ w, (C.wires uQ).getD w false = true →
        (C.wires (quadIn Q1)).getD w false = true ∨ (C.wires (quadIn Q2)).getD w false = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hw26 : w < 26
        · change (C.gates.foldl step uQ).getD w false = true at hw
          change (C.gates.foldl step (quadIn Q1)).getD w false = true ∨
            (C.gates.foldl step (quadIn Q2)).getD w false = true
          rw [wires_prefix _ _ _ (by rw [huQLen]; exact hw26)] at hw
          rw [wires_prefix _ _ _ (by rw [quadIn_len]; exact hw26),
              wires_prefix _ _ _ (by rw [quadIn_len]; exact hw26)]
          dsimp only [uQ] at hw
          rw [List.getD_eq_getElem _ _ (by simp [quadIn_len, hw26]), List.getElem_zipWith] at hw
          rw [List.getD_eq_getElem _ _ (by rw [quadIn_len]; exact hw26),
              List.getD_eq_getElem _ _ (by rw [quadIn_len]; exact hw26)]
          exact Bool.or_eq_true _ _ |>.mp hw
        · by_cases hwEnd : w < 26 + C.gates.length
          · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
            have hj : j < C.gates.length := by omega
            have hmem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hlen : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hmem
            have heq := list_len2 _ hlen
            let a := (C.gates.getD j dGate).inputs.getD 0 0
            let b := (C.gates.getD j dGate).inputs.getD 1 0
            have haLt : a < 26 + j := hRB' j hj a (by rw [heq]; exact List.mem_cons_self)
            have hbLt : b < 26 + j := hRB' j hj b (by rw [heq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            have hevU := gateEval C hAO uQ j huQLen hj
            have hev1 := gateEval C hAO (quadIn Q1) j (quadIn_len Q1) hj
            have hev2 := gateEval C hAO (quadIn Q2) j (quadIn_len Q2) hj
            rcases hOps _ hmem with hand | hor
            · rw [hevU.1 hand, Bool.and_eq_true] at hw
              have haOr := ih a haLt hw.1
              have hbOr := ih b hbLt hw.2
              have hjMem : j ∈ andIdxs := by
                rw [List.mem_filter]
                exact ⟨List.mem_range.mpr hj, by rw [hand]; decide⟩
              obtain ⟨k, hkLt, hkEq⟩ := List.mem_iff_getElem.mp hjMem
              have haEq := congrFun hSig ⟨k, hkLt⟩
              dsimp only [sig] at haEq
              rw [hkEq] at haEq
              have ha1 : (C.wires (quadIn Q1)).getD a false = true := by
                rcases haOr with h1 | h2
                · exact h1
                · exact haEq.trans h2
              have ha2 : (C.wires (quadIn Q2)).getD a false = true := haEq.symm.trans ha1
              rw [hev1.1 hand, hev2.1 hand, Bool.and_eq_true, Bool.and_eq_true]
              rcases hbOr with h1 | h2
              · exact Or.inl ⟨ha1, h1⟩
              · exact Or.inr ⟨ha2, h2⟩
            · rw [hevU.2 hor, Bool.or_eq_true] at hw
              rw [hev1.2 hor, hev2.2 hor, Bool.or_eq_true, Bool.or_eq_true]
              rcases hw with ha | hb
              · rcases ih a haLt ha with h1 | h2
                · exact Or.inl (Or.inl h1)
                · exact Or.inr (Or.inl h2)
              · rcases ih b hbLt hb with h1 | h2
                · exact Or.inl (Or.inr h1)
                · exact Or.inr (Or.inr h2)
          · change (C.gates.foldl step uQ).getD w false = true at hw
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len, huQLen]; omega)] at hw
            cases hw
    have hIncTrue : C.eval (incIn p l) = true := hInc p l hpInL
    have hUTrue : C.eval uQ = true := by
      refine mono_eval C hAO (incIn p l) uQ (incIn_len p l) huQLen (fun i hi hbit => ?_) hIncTrue
      dsimp only [uQ]
      rw [List.getD_eq_getElem _ _ (by simp [quadIn_len, hi]), List.getElem_zipWith, Bool.or_eq_true]
      rcases incIn_getD p l i hi hbit with rfl | rfl
      · right
        rw [← List.getD_eq_getElem _ _ (by rw [quadIn_len]; exact Nat.lt_trans p.isLt (by omega))]
        exact quadIn_getD_left Q2 p hp2
      · left
        rw [← List.getD_eq_getElem _ _ (by rw [quadIn_len]; omega)]
        exact quadIn_getD_right Q1 l hlMiss
    rcases hUnion C.output hUTrue with h1 | h2
    · change C.eval (quadIn Q1) = true at h1
      dsimp only [quadIn] at h1
      rw [hQuad Q1 hQ1] at h1
      cases h1
    · change C.eval (quadIn Q2) = true at h2
      dsimp only [quadIn] at h2
      rw [hQuad Q2 hQ2] at h2
      cases h2
  have hLePow : 130 ≤ 2 ^ PEqualNP.ReadTwo.nAnd C := by
    have hc := Fintype.card_le_of_injective sig hSigInj
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin, hRepsLen, hAndCount] at hc
    exact hc
  have hLtPow : 2 ^ 7 < 2 ^ PEqualNP.ReadTwo.nAnd C :=
    lt_of_lt_of_le (by norm_num) hLePow
  have hLtAnd : 7 < PEqualNP.ReadTwo.nAnd C :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hLtPow
  omega

private theorem hMiss0B : r13.all (fun l =>
    (!(inc 0 l || inc 1 l || inc 2 l || inc 5 l)) == (l == 3 || l == 7 || l == 8)) = true := by
  decide

private theorem us_props (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C)
    (hInc : ∀ (x3 x4 : Fin 13), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = x3)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = x4)) = true)
    (hQuad : ∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 ∈ x4)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = false) :
    ∃ (U0 : Finset (Fin 26)) (S : ℕ → Finset (Fin 26)),
      U0.card = 19 ∧
      S C.output = U0 ∧
      C.output < 26 + C.gates.length ∧
      (∀ i ∈ U0, S i.val = {i}) ∧
      (∀ (w : ℕ) (hw : w < 26), (⟨w, hw⟩ : Fin 26) ∉ U0 → S w = ∅) ∧
      (∀ j < C.gates.length,
        let g := C.gates.getD j dGate
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → S (26 + j) ⊆ S a ∨ S (26 + j) ⊆ S b) ∧
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → S (26 + j) ⊆ S a ∪ S b)) := by
  let Q0 : Finset (Fin 13) := toF (reps[0]'(by rw [hRepsLen]; omega)) 0
  have hQ0 : Q0 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 :=
    hToF_quad _ (List.getElem_mem (by rw [hRepsLen]; omega)) 0
  have hCovP : ∀ p : Fin 13, p ∉ Q0 →
      ∃ l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0,
        p ∈ PEqualNP.HeptadCover.singerLines3 l :=
    hToF_cov _ (List.getElem_mem (by rw [hRepsLen]; omega)) 0
  have hCovL : ∀ l : Fin 13, l ∉ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0 →
      ∃ p ∈ Q0, p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    intro l hl
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_disjoint_iff] at hl
    exact let ⟨p, hpL, hpQ⟩ := hl; ⟨p, hpQ, hpL⟩
  let xBase : List Bool := quadIn Q0
  have hxBaseLen : xBase.length = 26 := quadIn_len Q0
  have hBaseFalse : C.eval xBase = false := hQuad Q0 hQ0
  let U0 : Finset (Fin 26) := Finset.univ.filter fun i : Fin 26 => xBase.getD i.val false = false
  have hQ0Val : ∀ p : Fin 13, p ∈ Q0 ↔ p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 5 := by
    intro p
    have hpLt : p.val < 13 := p.isLt
    rw [hToF_mem _ (List.getElem_mem (by rw [hRepsLen]; omega)) 0 p]
    have hSub : (p.val + (13 - (0 : Fin 13).val)) % 13 = p.val := by
      change (p.val + (13 - 0)) % 13 = p.val; omega
    have hRep0 : reps[0]'(by rw [hRepsLen]; omega) = (0, 1, 2, 5) := rfl
    rw [hSub, hRep0]
    dsimp only [mem4]
    simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
  have hMiss0Val : ∀ l : Fin 13,
      l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0 ↔
        l.val = 3 ∨ l.val = 7 ∨ l.val = 8 := by
    intro l
    have hlLt : l.val < 13 := l.isLt
    have hb := List.all_eq_true.mp hMiss0B l.val (hR13Mem l.val hlLt)
    rw [beq_iff_eq] at hb
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.disjoint_left, hMemS3, hQ0Val]
    constructor
    · intro hDisj
      have hF0 : inc 0 l.val = false := Bool.eq_false_iff.mpr fun h => @hDisj ⟨0, by omega⟩ h (Or.inl rfl)
      have hF1 : inc 1 l.val = false := Bool.eq_false_iff.mpr fun h => @hDisj ⟨1, by omega⟩ h (Or.inr (Or.inl rfl))
      have hF2 : inc 2 l.val = false := Bool.eq_false_iff.mpr fun h => @hDisj ⟨2, by omega⟩ h (Or.inr (Or.inr (Or.inl rfl)))
      have hF5 : inc 5 l.val = false := Bool.eq_false_iff.mpr fun h => @hDisj ⟨5, by omega⟩ h (Or.inr (Or.inr (Or.inr rfl)))
      rw [hF0, hF1, hF2, hF5] at hb
      simp only [Bool.or_self, Bool.not_false] at hb
      have hb' : (l.val == 3 || l.val == 7 || l.val == 8) = true := hb.symm
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at hb'
      exact hb'
    · have hAllF : l.val = 3 ∨ l.val = 7 ∨ l.val = 8 →
          inc 0 l.val = false ∧ inc 1 l.val = false ∧ inc 2 l.val = false ∧ inc 5 l.val = false := by
        intro hLv
        have hL : (!(inc 0 l.val || inc 1 l.val || inc 2 l.val || inc 5 l.val)) = true := by
          rw [hb]; simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]; exact hLv
        simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hL
        exact ⟨hL.1.1.1, hL.1.1.2, hL.1.2, hL.2⟩
      rintro hLv p hpL (h | h | h | h)
      · rw [h, (hAllF hLv).1] at hpL; cases hpL
      · rw [h, (hAllF hLv).2.1] at hpL; cases hpL
      · rw [h, (hAllF hLv).2.2.1] at hpL; cases hpL
      · rw [h, (hAllF hLv).2.2.2] at hpL; cases hpL
  let bad : Finset (Fin 26) := {0, 1, 2, 5, 16, 20, 21}
  have hU0Eq : U0 = Finset.univ \ bad := by
    ext i
    simp only [U0, bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    have hiLt : i.val < 26 := i.isLt
    by_cases h13 : i.val < 13
    · have hx : xBase.getD i.val false = decide ((⟨i.val, h13⟩ : Fin 13) ∈ Q0) := by
        dsimp only [xBase, quadIn]
        rw [List.getD_append _ _ _ _ (by simp [h13]), List.getD_eq_getElem _ _ (by simp [h13]),
          List.getElem_ofFn]
      rw [hx, decide_eq_false_iff_not, hQ0Val ⟨i.val, h13⟩]
      dsimp only []
      omega
    · have hx : xBase.getD i.val false =
          decide ((⟨i.val - 13, by omega⟩ : Fin 13) ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0) := by
        dsimp only [xBase, quadIn]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_ofFn]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      rw [hx, decide_eq_false_iff_not, hMiss0Val ⟨i.val - 13, by omega⟩]
      dsimp only []
      omega
  have hU0Card : U0.card = 19 := by
    rw [hU0Eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    decide
  let xSingle : Fin 26 → List Bool := fun i =>
    List.ofFn fun k : Fin 26 => xBase.getD k.val false || decide (k = i)
  have hxSingleLen : ∀ i, (xSingle i).length = 26 := fun i => by
    dsimp only [xSingle]; exact List.length_ofFn
  have hSingleTrue : ∀ i ∈ U0, C.eval (xSingle i) = true := by
    intro i hi
    have hBaseI : xBase.getD i.val false = false := (Finset.mem_filter.mp hi).2
    have hEdge : ∃ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
        ((p.val = i.val ∧ l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0) ∨
         (13 + l.val = i.val ∧ p ∈ Q0)) := by
      by_cases h13 : i.val < 13
      · let p : Fin 13 := ⟨i.val, h13⟩
        have hpNot : p ∉ Q0 := by
          intro hp
          have ht := quadIn_getD_left Q0 p hp
          change xBase.getD i.val false = true at ht
          rw [hBaseI] at ht; cases ht
        obtain ⟨l, hlMiss, hpIn⟩ := hCovP p hpNot
        exact ⟨p, l, hpIn, Or.inl ⟨rfl, hlMiss⟩⟩
      · let l : Fin 13 := ⟨i.val - 13, by omega⟩
        have hlNot : l ∉ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q0 := by
          intro hl
          have ht := quadIn_getD_right Q0 l hl
          have heq : 13 + l.val = i.val := by change 13 + (i.val - 13) = i.val; omega
          rw [heq] at ht
          change xBase.getD i.val false = true at ht
          rw [hBaseI] at ht; cases ht
        obtain ⟨p, hpQ0, hpIn⟩ := hCovL l hlNot
        exact ⟨p, l, hpIn, Or.inr ⟨by change 13 + (i.val - 13) = i.val; omega, hpQ0⟩⟩
    obtain ⟨p, l, hpIn, hSpec⟩ := hEdge
    refine mono_eval C hAO (incIn p l) (xSingle i) (incIn_len p l) (hxSingleLen i) ?_ (hInc p l hpIn)
    intro k hk hbit
    dsimp only [xSingle]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn, Bool.or_eq_true]
    rcases incIn_getD p l k hk hbit with rfl | rfl
    · rcases hSpec with ⟨hpEq, _hlMiss⟩ | ⟨_hlEq, hpQ0⟩
      · right; simp [hpEq]
      · left; exact quadIn_getD_left Q0 p hpQ0
    · rcases hSpec with ⟨_hpEq, hlMiss⟩ | ⟨hlEq, _hpQ0⟩
      · left; exact quadIn_getD_right Q0 l hlMiss
      · right; simp [hlEq]
  let S : ℕ → Finset (Fin 26) := fun w =>
    if (C.wires xBase).getD w false = true then ∅
    else U0.filter fun i => (C.wires (xSingle i)).getD w false = true
  have hSInput : ∀ i ∈ U0, S i.val = {i} := by
    intro i hi
    have hbf : (C.wires xBase).getD i.val false = false := by
      change (C.gates.foldl step xBase).getD i.val false = false
      rw [wires_prefix _ _ _ (by rw [hxBaseLen]; exact i.isLt)]
      exact (Finset.mem_filter.mp hi).2
    dsimp only [S]
    rw [ite_eq_right (by rw [hbf]; decide)]
    ext k
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_hk, hkw⟩
      change (C.gates.foldl step (xSingle k)).getD i.val false = true at hkw
      rw [wires_prefix _ _ _ (by rw [hxSingleLen]; exact i.isLt)] at hkw
      dsimp only [xSingle] at hkw
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn, Bool.or_eq_true] at hkw
      rcases hkw with hqb | hki
      · have hbi := (Finset.mem_filter.mp hi).2
        rw [hqb] at hbi; cases hbi
      · exact (decide_eq_true_eq.mp hki).symm
    · rintro rfl
      refine ⟨hi, ?_⟩
      change (C.gates.foldl step (xSingle k)).getD k.val false = true
      rw [wires_prefix _ _ _ (by rw [hxSingleLen]; exact k.isLt)]
      dsimp only [xSingle]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.isLt), List.getElem_ofFn]
      rw [decide_eq_true rfl, Bool.or_true]
  have hSOut : S C.output = U0 := by
    dsimp only [S]
    rw [ite_eq_right (by change C.eval xBase ≠ true; rw [hBaseFalse]; decide)]
    ext i
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    exact fun hi => hSingleTrue i hi
  have hOutLt : C.output < 26 + C.gates.length := by
    obtain ⟨i0, hi0⟩ : U0.Nonempty := Finset.card_pos.mp (by omega)
    have ht := hSingleTrue i0 hi0
    by_contra hge
    change (C.gates.foldl step (xSingle i0)).getD C.output false = true at ht
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [wires_len, hxSingleLen]; omega)] at ht
    cases ht
  have hSGates : ∀ j < C.gates.length,
      let g := C.gates.getD j dGate
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → S (26 + j) ⊆ S a ∨ S (26 + j) ⊆ S b) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → S (26 + j) ⊆ S a ∪ S b) := by
    intro j hj
    have hevB := gateEval C hAO xBase j hxBaseLen hj
    constructor
    · intro hand
      by_cases hJ : (C.wires xBase).getD (26 + j) false = true
      · left; dsimp only [S]; rw [ite_eq_left hJ]; exact Finset.empty_subset _
      · have hBF : ((C.wires xBase).getD ((C.gates.getD j dGate).inputs.getD 0 0) false &&
            (C.wires xBase).getD ((C.gates.getD j dGate).inputs.getD 1 0) false) = false := by
          rw [← hevB.1 hand]; exact Bool.eq_false_iff.mpr hJ
        rw [Bool.and_eq_false_iff] at hBF
        rcases hBF with haF | hbF
        · left
          intro i hi
          dsimp only [S] at hi ⊢
          rw [ite_eq_right hJ, Finset.mem_filter] at hi
          rw [ite_eq_right (by rw [haF]; decide), Finset.mem_filter]
          refine ⟨hi.1, ?_⟩
          have hevI := gateEval C hAO (xSingle i) j (hxSingleLen i) hj
          have ht := hi.2
          rw [hevI.1 hand, Bool.and_eq_true] at ht
          exact ht.1
        · right
          intro i hi
          dsimp only [S] at hi ⊢
          rw [ite_eq_right hJ, Finset.mem_filter] at hi
          rw [ite_eq_right (by rw [hbF]; decide), Finset.mem_filter]
          refine ⟨hi.1, ?_⟩
          have hevI := gateEval C hAO (xSingle i) j (hxSingleLen i) hj
          have ht := hi.2
          rw [hevI.1 hand, Bool.and_eq_true] at ht
          exact ht.2
    · intro hor
      by_cases hJ : (C.wires xBase).getD (26 + j) false = true
      · dsimp only [S]; rw [ite_eq_left hJ]; exact Finset.empty_subset _
      · have hBF : ((C.wires xBase).getD ((C.gates.getD j dGate).inputs.getD 0 0) false ||
            (C.wires xBase).getD ((C.gates.getD j dGate).inputs.getD 1 0) false) = false := by
          rw [← hevB.2 hor]; exact Bool.eq_false_iff.mpr hJ
        rw [Bool.or_eq_false_iff] at hBF
        intro i hi
        dsimp only [S] at hi ⊢
        rw [ite_eq_right hJ, Finset.mem_filter] at hi
        rw [Finset.mem_union, ite_eq_right (by rw [hBF.1]; decide), ite_eq_right (by rw [hBF.2]; decide)]
        have hevI := gateEval C hAO (xSingle i) j (hxSingleLen i) hj
        have ht := hi.2
        rw [hevI.2 hor, Bool.or_eq_true] at ht
        rcases ht with ha | hb
        · exact Or.inl (Finset.mem_filter.mpr ⟨hi.1, ha⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨hi.1, hb⟩)
  have hU0Empty : ∀ (w : ℕ) (hw : w < 26), (⟨w, hw⟩ : Fin 26) ∉ U0 → S w = ∅ := by
    intro w hw hwU
    have hbt : (C.wires xBase).getD w false = true := by
      change (C.gates.foldl step xBase).getD w false = true
      rw [wires_prefix _ _ _ (by rw [hxBaseLen]; exact hw)]
      dsimp only [U0] at hwU
      rw [Finset.mem_filter] at hwU
      exact Bool.eq_true_of_not_eq_false fun h => hwU ⟨Finset.mem_univ _, h⟩
    dsimp only [S]; exact ite_eq_left hbt
  exact ⟨U0, S, hU0Card, hSOut, hOutLt, hSInput, hU0Empty, hSGates⟩

private theorem or_lower_bound (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 26 C)
    (hInc : ∀ (x3 x4 : Fin 13), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = x3)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = x4)) = true)
    (hQuad : ∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 ∈ x4)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = false) :
    18 ≤ PEqualNP.ReadTwo.nOr C := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hOps := hAO.1
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j dGate).inputs, i < 26 + j := hAO.2.1
  have hLen2 := hAO.2.2
  obtain ⟨U0, S, hU0Card, hSOut, hOutLt, hSInput, hU0Empty, hSGates⟩ := us_props C hAO hInc hQuad
  have hParts : ∀ j ≤ C.gates.length, ∃ parts : Finset (Finset (Fin 26)),
      (∀ A ∈ parts, A.Nonempty ∧ A ⊆ U0) ∧
      (∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B) ∧
      (∀ w < 26 + j, ∃ A ∈ parts, S w ⊆ A) ∧
      19 ≤ parts.card + ((C.gates.take j).filter fun g =>
        decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)).length := by
    intro j
    induction j with
    | zero =>
      intro _
      let parts0 : Finset (Finset (Fin 26)) := U0.image fun i => ({i} : Finset (Fin 26))
      refine ⟨parts0, ?_, ?_, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩
        exact ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩
      · intro A hA B hB hNe
        rcases Finset.mem_image.mp hA with ⟨i, _, rfl⟩
        rcases Finset.mem_image.mp hB with ⟨k, _, rfl⟩
        rw [Finset.disjoint_singleton]
        exact fun h => hNe (congrArg (fun x : Fin 26 => ({x} : Finset (Fin 26))) h)
      · intro w hw
        have hw26 : w < 26 := by omega
        by_cases hwU : (⟨w, hw26⟩ : Fin 26) ∈ U0
        · exact ⟨{⟨w, hw26⟩}, Finset.mem_image_of_mem _ hwU, by rw [hSInput _ hwU]⟩
        · obtain ⟨i0, hi0⟩ : U0.Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨{i0}, Finset.mem_image_of_mem _ hi0, by rw [hU0Empty w hw26 hwU]; exact Finset.empty_subset _⟩
      · rw [List.take_zero, List.filter_nil, List.length_nil, Nat.add_zero]
        dsimp only [parts0]
        rw [Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_inj.mp h), hU0Card]
    | succ j ih =>
      intro hjSucc
      have hj : j < C.gates.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hjSucc
      obtain ⟨parts, hNonempty, hDisj, hCover, hCount⟩ := ih (Nat.le_of_succ_le hjSucc)
      have hmem : C.gates.getD j dGate ∈ C.gates := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      have hlen : (C.gates.getD j dGate).inputs.length = 2 := hLen2 _ hmem
      have heq := list_len2 _ hlen
      let a := (C.gates.getD j dGate).inputs.getD 0 0
      let b := (C.gates.getD j dGate).inputs.getD 1 0
      have haLt : a < 26 + j := hRB' j hj a (by rw [heq]; exact List.mem_cons_self)
      have hbLt : b < 26 + j := hRB' j hj b (by rw [heq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hTakeSucc : C.gates.take (j + 1) = C.gates.take j ++ [C.gates.getD j dGate] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
          List.getD_eq_getElem _ _ hj]
      rcases hOps _ hmem with hand | hor
      · refine ⟨parts, hNonempty, hDisj, ?_, ?_⟩
        · intro w hw
          by_cases hwOld : w < 26 + j
          · exact hCover w hwOld
          · have hwEq : w = 26 + j := by omega
            rw [hwEq]
            rcases (hSGates j hj).1 hand with hSa | hSb
            · obtain ⟨A, hA, hSub⟩ := hCover a haLt
              exact ⟨A, hA, hSa.trans hSub⟩
            · obtain ⟨B, hB, hSub⟩ := hCover b hbLt
              exact ⟨B, hB, hSb.trans hSub⟩
        · rw [hTakeSucc, List.filter_append, List.length_append]
          exact Nat.le_trans hCount (Nat.add_le_add_left (Nat.le_add_right _ _) _)
      · obtain ⟨A, hA, hSubA⟩ := hCover a haLt
        obtain ⟨B, hB, hSubB⟩ := hCover b hbLt
        have hFilterAdd : ((C.gates.take (j + 1)).filter fun g =>
            decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)).length =
            ((C.gates.take j).filter fun g =>
              decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)).length + 1 := by
          rw [hTakeSucc, List.filter_append, List.length_append, List.filter_cons,
            ite_eq_left (by rw [hor]; decide),
            List.filter_nil, List.length_singleton]
        by_cases hAB : A = B
        · refine ⟨parts, hNonempty, hDisj, ?_, ?_⟩
          · intro w hw
            by_cases hwOld : w < 26 + j
            · exact hCover w hwOld
            · have hwEq : w = 26 + j := by omega
              rw [hwEq]
              refine ⟨A, hA, (hSGates j hj).2 hor |>.trans ?_⟩
              rw [Finset.union_subset_iff]
              exact ⟨hSubA, hAB ▸ hSubB⟩
          · rw [hFilterAdd]; omega
        · let parts' : Finset (Finset (Fin 26)) := insert (A ∪ B) ((parts.erase A).erase B)
          refine ⟨parts', ?_, ?_, ?_, ?_⟩
          · intro X hX
            rcases Finset.mem_insert.mp hX with rfl | hX'
            · exact ⟨Finset.Nonempty.inl (hNonempty A hA).1,
                Finset.union_subset (hNonempty A hA).2 (hNonempty B hB).2⟩
            · have hXp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hX')
              exact hNonempty X hXp
          · intro X hX Y hY hXY
            rcases Finset.mem_insert.mp hX with rfl | hX' <;>
              rcases Finset.mem_insert.mp hY with rfl | hY'
            · exact False.elim (hXY rfl)
            · have hYp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hY')
              have hYneB : Y ≠ B := Finset.ne_of_mem_erase hY'
              have hYneA : Y ≠ A := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hY')
              exact Finset.disjoint_union_left.mpr ⟨(hDisj A hA Y hYp hYneA.symm),
                (hDisj B hB Y hYp hYneB.symm)⟩
            · have hXp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hX')
              have hXneB : X ≠ B := Finset.ne_of_mem_erase hX'
              have hXneA : X ≠ A := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hX')
              exact Finset.disjoint_union_right.mpr ⟨hDisj X hXp A hA hXneA,
                hDisj X hXp B hB hXneB⟩
            · have hXp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hX')
              have hYp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hY')
              exact hDisj X hXp Y hYp hXY
          · intro w hw
            by_cases hwOld : w < 26 + j
            · obtain ⟨X, hXp, hSw⟩ := hCover w hwOld
              by_cases hXA : X = A
              · refine ⟨A ∪ B, Finset.mem_insert_self _ _, hSw.trans (hXA ▸ Finset.subset_union_left)⟩
              · by_cases hXB : X = B
                · refine ⟨A ∪ B, Finset.mem_insert_self _ _, hSw.trans (hXB ▸ Finset.subset_union_right)⟩
                · refine ⟨X, Finset.mem_insert_of_mem (Finset.mem_erase.mpr
                    ⟨hXB, Finset.mem_erase.mpr ⟨hXA, hXp⟩⟩), hSw⟩
            · have hwEq : w = 26 + j := by omega
              rw [hwEq]
              refine ⟨A ∪ B, Finset.mem_insert_self _ _, (hSGates j hj).2 hor |>.trans ?_⟩
              exact Finset.union_subset_union hSubA hSubB
          · have hNotIn : A ∪ B ∉ (parts.erase A).erase B := by
              intro hIn
              have hNeA := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hIn)
              have hpIn := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hIn)
              have hd := hDisj A hA (A ∪ B) hpIn hNeA.symm
              obtain ⟨x0, hx0⟩ := (hNonempty A hA).1
              exact Finset.disjoint_left.mp hd hx0 (Finset.mem_union_left B hx0)
            have hBIn : B ∈ parts.erase A := Finset.mem_erase.mpr ⟨Ne.symm hAB, hB⟩
            have hCardE1 : (parts.erase A).card = parts.card - 1 := Finset.card_erase_of_mem hA
            have hCardE2 : ((parts.erase A).erase B).card = parts.card - 2 := by
              rw [Finset.card_erase_of_mem hBIn, hCardE1]; omega
            have hCardP : parts.card ≥ 2 := by
              have hc := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
              omega
            have hCardNew : parts'.card = parts.card - 1 := by
              dsimp only [parts']
              rw [Finset.card_insert_of_notMem hNotIn, hCardE2]; omega
            rw [hFilterAdd, hCardNew]; omega
  obtain ⟨parts, hNonempty, hDisj, hCover, hCount⟩ := hParts C.gates.length le_rfl
  obtain ⟨A0, hA0, hSubOut⟩ := hCover C.output hOutLt
  rw [hSOut] at hSubOut
  have hEqSing : parts = {A0} := by
    ext X
    simp only [Finset.mem_singleton]
    constructor
    · intro hX
      by_contra hNe
      have hd := hDisj X hX A0 hA0 hNe
      obtain ⟨x0, hx0⟩ := (hNonempty X hX).1
      exact Finset.disjoint_left.mp hd hx0 (hSubOut ((hNonempty X hX).2 hx0))
    · rintro rfl; exact hA0
  rw [hEqSing, Finset.card_singleton, List.take_of_length_le le_rfl] at hCount
  change 19 ≤ 1 + PEqualNP.ReadTwo.nOr C at hCount
  omega

end PEqualNP.Outside.L_meta_5274

theorem PEqualNP.Outside.L_meta_5274 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) → (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x1.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.false) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x1 := by
  intro C hAO hInc hQuad
  exact ⟨PEqualNP.Outside.L_meta_5274.and_lower_bound C hAO hInc hQuad,
    PEqualNP.Outside.L_meta_5274.or_lower_bound C hAO hInc hQuad⟩
