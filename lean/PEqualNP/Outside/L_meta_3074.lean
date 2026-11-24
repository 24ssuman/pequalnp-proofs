import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_1669

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3074

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma kept (rs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (rs.foldl step w).getD i false = w.getD i false := by
  induction rs generalizing w with
  | nil => rfl
  | cons g rs ih =>
    rw [List.foldl_cons]
    have hi' : i < (step w g).length := by
      dsimp [step]
      rw [List.length_append]
      omega
    rw [ih (step w g) hi']
    dsimp [step]
    rw [List.getD_append _ _ _ _ hi]

lemma ofFn_getD (y : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rfl
  · contradiction

lemma step_first (y : Fin 9 → Bool) :
    step (List.ofFn y) ⟨GateOp.and, [0, 3]⟩ = List.ofFn y ++ [y 0 && y 3] := by
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, Bool.and_true, id_eq]
  have h0 : (List.ofFn y).getD 0 false = y 0 := ofFn_getD y 0 (by omega)
  have h3 : (List.ofFn y).getD 3 false = y 3 := ofFn_getD y 3 (by omega)
  rw [h0, h3]

end PEqualNP.Outside.L_meta_3074

theorem PEqualNP.Outside.L_meta_3074 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) → (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) → (15 : ℕ) ≤ x1.size := by
  intro x1 hFan _ _ hEval _
  let firstGate : Gate := ⟨GateOp.and, [0, 3]⟩
  let C : Circuit := ⟨firstGate :: x1.gates, x1.output⟩
  have hFanC : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons] at hg
    rcases hg with rfl | hg
    · refine ⟨by simp [firstGate], by simp [firstGate]⟩
    · exact hFan g hg
  have hWire9 : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3) := by
    intro y
    change ((firstGate :: x1.gates).foldl PEqualNP.Outside.L_meta_3074.step (List.ofFn y)).getD 9 false = _
    rw [List.foldl_cons, PEqualNP.Outside.L_meta_3074.step_first]
    have h9 : 9 < (List.ofFn y ++ [y 0 && y 3]).length := by simp
    rw [PEqualNP.Outside.L_meta_3074.kept x1.gates _ 9 h9]
    simp
  have hFun : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext y
    change C.eval (List.ofFn y) = _
    change ((firstGate :: x1.gates).foldl PEqualNP.Outside.L_meta_3074.step (List.ofFn y)).getD x1.output false = _
    rw [List.foldl_cons, PEqualNP.Outside.L_meta_3074.step_first]
    change x1.eval (List.ofFn y ++ [y 0 && y 3]) = _
    exact hEval y
  have h16 := PEqualNP.Outside.L_meta_1669 C hFanC hWire9 hFun
  change 16 ≤ (firstGate :: x1.gates).length at h16
  simp only [List.length_cons] at h16
  have hsz : x1.size = x1.gates.length := rfl
  omega
