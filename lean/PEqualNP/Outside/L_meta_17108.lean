import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17108

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, gateStep]
    omega

private lemma foldl_gateStep_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < w.length) :
    (gs.foldl gateStep w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hlen : k < (gateStep w g).length := by
      simp [gateStep]
      omega
    rw [List.foldl_cons, ih (gateStep w g) hlen]
    simp [gateStep, List.getD, List.getElem?_append_left hk]

private lemma wires_getD_first (g : Gate) (gs : List Gate) (xs : List Bool) :
    (({ gates := g :: gs, output := o } : Circuit).wires xs).getD xs.length false =
      g.op.eval (g.inputs.map fun i => xs.getD i false) := by
  change ((g :: gs).foldl gateStep xs).getD xs.length false = _
  rw [List.foldl_cons, foldl_gateStep_getD_lt gs (gateStep xs g) xs.length (by simp [gateStep])]
  simp [gateStep, List.getD]

private lemma getD_ofFn {n : ℕ} (y : Fin n → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < n then y ⟨i, h⟩ else false := by
  by_cases h : i < n
  · simp [List.getD, h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    simp [h]

private lemma list_le_two {α : Type*} (l : List α) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  · simp at h

private def target9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) ||
  (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) ||
  (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)

private lemma target9_nonconst :
    target9 (fun _ => false) ≠ target9 (fun _ => true) := by
  decide

private lemma gates_nonempty_of_target9 (D : Circuit) (hD : circuitFun 9 D = target9) :
    D.gates ≠ [] := by
  intro hnil
  have eval_eq : ∀ x : Fin 9 → Bool, (List.ofFn x).getD D.output false = target9 x := by
    intro x
    have hx := congrFun hD x
    simpa [circuitFun, Circuit.eval, Circuit.wires, hnil] using hx
  by_cases ho : D.output < 9
  · let k : Fin 9 := ⟨D.output, ho⟩
    have h1 := eval_eq (fun i => decide (i = k))
    rw [getD_ofFn] at h1
    have hlhs : (if h : D.output < 9 then decide (⟨D.output, h⟩ = k) else false) = true := by
      simp [ho, k]
    rw [hlhs] at h1
    have hall : ∀ c : Fin 9, target9 (fun i => decide (i = c)) = false := by decide
    rw [hall k] at h1
    contradiction
  · have h1 := eval_eq (fun _ => true)
    rw [getD_ofFn] at h1
    simp only [ho, dite_false] at h1
    have htrue : target9 (fun _ => true) = true := by decide
    rw [htrue] at h1
    contradiction

private lemma solve_all
    (hRed : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
      (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧
      (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
      (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧
        (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs
          (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true))
    (hcases : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C →
      ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y i)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y i && y j)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y i || y j))) →
      circuitFun 9 C = target9 → 16 ≤ C.size)
    {t : ℕ} (ht : HasCircuitSize 9 target9 t) : 16 ≤ t := by
  classical
  rcases ht with ⟨C, hFC, hCt, hCe⟩
  have hCf : circuitFun 9 C = target9 := funext hCe
  have hex : ∃ k : ℕ, ∃ D : Circuit, FanInTwo D ∧ circuitFun 9 D = target9 ∧ D.size = k :=
    ⟨C.size, C, hFC, hCf, rfl⟩
  let k := Nat.find hex
  have hk_spec : ∃ D : Circuit, FanInTwo D ∧ circuitFun 9 D = target9 ∧ D.size = k :=
    Nat.find_spec hex
  rcases hk_spec with ⟨D, hFD, hDf, hDk⟩
  have hkC : k ≤ C.size := Nat.find_min' hex ⟨C, hFC, hCf, rfl⟩
  have hk_le_t : k ≤ t := hkC.trans hCt
  have hMinD : IsMinimalCircuit 9 D := by
    refine ⟨hFD, ?_⟩
    intro E hFE hED
    exact hDk ▸ Nat.find_min' hex ⟨E, hFE, hED.trans hDf, rfl⟩
  have hNonConstF : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [hDf]
    exact target9_nonconst
  obtain ⟨hNonConstG, hDistinct, _⟩ := hRed 9 D hMinD hNonConstF
  have hDne : D.gates ≠ [] := gates_nonempty_of_target9 D hDf
  rcases D with ⟨gates, o⟩
  rcases gates with _ | ⟨g, gs⟩
  · exact (hDne rfl).elim
  have hpos : 0 < (g :: gs).length := by simp
  obtain ⟨xNC, yNC, hNC⟩ := hNonConstG 0 hpos
  have hfg : g ∈ ({ gates := g :: gs, output := o } : Circuit).gates := List.mem_cons_self
  obtain ⟨hgop, hglen⟩ := hFD g hfg
  have hwire9 : ∀ y : Fin 9 → Bool,
      (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false =
        g.op.eval (g.inputs.map fun i => if h : i < 9 then y ⟨i, h⟩ else false) := by
    intro y
    have hlen9 : (List.ofFn y).length = 9 := by simp
    have hw := wires_getD_first g gs (List.ofFn y) (o := o)
    rw [hlen9] at hw
    rw [hw]
    congr 1
    apply List.map_congr_left
    intro i _
    exact getD_ofFn y i
  have hconst_contra : ∀ b : Bool,
      (∀ y : Fin 9 → Bool, (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false = b) →
      False := by
    intro b hb
    apply hNC
    rw [hb xNC, hb yNC]
  have hcopy_contra : ∀ (i : ℕ) (hi : i < 9),
      (∀ y : Fin 9 → Bool, (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false = y ⟨i, hi⟩) →
      False := by
    intro i hi hcp
    obtain ⟨xD, hxD⟩ := hDistinct i 0 (by omega) hpos
    have hwi : (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn xD)).getD i false =
        xD ⟨i, hi⟩ := by
      have hw : (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn xD)).getD i false =
          (List.ofFn xD).getD i false :=
        foldl_gateStep_getD_lt (g :: gs) (List.ofFn xD) i (by simp; omega)
      rw [hw, getD_ofFn]
      simp [hi]
    have hx9 : (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn xD)).getD (9 + 0) false =
        xD ⟨i, hi⟩ := hcp xD
    exact hxD (hwi.trans hx9.symm)
  have h_not_case : ∀ i : Fin 9,
      (∀ y : Fin 9 → Bool, (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false = !(y i)) →
      16 ≤ t := by
    intro i hi
    exact (hcases i _ hFD (Or.inl hi) hDf).trans (hDk ▸ hk_le_t)
  have h_and_case : ∀ i j : Fin 9, i < j →
      (∀ y : Fin 9 → Bool, (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false = (y i && y j)) →
      16 ≤ t := by
    intro i j hij hji
    exact (hcases i _ hFD (Or.inr (Or.inl ⟨j, hij, hji⟩)) hDf).trans (hDk ▸ hk_le_t)
  have h_or_case : ∀ i j : Fin 9, i < j →
      (∀ y : Fin 9 → Bool, (({ gates := g :: gs, output := o } : Circuit).wires (List.ofFn y)).getD 9 false = (y i || y j)) →
      16 ≤ t := by
    intro i j hij hji
    exact (hcases i _ hFD (Or.inr (Or.inr ⟨j, hij, hji⟩)) hDf).trans (hDk ▸ hk_le_t)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
  rcases hgop with h_op | h_op | h_op
  · rcases list_le_two g.inputs hglen with hnil | ⟨a, ha⟩ | ⟨a, b, hab⟩
    · exact (hconst_contra true fun y => by rw [hwire9 y, h_op, hnil]; rfl).elim
    · by_cases ha9 : a < 9
      · exact (hcopy_contra a ha9 fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]).elim
      · exact (hconst_contra false fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]).elim
    · by_cases ha9 : a < 9
      · by_cases hb9 : b < 9
        · rcases lt_trichotomy a b with hlt | heq | hgt
          · exact h_and_case ⟨a, ha9⟩ ⟨b, hb9⟩ hlt fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]
          · subst heq
            exact (hcopy_contra a ha9 fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, GateOp.eval]).elim
          · exact h_and_case ⟨b, hb9⟩ ⟨a, ha9⟩ hgt fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval, Bool.and_comm]
        · exact (hconst_contra false fun y => by
            rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]).elim
      · exact (hconst_contra false fun y => by
          rw [hwire9 y, h_op, hab]; simp [ha9, GateOp.eval]).elim
  · rcases list_le_two g.inputs hglen with hnil | ⟨a, ha⟩ | ⟨a, b, hab⟩
    · exact (hconst_contra false fun y => by rw [hwire9 y, h_op, hnil]; rfl).elim
    · by_cases ha9 : a < 9
      · exact (hcopy_contra a ha9 fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]).elim
      · exact (hconst_contra false fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]).elim
    · by_cases ha9 : a < 9
      · by_cases hb9 : b < 9
        · rcases lt_trichotomy a b with hlt | heq | hgt
          · exact h_or_case ⟨a, ha9⟩ ⟨b, hb9⟩ hlt fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]
          · subst heq
            exact (hcopy_contra a ha9 fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, GateOp.eval]).elim
          · exact h_or_case ⟨b, hb9⟩ ⟨a, ha9⟩ hgt fun y => by
              rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval, Bool.or_comm]
        · exact (hcopy_contra a ha9 fun y => by
            rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]).elim
      · by_cases hb9 : b < 9
        · exact (hcopy_contra b hb9 fun y => by
            rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]).elim
        · exact (hconst_contra false fun y => by
            rw [hwire9 y, h_op, hab]; simp [ha9, hb9, GateOp.eval]).elim
  · rcases list_le_two g.inputs hglen with hnil | ⟨a, ha⟩ | ⟨a, b, hab⟩
    · exact (hconst_contra true fun y => by rw [hwire9 y, h_op, hnil]; rfl).elim
    · by_cases ha9 : a < 9
      · exact h_not_case ⟨a, ha9⟩ fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]
      · exact (hconst_contra true fun y => by
          rw [hwire9 y, h_op, ha]; simp [ha9, GateOp.eval]).elim
    · by_cases ha9 : a < 9
      · exact h_not_case ⟨a, ha9⟩ fun y => by
          rw [hwire9 y, h_op, hab]; simp [ha9, GateOp.eval]
      · exact (hconst_contra true fun y => by
          rw [hwire9 y, h_op, hab]; simp [ha9, GateOp.eval]).elim

end PEqualNP.Outside.L_meta_17108

theorem PEqualNP.Outside.L_meta_17108 : ((∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) t → 16 ≤ t) := by
  intro hRed h0 h1 h2 h3 h4 h5 h6 h7 h8 t ht
  refine PEqualNP.Outside.L_meta_17108.solve_all hRed ?_ ht
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
