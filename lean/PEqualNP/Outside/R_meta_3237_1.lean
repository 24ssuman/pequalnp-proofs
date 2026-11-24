import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3237_1
    (h1 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool),
      (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) →
      (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 →
        x4.op = (fun (x7 x8 : Bool) => x7 == Bool.true && x8 == Bool.true) ∧
        [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left,
          [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) →
      (∀ (x5 : Fin (9 : ℕ) → Bool),
        (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) =
        (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) ||
          x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) ||
          x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) ||
          x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
          x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
          x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (14 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool),
      (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) →
      (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 →
        x4.op = (fun (x7 x8 : Bool) => x7 == Bool.true && x8 == Bool.false) ∧
        [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left,
          [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) →
      (∀ (x5 : Fin (9 : ℕ) → Bool),
        (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) =
        (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) ||
          x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) ||
          x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) ||
          x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
          x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
          x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (14 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.true && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro x1 x2 h_gates h_gate0 h_eval
  by_cases h0 : ∃ x4, x1.gates[(0 : ℕ)]? = Option.some x4
  · obtain ⟨x4, hx4⟩ := h0
    obtain ⟨⟨x6, hx6⟩, hle⟩ := h_gate0 x4 hx4
    by_cases h6 : x6 = true
    · subst h6
      apply h1 x1 x2 h_gates _ h_eval
      intro y hy
      have hyx : y = x4 := Option.some.inj (hy.symm.trans hx4)
      subst hyx
      exact ⟨hx6, hle⟩
    · have h6_false : x6 = false := Bool.eq_false_iff.mpr h6
      subst h6_false
      apply h2 x1 x2 h_gates _ h_eval
      intro y hy
      have hyx : y = x4 := Option.some.inj (hy.symm.trans hx4)
      subst hyx
      exact ⟨hx6, hle⟩
  · apply h1 x1 x2 h_gates _ h_eval
    intro x4 hx4
    exact False.elim (h0 ⟨x4, hx4⟩)
