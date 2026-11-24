import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_612_101
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (noJunk : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → PEqualNP.TopForm.TopForm G D → (junk G D).card = 0 →
      G.edgeFinset.card + t ≤ D.size + 1)
    (oneJunk : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → PEqualNP.TopForm.TopForm G D → (junk G D).card = 1 →
      G.edgeFinset.card + t ≤ D.size + 1)
    (manyJunk : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → PEqualNP.TopForm.TopForm G D → 2 ≤ (junk G D).card →
      G.edgeFinset.card + t ≤ D.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hEdges hNoCycle hexCover hminCover hMono hEval
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hNonempty : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hEdges
    exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr huv)⟩
  have hFour : NoFourCycle G := by
    intro a c hac
    apply Finset.card_le_one.mpr
    intro b hb d hd
    have hbAdj := (Finset.mem_filter.mp hb).2
    have hdAdj := (Finset.mem_filter.mp hd).2
    by_contra hbd
    exact hNoCycle a b c d hbAdj.1.ne hac hdAdj.1.ne hbAdj.2.ne.symm hbd hdAdj.2.ne
      hbAdj.1 hbAdj.2.symm hdAdj.2 hdAdj.1.symm
  have hFun : circuitFun n C = NestedCover.graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    have hx : C.eval (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
      cases h : C.eval (List.ofFn x) with
      | false => exact (decide_eq_false (fun he => by simpa [h] using (hEval x).mpr he)).symm
      | true => exact (decide_eq_true ((hEval x).mp h)).symm
    simpa using hx
  obtain ⟨D, hLeast, hTop, hSize⟩ := normalize n G C hNonempty hMono hFun
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  by_cases h0 : (junk G D).card = 0
  · exact (noJunk n t G D hFour hNonempty hexCover hminCover hLeast hTop h0).trans (Nat.add_le_add_right hSize 1)
  · by_cases h1 : (junk G D).card = 1
    · exact (oneJunk n t G D hFour hNonempty hexCover hminCover hLeast hTop h1).trans (Nat.add_le_add_right hSize 1)
    · exact (manyJunk n t G D hFour hNonempty hexCover hminCover hLeast hTop (by omega)).trans (Nat.add_le_add_right hSize 1)
