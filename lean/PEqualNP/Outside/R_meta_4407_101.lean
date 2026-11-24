import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4407_101
    (monotoneOnly :
      ∀ (x1 : Finset (Fin 9)) (C : Circuit),
        x1.card ≤ 2 → Monotone2 C → C.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ x1, x i = true)]) ≠
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
              x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    (baseNot :
      ∀ (x1 : Finset (Fin 9)) (C : Circuit) (p : Fin 11),
        x1.card ≤ 2 → Monotone2 C → C.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          have w := List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ x1, x i = true)];
          C.eval (w ++ [!(w.getD p.val false)]) ≠
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
              x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    (gateNotAliases :
      ∀ (x1 : Finset (Fin 9)) (x2 x3 : Circuit) (p : ℕ),
        (x1 = ∅ ∨ x1 = {0, 4} ∨ ∃ a : Fin 9, a.val ∈ ([0, 1, 2, 3, 4, 6] : List ℕ) ∧ x1 = {a}) →
        Monotone2 x2 → Monotone2 x3 → x2.size + x3.size ≤ 12 → 11 ≤ p → p < 11 + x2.size →
        ∃ x : Fin 9 → Bool,
          have w := x2.wires (List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ x1, x i = true)]);
          x3.eval (w ++ [!(w.getD p false)]) ≠
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
              x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    (gateNotPairs :
      ∀ (x1 : Finset (Fin 9)) (x2 x3 : Circuit) (p : ℕ),
        (∃ a b : Fin 9, (a.val * 10 + b.val) ∈
          ([1, 2, 12, 3, 13, 23, 14, 24, 34, 15, 25, 6, 16, 26, 36, 46, 56, 27, 67, 28] : List ℕ) ∧
          a < b ∧ x1 = {a, b}) →
        Monotone2 x2 → Monotone2 x3 → x2.size + x3.size ≤ 12 → 11 ≤ p → p < 11 + x2.size →
        ∃ x : Fin 9 → Bool,
          have w := x2.wires (List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ x1, x i = true)]);
          x3.eval (w ++ [!(w.getD p false)]) ≠
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
              x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) :
    ∀ (x1 : Finset (Fin (9 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Option ℕ),   x1.card ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.Monotone2 x3 →         x2.size + x3.size ≤ (12 : ℕ) →           have x9 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x9 : Fin (9 : ℕ) → Bool) => List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x10 ∈ x1, x9 x10 = Bool.true)];           have x10 : List Bool → Option ℕ → List Bool := fun (x10 : List Bool) (x11 : Option ℕ) => x10 ++ [!x11.elim Bool.false fun (x12 : ℕ) => x10.getD x12 Bool.false];           have x11 : (Fin (9 : ℕ) → Bool) → Bool := fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)));           ∃ (x12 : Fin (9 : ℕ) → Bool), x3.eval (x10 (x2.wires (x9 x12)) x4) ≠ x11 x12 := by
  intro x1 x2 x3 x4 hcard hm2 hm3 hsz
  dsimp only
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_len : ∀ (gs : List Gate) (u : List Bool),
      (gs.foldl step u).length = u.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro u; rfl
    | cons g gs ih =>
      intro u
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have wires_append : ∀ (gs₁ gs₂ : List Gate) (u : List Bool),
      (gs₁ ++ gs₂).foldl step u = gs₂.foldl step (gs₁.foldl step u) := by
    intro gs₁ gs₂ u
    exact List.foldl_append
  have wires_prefix : ∀ (gs : List Gate) (u : List Bool) (i : ℕ), i < u.length →
      (gs.foldl step u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u i _; rfl
    | cons g gs ih =>
      intro u i hi
      rw [List.foldl_cons, ih]
      · dsimp only [step]; rw [List.getD_append _ _ _ _ hi]
      · simp [step]; omega
  let baseOf := fun (S : Finset (Fin 9)) (x : Fin 9 → Bool) =>
    List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ S, x i = true)]
  let edge := fun x : Fin 9 → Bool =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have base_len : ∀ S x, (baseOf S x).length = 11 := by
    intro S x; simp [baseOf]
  have constTrueCase :
      ∃ x : Fin 9 → Bool, x3.eval (x2.wires (baseOf x1 x) ++ [true]) ≠ edge x := by
    by_contra! heq
    let V := Sum Bool ℕ
    let evalVal : List Bool → V → Bool :=
      fun cur v => Sum.casesOn v (fun b => b) (fun i => cur.getD i false)
    let compileBin : Bool → ℕ → V → V → Option Gate × V := fun isOr nextIdx va vb =>
      Sum.casesOn va
        (fun b1 => Sum.casesOn vb
          (fun b2 => (none, Sum.inl (if isOr then b1 || b2 else b1 && b2)))
          (fun ib => (none, if (if isOr then b1 else !b1) then Sum.inl b1 else Sum.inr ib)))
        (fun ia => Sum.casesOn vb
          (fun b2 => (none, if (if isOr then b2 else !b2) then Sum.inl b2 else Sum.inr ia))
          (fun ib => (some ⟨if isOr then GateOp.or else GateOp.and, [ia, ib]⟩, Sum.inr nextIdx)))
    let compileList : Bool → ℕ → (ℕ → V) → List ℕ → Option Gate × V :=
      fun isOr nextIdx v ins =>
        List.casesOn ins
          (none, Sum.inl (!isOr))
          (fun a r1 => List.casesOn r1
            (none, v a)
            (fun b r2 => List.casesOn r2
              (compileBin isOr nextIdx (v a) (v b))
              (fun _ _ => (none, Sum.inl false))))
    let compileOne : ℕ → List V → Gate → Option Gate × V := fun nextIdx mp g =>
      let v : ℕ → V := fun i => mp.getD i (Sum.inl false)
      GateOp.casesOn g.op
        (compileList false nextIdx v g.inputs)
        (compileList true nextIdx v g.inputs)
        (none, Sum.inl false)
        (fun _ => (none, Sum.inl false))
        (none, Sum.inl false)
    have compileOne_mono : ∀ (nextIdx : ℕ) (mp : List V) (g g' : Gate),
        (compileOne nextIdx mp g).1 = some g' →
        g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
      intro nextIdx mp g g' hopt
      rcases g with ⟨op, ins⟩
      dsimp only [compileOne] at hopt
      cases op
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
          dsimp only [compileList, compileBin] at hopt
        · cases hopt
        · cases hopt
        · cases hva : mp.getD a (Sum.inl false) <;> rw [hva] at hopt <;>
            cases hvb : mp.getD b (Sum.inl false) <;> rw [hvb] at hopt <;>
            dsimp only at hopt
          · cases hopt
          · cases hopt
          · cases hopt
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hopt
            subst hopt; exact ⟨by simp, by simp⟩
        · cases hopt
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
          dsimp only [compileList, compileBin] at hopt
        · cases hopt
        · cases hopt
        · cases hva : mp.getD a (Sum.inl false) <;> rw [hva] at hopt <;>
            cases hvb : mp.getD b (Sum.inl false) <;> rw [hvb] at hopt <;>
            dsimp only at hopt
          · cases hopt
          · cases hopt
          · cases hopt
          · simp only [↓reduceIte, Option.some.injEq] at hopt
            subst hopt; exact ⟨by simp, by simp⟩
        · cases hopt
      · cases hopt
      · cases hopt
      · cases hopt
    have compileOne_ok : ∀ (nextIdx : ℕ) (mp : List V) (g : Gate)
        (orig cur : List Bool),
        g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
        g.inputs.length ≤ 2 →
        cur.length = nextIdx →
        mp.length = orig.length →
        (∀ k, orig.getD k false = evalVal cur (mp.getD k (Sum.inl false))) →
        (∀ k i, mp.getD k (Sum.inl false) = Sum.inr i → i < cur.length) →
        let res := compileOne nextIdx mp g
        let cur' := Option.casesOn res.1 cur (step cur)
        (cur'.length = Option.casesOn res.1 cur.length (fun _ => cur.length + 1)) ∧
        (∀ k, (step orig g).getD k false = evalVal cur' ((mp ++ [res.2]).getD k (Sum.inl false))) ∧
        (∀ k i, (mp ++ [res.2]).getD k (Sum.inl false) = Sum.inr i → i < cur'.length) := by
      intro nextIdx mp g orig cur hgop hglen hcur hmp heval hbd
      have step_none : ∀ (outV : V),
          g.op.eval (g.inputs.map fun i => orig.getD i false) = evalVal cur outV →
          (∀ k, (step orig g).getD k false = evalVal cur ((mp ++ [outV]).getD k (Sum.inl false))) ∧
          ((∀ i, outV = Sum.inr i → i < cur.length) →
            ∀ k i, (mp ++ [outV]).getD k (Sum.inl false) = Sum.inr i → i < cur.length) := by
        intro outV hout
        refine ⟨fun k => ?_, fun houtBd k i hi => ?_⟩
        · by_cases hk : k < orig.length
          · have hk' : k < mp.length := hmp ▸ hk
            dsimp only [step]
            rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk']
            exact heval k
          · by_cases hkeq : k = orig.length
            · subst hkeq
              dsimp only [step]
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              rw [List.getD_append_right _ _ _ _ (by omega), hmp, Nat.sub_self]
              exact hout
            · have hk1 : (step orig g).length ≤ k := by simp [step]; omega
              have hk2 : (mp ++ [outV]).length ≤ k := by simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk1]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk2]
              rfl
        · by_cases hk : k < mp.length
          · rw [List.getD_append _ _ _ _ hk] at hi
            exact hbd k i hi
          · by_cases hkeq : k = mp.length
            · subst hkeq
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self] at hi
              exact houtBd i hi
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
              cases hi
      have step_some : ∀ (g' : Gate),
          g.op.eval (g.inputs.map fun i => orig.getD i false) =
            g'.op.eval (g'.inputs.map fun i => cur.getD i false) →
          (∀ k, (step orig g).getD k false =
            evalVal (step cur g') ((mp ++ [Sum.inr nextIdx]).getD k (Sum.inl false))) ∧
          (∀ k i, (mp ++ [Sum.inr nextIdx]).getD k (Sum.inl false) = Sum.inr i →
            i < (step cur g').length) := by
        intro g' hout
        refine ⟨fun k => ?_, fun k i hi => ?_⟩
        · by_cases hk : k < orig.length
          · have hk' : k < mp.length := hmp ▸ hk
            dsimp only [step]
            rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk']
            have h0 := heval k
            cases hmk : mp.getD k (Sum.inl false) with
            | inl b =>
              rw [hmk] at h0
              exact h0
            | inr idx =>
              have hidx : idx < cur.length := hbd k idx hmk
              rw [hmk] at h0
              dsimp only [evalVal] at h0 ⊢
              rw [List.getD_append _ _ _ _ hidx]
              exact h0
          · by_cases hkeq : k = orig.length
            · subst hkeq
              dsimp only [step]
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              rw [List.getD_append_right _ _ _ _ (by omega), hmp, Nat.sub_self]
              rw [show ([Sum.inr nextIdx] : List V).getD 0 (Sum.inl false) = Sum.inr nextIdx from rfl]
              dsimp only [evalVal]
              rw [List.getD_append_right _ _ _ _ (by omega), hcur, Nat.sub_self]
              exact hout
            · have hk1 : (step orig g).length ≤ k := by simp [step]; omega
              have hk2 : (mp ++ [Sum.inr nextIdx]).length ≤ k := by simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk1]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk2]
              rfl
        · by_cases hk : k < mp.length
          · rw [List.getD_append _ _ _ _ hk] at hi
            have hidx := hbd k i hi
            simp [step]; omega
          · by_cases hkeq : k = mp.length
            · subst hkeq
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self] at hi
              cases hi
              simp [step, hcur]
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
              cases hi
      have hg' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgop
      rcases g with ⟨op, ins⟩
      dsimp only at hg' hglen
      rcases hg' with rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · have hs := step_none (Sum.inl true) rfl
          exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
        · have h1 : GateOp.and.eval ([a].map fun i => orig.getD i false) =
              evalVal cur (mp.getD a (Sum.inl false)) := by
            dsimp only [List.map, GateOp.eval]
            rw [heval a]
            simp
          have hs := step_none (mp.getD a (Sum.inl false)) h1
          exact ⟨rfl, hs.1, hs.2 (fun i hi => hbd a i hi)⟩
        · dsimp only [compileOne, compileList, compileBin]
          have ha' := heval a
          have hb' := heval b
          cases hva : mp.getD a (Sum.inl false) with
          | inl ba =>
            rw [hva] at ha'
            cases hvb : mp.getD b (Sum.inl false) with
            | inl bb =>
              rw [hvb] at hb'
              have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                  evalVal cur (Sum.inl (ba && bb)) := by
                dsimp only [List.map, GateOp.eval]
                rw [ha', hb']
                dsimp only [evalVal]
                simp
              have hs := step_none (Sum.inl (ba && bb)) h1
              exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
            | inr ib =>
              rw [hvb] at hb'
              cases ba
              · have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inl false) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inl false) h1
                exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
              · have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inr ib) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha', hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inr ib) h1
                exact ⟨rfl, hs.1, hs.2 (fun i hi => by cases hi; exact hbd b _ hvb)⟩
          | inr ia =>
            rw [hva] at ha'
            cases hvb : mp.getD b (Sum.inl false) with
            | inl bb =>
              rw [hvb] at hb'
              cases bb
              · have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inl false) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inl false) h1
                exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
              · have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inr ia) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha', hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inr ia) h1
                exact ⟨rfl, hs.1, hs.2 (fun i hi => by cases hi; exact hbd a _ hva)⟩
            | inr ib =>
              rw [hvb] at hb'
              have h1 : GateOp.and.eval ([a, b].map fun i => orig.getD i false) =
                  GateOp.and.eval ([ia, ib].map fun i => cur.getD i false) := by
                dsimp only [List.map, GateOp.eval]
                rw [ha', hb']
              have hs := step_some ⟨GateOp.and, [ia, ib]⟩ h1
              exact ⟨by simp [step], hs.1, hs.2⟩
        · simp at hglen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · have hs := step_none (Sum.inl false) rfl
          exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
        · have h1 : GateOp.or.eval ([a].map fun i => orig.getD i false) =
              evalVal cur (mp.getD a (Sum.inl false)) := by
            dsimp only [List.map, GateOp.eval]
            rw [heval a]
            simp
          have hs := step_none (mp.getD a (Sum.inl false)) h1
          exact ⟨rfl, hs.1, hs.2 (fun i hi => hbd a i hi)⟩
        · dsimp only [compileOne, compileList, compileBin]
          have ha' := heval a
          have hb' := heval b
          cases hva : mp.getD a (Sum.inl false) with
          | inl ba =>
            rw [hva] at ha'
            cases hvb : mp.getD b (Sum.inl false) with
            | inl bb =>
              rw [hvb] at hb'
              have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                  evalVal cur (Sum.inl (ba || bb)) := by
                dsimp only [List.map, GateOp.eval]
                rw [ha', hb']
                dsimp only [evalVal]
                simp
              have hs := step_none (Sum.inl (ba || bb)) h1
              exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
            | inr ib =>
              rw [hvb] at hb'
              cases ba
              · have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inr ib) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha', hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inr ib) h1
                exact ⟨rfl, hs.1, hs.2 (fun i hi => by cases hi; exact hbd b _ hvb)⟩
              · have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inl true) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inl true) h1
                exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
          | inr ia =>
            rw [hva] at ha'
            cases hvb : mp.getD b (Sum.inl false) with
            | inl bb =>
              rw [hvb] at hb'
              cases bb
              · have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inr ia) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [ha', hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inr ia) h1
                exact ⟨rfl, hs.1, hs.2 (fun i hi => by cases hi; exact hbd a _ hva)⟩
              · have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                    evalVal cur (Sum.inl true) := by
                  dsimp only [List.map, GateOp.eval]
                  rw [hb']
                  dsimp only [evalVal]
                  simp
                have hs := step_none (Sum.inl true) h1
                exact ⟨rfl, hs.1, hs.2 (fun _ h => by cases h)⟩
            | inr ib =>
              rw [hvb] at hb'
              have h1 : GateOp.or.eval ([a, b].map fun i => orig.getD i false) =
                  GateOp.or.eval ([ia, ib].map fun i => cur.getD i false) := by
                dsimp only [List.map, GateOp.eval]
                rw [ha', hb']
              have hs := step_some ⟨GateOp.or, [ia, ib]⟩ h1
              exact ⟨by simp [step], hs.1, hs.2⟩
        · simp at hglen
    let stepComp : List Gate × List V → Gate → List Gate × List V := fun acc g =>
      let res := compileOne (11 + x2.size + acc.1.length) acc.2 g
      Option.casesOn res.1 (acc.1, acc.2 ++ [res.2]) (fun g' => (acc.1 ++ [g'], acc.2 ++ [res.2]))
    have runComp : ∀ (rem : List Gate) (tail : List Gate) (mp : List V),
        (∀ g ∈ rem, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        ∃ ext : List Gate,
          (rem.foldl stepComp (tail, mp)).1 = tail ++ ext ∧
          ext.length ≤ rem.length ∧
          (∀ g ∈ ext, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          ∀ (orig cur : List Bool),
            cur.length = 11 + x2.size + tail.length →
            mp.length = orig.length →
            (∀ k, orig.getD k false = evalVal cur (mp.getD k (Sum.inl false))) →
            (∀ k i, mp.getD k (Sum.inl false) = Sum.inr i → i < cur.length) →
            ∀ k, (rem.foldl step orig).getD k false =
              evalVal (ext.foldl step cur) ((rem.foldl stepComp (tail, mp)).2.getD k (Sum.inl false)) := by
      intro rem
      induction rem with
      | nil =>
        intro tail mp _
        refine ⟨[], by simp, by simp, fun _ h => by simp at h, fun orig cur _ _ heval _ k => heval k⟩
      | cons g rem ih =>
        intro tail mp hm
        have hg := hm g (by simp)
        have hrem : ∀ a ∈ rem, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
          fun a ha => hm a (List.mem_cons_of_mem _ ha)
        cases hopt : (compileOne (11 + x2.size + tail.length) mp g).1 with
        | none =>
          have hst : stepComp (tail, mp) g =
              (tail, mp ++ [(compileOne (11 + x2.size + tail.length) mp g).2]) := by
            dsimp only [stepComp]; rw [hopt]
          rw [List.foldl_cons, hst]
          obtain ⟨ext, hextEq, hextLen, hextM, hextEval⟩ :=
            ih tail (mp ++ [(compileOne (11 + x2.size + tail.length) mp g).2]) hrem
          refine ⟨ext, hextEq, by dsimp only [List.length_cons]; omega, hextM,
            fun orig cur hcur hmp heval hbd k => ?_⟩
          have ok := compileOne_ok (11 + x2.size + tail.length) mp g orig cur hg.1 hg.2 hcur hmp heval hbd
          dsimp only at ok
          rw [hopt] at ok
          dsimp only at ok
          rw [List.foldl_cons]
          exact hextEval (step orig g) cur hcur (by simp [step, hmp]) ok.2.1 ok.2.2 k
        | some g' =>
          have hst : stepComp (tail, mp) g =
              (tail ++ [g'], mp ++ [(compileOne (11 + x2.size + tail.length) mp g).2]) := by
            dsimp only [stepComp]; rw [hopt]
          rw [List.foldl_cons, hst]
          obtain ⟨ext, hextEq, hextLen, hextM, hextEval⟩ :=
            ih (tail ++ [g']) (mp ++ [(compileOne (11 + x2.size + tail.length) mp g).2]) hrem
          refine ⟨g' :: ext, ?_, by simp; omega, fun a ha => ?_,
            fun orig cur hcur hmp heval hbd k => ?_⟩
          · rw [hextEq]; simp [List.append_assoc]
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact compileOne_mono (11 + x2.size + tail.length) mp g a hopt
            · exact hextM a ha
          · have ok := compileOne_ok (11 + x2.size + tail.length) mp g orig cur hg.1 hg.2 hcur hmp heval hbd
            dsimp only at ok
            rw [hopt] at ok
            dsimp only at ok
            rw [List.foldl_cons, List.foldl_cons]
            exact hextEval (step orig g) (step cur g')
              (by rw [ok.1, hcur]; simp only [List.length_append, List.length_singleton]; omega)
              (by simp [step, hmp]) ok.2.1 ok.2.2 k
    let mp₀ : List V := (List.range (11 + x2.size)).map Sum.inr ++ [Sum.inl true]
    obtain ⟨ext, _, hextLen, hextM, hextEval⟩ :=
      runComp x3.gates [] mp₀ (fun g hg => hm3 g hg)
    let res := x3.gates.foldl stepComp ([], mp₀)
    have hEvalAll : ∀ x : Fin 9 → Bool,
        evalVal (ext.foldl step (x2.wires (baseOf x1 x))) (res.2.getD x3.output (Sum.inl false)) = edge x := by
      intro x
      have hcur0 : (x2.wires (baseOf x1 x)).length = 11 + x2.size := by
        change (x2.gates.foldl step (baseOf x1 x)).length = 11 + x2.gates.length
        rw [wires_len, base_len]
      have hmp0 : mp₀.length = (x2.wires (baseOf x1 x) ++ [true]).length := by
        simp [mp₀, hcur0]
      have hev0 : ∀ k, (x2.wires (baseOf x1 x) ++ [true]).getD k false =
          evalVal (x2.wires (baseOf x1 x)) (mp₀.getD k (Sum.inl false)) := by
        intro k
        by_cases hk : k < 11 + x2.size
        · rw [List.getD_append _ _ _ _ (by omega)]
          dsimp only [mp₀]
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          simp [hk, evalVal]
        · by_cases hkeq : k = 11 + x2.size
          · subst hkeq
            rw [List.getD_append_right _ _ _ _ (by omega), hcur0, Nat.sub_self]
            dsimp only [mp₀]
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp [evalVal]
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hcur0]; omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mp₀]; omega)]
            rfl
      have hbd0 : ∀ k i, mp₀.getD k (Sum.inl false) = Sum.inr i → i < (x2.wires (baseOf x1 x)).length := by
        intro k i hi
        by_cases hk : k < 11 + x2.size
        · dsimp only [mp₀] at hi
          rw [List.getD_append _ _ _ _ (by simp; omega)] at hi
          simp [hk] at hi
          cases hi
          rw [hcur0]; omega
        · by_cases hkeq : k = 11 + x2.size
          · subst hkeq
            dsimp only [mp₀] at hi
            rw [List.getD_append_right _ _ _ _ (by simp)] at hi
            simp at hi
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [mp₀]; omega)] at hi
            cases hi
      have hfinal := hextEval (x2.wires (baseOf x1 x) ++ [true]) (x2.wires (baseOf x1 x))
        hcur0 hmp0 hev0 hbd0 x3.output
      rw [← hfinal]
      exact heq x
    cases hout : res.2.getD x3.output (Sum.inl false) with
    | inl b =>
      cases b
      · have h0 := hEvalAll (fun i => decide (i = 0 ∨ i = 1))
        rw [hout] at h0
        dsimp only [evalVal] at h0
        have hed : edge (fun i : Fin 9 => decide (i = 0 ∨ i = 1)) = true := by decide
        exact Bool.false_ne_true (h0.trans hed)
      · have h0 := hEvalAll (fun _ => false)
        rw [hout] at h0
        dsimp only [evalVal] at h0
        have hed : edge (fun _ : Fin 9 => false) = false := by decide
        exact Bool.false_ne_true (h0.trans hed).symm
    | inr outIdx =>
      let C : Circuit := ⟨x2.gates ++ ext, outIdx⟩
      have hmC : Monotone2 C := by
        intro g hg
        rcases List.mem_append.mp hg with hg2 | hgE
        · exact hm2 g hg2
        · exact hextM g hgE
      have hszC : C.size ≤ 12 := by
        change (x2.gates ++ ext).length ≤ 12
        rw [List.length_append]
        change x2.gates.length + x3.gates.length ≤ 12 at hsz
        omega
      obtain ⟨x, hxBad⟩ := monotoneOnly x1 C hcard hmC hszC
      apply hxBad
      have hCeq : C.eval (baseOf x1 x) = evalVal (ext.foldl step (x2.wires (baseOf x1 x))) (Sum.inr outIdx) := by
        dsimp only [Circuit.eval, Circuit.wires, C, evalVal]
        rw [wires_append]
      have hEvalX := hEvalAll x
      rw [hout] at hEvalX
      exact hCeq.trans hEvalX
  cases x4 with
  | none =>
    simpa [baseOf, edge] using constTrueCase
  | some p =>
    by_cases hp1 : p < 11
    · let shiftX2 : ℕ → ℕ := fun i => if i < 11 then i else i + 1
      let toNew : ℕ → ℕ := fun i =>
        if i < 11 then i else if i < 11 + x2.size then i + 1 else if i = 11 + x2.size then 11 else i
      let r2 : Gate → Gate := fun g => ⟨g.op, g.inputs.map shiftX2⟩
      let r3 : Gate → Gate := fun g => ⟨g.op, g.inputs.map toNew⟩
      let C : Circuit := ⟨x2.gates.map r2 ++ x3.gates.map r3, toNew x3.output⟩
      have hmC : Monotone2 C := by
        intro g hg
        rcases List.mem_append.mp hg with hg2 | hg3
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg2
          exact ⟨(hm2 a ha).1, by simpa [r2] using (hm2 a ha).2⟩
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg3
          exact ⟨(hm3 a ha).1, by simpa [r3] using (hm3 a ha).2⟩
      have hszC : C.size ≤ 12 := by
        change (x2.gates.map r2 ++ x3.gates.map r3).length ≤ 12
        rw [List.length_append, List.length_map, List.length_map]
        exact hsz
      obtain ⟨x, hxBad⟩ := baseNot x1 C ⟨p, hp1⟩ hcard hmC hszC
      refine ⟨x, ?_⟩
      change x3.eval (x2.wires (baseOf x1 x) ++ [!((x2.wires (baseOf x1 x)).getD p false)]) ≠ edge x
      let nbit : Bool := !((baseOf x1 x).getD p false)
      have hnbit : (!((x2.wires (baseOf x1 x)).getD p false)) = nbit := by
        dsimp only [Circuit.wires]
        rw [wires_prefix _ _ _ (by rw [base_len]; exact hp1)]
      rw [hnbit]
      have rel2 : ∀ (gs : List Gate) (u v : List Bool),
          u.length + 1 = v.length → 11 ≤ u.length →
          (∀ i, u.getD i false = v.getD (shiftX2 i) false) →
          ∀ i, (gs.foldl step u).getD i false = ((gs.map r2).foldl step v).getD (shiftX2 i) false := by
        intro gs
        induction gs with
        | nil => intro u v _ _ h i; exact h i
        | cons g gs ih =>
          intro u v hlen hu h
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          apply ih
          · simp [step]; omega
          · simp [step]; omega
          · intro i
            have hpin : g.inputs.map (fun j => u.getD j false) =
                (g.inputs.map shiftX2).map (fun j => v.getD j false) := by
              simp only [List.map_map]
              exact List.map_congr_left fun j _ => h j
            let z := g.op.eval (g.inputs.map fun j => u.getD j false)
            dsimp only [step, r2]
            rw [← hpin]
            change (u ++ [z]).getD i false = (v ++ [z]).getD (shiftX2 i) false
            by_cases hi11 : i < 11
            · simp only [shiftX2, hi11, ↓reduceIte]
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              simpa [shiftX2, hi11] using h i
            · simp only [shiftX2, hi11, ↓reduceIte]
              by_cases hil : i < u.length
              · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
                simpa [shiftX2, hi11] using h i
              · by_cases hieq : i = u.length
                · subst hieq
                  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
                  rw [List.getD_append_right _ _ _ _ (by omega), show u.length + 1 - v.length = 0 by omega]
                · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have rel3 : ∀ (gs : List Gate) (u v : List Bool),
          u.length = v.length → 12 + x2.size ≤ u.length →
          (∀ i, u.getD i false = v.getD (toNew i) false) →
          ∀ i, (gs.foldl step u).getD i false = ((gs.map r3).foldl step v).getD (toNew i) false := by
        intro gs
        induction gs with
        | nil => intro u v _ _ h i; exact h i
        | cons g gs ih =>
          intro u v hlen hu h
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          apply ih
          · simp [step, hlen]
          · simp [step]; omega
          · intro i
            have hpin : g.inputs.map (fun j => u.getD j false) =
                (g.inputs.map toNew).map (fun j => v.getD j false) := by
              simp only [List.map_map]
              exact List.map_congr_left fun j _ => h j
            let z := g.op.eval (g.inputs.map fun j => u.getD j false)
            dsimp only [step, r3]
            rw [← hpin]
            change (u ++ [z]).getD i false = (v ++ [z]).getD (toNew i) false
            by_cases hi : i < u.length
            · have hto : toNew i < v.length := by dsimp [toNew]; split_ifs <;> omega
              rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hto]
              exact h i
            · by_cases hieq : i = u.length
              · subst hieq
                have hto : toNew u.length = u.length := by dsimp [toNew]; split_ifs <;> omega
                rw [hto, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
                rw [List.getD_append_right _ _ _ _ (by omega), ← hlen, Nat.sub_self]
              · have hto : toNew i = i := by dsimp [toNew]; split_ifs <;> omega
                rw [hto, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have hInit2 : ∀ i, (baseOf x1 x).getD i false =
          (baseOf x1 x ++ [nbit]).getD (shiftX2 i) false := by
        intro i
        have hbl : (baseOf x1 x).length = 11 := base_len x1 x
        by_cases hi : i < 11
        · simp only [shiftX2, hi, ↓reduceIte]
          rw [List.getD_append _ [nbit] _ _ (by rw [hbl]; exact hi)]
        · simp only [shiftX2, hi, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hbl]; omega)]
      have hMid2 : ∀ i, (x2.wires (baseOf x1 x)).getD i false =
          ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit])).getD (shiftX2 i) false :=
        rel2 x2.gates (baseOf x1 x) (baseOf x1 x ++ [nbit])
          (by simp [base_len]) (by simp [base_len]) hInit2
      have hv11 : ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit])).getD 11 false = nbit := by
        have hbl : (baseOf x1 x).length = 11 := base_len x1 x
        rw [wires_prefix _ _ _ (by simp [hbl])]
        rw [List.getD_append_right _ _ _ _ (by omega), hbl, Nat.sub_self]
        rfl
      have hwLen : (x2.wires (baseOf x1 x)).length = 11 + x2.size := by
        change (x2.gates.foldl step (baseOf x1 x)).length = 11 + x2.gates.length; rw [wires_len, base_len]
      have huLen : (x2.wires (baseOf x1 x) ++ [nbit]).length = 12 + x2.size := by
        simp [hwLen]; omega
      have hvLen : ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit])).length = 12 + x2.size := by
        change ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit])).length = 12 + x2.gates.length
        rw [wires_len]; simp [base_len]
      have hMid3 : ∀ i, (x2.wires (baseOf x1 x) ++ [nbit]).getD i false =
          ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit])).getD (toNew i) false := by
        intro i
        by_cases hi11 : i < 11
        · have hto : toNew i = i := by simp [toNew, hi11]
          rw [hto, List.getD_append _ [nbit] _ _ (by rw [hwLen]; omega)]
          simpa [shiftX2, hi11] using hMid2 i
        · by_cases hi2 : i < 11 + x2.size
          · have hto : toNew i = i + 1 := by simp [toNew, hi11, hi2]
            rw [hto, List.getD_append _ [nbit] _ _ (by rw [hwLen]; exact hi2)]
            simpa [shiftX2, hi11] using hMid2 i
          · by_cases hieq : i = 11 + x2.size
            · subst hieq
              have hto : toNew (11 + x2.size) = 11 := by simp [toNew]
              rw [hto, hv11]
              rw [List.getD_append_right _ [nbit] _ _ (by rw [hwLen]), hwLen, Nat.sub_self]
              rfl
            · have hto : toNew i = i := by simp [toNew, hi11, hi2, hieq]
              rw [hto, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hwLen]; omega)]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hvLen]; omega)]
      have hFin := rel3 x3.gates (x2.wires (baseOf x1 x) ++ [nbit])
        ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit]))
        (huLen.trans hvLen.symm) (by omega) hMid3 x3.output
      have hCeval : C.eval (baseOf x1 x ++ [nbit]) =
          ((x3.gates.map r3).foldl step ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit]))).getD (toNew x3.output) false := by
        dsimp only [Circuit.eval, Circuit.wires, C]
        rw [wires_append]
      have hx3eval : x3.eval (x2.wires (baseOf x1 x) ++ [nbit]) = C.eval (baseOf x1 x ++ [nbit]) := by
        calc x3.eval (x2.wires (baseOf x1 x) ++ [nbit])
          _ = ((x3.gates.map r3).foldl step ((x2.gates.map r2).foldl step (baseOf x1 x ++ [nbit]))).getD (toNew x3.output) false := hFin
          _ = C.eval (baseOf x1 x ++ [nbit]) := hCeval.symm
      rw [hx3eval]
      exact hxBad
    · by_cases hp2 : p < 11 + x2.size
      · have hp11 : 11 ≤ p := Nat.le_of_not_lt hp1
        let flip : Fin 9 → Fin 9 := fun i => ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List (Fin 9)).getD i.val 0
        let move : ℕ → ℕ := fun i => if h : i < 9 then (flip ⟨i, h⟩).val else i
        have small : ∀ i, i < 9 → move i < 9 := fun i hi => by
          rw [show move i = (flip ⟨i, hi⟩).val from dite_eq_left hi]
          exact (flip ⟨i, hi⟩).isLt
        have high : ∀ i, 9 ≤ i → move i = i := fun i hi => dite_eq_right (by omega)
        have flip0 : flip 0 = 0 := rfl
        have flip4 : flip 4 = 4 := rfl
        have preserve : ∀ x : Fin 9 → Bool, edge (x ∘ flip) = edge x := by decide +kernel
        have flipCase : ∀ (S' : Finset (Fin 9))
            (hS' : S' = x1.image flip)
            (sub : ∃ x : Fin 9 → Bool,
              let w := (⟨x2.gates.map (fun g => ⟨g.op, g.inputs.map move⟩), move x2.output⟩ : Circuit).wires (baseOf S' x);
              (⟨x3.gates.map (fun g => ⟨g.op, g.inputs.map move⟩), move x3.output⟩ : Circuit).eval (w ++ [!(w.getD p false)]) ≠ edge x),
            ∃ x : Fin 9 → Bool,
              let w := x2.wires (baseOf x1 x);
              x3.eval (w ++ [!(w.getD p false)]) ≠ edge x := by
          intro S' hS' sub
          obtain ⟨x, hxBad⟩ := sub
          refine ⟨x ∘ flip, ?_⟩
          let relabel : Gate → Gate := fun g => ⟨g.op, g.inputs.map move⟩
          let sameWires : List Bool → List Bool → Prop := fun u v =>
            u.length = v.length ∧ 9 ≤ u.length ∧ ∀ i, u.getD i false = v.getD (move i) false
          have stable : ∀ u v b, sameWires u v → sameWires (u ++ [b]) (v ++ [b]) := by
            intro u v b h
            have hl := h.1
            have hu := h.2.1
            have hs := h.2.2
            refine ⟨by simp [hl], by simp; omega, fun i => ?_⟩
            by_cases raw : i < 9
            · rw [List.getD_append _ _ _ _ (by omega),
                  List.getD_append _ _ _ _ (by have := small i raw; omega)]
              exact hs i
            · rw [high i (by omega)]
              by_cases inside : i < u.length
              · rw [List.getD_append _ _ _ _ inside, List.getD_append _ _ _ _ (by omega)]
                simpa [high i (by omega)] using hs i
              · rw [List.getD_append_right _ _ _ _ (by omega),
                    List.getD_append_right _ _ _ _ (by omega), hl]
          have run : ∀ (gs : List Gate) (u v : List Bool), sameWires u v →
              sameWires (gs.foldl step u) ((gs.map relabel).foldl step v) := by
            intro gs
            induction gs with
            | nil => intro u v h; exact h
            | cons g gs ih =>
              intro u v h
              rw [List.map_cons, List.foldl_cons, List.foldl_cons]
              apply ih
              have pins : g.inputs.map (fun i => u.getD i false) =
                  (relabel g).inputs.map (fun i => v.getD i false) := by
                simp only [relabel, List.map_map]
                exact List.map_congr_left fun i _ => h.2.2 i
              change sameWires (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
                (v ++ [g.op.eval ((relabel g).inputs.map fun i => v.getD i false)])
              rw [← pins]
              exact stable _ _ _ h
          have reflectBits : decide (∃ i ∈ x1, (x ∘ flip) i = true) = decide (∃ i ∈ S', x i = true) := by
            subst hS'
            apply Bool.decide_congr
            constructor
            · rintro ⟨i, hi, hx⟩; exact ⟨flip i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hx⟩
            · rintro ⟨j, hj, hx⟩
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
              exact ⟨i, hi, hx⟩
          have hbase : sameWires (baseOf x1 (x ∘ flip)) (baseOf S' x) := by
            refine ⟨by simp [base_len], by simp [base_len], fun i => ?_⟩
            by_cases raw : i < 9
            · have lookup (y : Fin 9 → Bool) (j : Fin 9) : (List.ofFn y).getD j.val false = y j := by
                rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
              change (List.ofFn (x ∘ flip) ++ _).getD i false = (List.ofFn x ++ _).getD (move i) false
              rw [List.getD_append _ _ _ _ (by simpa using raw),
                  List.getD_append _ _ _ _ (by have := small i raw; simpa using this),
                  show move i = (flip ⟨i, raw⟩).val from dite_eq_left raw]
              exact (lookup (x ∘ flip) ⟨i, raw⟩).trans (lookup x (flip ⟨i, raw⟩)).symm
            · rw [high i (by omega)]
              have firstEq : ((x ∘ flip) 0 || (x ∘ flip) 4) = (x 0 || x 4) := by
                simp only [Function.comp_apply, flip0, flip4]
              change (List.ofFn (x ∘ flip) ++ [_, _]).getD i false =
                (List.ofFn x ++ [_, _]).getD i false
              rw [List.getD_append_right _ _ _ _ (by simp; omega),
                  List.getD_append_right _ _ _ _ (by simp; omega),
                  List.length_ofFn, List.length_ofFn, firstEq, reflectBits]
          have hs2 := run x2.gates (baseOf x1 (x ∘ flip)) (baseOf S' x) hbase
          have hpEq : (x2.wires (baseOf x1 (x ∘ flip))).getD p false =
              ((⟨x2.gates.map relabel, move x2.output⟩ : Circuit).wires (baseOf S' x)).getD p false := by
            have hp := hs2.2.2 p
            rw [high p (by omega)] at hp
            exact hp
          have hs3 := run x3.gates _ _ (stable _ _ (!((x2.wires (baseOf x1 (x ∘ flip))).getD p false)) hs2)
          have hevalEq : x3.eval (x2.wires (baseOf x1 (x ∘ flip)) ++ [!((x2.wires (baseOf x1 (x ∘ flip))).getD p false)]) =
              (⟨x3.gates.map relabel, move x3.output⟩ : Circuit).eval ((⟨x2.gates.map relabel, move x2.output⟩ : Circuit).wires (baseOf S' x) ++ [!(((⟨x2.gates.map relabel, move x2.output⟩ : Circuit).wires (baseOf S' x)).getD p false)]) := by
            have h0 := hs3.2.2 x3.output
            change x3.eval (x2.wires (baseOf x1 (x ∘ flip)) ++ [!((x2.wires (baseOf x1 (x ∘ flip))).getD p false)]) =
              (⟨x3.gates.map relabel, move x3.output⟩ : Circuit).eval ((⟨x2.gates.map relabel, move x2.output⟩ : Circuit).wires (baseOf S' x) ++ [!((x2.wires (baseOf x1 (x ∘ flip))).getD p false)]) at h0
            rw [h0, hpEq]
          dsimp only
          rw [hevalEq, preserve x]
          exact hxBad
        have mapMono : ∀ C' : Circuit, Monotone2 C' → Monotone2 ⟨C'.gates.map (fun g => ⟨g.op, g.inputs.map move⟩), move C'.output⟩ := by
          intro C' hC' g hg
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
          exact ⟨(hC' a ha).1, by simpa using (hC' a ha).2⟩
        have mapSz : ∀ C' : Circuit, (⟨C'.gates.map (fun g => ⟨g.op, g.inputs.map move⟩), move C'.output⟩ : Circuit).size = C'.size :=
          fun C' => List.length_map _
        let aliases : List ℕ := [0, 1, 2, 3, 4, 6]
        let pairs : List ℕ := [1, 2, 12, 3, 13, 23, 14, 24, 34, 15, 25, 6, 16, 26, 36, 46, 56, 27, 67, 28]
        rcases Nat.lt_or_eq_of_le hcard with hlt1 | h2
        · have hle1 : x1.card ≤ 1 := by omega
          rcases Finset.card_le_one_iff_subset_singleton.mp hle1 with ⟨a, ha⟩
          by_cases he : x1 = ∅
          · exact gateNotAliases x1 x2 x3 p (Or.inl he) hm2 hm3 hsz hp11 hp2
          · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr he
            have hbx : x1 = {b} := by
              apply Finset.eq_singleton_iff_unique_mem.mpr
              have hba : b = a := Finset.mem_singleton.mp (ha hb)
              exact ⟨hb, fun y hy => (Finset.mem_singleton.mp (ha hy)).trans hba.symm⟩
            by_cases hmem : b.val ∈ aliases
            · exact gateNotAliases x1 x2 x3 p (Or.inr (Or.inr ⟨b, hmem, hbx⟩)) hm2 hm3 hsz hp11 hp2
            · have hfmem : (flip b).val ∈ aliases := by
                fin_cases b <;> simp [aliases] at hmem ⊢ <;> decide
              apply flipCase {flip b} (by rw [hbx, Finset.image_singleton])
              exact gateNotAliases {flip b} _ _ p (Or.inr (Or.inr ⟨flip b, hfmem, rfl⟩))
                (mapMono x2 hm2) (mapMono x3 hm3) (by simpa [mapSz] using hsz) hp11 (by simpa [mapSz] using hp2)
        · obtain ⟨a, b, hab, hx1⟩ := Finset.card_eq_two.mp h2
          have hpair : ∀ a b : Fin 9, a < b → x1 = {a, b} →
              ∃ x : Fin 9 → Bool,
                let w := x2.wires (baseOf x1 x);
                x3.eval (w ++ [!(w.getD p false)]) ≠ edge x := by
            intro a b hlt hxab
            subst hxab
            by_cases h04 : a.val = 0 ∧ b.val = 4
            · have hx04 : ({a, b} : Finset (Fin 9)) = {0, 4} := by
                have ha0 : a = 0 := Fin.ext h04.1
                have hb4 : b = 4 := Fin.ext h04.2
                subst ha0; subst hb4; rfl
              exact gateNotAliases {a, b} x2 x3 p (Or.inr (Or.inl hx04)) hm2 hm3 hsz hp11 hp2
            · by_cases hpMem : a.val * 10 + b.val ∈ pairs
              · exact gateNotPairs {a, b} x2 x3 p ⟨a, b, hpMem, hlt, rfl⟩ hm2 hm3 hsz hp11 hp2
              · have hflipPair : ∀ a b : Fin 9, a < b → ¬(a.val = 0 ∧ b.val = 4) →
                    a.val * 10 + b.val ∉ pairs →
                    ((flip a < flip b ∧ (flip a).val * 10 + (flip b).val ∈ pairs) ∨
                     (flip b < flip a ∧ (flip b).val * 10 + (flip a).val ∈ pairs)) := by decide
                rcases hflipPair a b hlt h04 hpMem with ⟨hfl, hfm⟩ | ⟨hfl, hfm⟩
                · apply flipCase {flip a, flip b} (by simp [Finset.image_insert])
                  exact gateNotPairs {flip a, flip b} _ _ p ⟨flip a, flip b, hfm, hfl, rfl⟩
                    (mapMono x2 hm2) (mapMono x3 hm3) (by simpa [mapSz] using hsz) hp11 (by simpa [mapSz] using hp2)
                · apply flipCase {flip b, flip a} (by simp [Finset.image_insert, Finset.pair_comm])
                  exact gateNotPairs {flip b, flip a} _ _ p ⟨flip b, flip a, hfm, hfl, rfl⟩
                    (mapMono x2 hm2) (mapMono x3 hm3) (by simpa [mapSz] using hsz) hp11 (by simpa [mapSz] using hp2)
          rcases lt_trichotomy a b with hlt | heq | hgt
          · exact hpair a b hlt hx1
          · exact False.elim (hab heq)
          · exact hpair b a hgt (hx1.trans (Finset.pair_comm a b))
      · obtain ⟨x, hxBad⟩ := constTrueCase
        refine ⟨x, ?_⟩
        have hl : (x2.wires (baseOf x1 x)).length ≤ p := by
          dsimp only [Circuit.wires]
          change ¬ p < 11 + x2.gates.length at hp2
          rw [wires_len, base_len]
          omega
        have hnone : (x2.wires (baseOf x1 x)).getD p false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]; rfl
        change x3.eval (x2.wires (baseOf x1 x) ++ [!((x2.wires (baseOf x1 x)).getD p false)]) ≠ edge x
        rw [hnone]
        exact hxBad