/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Algorithms.DiscreteLog
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fintype

/-!
# Generic Group Lower Bound for the Discrete Logarithm

Computing a discrete logarithm costs `Ω(√|G|)` group operations, if the group is only available
through its operations. This is Shoup's bound, derandomised: instead of a random encoding, the
group is *chosen after the algorithm*. See `Algolean.Models.GenericGroup` for why that quantifier
ordering, rather than any syntactic genericity hypothesis, is what makes the bound meaningful.

The bound is not vacuous: `Algolean.Algorithms.bruteForceDLog` satisfies `SolvesDLog`
(`solvesDLog_bruteForceDLog`), and so does baby-step giant-step.

## The proof

Fix a large prime `p` and take the carrier `Lbl p`, a type synonym for `ZMod p` carrying *no*
group structure. Run the algorithm on the two fixed labels `g := lblG p` and `H := lblH p`, giving
one fixed syntax tree `P := alg (Lbl p) p (dlogInputs g H)`.

Run `P` symbolically, pretending the answer is an indeterminate `X`. Every label carries a linear
form `Frm p = ZMod p × ZMod p`, where `(a, b)` reads as `a + b·X` (`Frm.ev`), and the simulator
state `St p` is an association list of `(label, form)` pairs starting at `st0 p`, which sends
`g ↦ 1` and `H ↦ X`. The simulator `sim` answers:

* `eq x y` by *label* equality — exactly what a real run does, at no cost, leaking nothing;
* `add x y` and `neg x` by `ensure`ing both operands have forms (a label conjured out of thin air
  gets a fresh *constant* form) and then handing back the label carrying the resulting form,
  allocating a fresh one if there is none.

The simulation runs on a **fuel** budget `B := √p / 5`, which is what breaks the circularity
between "the state is small" and "the run is cheap": without it a program could drive the state to
size `p` down a branch the real execution never takes. Only `add` and `neg` extend the state, by at
most `3` entries each, so the final state `ψ` has `|ψ| ≤ 2 + 3B` entries, with distinct labels and
distinct forms (`sim_nodup`).

**Turning a symbolic run into a real one.** Call `X` *good* when distinct forms of `ψ` take
distinct values at `X`. For a good `X` the map `label ↦ form.ev X` is a partial injection of
`ZMod p` into itself, so it extends to a permutation `σ` (`exists_perm`); transporting the group
structure of `ZMod p` back along `σ` equips `Lbl p` with an `AddCommGroup` for which `E := σ` is
additive and injective. `sim_sound` then shows by induction that with respect to *that* structure
the simulation was faithful: it never overcounts, and any output it produced is the real one. The
`add` step is the heart of it — the label the simulator invented really is the sum, because `E` is
injective and `E l = (u + v).ev X = E x + E y = E (x + y)`. Moreover `E g = 1` and `E H = X`, so
`X.val • g = H`, as `SolvesDLog` requires.

**Counting.** Two distinct forms with equal slope never collide, and two with different slopes
collide at exactly one point (`collide_eq`, using that `ZMod p` is a field), so at most `|ψ|²`
values of `X` are bad and two good ones survive as soon as `|ψ|² + 2 ≤ p`. If the simulation
*finished* with output `k`, correctness forces `(k : ZMod p) = X` for each good `X`, so the two
good values coincide — the algorithm committed to an answer before learning enough to tell two
possible discrete logarithms apart. So the fuel *ran out*, and then `sim` spent exactly `B`, which
by `sim_sound` the real run must also have spent.

With `M := Nat.sqrt p`, `B := M / 5` and `p ≥ 100`: `|ψ| ≤ 2 + 3B ≤ M - 1`, hence
`|ψ|² + 2 ≤ M² ≤ p`; and `10 * B ≥ M`, so the cost is at least `√p / 10`.

## Main results

- `SolvesDLog`: the correctness hypothesis, quantified over every group.
- `solvesDLog_bruteForceDLog`: brute force satisfies it, so the bound is not vacuous.
- `exists_group_sqrt_le_groupOps`: for every `N` there is a group of order at least `N` and a
  secret on which the algorithm spends at least `√|G| / 10` group operations.
- `dlog_generic_lower_bound`: the same statement in the `∃ c > 0` form.

## References

Victor Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, EUROCRYPT 1997.

Ueli Maurer, *Abstract Models of Computation in Cryptography*, IMA 2005.
-/

@[expose] public section

namespace Algolean

namespace LowerBounds

open Algorithms Cslib

/-!
## Solving the discrete logarithm

The correctness hypothesis. It asks the algorithm to return *a* discrete logarithm of `x • g` to
base `g` — not the least one — in every finite group, run at that group's own order.
-/

/--
`SolvesDLog alg` says that `alg`, run in any finite group at that group's order, on the base `g`
and the target `x • g`, returns a discrete logarithm of the target.
-/
def SolvesDLog (alg : GroupAlg 2 ℕ) : Prop :=
  ∀ (G : Type) [Fintype G] [AddCommGroup G] [DecidableEq G] (g : G) (x : ℕ),
    GroupProg.eval (alg G (Fintype.card G) (dlogInputs g (x • g))) • g = x • g

/-- **Brute force solves the discrete logarithm**, so the lower bound below is not vacuous. -/
theorem solvesDLog_bruteForceDLog : SolvesDLog bruteForceDLog :=
  fun _ _ _ _ => bruteForceDLog_eval_nsmul

/-!
## The symbolic simulation

Everything in this section is the proof device: labels carrying linear forms, a simulator that
runs a program against them, and the extraction of a real group from a symbolic run.
-/

namespace Shoup

/-- Labels: the carrier of the groups we construct. This is a type synonym for `ZMod p` so that
Lean never picks up the ring structure of `ZMod p` by accident. -/
private def Lbl (p : ℕ) : Type := ZMod p

private instance instDecEqLbl {p : ℕ} : DecidableEq (Lbl p) :=
  inferInstanceAs (DecidableEq (ZMod p))
private instance instInhabitedLbl {p : ℕ} : Inhabited (Lbl p) := ⟨(0 : ZMod p)⟩
private instance instFintypeLbl {p : ℕ} [NeZero p] : Fintype (Lbl p) :=
  inferInstanceAs (Fintype (ZMod p))

private lemma card_Lbl (p : ℕ) [NeZero p] : Fintype.card (Lbl p) = p := ZMod.card p

/-- The equivalence between `Lbl p` and `ZMod p`. -/
private def lblEquiv (p : ℕ) : Lbl p ≃ ZMod p := Equiv.refl _

/-- A linear form `a + b * X` over `ZMod p`. -/
private abbrev Frm (p : ℕ) := ZMod p × ZMod p

/-- Evaluate a linear form at `X`. -/
private def Frm.ev {p : ℕ} (f : Frm p) (X : ZMod p) : ZMod p := f.1 + f.2 * X

@[simp] private lemma Frm.ev_add {p : ℕ} (f g : Frm p) (X : ZMod p) :
    (f + g).ev X = f.ev X + g.ev X := by
  simp [Frm.ev, Prod.fst_add, Prod.snd_add, add_mul]; ring

@[simp] private lemma Frm.ev_neg {p : ℕ} (f : Frm p) (X : ZMod p) :
    (-f).ev X = -(f.ev X) := by
  simp [Frm.ev, Prod.fst_neg, Prod.snd_neg, neg_mul]; ring

/-- The simulator's state: an association list mapping labels to the linear form describing their
discrete logarithm. -/
private abbrev St (p : ℕ) := List (Lbl p × Frm p)

/-- Look up the form attached to a label. -/
private def lookLbl {p : ℕ} (s : St p) (l : Lbl p) : Option (Frm p) :=
  (s.find? (fun e => e.1 = l)).map Prod.snd

/-- Look up the label attached to a form. -/
private def lookFrm {p : ℕ} (s : St p) (f : Frm p) : Option (Lbl p) :=
  (s.find? (fun e => e.2 = f)).map Prod.fst

/-! ### Association-list lemmas -/

private lemma mem_of_lookLbl {p : ℕ} {s : St p} {l : Lbl p} {f : Frm p}
    (h : lookLbl s l = some f) : (l, f) ∈ s := by
  simp only [lookLbl, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, hxf⟩ := h
  have h1 : x.1 = l := by simpa using List.find?_some hx
  have : x = (l, f) := Prod.ext h1 hxf
  exact this ▸ List.mem_of_find?_eq_some hx

private lemma mem_of_lookFrm {p : ℕ} {s : St p} {l : Lbl p} {f : Frm p}
    (h : lookFrm s f = some l) : (l, f) ∈ s := by
  simp only [lookFrm, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, hxl⟩ := h
  have h1 : x.2 = f := by simpa using List.find?_some hx
  have : x = (l, f) := Prod.ext hxl h1
  exact this ▸ List.mem_of_find?_eq_some hx

private lemma not_mem_of_lookLbl_none {p : ℕ} {s : St p} {l : Lbl p} (h : lookLbl s l = none)
    (f : Frm p) : (l, f) ∉ s := by
  simp only [lookLbl, Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hm
  simpa using h _ hm

private lemma not_mem_of_lookFrm_none {p : ℕ} {s : St p} {f : Frm p} (h : lookFrm s f = none)
    (l : Lbl p) : (l, f) ∉ s := by
  simp only [lookFrm, Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hm
  simpa using h _ hm

/-! ### Fresh labels and constants -/

open Classical in
/-- A label not yet occurring in the state (junk if there is none). -/
private noncomputable def freshLbl {p : ℕ} (s : St p) : Lbl p :=
  if h : ∃ l : Lbl p, lookLbl s l = none then h.choose else default

open Classical in
/-- A constant `c` such that the form `(c, 0)` does not yet occur in the state. -/
private noncomputable def freshCst {p : ℕ} (s : St p) : ZMod p :=
  if h : ∃ c : ZMod p, lookFrm s (c, 0) = none then h.choose else 0

private lemma freshLbl_spec {p : ℕ} {s : St p} (h : ∃ l : Lbl p, lookLbl s l = none) :
    lookLbl s (freshLbl s) = none := by
  rw [freshLbl, dif_pos h]; exact h.choose_spec

private lemma freshCst_spec {p : ℕ} {s : St p} (h : ∃ c : ZMod p, lookFrm s (c, 0) = none) :
    lookFrm s (freshCst s, 0) = none := by
  rw [freshCst, dif_pos h]; exact h.choose_spec

private lemma exists_fresh_lbl {p : ℕ} [NeZero p] {s : St p} (h : s.length < p) :
    ∃ l : Lbl p, lookLbl s l = none := by
  by_contra hcon
  have hcon' : ∀ l : Lbl p, lookLbl s l ≠ none := fun l hl => hcon ⟨l, hl⟩
  have hsub : (Finset.univ : Finset (Lbl p)) ⊆ (s.map Prod.fst).toFinset := by
    intro l _
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (hcon' l)
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨(l, f), mem_of_lookLbl hf, rfl⟩)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, card_Lbl] at h1
  have h2 : (s.map Prod.fst).toFinset.card ≤ s.length := by
    simpa using List.toFinset_card_le (s.map Prod.fst)
  omega

private lemma exists_fresh_cst {p : ℕ} [NeZero p] {s : St p} (h : s.length < p) :
    ∃ c : ZMod p, lookFrm s (c, 0) = none := by
  by_contra hcon
  have hcon' : ∀ c : ZMod p, lookFrm s (c, 0) ≠ none := fun c hc => hcon ⟨c, hc⟩
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆
      ((s.map Prod.snd).toFinset.filter (fun f => f.2 = 0)).image Prod.fst := by
    intro c _
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 (hcon' c)
    refine Finset.mem_image.2 ⟨(c, 0), ?_, rfl⟩
    exact Finset.mem_filter.2
      ⟨List.mem_toFinset.2 (List.mem_map.2 ⟨(l, (c, 0)), mem_of_lookFrm hl, rfl⟩), by simp⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  have h2 : (((s.map Prod.snd).toFinset.filter (fun f => f.2 = 0)).image Prod.fst).card
      ≤ s.length := by
    refine le_trans (Finset.card_image_le) (le_trans (Finset.card_filter_le _ _) ?_)
    simpa using List.toFinset_card_le (s.map Prod.snd)
  omega

/-! ### The simulator -/

/-- Result of running the symbolic simulation: an optional output (`none` when the fuel ran out),
the final state, and the number of group operations performed. -/
private structure Res (p : ℕ) (α : Type) where
  /-- The value the simulated program returned, or `none` if the fuel ran out first. -/
  out : Option α
  /-- The simulator state at the point the simulation stopped. -/
  st : St p
  /-- The number of element-producing queries the simulation charged. -/
  cost : ℕ

/-- Make sure the label `l` has a form attached; a label the algorithm produces out of thin air is
assigned a *constant* form not already present. -/
private noncomputable def ensure {p : ℕ} (s : St p) (l : Lbl p) : St p :=
  match lookLbl s l with
  | some _ => s
  | none => (l, (freshCst s, 0)) :: s

/-- Return the label carrying the form `f`, allocating a fresh one if necessary. -/
private noncomputable def addFrm {p : ℕ} (s : St p) (f : Frm p) : Lbl p × St p :=
  match lookFrm s f with
  | some l => (l, s)
  | none => (freshLbl s, (freshLbl s, f) :: s)

/-- One `add` step of the simulation: make sure both operands have forms, then look up (or
allocate) the label carrying the sum of those forms. -/
private noncomputable def stepAdd {p : ℕ} (s : St p) (x y : Lbl p) : Lbl p × St p :=
  addFrm (ensure (ensure s x) y)
    ((lookLbl (ensure (ensure s x) y) x).getD 0 + (lookLbl (ensure (ensure s x) y) y).getD 0)

/-- One `neg` step of the simulation. -/
private noncomputable def stepNeg {p : ℕ} (s : St p) (x : Lbl p) : Lbl p × St p :=
  addFrm (ensure s x) (-(lookLbl (ensure s x) x).getD 0)

/-- Charge one group operation to a result. -/
private def Res.bump {p : ℕ} {α : Type} (r : Res p α) : Res p α := ⟨r.out, r.st, 1 + r.cost⟩

/-- The symbolic simulation of a group program, with a fuel bound on the number of group
operations. -/
private noncomputable def sim {p : ℕ} {α : Type} : GroupProg (Lbl p) α → St p → ℕ → Res p α
  | .pure a, s, _ => ⟨some a, s, 0⟩
  | .liftBind (.eq x y) cont, s, B => sim (cont (decide (x = y))) s B
  | .liftBind (.add _ _) _, s, 0 => ⟨none, s, 0⟩
  | .liftBind (.neg _) _, s, 0 => ⟨none, s, 0⟩
  | .liftBind (.add x y) cont, s, B + 1 =>
      Res.bump (sim (cont (stepAdd s x y).1) (stepAdd s x y).2 B)
  | .liftBind (.neg x) cont, s, B + 1 =>
      Res.bump (sim (cont (stepNeg s x).1) (stepNeg s x).2 B)

private lemma sim_pure {p : ℕ} {α : Type} (a : α) (s : St p) (B : ℕ) :
    sim (.pure a : GroupProg (Lbl p) α) s B = ⟨some a, s, 0⟩ := rfl

/-! ### Basic properties of `ensure` and `addFrm` -/

@[simp] private lemma lookLbl_cons_self {p : ℕ} (l : Lbl p) (f : Frm p) (s : St p) :
    lookLbl ((l, f) :: s) l = some f := by
  simp [lookLbl, List.find?_cons_of_pos]

private lemma lookLbl_cons_of_ne {p : ℕ} {l l' : Lbl p} (f : Frm p) (s : St p) (h : l' ≠ l) :
    lookLbl ((l', f) :: s) l = lookLbl s l := by
  simp [lookLbl, List.find?_cons_of_neg, h]

private lemma ensure_sublist {p : ℕ} (s : St p) (l : Lbl p) : s.Sublist (ensure s l) := by
  unfold ensure; split
  · exact List.Sublist.refl _
  · exact List.sublist_cons_self _ _

private lemma ensure_length {p : ℕ} (s : St p) (l : Lbl p) :
    (ensure s l).length ≤ s.length + 1 := by
  unfold ensure; split <;> simp

private lemma ensure_lookLbl_self {p : ℕ} (s : St p) (l : Lbl p) :
    ∃ f, lookLbl (ensure s l) l = some f := by
  unfold ensure; split
  · next f h => exact ⟨f, h⟩
  · exact ⟨_, lookLbl_cons_self _ _ _⟩

private lemma lookLbl_ensure {p : ℕ} {s : St p} {l : Lbl p} {f : Frm p} (l' : Lbl p)
    (h : lookLbl s l = some f) : lookLbl (ensure s l') l = some f := by
  unfold ensure; split
  · exact h
  · next hnone =>
    have hne : l' ≠ l := by rintro rfl; rw [hnone] at h; simp at h
    rw [lookLbl_cons_of_ne _ _ hne]; exact h

private lemma addFrm_sublist {p : ℕ} (s : St p) (q : Frm p) : s.Sublist (addFrm s q).2 := by
  unfold addFrm; split
  · exact List.Sublist.refl _
  · exact List.sublist_cons_self _ _

private lemma addFrm_length {p : ℕ} (s : St p) (q : Frm p) :
    (addFrm s q).2.length ≤ s.length + 1 := by
  unfold addFrm; split <;> simp

private lemma addFrm_mem {p : ℕ} (s : St p) (q : Frm p) : ((addFrm s q).1, q) ∈ (addFrm s q).2 := by
  unfold addFrm; split
  · next l h => exact mem_of_lookFrm h
  · simp

/-! ### The `Nodup` invariant -/

/-- Both the labels and the forms occurring in the state are duplicate-free. -/
private def NodupSt {p : ℕ} (s : St p) : Prop := (s.map Prod.fst).Nodup ∧ (s.map Prod.snd).Nodup

private lemma ensure_nodup {p : ℕ} [NeZero p] {s : St p} (hlen : s.length < p) (hs : NodupSt s)
    (l : Lbl p) : NodupSt (ensure s l) := by
  unfold ensure; split
  · exact hs
  · next hnone =>
    refine ⟨?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, hs.1⟩
      rintro hm
      obtain ⟨⟨l', f'⟩, hmem, rfl⟩ := List.mem_map.1 hm
      exact not_mem_of_lookLbl_none hnone f' hmem
    · refine List.nodup_cons.2 ⟨?_, hs.2⟩
      rintro hm
      obtain ⟨⟨l', f'⟩, hmem, hf⟩ := List.mem_map.1 hm
      have hf' : f' = (freshCst s, 0) := hf
      subst hf'
      exact not_mem_of_lookFrm_none (freshCst_spec (exists_fresh_cst hlen)) l' hmem

private lemma addFrm_nodup {p : ℕ} [NeZero p] {s : St p} (hlen : s.length < p) (hs : NodupSt s)
    (q : Frm p) : NodupSt (addFrm s q).2 := by
  unfold addFrm; split
  · exact hs
  · next hnone =>
    change NodupSt ((freshLbl s, q) :: s)
    refine ⟨?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, hs.1⟩
      rintro hm
      obtain ⟨⟨l', f'⟩, hmem, rfl⟩ := List.mem_map.1 hm
      exact not_mem_of_lookLbl_none (freshLbl_spec (exists_fresh_lbl hlen)) f' hmem
    · refine List.nodup_cons.2 ⟨?_, hs.2⟩
      rintro hm
      obtain ⟨⟨l', f'⟩, hmem, hf⟩ := List.mem_map.1 hm
      have hf' : f' = q := hf
      subst hf'
      exact not_mem_of_lookFrm_none hnone l' hmem

/-! ### Properties of the two step functions -/

private lemma stepAdd_sublist {p : ℕ} (s : St p) (x y : Lbl p) : s.Sublist (stepAdd s x y).2 :=
  ((ensure_sublist s x).trans (ensure_sublist _ y)).trans (addFrm_sublist _ _)

private lemma stepNeg_sublist {p : ℕ} (s : St p) (x : Lbl p) : s.Sublist (stepNeg s x).2 :=
  (ensure_sublist s x).trans (addFrm_sublist _ _)

private lemma stepAdd_length {p : ℕ} (s : St p) (x y : Lbl p) :
    (stepAdd s x y).2.length ≤ s.length + 3 := by
  have h1 := ensure_length s x
  have h2 := ensure_length (ensure s x) y
  have h3 := addFrm_length (ensure (ensure s x) y)
    ((lookLbl (ensure (ensure s x) y) x).getD 0 + (lookLbl (ensure (ensure s x) y) y).getD 0)
  simpa [stepAdd] using (by omega :
    (addFrm (ensure (ensure s x) y)
      ((lookLbl (ensure (ensure s x) y) x).getD 0
        + (lookLbl (ensure (ensure s x) y) y).getD 0)).2.length ≤ s.length + 3)

private lemma stepNeg_length {p : ℕ} (s : St p) (x : Lbl p) :
    (stepNeg s x).2.length ≤ s.length + 3 := by
  have h1 := ensure_length s x
  have h3 := addFrm_length (ensure s x) (-(lookLbl (ensure s x) x).getD 0)
  simpa [stepNeg] using (by omega :
    (addFrm (ensure s x) (-(lookLbl (ensure s x) x).getD 0)).2.length ≤ s.length + 3)

private lemma stepAdd_nodup {p : ℕ} [NeZero p] {s : St p} (hlen : s.length + 2 < p) (hs : NodupSt s)
    (x y : Lbl p) : NodupSt (stepAdd s x y).2 := by
  have h1 := ensure_length s x
  have h2 := ensure_length (ensure s x) y
  exact addFrm_nodup (by omega) (ensure_nodup (by omega) (ensure_nodup (by omega) hs x) y) _

private lemma stepNeg_nodup {p : ℕ} [NeZero p] {s : St p} (hlen : s.length + 1 < p) (hs : NodupSt s)
    (x : Lbl p) : NodupSt (stepNeg s x).2 := by
  have h1 := ensure_length s x
  exact addFrm_nodup (by omega) (ensure_nodup (by omega) hs x) _

/-- The semantic content of an `add` step: both operands carry forms in the resulting state, and
the returned label carries their sum. -/
private lemma stepAdd_spec {p : ℕ} (s : St p) (x y : Lbl p) :
    ∃ u v : Frm p, (x, u) ∈ (stepAdd s x y).2 ∧ (y, v) ∈ (stepAdd s x y).2 ∧
      ((stepAdd s x y).1, u + v) ∈ (stepAdd s x y).2 := by
  obtain ⟨u, hu0⟩ := ensure_lookLbl_self s x
  have hu : lookLbl (ensure (ensure s x) y) x = some u := lookLbl_ensure y hu0
  obtain ⟨v, hv⟩ := ensure_lookLbl_self (ensure s x) y
  refine ⟨u, v, ?_, ?_, ?_⟩
  · exact (addFrm_sublist _ _).mem (mem_of_lookLbl hu)
  · exact (addFrm_sublist _ _).mem (mem_of_lookLbl hv)
  · have : stepAdd s x y = addFrm (ensure (ensure s x) y) (u + v) := by
      simp [stepAdd, hu, hv]
    rw [this]; exact addFrm_mem _ _

/-- The semantic content of a `neg` step. -/
private lemma stepNeg_spec {p : ℕ} (s : St p) (x : Lbl p) :
    ∃ u : Frm p, (x, u) ∈ (stepNeg s x).2 ∧ ((stepNeg s x).1, -u) ∈ (stepNeg s x).2 := by
  obtain ⟨u, hu⟩ := ensure_lookLbl_self s x
  refine ⟨u, (addFrm_sublist _ _).mem (mem_of_lookLbl hu), ?_⟩
  have : stepNeg s x = addFrm (ensure s x) (-u) := by simp [stepNeg, hu]
  rw [this]; exact addFrm_mem _ _

/-! ### Global properties of the simulation -/

private lemma sim_sublist {p : ℕ} {α : Type} (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    s.Sublist (sim P s B).st := by
  induction P, s, B using sim.induct with
  | case1 a s B => exact List.Sublist.refl s
  | case2 x y cont s B ih => exact ih
  | case3 x y cont s => exact List.Sublist.refl s
  | case4 x cont s => exact List.Sublist.refl s
  | case5 x y cont s B ih => exact (stepAdd_sublist s x y).trans ih
  | case6 x cont s B ih => exact (stepNeg_sublist s x).trans ih

private lemma sim_length {p : ℕ} {α : Type} (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    (sim P s B).st.length ≤ s.length + 3 * B := by
  induction P, s, B using sim.induct with
  | case1 a s B => exact Nat.le_add_right _ _
  | case2 x y cont s B ih => exact ih
  | case3 x y cont s => exact Nat.le_add_right _ _
  | case4 x cont s => exact Nat.le_add_right _ _
  | case5 x y cont s B ih =>
      refine le_trans ih ?_
      have := stepAdd_length s x y
      omega
  | case6 x cont s B ih =>
      refine le_trans ih ?_
      have := stepNeg_length s x
      omega

private lemma sim_cost_of_none {p : ℕ} {α : Type} (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    (sim P s B).out = none → (sim P s B).cost = B := by
  induction P, s, B using sim.induct with
  | case1 a s B => intro h; rw [sim_pure] at h; exact absurd h (by simp)
  | case2 x y cont s B ih => exact ih
  | case3 x y cont s => intro _; rfl
  | case4 x cont s => intro _; rfl
  | case5 x y cont s B ih =>
      change (sim (cont (stepAdd s x y).1) (stepAdd s x y).2 B).out = none →
        1 + (sim (cont (stepAdd s x y).1) (stepAdd s x y).2 B).cost = B + 1
      intro h; have := ih h; omega
  | case6 x cont s B ih =>
      change (sim (cont (stepNeg s x).1) (stepNeg s x).2 B).out = none →
        1 + (sim (cont (stepNeg s x).1) (stepNeg s x).2 B).cost = B + 1
      intro h; have := ih h; omega

private lemma sim_nodup {p : ℕ} [NeZero p] {α : Type} (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    s.length + 3 * B < p → NodupSt s → NodupSt (sim P s B).st := by
  induction P, s, B using sim.induct with
  | case1 a s B => intro _ h; exact h
  | case2 x y cont s B ih => exact ih
  | case3 x y cont s => intro _ h; exact h
  | case4 x cont s => intro _ h; exact h
  | case5 x y cont s B ih =>
      intro hlen hnd
      change NodupSt (sim (cont (stepAdd s x y).1) (stepAdd s x y).2 B).st
      have h1 := stepAdd_length s x y
      exact ih (by omega) (stepAdd_nodup (by omega) hnd x y)
  | case6 x cont s B ih =>
      intro hlen hnd
      change NodupSt (sim (cont (stepNeg s x).1) (stepNeg s x).2 B).st
      have h1 := stepNeg_length s x
      exact ih (by omega) (stepNeg_nodup (by omega) hnd x)

/-! ### Soundness of the simulation

If a group structure on `Lbl p` is compatible (via `e`) with the forms recorded in the final state
`ψ`, then the simulation faithfully tracks a real execution: it never overcounts the cost, and
whenever it produces an output, that is the real output. -/

private lemma sim_sound {p : ℕ} {α : Type} [inst : AddCommGroup (Lbl p)]
    (e : Lbl p → ZMod p) (X : ZMod p)
    (hadd : ∀ x y : Lbl p, e (x + y) = e x + e y)
    (hneg : ∀ x : Lbl p, e (-x) = -(e x))
    (einj : Function.Injective e)
    (ψ : St p) (hagree : ∀ l f, (l, f) ∈ ψ → e l = f.ev X)
    (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) (hst : (sim P s B).st = ψ) :
    (sim P s B).cost ≤ GroupProg.groupOps P ∧
      ∀ a, (sim P s B).out = some a → GroupProg.eval P = a := by
  induction P, s, B using sim.induct generalizing ψ with
  | case1 a s B =>
      exact ⟨Nat.zero_le _, fun a' ha' => Option.some.inj ha'⟩
  | case2 x y cont s B ih =>
      obtain ⟨ihc, iho⟩ := ih ψ hagree hst
      refine ⟨?_, fun a ha => ?_⟩
      · change (sim (cont (decide (x = y))) s B).cost
            ≤ GroupProg.groupOps (FreeM.liftBind (GroupQuery.eq x y) cont)
        rw [GroupProg.groupOps_liftBind]
        simp only [GroupQuery.answer_eq, GroupQuery.groupOps_charge_eq]
        omega
      · change GroupProg.eval (FreeM.liftBind (GroupQuery.eq x y) cont) = a
        rw [GroupProg.eval_liftBind]
        simp only [GroupQuery.answer_eq]
        exact iho a ha
  | case3 x y cont s =>
      refine ⟨Nat.zero_le _, fun a ha => ?_⟩
      exact absurd (show (none : Option α) = some a from ha) (by simp)
  | case4 x cont s =>
      refine ⟨Nat.zero_le _, fun a ha => ?_⟩
      exact absurd (show (none : Option α) = some a from ha) (by simp)
  | case5 x y cont s B ih =>
      obtain ⟨u, v, hxu, hyv, hlq⟩ := stepAdd_spec s x y
      have hsub : (stepAdd s x y).2.Sublist ψ := by
        rw [← hst]; exact sim_sublist _ _ _
      have hex : e x = u.ev X := hagree _ _ (hsub.mem hxu)
      have hey : e y = v.ev X := hagree _ _ (hsub.mem hyv)
      have hel : e (stepAdd s x y).1 = (u + v).ev X := hagree _ _ (hsub.mem hlq)
      have hkey : (stepAdd s x y).1 = x + y := by
        apply einj
        rw [hel, hadd, hex, hey, Frm.ev_add]
      obtain ⟨ihc, iho⟩ := ih ψ hagree hst
      refine ⟨?_, ?_⟩
      · change 1 + (sim (cont (stepAdd s x y).1) (stepAdd s x y).2 B).cost
            ≤ GroupProg.groupOps (FreeM.liftBind (GroupQuery.add x y) cont)
        rw [GroupProg.groupOps_liftBind]
        simp only [GroupQuery.answer_add, GroupQuery.groupOps_charge_add]
        rw [← hkey]; omega
      · intro a ha
        change GroupProg.eval (FreeM.liftBind (GroupQuery.add x y) cont) = a
        rw [GroupProg.eval_liftBind]
        simp only [GroupQuery.answer_add]
        rw [← hkey]
        exact iho a ha
  | case6 x cont s B ih =>
      obtain ⟨u, hxu, hlq⟩ := stepNeg_spec s x
      have hsub : (stepNeg s x).2.Sublist ψ := by
        rw [← hst]; exact sim_sublist _ _ _
      have hex : e x = u.ev X := hagree _ _ (hsub.mem hxu)
      have hel : e (stepNeg s x).1 = (-u).ev X := hagree _ _ (hsub.mem hlq)
      have hkey : (stepNeg s x).1 = -x := by
        apply einj
        rw [hel, hneg, hex, Frm.ev_neg]
      obtain ⟨ihc, iho⟩ := ih ψ hagree hst
      refine ⟨?_, ?_⟩
      · change 1 + (sim (cont (stepNeg s x).1) (stepNeg s x).2 B).cost
            ≤ GroupProg.groupOps (FreeM.liftBind (GroupQuery.neg x) cont)
        rw [GroupProg.groupOps_liftBind]
        simp only [GroupQuery.answer_neg, GroupQuery.groupOps_charge_neg]
        rw [← hkey]; omega
      · intro a ha
        change GroupProg.eval (FreeM.liftBind (GroupQuery.neg x) cont) = a
        rw [GroupProg.eval_liftBind]
        simp only [GroupQuery.answer_neg]
        rw [← hkey]
        exact iho a ha

/-! ### Counting the good specialisations -/

/-- `X` is *good* for `ψ` when distinct forms recorded in `ψ` take distinct values at `X`. -/
private def Good {p : ℕ} (ψ : St p) (X : ZMod p) : Prop :=
  ∀ f ∈ ψ.map Prod.snd, ∀ f' ∈ ψ.map Prod.snd, Frm.ev f X = Frm.ev f' X → f = f'

/-- The unique point at which two forms of different slopes agree. -/
private noncomputable def collide {p : ℕ} [Fact p.Prime] (f f' : Frm p) : ZMod p :=
  (f'.1 - f.1) / (f.2 - f'.2)

private lemma collide_eq {p : ℕ} [Fact p.Prime] {f f' : Frm p} {X : ZMod p}
    (hne : f ≠ f') (h : Frm.ev f X = Frm.ev f' X) : X = collide f f' := by
  simp only [Frm.ev] at h
  have hslope : f.2 ≠ f'.2 := by
    intro hs
    refine hne (Prod.ext ?_ hs)
    rw [hs] at h
    exact add_right_cancel h
  rw [collide, eq_div_iff (sub_ne_zero.2 hslope)]
  linear_combination h

private lemma exists_two_good {p : ℕ} [Fact p.Prime] (ψ : St p)
    (hlen : ψ.length * ψ.length + 2 ≤ p) :
    ∃ X₁ X₂ : ZMod p, X₁ ≠ X₂ ∧ Good ψ X₁ ∧ Good ψ X₂ := by
  classical
  have hbad : (Finset.univ.filter (fun X : ZMod p => ¬ Good ψ X)) ⊆
      (((ψ.map Prod.snd).toFinset) ×ˢ ((ψ.map Prod.snd).toFinset)).image
        (fun q => collide q.1 q.2) := by
    intro X hX
    have hX2 : ¬ Good ψ X := (Finset.mem_filter.1 hX).2
    rw [Good] at hX2
    push Not at hX2
    obtain ⟨f, hf, f', hf', hev, hne⟩ := hX2
    exact Finset.mem_image.2 ⟨(f, f'),
      Finset.mem_product.2 ⟨List.mem_toFinset.2 hf, List.mem_toFinset.2 hf'⟩,
      (collide_eq hne hev).symm⟩
  have hcard : (Finset.univ.filter (fun X : ZMod p => ¬ Good ψ X)).card
      ≤ ψ.length * ψ.length := by
    refine le_trans (Finset.card_le_card hbad) (le_trans Finset.card_image_le ?_)
    rw [Finset.card_product]
    have h1 : ((ψ.map Prod.snd).toFinset).card ≤ ψ.length := by
      simpa using List.toFinset_card_le (ψ.map Prod.snd)
    exact Nat.mul_le_mul h1 h1
  have hsplit : (Finset.univ.filter (fun X : ZMod p => Good ψ X)).card
      + (Finset.univ.filter (fun X : ZMod p => ¬ Good ψ X)).card = p := by
    rw [Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
      (p := fun X : ZMod p => Good ψ X), Finset.card_univ, ZMod.card]
  obtain ⟨X₁, h1, X₂, h2, hne⟩ :=
    Finset.one_lt_card.1
      (show 1 < (Finset.univ.filter (fun X : ZMod p => Good ψ X)).card by omega)
  exact ⟨X₁, X₂, hne, (Finset.mem_filter.1 h1).2, (Finset.mem_filter.1 h2).2⟩

/-- From a good `X` we obtain a permutation of `ZMod p` realising every form of `ψ`. -/
private lemma exists_perm {p : ℕ} [NeZero p] (ψ : St p) (hnd : NodupSt ψ) (X : ZMod p)
    (hgood : Good ψ X) :
    ∃ σ : Equiv.Perm (ZMod p), ∀ l f, (l, f) ∈ ψ → σ l = Frm.ev f X := by
  classical
  have hFinj : Function.Injective
      (fun q : {q : Lbl p × Frm p // q ∈ ψ} => (q.1.1 : ZMod p)) := by
    rintro ⟨⟨l, f⟩, hm⟩ ⟨⟨l', f'⟩, hm'⟩ h
    exact Subtype.ext (List.inj_on_of_nodup_map hnd.1 hm hm' h)
  have hGinj : Function.Injective
      (fun q : {q : Lbl p × Frm p // q ∈ ψ} => Frm.ev q.1.2 X) := by
    rintro ⟨⟨l, f⟩, hm⟩ ⟨⟨l', f'⟩, hm'⟩ h
    have hff : f = f' :=
      hgood f (List.mem_map_of_mem hm) f' (List.mem_map_of_mem hm') h
    exact Subtype.ext (List.inj_on_of_nodup_map hnd.2 hm hm' hff)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hFinj hGinj
  exact ⟨σ, fun l f hm => hσ ⟨(l, f), hm⟩⟩

/-! ### The distinguished generator and challenge -/

/-- The label playing the role of the generator. -/
private def lblG (p : ℕ) : Lbl p := (0 : ZMod p)

/-- The label playing the role of the challenge `x • g`. -/
private def lblH (p : ℕ) : Lbl p := (1 : ZMod p)

/-- The initial state: `g` has form `1` and `H` has form `X`. -/
private def st0 (p : ℕ) : St p :=
  [(lblG p, ((1 : ZMod p), (0 : ZMod p))), (lblH p, ((0 : ZMod p), (1 : ZMod p)))]

private lemma st0_length (p : ℕ) : (st0 p).length = 2 := rfl

private lemma st0_nodup {p : ℕ} [Fact p.Prime] : NodupSt (st0 p) := by
  have h : lblG p ≠ lblH p := fun hh => (zero_ne_one : (0 : ZMod p) ≠ 1) hh
  have h' : ((1 : ZMod p), (0 : ZMod p)) ≠ ((0 : ZMod p), (1 : ZMod p)) := by
    intro hh
    exact (one_ne_zero : (1 : ZMod p) ≠ 0) (congrArg Prod.fst hh)
  refine ⟨?_, ?_⟩
  · change ([lblG p, lblH p] : List (Lbl p)).Nodup
    exact List.nodup_cons.2 ⟨by simpa using h, List.nodup_singleton _⟩
  · change ([((1 : ZMod p), (0 : ZMod p)), ((0 : ZMod p), (1 : ZMod p))] : List (Frm p)).Nodup
    exact List.nodup_cons.2 ⟨by simp [h'], List.nodup_singleton _⟩

private lemma mem_st0_G (p : ℕ) : (lblG p, ((1 : ZMod p), (0 : ZMod p))) ∈ st0 p := by simp [st0]

private lemma mem_st0_H (p : ℕ) : (lblH p, ((0 : ZMod p), (1 : ZMod p))) ∈ st0 p := by simp [st0]

/-- With a compatible group structure, `X.val • g` really is `H`, and `n • g` is `n`. -/
private lemma smul_lblG {p : ℕ} [NeZero p] [inst : AddCommGroup (Lbl p)]
    (E : Lbl p ≃ ZMod p) (X : ZMod p)
    (hadd : ∀ x y : Lbl p, E (x + y) = E x + E y)
    (heg : E (lblG p) = 1) (heH : E (lblH p) = X) :
    (X.val • lblG p = lblH p) ∧ ∀ n : ℕ, E (n • lblG p) = (n : ZMod p) := by
  have hnsmul : ∀ (n : ℕ) (a : Lbl p), E (n • a) = n • E a :=
    fun n a => map_nsmul (AddMonoidHom.mk' (fun l : Lbl p => E l) hadd) n a
  have hn : ∀ n : ℕ, E (n • lblG p) = (n : ZMod p) := by
    intro n; rw [hnsmul, heg, nsmul_eq_mul, mul_one]
  refine ⟨E.injective ?_, hn⟩
  rw [hn, heH]
  exact ZMod.natCast_rightInverse X

/-! ### The two halves of the argument -/

section Main

variable {p : ℕ}

/-- If the simulation terminates with output `k`, then `k` is forced to equal every good `X` --
which is impossible once there are two of them. -/
private lemma out_forces [Fact p.Prime] (alg : GroupAlg 2 ℕ) (hcorrect : SolvesDLog alg) (B : ℕ)
    (hnd : NodupSt (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st)
    (X : ZMod p)
    (hgood : Good (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st X)
    (k : ℕ)
    (hout : (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).out = some k) :
    (k : ZMod p) = X := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_perm _ hnd X hgood
  letI E : Lbl p ≃ ZMod p := (lblEquiv p).trans σ
  letI inst : AddCommGroup (Lbl p) := Equiv.addCommGroup E
  have hadd : ∀ x y : Lbl p, E (x + y) = E x + E y := fun x y => map_add (Equiv.addEquiv E) x y
  have hneg : ∀ x : Lbl p, E (-x) = -(E x) := fun x => map_neg (Equiv.addEquiv E) x
  have hagree : ∀ l f, (l, f) ∈ (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st →
      E l = Frm.ev f X := fun l f hm => hσ l f hm
  have hsub0 :
      (st0 p).Sublist (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st :=
    sim_sublist _ _ _
  have heg : E (lblG p) = 1 := by
    rw [hagree _ _ (hsub0.mem (mem_st0_G p))]; simp [Frm.ev]
  have heH : E (lblH p) = X := by
    rw [hagree _ _ (hsub0.mem (mem_st0_H p))]; simp [Frm.ev]
  obtain ⟨hxg, hn⟩ := smul_lblG E X hadd heg heH
  have hev : GroupProg.eval (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) = k :=
    (sim_sound (fun l => E l) X hadd hneg E.injective _ hagree _ (st0 p) B rfl).2 k hout
  have hC := hcorrect (Lbl p) (lblG p) X.val
  rw [card_Lbl, hxg, hev] at hC
  have := congrArg (fun l : Lbl p => E l) hC
  simpa [hn, heH] using this

/-- The final assembly: for every `N` there is a group of order at least `N`, and a secret in it,
on which the algorithm spends at least `√|G| / 10` group operations. -/
private lemma sqrt_le_groupOps_of_solvesDLog (alg : GroupAlg 2 ℕ)
    (hcorrect : SolvesDLog alg) (N : ℕ) :
    ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
      N ≤ Fintype.card G ∧ x < Fintype.card G ∧
        Nat.sqrt (Fintype.card G) ≤
          10 * GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) := by
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (max N 100)
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hp100 : 100 ≤ p := le_trans (le_max_right N 100) hpge
  have hpN : N ≤ p := le_trans (le_max_left N 100) hpge
  have hM10 : 10 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by omega)
  have hMsq : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  obtain ⟨M, hMdef⟩ : ∃ M, Nat.sqrt p = M + 1 := ⟨Nat.sqrt p - 1, by omega⟩
  have hMsq' : (M + 1) * (M + 1) ≤ p := hMdef ▸ hMsq
  have hexp : (M + 1) * (M + 1) = M * M + 2 * M + 1 := by ring
  have hM9 : 9 ≤ M := by omega
  set B := Nat.sqrt p / 5 with hBdef
  rw [hMdef] at hBdef
  have hB : 3 * B + 3 ≤ M := by omega
  have hlen0 : (st0 p).length + 3 * B < p := by rw [st0_length]; omega
  have hnd : NodupSt (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st :=
    sim_nodup _ _ _ hlen0 st0_nodup
  have hlenR :
      (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st.length ≤ M := by
    have := sim_length (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B
    rw [st0_length] at this
    omega
  have hsq : (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st.length
      * (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st.length + 2 ≤ p := by
    have h1 := Nat.mul_le_mul hlenR hlenR
    omega
  obtain ⟨X₁, X₂, hne, hg1, hg2⟩ := exists_two_good _ hsq
  by_cases hout :
      ∃ k, (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).out = some k
  · obtain ⟨k, hk⟩ := hout
    exact absurd ((out_forces alg hcorrect B hnd X₁ hg1 k hk).symm.trans
      (out_forces alg hcorrect B hnd X₂ hg2 k hk)) hne
  · have hnone : (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).out = none := by
      cases hR : (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).out with
      | none => rfl
      | some k => exact absurd ⟨k, hR⟩ hout
    have hcostB : (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).cost = B :=
      sim_cost_of_none _ _ _ hnone
    obtain ⟨σ, hσ⟩ := exists_perm _ hnd X₁ hg1
    letI E : Lbl p ≃ ZMod p := (lblEquiv p).trans σ
    letI inst : AddCommGroup (Lbl p) := Equiv.addCommGroup E
    have hadd : ∀ x y : Lbl p, E (x + y) = E x + E y := fun x y => map_add (Equiv.addEquiv E) x y
    have hneg : ∀ x : Lbl p, E (-x) = -(E x) := fun x => map_neg (Equiv.addEquiv E) x
    have hagree :
        ∀ l f, (l, f) ∈ (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st →
          E l = Frm.ev f X₁ := fun l f hm => hσ l f hm
    have hsub0 :
        (st0 p).Sublist (sim (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B).st :=
      sim_sublist _ _ _
    have heg : E (lblG p) = 1 := by
      rw [hagree _ _ (hsub0.mem (mem_st0_G p))]; simp [Frm.ev]
    have heH : E (lblH p) = X₁ := by
      rw [hagree _ _ (hsub0.mem (mem_st0_H p))]; simp [Frm.ev]
    obtain ⟨hxg, hn⟩ := smul_lblG E X₁ hadd heg heH
    have hcost : B ≤ GroupProg.groupOps (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) := by
      have := (sim_sound (fun l => E l) X₁ hadd hneg E.injective _ hagree
        (alg (Lbl p) p (dlogInputs (lblG p) (lblH p))) (st0 p) B rfl).1
      omega
    refine ⟨Lbl p, instFintypeLbl, inst, instDecEqLbl, lblG p, X₁.val, ?_, ?_, ?_⟩
    · rw [card_Lbl]; exact hpN
    · rw [card_Lbl]; exact ZMod.val_lt X₁
    · rw [card_Lbl, hxg]
      omega

end Main

end Shoup

/-!
## The bound
-/

/--
**The generic group lower bound for the discrete logarithm.** An algorithm that solves the
discrete logarithm in *every* finite group cannot be efficient in all of them: for every `N` there
is a group of order at least `N`, and a secret in it, on which the algorithm spends at least
`√|G| / 10` group operations.

Note the order of the quantifiers. The algorithm is fixed first, and is handed only the carrier
and the order; the group is produced afterwards, by the proof, out of the run it has just watched.
The existential is not slack: the same statement with the group named in advance is false.
-/
theorem exists_group_sqrt_le_groupOps {alg : GroupAlg 2 ℕ} (hcorrect : SolvesDLog alg) (N : ℕ) :
    ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
      N ≤ Fintype.card G ∧ x < Fintype.card G ∧
        Nat.sqrt (Fintype.card G) ≤
          10 * GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) :=
  Shoup.sqrt_le_groupOps_of_solvesDLog alg hcorrect N

/--
**The same bound, in the `Ω(√|G|)` form.** There is a positive constant `c` such that every
correct generic algorithm is, on arbitrarily large groups, forced to spend `c * √|G|` group
operations on some secret.
-/
theorem dlog_generic_lower_bound :
    ∃ c > (0 : ℚ), ∀ alg : GroupAlg 2 ℕ, SolvesDLog alg → ∀ N : ℕ,
      ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
        N ≤ Fintype.card G ∧ x < Fintype.card G ∧
          c * (Nat.sqrt (Fintype.card G) : ℚ) ≤
            (GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) : ℚ) := by
  refine ⟨1 / 10, by norm_num, fun alg hcorrect N => ?_⟩
  obtain ⟨G, instF, instA, instD, g, x, hcard, hx, hcost⟩ :=
    exists_group_sqrt_le_groupOps hcorrect N
  refine ⟨G, instF, instA, instD, g, x, hcard, hx, ?_⟩
  have hq : (Nat.sqrt (Fintype.card G) : ℚ) ≤
      10 * (GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) : ℚ) := by
    exact_mod_cast hcost
  linarith

end LowerBounds

end Algolean
