module Refine where

open import Prelude.Function
open import Def public



Ref-map : ∀{α n k} → Vec (Set α) (suc n) → Vec (Set α) (suc k) → (Set α) ʷ
Ref-map vars1 vars2 = System vars1 ⇒ System vars2




action-dom-embed : ∀ {α n k vars1 vars2} → (act1 : Action {α} {n} vars1) → (act2 : Action {α} {k} vars2) → [ Ref-map vars1 vars2 ] → Set α
action-dom-embed {α} {_} {_} {vars1} {vars2} act1 act2 ref-map = ∀ n → (sys : System vars1 n) → ((cond act1) n sys → (cond act2) n (ref-map n sys) )

action-range-embed : ∀ {α n k vars1 vars2} → (act1 : Action {α} {n} vars1) → (act2 : Action {α} {k} vars2) → [ Ref-map vars1 vars2 ] → Set α
action-range-embed {α} {_} {_} {vars1} {vars2} act1 act2 ref-map = ∀ n → (sys1 : System vars1 n) → (nsys1 : System vars1 (suc n)) → (cond act1) n sys1 → resp act1 n sys1 nsys1 → (resp act2) n (ref-map n sys1) (ref-map (suc n) nsys1)

action-embed : ∀ {α n k vars1 vars2} → (act1 : Action {α} {n} vars1) → (act2 : Action {α} {k} vars2) → [ Ref-map vars1 vars2 ] → Set α
action-embed {α} {_} {_} {vars1} {vars2} act1 act2 ref-map = action-dom-embed act1 act2 ref-map × action-range-embed act1 act2 ref-map

action-stut-embed : ∀ {α n k vars1} → {vars2 : Vec (Set α) (suc k)} → (act : Action {α} {n} vars1) → [ Ref-map vars1 vars2 ] → Set α
action-stut-embed {α} {_} {_} {vars1} {vars2} act ref-map = ∀ n → (sys1 : System vars1 n) → (nsys1 : System vars1 (suc n)) → (cond act) n sys1 → resp act n sys1 nsys1 → varsEq {vars = vars2} (ref-map n sys1) (ref-map (suc n) nsys1)


action-spec-embed : ∀ {α n1 n2 k vars1 vars2} → (act : Action {α} {n1} vars1) → (spec : Spec {α} {n2} {k} vars2) → [ Ref-map vars1 vars2 ] → Set (lsuc α)
action-spec-embed act spec ref-map = ∃ λ act2 → (act2 ∈v spec) × (action-embed act act2 ref-map) 

action-spec-rembed : ∀ {α n1 n2 k vars1 vars2} → (act : Action {α} {n1} vars1) → (spec : Spec {α} {n2} {k} vars2) → [ Ref-map vars2 vars1 ] → Set (lsuc α)
action-spec-rembed act spec ref-map = ∃ λ act2 → (act2 ∈v spec) × (action-embed act2 act ref-map) 

action-spec-embed-with-stut : ∀ {α n1 n2 k vars1 vars2} → (act : Action {α} {n1} vars1) → (spec : Spec {α} {n2} {k} vars2) → [ Ref-map vars1 vars2 ] → Set (lsuc α)
action-spec-embed-with-stut {vars2 = vars2} act spec ref-map = action-spec-embed act spec ref-map ⊎ action-stut-embed {vars2 = vars2} act ref-map

spec-embed : ∀ {α n1 n2 k1 k2 vars1 vars2} → (spec1 : Spec {α} {n1} {k1} vars1) → (spec2 : Spec {α} {n2} {k2} vars2) → [ Ref-map vars1 vars2 ] → Set (lsuc α)
spec-embed {α} {k1 = .0} (x ∷ []) spec2 ref-map = action-spec-embed-with-stut x spec2 ref-map
spec-embed {α} {k1 = .(suc _)} (x ∷ x₁ ∷ spec1) spec2 ref-map = action-spec-embed-with-stut x spec2 ref-map × spec-embed (x₁ ∷ spec1) spec2 ref-map



spec-action-covering : ∀{α n1 n2 k vars1 vars2} → (spec1 : Spec {α} {n1} {k} vars1) → (act :  Action {α} {n2} vars2) → [ Ref-map vars1 vars2 ] → Set (lsuc α)
spec-action-covering {α} {vars1 = vars1} {vars2 = vars2} spec1 act ref-map
    = Σ {b = α} (∃ λ n → Vec (action-spec-rembed act spec1 ref-map) n ) λ x
                                                → let conds = fmap (cond ∘ fst) (snd x)
                                                  in ∀ n → (sys2 : System vars2 n) →
                                                     cond act n sys2 →
                                                     (psys : System vars1 n) →
                                                     let s = vfoldr (λ x y → (x n psys) ⊎ y) (⊥′ {α}) conds
                                                     in (ref-map n psys ≡ sys2) → s


-- spec-covering : ∀ {α n k1 k2 vars} → (spec1 : Spec {α} {n} {k1} vars) → (spec2 : Spec {α} {n} {k2} vars) → Set (lsuc α)
-- spec-covering spec1 (x ∷ []) = spec-action-covering spec1 x
-- spec-covering spec1 (x ∷ x₁ ∷ spec2) = spec-action-covering spec1 x × spec-covering spec1 (x₁ ∷ spec2)
-- -- There are multiple spec-covering and each one determines a different spec2 implementation.


-- spec-refinement : ∀ {α n k1 k2 vars} → (spec1 : Spec {α} {n} {k1} vars) → (spec2 : Spec {α} {n} {k2} vars) → Set (lsuc α)
-- spec-refinement spec1 spec2 = spec-embed spec1 spec2 × spec-covering spec1 spec2




-- -- spec-covering allows us to construct actions of spec2 from actions of spec1,
-- -- thus any temporal proofs that used actions of spec2 is also valid for spec1 (with the refinement mapping).
-- -- There are a multitude of implementations of spec2 , depending on the choice of actions of spec1 that will be chosen in the covering.
-- -- For each behavior of spec1, one can construct an implementation of spec2 that permits this behavior. (Is this true ?) This is necessary to
-- -- be able to use the theorems of spec2 for the behaviors of spec1.

-- -- temporal restrictions on the other hand do not need to construct the actions of spec2. We simply take that behavior through the refinement mapping and check whether it
-- -- respects it.

