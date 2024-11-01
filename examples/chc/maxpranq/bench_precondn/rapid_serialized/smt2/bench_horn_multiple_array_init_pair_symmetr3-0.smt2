; main()
; {
;    i = 1 @l7
;    while (i < alength) @l9
;    {
;       a[i] = (alength) + (x) @l13
;       b[i] = x @l14
;       i = (i) + (1) @l15
;    }
;    i = 0 @l17
;    while (i < alength) @l18
;    {
;       c[i] = (a[i]) - (b[i]) @l20
;       i = (i) + (1) @l21
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Time Int) Int)
(declare-fun c (Time Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const l7 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-const l17 Time)
(declare-fun l18 (Nat) Time)
(declare-const nl18 Nat)
(declare-fun l20 (Nat) Time)
(declare-fun l21 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l18 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l18 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l18 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l18 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (= (i (l9 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (i (l9 Itl9)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (and
                  ;Update array variable a at location l13
                  (and
                     (= (a (l14 Itl9) (i (l9 Itl9))) (+ alength x))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (a (l14 Itl9) pos) (a (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l14
                  (and
                     (= (b (l15 Itl9) (i (l9 Itl9))) x)
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (b (l15 Itl9) pos) (b (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l9 (s Itl9)) pos) (b (l15 Itl9) pos))
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l9 (s Itl9)) pos) (a (l14 Itl9) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) alength)
         )
      )
      ;Loop at location l18
      (and
         ;Define variable values at beginning of loop
         (= (i (l18 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (< (i (l18 Itl18)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (and
                  ;Update array variable c at location l20
                  (and
                     (= (c (l21 Itl18) (i (l18 Itl18))) (- (a (l9 nl9) (i (l18 Itl18))) (b (l9 nl9) (i (l18 Itl18)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l18 Itl18)))
                           )
                           (= (c (l21 Itl18) pos) (c (l18 Itl18) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l18 (s Itl18)) pos) (c (l21 Itl18) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l18 nl18)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l18 nl18)))
         (forall ((pos Int))
            (= (c main_end pos) (c (l18 nl18) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (<= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (>= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (<= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (>= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (<= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (>= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (<= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (>= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (c (l18 boundL) pos) (c (l18 Itl18) pos))
               )
               (= (c (l18 boundL) pos) (c (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l18 boundL) pos) (c (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (c (l18 boundL) pos) (c (l18 Itl18) pos))
               )
               (<= (c (l18 boundL) pos) (c (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l18 boundL) pos) (c (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (c (l18 boundL) pos) (c (l18 Itl18) pos))
               )
               (>= (c (l18 boundL) pos) (c (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l18 boundL) pos) (c (l18 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l9
(assert
   (=
      Dense-i-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (i (l9 (s Itl9))) (i (l9 Itl9)))
               (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l9 xInt)
         (and
            (<= (i (l9 zero)) xInt)
            (< xInt (i (l9 nl9)))
            Dense-i-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (i (l9 it)) xInt)
               (= (i (l9 (s it))) (+ (i (l9 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l18
(assert
   (=
      Dense-i-l18
      (forall ((Itl18 Nat))
         (=>
            (Sub Itl18 nl18)
            (or
               (= (i (l18 (s Itl18))) (i (l18 Itl18)))
               (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l18 xInt)
         (and
            (<= (i (l18 zero)) xInt)
            (< xInt (i (l18 nl18)))
            Dense-i-l18
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l18 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl18)
               (= (i (l18 it)) xInt)
               (= (i (l18 (s it))) (+ (i (l18 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l9
            (= (i (l9 (s it1))) (+ (i (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (i (l9 it1)) (i (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l18
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l18
            (= (i (l18 (s it1))) (+ (i (l18 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl18))
         )
         (not
            (= (i (l18 it1)) (i (l18 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (i (l9 zero)) alength)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l18
(assert
   (=>
      (< (i (l18 zero)) alength)
      (exists ((Itl18 Nat))
         (= (s Itl18) nl18)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
            (< pos alength)
            (<= alength (i main_end))
         )
         (= alength (c main_end pos))
      )
   )
)

(check-sat)

