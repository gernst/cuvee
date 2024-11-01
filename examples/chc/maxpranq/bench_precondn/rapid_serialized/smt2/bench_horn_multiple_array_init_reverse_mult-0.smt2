; main()
; {
;    i = 1 @l6
;    while (i < alength) @l7
;    {
;       a[i] = 1 @l9
;       i = (i) + (1) @l10
;    }
;    i = (alength) - (1) @l12
;    while (i >= 0) @l13
;    {
;       a[i] = (a[i]) - (1) @l15
;       i = (i) - (1) @l16
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const l6 Time)
(declare-fun l7 (Nat) Time)
(declare-const nl7 Nat)
(declare-fun l9 (Nat) Time)
(declare-fun l10 (Nat) Time)
(declare-const l12 Time)
(declare-fun l13 (Nat) Time)
(declare-const nl13 Nat)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l7 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l7 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l7 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l7 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l7 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l7 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l7 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l7 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l13 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l7
      (and
         ;Define variable values at beginning of loop
         (= (i (l7 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl7 Nat))
            (=>
               (Sub Itl7 nl7)
               (< (i (l7 Itl7)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl7 Nat))
            (=>
               (Sub Itl7 nl7)
               (and
                  ;Update array variable a at location l9
                  (and
                     (= (a (l10 Itl7) (i (l7 Itl7))) 1)
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l7 Itl7)))
                           )
                           (= (a (l10 Itl7) pos) (a (l7 Itl7) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l7 (s Itl7))) (+ (i (l7 Itl7)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l7 (s Itl7)) pos) (a (l10 Itl7) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l7 nl7)) alength)
         )
      )
      ;Loop at location l13
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l13 zero)) (- alength 1))
            (forall ((pos Int))
               (= (a (l13 zero) pos) (a (l7 nl7) pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (>= (i (l13 Itl13)) 0)
            )
         )
         ;Semantics of the body
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (and
                  ;Update array variable a at location l15
                  (and
                     (= (a (l16 Itl13) (i (l13 Itl13))) (- (a (l13 Itl13) (i (l13 Itl13))) 1))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l13 Itl13)))
                           )
                           (= (a (l16 Itl13) pos) (a (l13 Itl13) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l13 (s Itl13))) (- (i (l13 Itl13)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l13 (s Itl13)) pos) (a (l16 Itl13) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (>= (i (l13 nl13)) 0)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l13 nl13)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l13 nl13) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (<= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (<= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l7 boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (>= (i (l7 boundL)) (i (l7 Itl7)))
               )
               (>= (i (l7 boundL)) (i (l7 (s Itl7))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l7
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l7 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l7 boundL)) (i (l7 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (<= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (<= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l7 pos boundL boundR)
         (forall ((Itl7 Nat))
            (=>
               (and
                  (Sub boundL (s Itl7))
                  (Sub Itl7 boundR)
                  (>= (a (l7 boundL) pos) (a (l7 Itl7) pos))
               )
               (>= (a (l7 boundL) pos) (a (l7 (s Itl7)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l7
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l7 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l7 boundL) pos) (a (l7 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (<= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (>= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (a (l13 boundL) pos) (a (l13 Itl13) pos))
               )
               (= (a (l13 boundL) pos) (a (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l13 boundL) pos) (a (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (a (l13 boundL) pos) (a (l13 Itl13) pos))
               )
               (<= (a (l13 boundL) pos) (a (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l13 boundL) pos) (a (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (a (l13 boundL) pos) (a (l13 Itl13) pos))
               )
               (>= (a (l13 boundL) pos) (a (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l13 boundL) pos) (a (l13 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l7
(assert
   (=
      Dense-i-l7
      (forall ((Itl7 Nat))
         (=>
            (Sub Itl7 nl7)
            (or
               (= (i (l7 (s Itl7))) (i (l7 Itl7)))
               (= (i (l7 (s Itl7))) (+ (i (l7 Itl7)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l7
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l7 xInt)
         (and
            (<= (i (l7 zero)) xInt)
            (< xInt (i (l7 nl7)))
            Dense-i-l7
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l7
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l7 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl7)
               (= (i (l7 it)) xInt)
               (= (i (l7 (s it))) (+ (i (l7 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l13
(assert
   (=
      Dense-i-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (i (l13 (s Itl13))) (i (l13 Itl13)))
               (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l13 xInt)
         (and
            (<= (i (l13 zero)) xInt)
            (< xInt (i (l13 nl13)))
            Dense-i-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (i (l13 it)) xInt)
               (= (i (l13 (s it))) (+ (i (l13 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l7
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l7
            (= (i (l7 (s it1))) (+ (i (l7 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl7))
         )
         (not
            (= (i (l7 it1)) (i (l7 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l13
            (= (i (l13 (s it1))) (+ (i (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (i (l13 it1)) (i (l13 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l7
(assert
   (=>
      (< (i (l7 zero)) alength)
      (exists ((Itl7 Nat))
         (= (s Itl7) nl7)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l13
(assert
   (=>
      (>= (i (l13 zero)) 0)
      (exists ((Itl13 Nat))
         (= (s Itl13) nl13)
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
         (= 0 (a main_end pos))
      )
   )
)

(check-sat)

