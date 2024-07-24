; main()
; {
;    i = 1 @l7
;    while (i < alength) @l10
;    {
;       if (j <= k) @l13
;       {
;          a[i] = k @l14
;          i = (i) + (1) @l15
;       }
;       else
;       {
;          skip @l17
;       }
;    }
;    i = 0 @l20
;    while (i < alength) @l21
;    {
;       b[i] = (a[i]) - (j) @l23
;       i = (i) + (1) @l24
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Time Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const j Int)
(declare-const k Int)
(declare-const l7 Time)
(declare-fun l10 (Nat) Time)
(declare-const nl10 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l17 (Nat) Time)
(declare-const l20 Time)
(declare-fun l21 (Nat) Time)
(declare-const nl21 Nat)
(declare-fun l23 (Nat) Time)
(declare-fun l24 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l21 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l21 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l21 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l10
      (and
         ;Define variable values at beginning of loop
         (= (i (l10 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (< (i (l10 Itl10)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               ;Semantics of IfElse at location l13
               (and
                  ;Semantics of left branch
                  (=>
                     (<= j k)
                     (and
                        ;Update array variable a at location l14
                        (and
                           (= (a (l15 Itl10) (i (l10 Itl10))) k)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l10 Itl10)))
                                 )
                                 (= (a (l15 Itl10) pos) (a (l10 Itl10) pos))
                              )
                           )
                        )
                        (forall ((pos Int))
                           (= (a (l10 (s Itl10)) pos) (a (l15 Itl10) pos))
                        )
                        (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
                     )
                  )
                  ;Semantics of right branch
                  (=>
                     (not
                        (<= j k)
                     )
                     (and
                        (forall ((pos Int))
                           (= (a (l10 (s Itl10)) pos) (a (l10 Itl10) pos))
                        )
                        (= (i (l10 (s Itl10))) (i (l10 Itl10)))
                     )
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l10 nl10)) alength)
         )
      )
      ;Loop at location l21
      (and
         ;Define variable values at beginning of loop
         (= (i (l21 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (< (i (l21 Itl21)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (and
                  ;Update array variable b at location l23
                  (and
                     (= (b (l24 Itl21) (i (l21 Itl21))) (- (a (l10 nl10) (i (l21 Itl21))) j))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l21 Itl21)))
                           )
                           (= (b (l24 Itl21) pos) (b (l21 Itl21) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l21 (s Itl21)) pos) (b (l24 Itl21) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l21 nl21)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l21 nl21)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l21 nl21) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (<= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (>= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (<= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (>= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (<= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (>= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (<= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (>= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l10
(assert
   (=
      Dense-i-l10
      (forall ((Itl10 Nat))
         (=>
            (Sub Itl10 nl10)
            (or
               (= (i (l10 (s Itl10))) (i (l10 Itl10)))
               (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l10 xInt)
         (and
            (<= (i (l10 zero)) xInt)
            (< xInt (i (l10 nl10)))
            Dense-i-l10
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l10 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl10)
               (= (i (l10 it)) xInt)
               (= (i (l10 (s it))) (+ (i (l10 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l21
(assert
   (=
      Dense-i-l21
      (forall ((Itl21 Nat))
         (=>
            (Sub Itl21 nl21)
            (or
               (= (i (l21 (s Itl21))) (i (l21 Itl21)))
               (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l21 xInt)
         (and
            (<= (i (l21 zero)) xInt)
            (< xInt (i (l21 nl21)))
            Dense-i-l21
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l21 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl21)
               (= (i (l21 it)) xInt)
               (= (i (l21 (s it))) (+ (i (l21 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l10
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l10
            (= (i (l10 (s it1))) (+ (i (l10 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl10))
         )
         (not
            (= (i (l10 it1)) (i (l10 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l21
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l21
            (= (i (l21 (s it1))) (+ (i (l21 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl21))
         )
         (not
            (= (i (l21 it1)) (i (l21 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l10
(assert
   (=>
      (< (i (l10 zero)) alength)
      (exists ((Itl10 Nat))
         (= (s Itl10) nl10)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l21
(assert
   (=>
      (< (i (l21 zero)) alength)
      (exists ((Itl21 Nat))
         (= (s Itl21) nl21)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos alength)
            (<= alength (i main_end))
         )
         (>= (b main_end pos) 0)
      )
   )
)

(check-sat)

