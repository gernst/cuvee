; main()
; {
;    i = 1 @l6
;    while (i < alength) @l8
;    {
;       if (1 <= j) @l11
;       {
;          a[i] = j @l12
;          i = (i) + (1) @l13
;       }
;       else
;       {
;          skip @l15
;       }
;    }
;    i = 0 @l18
;    while (i < alength) @l19
;    {
;       b[i] = a[i] @l21
;       i = (i) + (1) @l22
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
(declare-const l6 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-const l18 Time)
(declare-fun l19 (Nat) Time)
(declare-const nl19 Nat)
(declare-fun l21 (Nat) Time)
(declare-fun l22 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l19 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l19 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l19 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l8
      (and
         ;Define variable values at beginning of loop
         (= (i (l8 zero)) 1)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (< (i (l8 Itl8)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               ;Semantics of IfElse at location l11
               (and
                  ;Semantics of left branch
                  (=>
                     (<= 1 j)
                     (and
                        ;Update array variable a at location l12
                        (and
                           (= (a (l13 Itl8) (i (l8 Itl8))) j)
                           (forall ((pos Int))
                              (=>
                                 (not
                                    (= pos (i (l8 Itl8)))
                                 )
                                 (= (a (l13 Itl8) pos) (a (l8 Itl8) pos))
                              )
                           )
                        )
                        (forall ((pos Int))
                           (= (a (l8 (s Itl8)) pos) (a (l13 Itl8) pos))
                        )
                        (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
                     )
                  )
                  ;Semantics of right branch
                  (=>
                     (not
                        (<= 1 j)
                     )
                     (and
                        (forall ((pos Int))
                           (= (a (l8 (s Itl8)) pos) (a (l8 Itl8) pos))
                        )
                        (= (i (l8 (s Itl8))) (i (l8 Itl8)))
                     )
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l8 nl8)) alength)
         )
      )
      ;Loop at location l19
      (and
         ;Define variable values at beginning of loop
         (= (i (l19 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (< (i (l19 Itl19)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (and
                  ;Update array variable b at location l21
                  (and
                     (= (b (l22 Itl19) (i (l19 Itl19))) (a (l8 nl8) (i (l19 Itl19))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l19 Itl19)))
                           )
                           (= (b (l22 Itl19) pos) (b (l19 Itl19) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l19 (s Itl19)) pos) (b (l22 Itl19) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l19 nl19)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l19 nl19)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l19 nl19) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (<= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (>= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (<= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (>= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (<= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (>= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (<= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (>= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l8
(assert
   (=
      Dense-i-l8
      (forall ((Itl8 Nat))
         (=>
            (Sub Itl8 nl8)
            (or
               (= (i (l8 (s Itl8))) (i (l8 Itl8)))
               (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l8 xInt)
         (and
            (<= (i (l8 zero)) xInt)
            (< xInt (i (l8 nl8)))
            Dense-i-l8
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l8 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl8)
               (= (i (l8 it)) xInt)
               (= (i (l8 (s it))) (+ (i (l8 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l19
(assert
   (=
      Dense-i-l19
      (forall ((Itl19 Nat))
         (=>
            (Sub Itl19 nl19)
            (or
               (= (i (l19 (s Itl19))) (i (l19 Itl19)))
               (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l19 xInt)
         (and
            (<= (i (l19 zero)) xInt)
            (< xInt (i (l19 nl19)))
            Dense-i-l19
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l19 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl19)
               (= (i (l19 it)) xInt)
               (= (i (l19 (s it))) (+ (i (l19 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l8
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l8
            (= (i (l8 (s it1))) (+ (i (l8 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl8))
         )
         (not
            (= (i (l8 it1)) (i (l8 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l19
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l19
            (= (i (l19 (s it1))) (+ (i (l19 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl19))
         )
         (not
            (= (i (l19 it1)) (i (l19 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l8
(assert
   (=>
      (< (i (l8 zero)) alength)
      (exists ((Itl8 Nat))
         (= (s Itl8) nl8)
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l19
(assert
   (=>
      (< (i (l19 zero)) alength)
      (exists ((Itl19 Nat))
         (= (s Itl19) nl19)
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
         (<= 1 (b main_end pos))
      )
   )
)

(check-sat)

