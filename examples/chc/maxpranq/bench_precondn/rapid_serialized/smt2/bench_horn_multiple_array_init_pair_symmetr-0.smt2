; main()
; {
;    i = 1 @l7
;    while (i < alength) @l9
;    {
;       a[i] = x @l12
;       b[i] = ((0) - (1)) * (x) @l13
;       i = (i) + (1) @l14
;    }
;    i = 0 @l16
;    while (i < alength) @l17
;    {
;       c[i] = (a[i]) + (b[i]) @l19
;       i = (i) + (1) @l20
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
(declare-const l7 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-const l16 Time)
(declare-fun l17 (Nat) Time)
(declare-const nl17 Nat)
(declare-fun l19 (Nat) Time)
(declare-fun l20 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l17 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l17 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l17 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l17 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l17 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l17 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l17 (Nat Nat Nat) Bool)

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
                  ;Update array variable a at location l12
                  (and
                     (= (a (l13 Itl9) (i (l9 Itl9))) x)
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (a (l13 Itl9) pos) (a (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l13
                  (and
                     (= (b (l14 Itl9) (i (l9 Itl9))) (* (- 0 1) x))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (b (l14 Itl9) pos) (b (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l9 (s Itl9)) pos) (b (l14 Itl9) pos))
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l9 (s Itl9)) pos) (a (l13 Itl9) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) alength)
         )
      )
      ;Loop at location l17
      (and
         ;Define variable values at beginning of loop
         (= (i (l17 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl17 Nat))
            (=>
               (Sub Itl17 nl17)
               (< (i (l17 Itl17)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl17 Nat))
            (=>
               (Sub Itl17 nl17)
               (and
                  ;Update array variable c at location l19
                  (and
                     (= (c (l20 Itl17) (i (l17 Itl17))) (+ (a (l9 nl9) (i (l17 Itl17))) (b (l9 nl9) (i (l17 Itl17)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l17 Itl17)))
                           )
                           (= (c (l20 Itl17) pos) (c (l17 Itl17) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l17 (s Itl17))) (+ (i (l17 Itl17)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l17 (s Itl17)) pos) (c (l20 Itl17) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l17 nl17)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l17 nl17)))
         (forall ((pos Int))
            (= (c main_end pos) (c (l17 nl17) pos))
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

; Definition: Premise for value-evolution-eq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (<= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (<= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (>= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (>= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l17 pos boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (= (c (l17 boundL) pos) (c (l17 Itl17) pos))
               )
               (= (c (l17 boundL) pos) (c (l17 (s Itl17)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l17 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l17 boundL) pos) (c (l17 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l17 pos boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (<= (c (l17 boundL) pos) (c (l17 Itl17) pos))
               )
               (<= (c (l17 boundL) pos) (c (l17 (s Itl17)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l17 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l17 boundL) pos) (c (l17 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l17 pos boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (>= (c (l17 boundL) pos) (c (l17 Itl17) pos))
               )
               (>= (c (l17 boundL) pos) (c (l17 (s Itl17)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l17
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l17 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l17 boundL) pos) (c (l17 boundR) pos))
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

; Definition: Dense for i-l17
(assert
   (=
      Dense-i-l17
      (forall ((Itl17 Nat))
         (=>
            (Sub Itl17 nl17)
            (or
               (= (i (l17 (s Itl17))) (i (l17 Itl17)))
               (= (i (l17 (s Itl17))) (+ (i (l17 Itl17)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l17
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l17 xInt)
         (and
            (<= (i (l17 zero)) xInt)
            (< xInt (i (l17 nl17)))
            Dense-i-l17
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l17
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l17 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl17)
               (= (i (l17 it)) xInt)
               (= (i (l17 (s it))) (+ (i (l17 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-i-l17
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l17
            (= (i (l17 (s it1))) (+ (i (l17 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl17))
         )
         (not
            (= (i (l17 it1)) (i (l17 it2)))
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

; Axiom: already-proven-lemma atLeastOneIteration-l17
(assert
   (=>
      (< (i (l17 zero)) alength)
      (exists ((Itl17 Nat))
         (= (s Itl17) nl17)
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
         (= 0 (c main_end pos))
      )
   )
)

(check-sat)

