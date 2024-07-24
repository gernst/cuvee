; main()
; {
;    i = 1 @l6
;    while (i < alength) @l8
;    {
;       a[i] = x @l11
;       b[i] = ((0) - (1)) * (x) @l12
;       i = (i) + (1) @l13
;    }
;    i = 0 @l15
;    while (i < alength) @l16
;    {
;       tmp = a[i] @l18
;       a[i] = ((0) - (1)) * (b[i]) @l19
;       b[i] = tmp @l20
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
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const x Int)
(declare-fun tmp (Time) Int)
(declare-const l6 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-const l15 Time)
(declare-fun l16 (Nat) Time)
(declare-const nl16 Nat)
(declare-fun l18 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-fun l20 (Nat) Time)
(declare-fun l21 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l8 (Int Nat Nat) Bool)
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
(declare-lemma-predicate BC-AxEvol-eq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l16 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l16 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l16 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l16 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l16 (Nat Nat Nat) Bool)

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
               (and
                  ;Update array variable a at location l11
                  (and
                     (= (a (l12 Itl8) (i (l8 Itl8))) x)
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l8 Itl8)))
                           )
                           (= (a (l12 Itl8) pos) (a (l8 Itl8) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l12
                  (and
                     (= (b (l13 Itl8) (i (l8 Itl8))) (* (- 0 1) x))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l8 Itl8)))
                           )
                           (= (b (l13 Itl8) pos) (b (l8 Itl8) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l8 (s Itl8)) pos) (b (l13 Itl8) pos))
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l8 (s Itl8)) pos) (a (l12 Itl8) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l8 nl8)) alength)
         )
      )
      ;Loop at location l16
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l16 zero)) 0)
            (forall ((pos Int))
               (= (b (l16 zero) pos) (b (l8 nl8) pos))
            )
            (forall ((pos Int))
               (= (a (l16 zero) pos) (a (l8 nl8) pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl16 Nat))
            (=>
               (Sub Itl16 nl16)
               (< (i (l16 Itl16)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl16 Nat))
            (=>
               (Sub Itl16 nl16)
               (and
                  ;Update array variable a at location l19
                  (and
                     (= (a (l20 Itl16) (i (l16 Itl16))) (* (- 0 1) (b (l16 Itl16) (i (l16 Itl16)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l16 Itl16)))
                           )
                           (= (a (l20 Itl16) pos) (a (l16 Itl16) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l20
                  (and
                     (= (b (l21 Itl16) (i (l16 Itl16))) (a (l16 Itl16) (i (l16 Itl16))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l16 Itl16)))
                           )
                           (= (b (l21 Itl16) pos) (b (l16 Itl16) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l16 (s Itl16))) (+ (i (l16 Itl16)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l16 (s Itl16)) pos) (b (l21 Itl16) pos))
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l16 (s Itl16)) pos) (a (l20 Itl16) pos))
                  )
                  ;Define value of variable tmp at beginning of next iteration
                  (= (tmp (l16 (s Itl16))) (a (l16 Itl16) (i (l16 Itl16))))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l16 nl16)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l16 nl16)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l16 nl16) pos))
         )
         (forall ((pos Int))
            (= (a main_end pos) (a (l16 nl16) pos))
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

; Definition: Premise for value-evolution-eq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l8 boundL) pos) (b (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (<= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l8 boundL) pos) (b (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (b (l8 boundL) pos) (b (l8 Itl8) pos))
               )
               (>= (b (l8 boundL) pos) (b (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l8 boundL) pos) (b (l8 boundR) pos))
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

; Definition: Premise for value-evolution-eq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (<= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (<= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (>= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (>= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (= (b (l16 boundL) pos) (b (l16 Itl16) pos))
               )
               (= (b (l16 boundL) pos) (b (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l16 boundL) pos) (b (l16 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (<= (b (l16 boundL) pos) (b (l16 Itl16) pos))
               )
               (<= (b (l16 boundL) pos) (b (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l16 boundL) pos) (b (l16 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (>= (b (l16 boundL) pos) (b (l16 Itl16) pos))
               )
               (>= (b (l16 boundL) pos) (b (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l16 boundL) pos) (b (l16 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (= (a (l16 boundL) pos) (a (l16 Itl16) pos))
               )
               (= (a (l16 boundL) pos) (a (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l16 boundL) pos) (a (l16 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (<= (a (l16 boundL) pos) (a (l16 Itl16) pos))
               )
               (<= (a (l16 boundL) pos) (a (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l16 boundL) pos) (a (l16 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l16 pos boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (>= (a (l16 boundL) pos) (a (l16 Itl16) pos))
               )
               (>= (a (l16 boundL) pos) (a (l16 (s Itl16)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l16
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l16 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l16 boundL) pos) (a (l16 boundR) pos))
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

; Definition: Dense for i-l16
(assert
   (=
      Dense-i-l16
      (forall ((Itl16 Nat))
         (=>
            (Sub Itl16 nl16)
            (or
               (= (i (l16 (s Itl16))) (i (l16 Itl16)))
               (= (i (l16 (s Itl16))) (+ (i (l16 Itl16)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l16
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l16 xInt)
         (and
            (<= (i (l16 zero)) xInt)
            (< xInt (i (l16 nl16)))
            Dense-i-l16
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l16
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l16 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl16)
               (= (i (l16 it)) xInt)
               (= (i (l16 (s it))) (+ (i (l16 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-i-l16
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l16
            (= (i (l16 (s it1))) (+ (i (l16 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl16))
         )
         (not
            (= (i (l16 it1)) (i (l16 it2)))
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

; Axiom: already-proven-lemma atLeastOneIteration-l16
(assert
   (=>
      (< (i (l16 zero)) alength)
      (exists ((Itl16 Nat))
         (= (s Itl16) nl16)
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
         (not
            (= (a main_end pos) (b main_end pos))
         )
      )
   )
)

(check-sat)

