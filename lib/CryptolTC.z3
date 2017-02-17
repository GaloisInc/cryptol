
(declare-datatypes ()
  ( (InfNat (mk-infnat (value Int) (isFin Bool) (isErr Bool)))
  )
)

(declare-datatypes ()
  ( (MaybeBool (mk-mb (prop Bool) (isErrorProp Bool)))
  )
)

(define-fun cryBool ((x Bool)) MaybeBool
  (mk-mb x false)
)

(define-fun cryErrProp () MaybeBool
  (mk-mb false true)
)

(define-fun cryInf () InfNat
  (mk-infnat 0 false false)
)

(define-fun cryNat ((x Int)) InfNat
  (mk-infnat x true false)
)

(define-fun cryErr () InfNat
  (mk-infnat 0 false true)
)

; ------------------------------------------------------------

(define-fun cryEq ((x InfNat) (y InfNat)) MaybeBool
  (ite (or (isErr x) (isErr y)) cryErrProp (cryBool
  (ite (isFin x)
     (ite (isFin y) (= (value x) (value y)) false)
     (not (isFin y))
  )))
)

(define-fun cryFin ((x InfNat)) MaybeBool
  (ite (isErr x) cryErrProp (cryBool
  (isFin x)))
)

(define-fun cryGeq ((x InfNat) (y InfNat)) MaybeBool
  (ite (or (isErr x) (isErr y)) cryErrProp (cryBool
  (ite (isFin x)
    (ite (isFin y) (>= (value x) (value y)) false)
    true
  )))
)

(define-fun cryAnd ((x MaybeBool) (y MaybeBool)) MaybeBool
  (ite (or (isErrorProp x) (isErrorProp y)) cryErrProp
    (cryBool (and (prop x) (prop y)))
  )
)

(define-fun cryTrue () MaybeBool
  (cryBool true)
)

; -----------------------------------------------------

(define-fun cryVar ((x InfNat)) Bool
  (and (not (isErr x)) (>= (value x) 0))
)

(define-fun cryAssume ((x MaybeBool)) Bool
  (ite (isErrorProp x) true (prop x))
)

(declare-fun cryUnknown () Bool)

(define-fun cryProve ((x MaybeBool)) Bool
  (ite (isErrorProp x) cryUnknown (not (prop x)))
)

; ------------------------------------------------------------

(define-fun cryAdd ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y)) cryErr
  (ite (isFin x)
       (ite (isFin y) (cryNat (+ (value x) (value y))) cryInf)
       cryInf
  ))
)

(define-fun crySub ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y) (not (isFin y))) cryErr
  (ite (isFin x)
       (ite (>= (value x) (value y)) (cryNat (- (value x) (value y))) cryErr)
       cryInf
  ))
)

(define-fun cryMul ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y)) cryErr
  (ite (isFin x)
       (ite (isFin y) (cryNat (* (value x) (value y)))
                      (ite (= (value x) 0) (cryNat 0) cryInf))
       (ite (and (isFin y) (= (value y) 0)) (cryNat 0) cryInf)
  ))
)

(define-fun cryDiv ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y) (not (isFin x))) cryErr
  (ite (isFin y)
       (ite (= (value y) 0) cryErr (cryNat (div (value x) (value y))))
       (cryNat 0)
  ))
)

(define-fun cryMod ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y) (not (isFin x))) cryErr
  (ite (isFin y)
       (ite (= (value y) 0) cryErr (cryNat (mod (value x) (value y))))
       x
  ))
)



(define-fun cryMin ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y)) cryErr
  (ite (isFin x)
       (ite (isFin y)
            (ite (<= (value x) (value y)) x y)
            x)
       y
  ))
)

(define-fun cryMax ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y)) cryErr
  (ite (isFin x)
       (ite (isFin y)
            (ite (<= (value x) (value y)) y x)
            y)
       x
  ))
)

(declare-fun cryWidthUnknown (Int) Int)

(define-fun cryWidthTable ((x Int)) Int
  (ite (< x 1) 0
  (ite (< x 2) 1
  (ite (< x 4) 2
  (ite (< x 8) 3
  (ite (< x 16) 4
  (ite (< x 32) 5
  (ite (< x 64) 6
  (ite (< x 128) 7
  (ite (< x 256) 8
  (ite (< x 512) 9
  (ite (< x 1024) 10
  (cryWidthUnknown x))))))))))))
)

(define-fun cryWidth ((x InfNat)) InfNat
  (ite (isErr x) cryErr
  (ite (isFin x) (cryNat (cryWidthTable (value x)))
       cryInf
  ))
)

(declare-fun cryExpUnknown (Int Int) Int)

(define-fun cryExpTable ((x Int) (y Int)) Int
  (ite (= y 0) 1
  (ite (= y 1) x
  (ite (= x 0) 0
  (cryExpUnknown x y))))
)

(define-fun cryExp ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y)) cryErr
    (ite (isFin x)
         (ite (isFin y)
              (cryNat (cryExpTable (value x) (value y)))
              (ite (< (value x) 2) x cryInf))
         (ite (isFin y)
              (ite (= (value y) 0) (cryNat 1) cryInf)
              cryInf)
  ))
)

(define-fun cryLenFromThenTo ((x InfNat) (y InfNat) (z InfNat)) InfNat
  (ite (or (isErr x) (not (isFin x))
           (isErr y) (not (isFin y))
           (isErr z) (not (isFin z))
           (= (value x) (value y))) cryErr (cryNat
  (ite (> (value x) (value y))
       (ite (> (value z) (value x)) 0 (+ (div (- (value x) (value z))
                                              (- (value x) (value y))) 1))
       (ite (< (value z) (value x)) 0 (+ (div (- (value z) (value x))
                                              (- (value y) (value x))) 1))
  )))
)


(define-fun cryLenFromThen ((x InfNat) (y InfNat) (z InfNat)) InfNat
  (ite (or (isErr x) (not (isFin x))
           (isErr y) (not (isFin y))
           (isErr z) (not (isFin z))
           (= (value x) (value y))) cryErr
  (ite (< (value y) (value x)) (cryLenFromThenTo x y (cryNat 0))
       (cryLenFromThenTo x y (cryNat (- (cryExpTable 2 (value z)) 1))))
  )
)

; -------------------


