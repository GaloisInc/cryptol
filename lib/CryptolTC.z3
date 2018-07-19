; ------------------------------------------------------------------------------
; Basic datatypes

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

; ------------------------------------------------------------------------------
; Cryptol version of logic


(define-fun cryEq ((x InfNat) (y InfNat)) MaybeBool
  (ite (or (isErr x) (isErr y)) cryErrProp (cryBool
  (ite (isFin x)
     (ite (isFin y) (= (value x) (value y)) false)
     (not (isFin y))
  )))
)

(define-fun cryNeq ((x InfNat) (y InfNat)) MaybeBool
  (ite (or (isErr x) (isErr y)) cryErrProp (cryBool
  (ite (isFin x)
     (ite (isFin y) (not (= (value x) (value y))) true)
     (isFin y)
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

; ------------------------------------------------------------------------------
; Basic Cryptol assume/assert


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



; ------------------------------------------------------------------------------
; Arithmetic


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

; Some axioms about cryWidthUnknown

(assert (forall ((x Int)) (> (cryWidthUnknown x) 64)))
(assert (forall ((x Int)) (or (> x (cryWidthUnknown x))
                              (< x 18446744073709551616))))
(assert (forall ((x Int) (y Int))
  (=> (and (>= x y) (> y 64))
      (>= (cryWidthUnknown x) (cryWidthUnknown y)))))


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
  (ite (< x 2048) 11
  (ite (< x 4096) 12
  (ite (< x 8192) 13
  (ite (< x 16384) 14
  (ite (< x 32768) 15
  (ite (< x 65536) 16
  (ite (< x 131072) 17
  (ite (< x 262144) 18
  (ite (< x 524288) 19
  (ite (< x 1048576) 20
  (ite (< x 2097152) 21
  (ite (< x 4194304) 22
  (ite (< x 8388608) 23
  (ite (< x 16777216) 24
  (ite (< x 33554432) 25
  (ite (< x 67108864) 26
  (ite (< x 134217728) 27
  (ite (< x 268435456) 28
  (ite (< x 536870912) 29
  (ite (< x 1073741824) 30
  (ite (< x 2147483648) 31
  (ite (< x 4294967296) 32
  (ite (< x 8589934592) 33
  (ite (< x 17179869184) 34
  (ite (< x 34359738368) 35
  (ite (< x 68719476736) 36
  (ite (< x 137438953472) 37
  (ite (< x 274877906944) 38
  (ite (< x 549755813888) 39
  (ite (< x 1099511627776) 40
  (ite (< x 2199023255552) 41
  (ite (< x 4398046511104) 42
  (ite (< x 8796093022208) 43
  (ite (< x 17592186044416) 44
  (ite (< x 35184372088832) 45
  (ite (< x 70368744177664) 46
  (ite (< x 140737488355328) 47
  (ite (< x 281474976710656) 48
  (ite (< x 562949953421312) 49
  (ite (< x 1125899906842624) 50
  (ite (< x 2251799813685248) 51
  (ite (< x 4503599627370496) 52
  (ite (< x 9007199254740992) 53
  (ite (< x 18014398509481984) 54
  (ite (< x 36028797018963968) 55
  (ite (< x 72057594037927936) 56
  (ite (< x 144115188075855872) 57
  (ite (< x 288230376151711744) 58
  (ite (< x 576460752303423488) 59
  (ite (< x 1152921504606846976) 60
  (ite (< x 2305843009213693952) 61
  (ite (< x 4611686018427387904) 62
  (ite (< x 9223372036854775808) 63
  (ite (< x 18446744073709551616) 64
  (cryWidthUnknown x))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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

(define-fun cryCeilDiv ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y) (not (isFin x)) (not (isFin y))) cryErr
  (ite (= (value y) 0) cryErr (cryNat (- (div (- (value x)) (value y)))))
  )
)

(define-fun cryCeilMod ((x InfNat) (y InfNat)) InfNat
  (ite (or (isErr x) (isErr y) (not (isFin x)) (not (isFin y))) cryErr
  (ite (= (value y) 0) cryErr (cryNat (mod (- (value x)) (value y))))
  )
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


