(set-option :print-success true)

(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
; (set-option :model_compress false)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun rmodeType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun rmode_2_U (RoundingMode) T@U)
(declare-fun U_2_rmode (T@U) RoundingMode)
(declare-fun TyType () T@T)
(declare-fun TBool () T@U)
(declare-fun TChar () T@U)
(declare-fun TInt () T@U)
(declare-fun TReal () T@U)
(declare-fun TORDINAL () T@U)
(declare-fun TyTagType () T@T)
(declare-fun TagBool () T@U)
(declare-fun TagChar () T@U)
(declare-fun TagInt () T@U)
(declare-fun TagReal () T@U)
(declare-fun TagORDINAL () T@U)
(declare-fun TagSet () T@U)
(declare-fun TagISet () T@U)
(declare-fun TagMultiSet () T@U)
(declare-fun TagSeq () T@U)
(declare-fun TagMap () T@U)
(declare-fun TagIMap () T@U)
(declare-fun TagClass () T@U)
(declare-fun ClassNameType () T@T)
(declare-fun NoTraitAtAll () T@U)
(declare-fun class._System.int () T@U)
(declare-fun class._System.bool () T@U)
(declare-fun class._System.set () T@U)
(declare-fun class._System.seq () T@U)
(declare-fun class._System.multiset () T@U)
(declare-fun FieldType (T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun alloc () T@U)
(declare-fun NameFamilyType () T@T)
(declare-fun allocName () T@U)
(declare-fun Tagclass._System.nat () T@U)
(declare-fun class._System.object? () T@U)
(declare-fun Tagclass._System.object? () T@U)
(declare-fun Tagclass._System.object () T@U)
(declare-fun class._System.array? () T@U)
(declare-fun Tagclass._System.array? () T@U)
(declare-fun Tagclass._System.array () T@U)
(declare-fun Tagclass._System.___hFunc0 () T@U)
(declare-fun Tagclass._System.___hPartialFunc0 () T@U)
(declare-fun Tagclass._System.___hTotalFunc0 () T@U)
(declare-fun Tagclass._System.___hFunc2 () T@U)
(declare-fun Tagclass._System.___hPartialFunc2 () T@U)
(declare-fun Tagclass._System.___hTotalFunc2 () T@U)
(declare-fun class._System.Tuple2 () T@U)
(declare-fun DtCtorIdType () T@T)
(declare-fun |##_System._tuple#2._#Make2| () T@U)
(declare-fun Tagclass._System.Tuple2 () T@U)
(declare-fun Tagclass._System.___hFunc1 () T@U)
(declare-fun Tagclass._System.___hPartialFunc1 () T@U)
(declare-fun Tagclass._System.___hTotalFunc1 () T@U)
(declare-fun class._System.Tuple0 () T@U)
(declare-fun |##_System._tuple#0._#Make0| () T@U)
(declare-fun Tagclass._System.Tuple0 () T@U)
(declare-fun class._module.__default () T@U)
(declare-fun Tagclass._module.__default () T@U)
(declare-fun $$Language$Dafny () Bool)
(declare-fun TBitvector (Int) T@U)
(declare-fun Inv0_TBitvector (T@U) Int)
(declare-fun TSet (T@U) T@U)
(declare-fun Inv0_TSet (T@U) T@U)
(declare-fun TISet (T@U) T@U)
(declare-fun Inv0_TISet (T@U) T@U)
(declare-fun TSeq (T@U) T@U)
(declare-fun Inv0_TSeq (T@U) T@U)
(declare-fun TMultiSet (T@U) T@U)
(declare-fun Inv0_TMultiSet (T@U) T@U)
(declare-fun TMap (T@U T@U) T@U)
(declare-fun Inv0_TMap (T@U) T@U)
(declare-fun Inv1_TMap (T@U) T@U)
(declare-fun TIMap (T@U T@U) T@U)
(declare-fun Inv0_TIMap (T@U) T@U)
(declare-fun Inv1_TIMap (T@U) T@U)
(declare-fun Tag (T@U) T@U)
(declare-fun LitInt (Int) Int)
(declare-fun BoxType () T@T)
(declare-fun $Box (T@U) T@U)
(declare-fun Lit (T@U) T@U)
(declare-fun LitReal (Real) Real)
(declare-fun charType () T@T)
(declare-fun |char#FromInt| (Int) T@U)
(declare-fun |char#ToInt| (T@U) Int)
(declare-fun |char#Plus| (T@U T@U) T@U)
(declare-fun |char#Minus| (T@U T@U) T@U)
(declare-fun $Unbox (T@T T@U) T@U)
(declare-fun $IsBox (T@U T@U) Bool)
(declare-fun $Is (T@U T@U) Bool)
(declare-fun MapType0Type (T@T T@T) T@T)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0TypeInv1 (T@T) T@T)
(declare-fun MapType0Select (T@U T@U) T@U)
(declare-fun MapType0Store (T@U T@U T@U) T@U)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun MapType (T@T T@T) T@T)
(declare-fun MapTypeInv0 (T@T) T@T)
(declare-fun MapTypeInv1 (T@T) T@T)
(declare-fun IMapType (T@T T@T) T@T)
(declare-fun IMapTypeInv0 (T@T) T@T)
(declare-fun IMapTypeInv1 (T@T) T@T)
(declare-fun MapType1Type (T@T) T@T)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun MapType1Select (T@U T@U T@U) T@U)
(declare-fun MapType1Store (T@U T@U T@U T@U) T@U)
(declare-fun refType () T@T)
(declare-fun $IsAllocBox (T@U T@U T@U) Bool)
(declare-fun $IsAlloc (T@U T@U T@U) Bool)
(declare-fun $IsGoodMultiSet (T@U) Bool)
(declare-fun |Seq#Index| (T@U Int) T@U)
(declare-fun |Seq#Length| (T@U) Int)
(declare-fun |Map#Elements| (T@U) T@U)
(declare-fun |Map#Domain| (T@U) T@U)
(declare-fun |IMap#Elements| (T@U) T@U)
(declare-fun |IMap#Domain| (T@U) T@U)
(declare-fun TypeTuple (T@U T@U) T@U)
(declare-fun TypeTupleCar (T@U) T@U)
(declare-fun TypeTupleCdr (T@U) T@U)
(declare-fun SetRef_to_SetBox (T@U) T@U)
(declare-fun Tclass._System.object? () T@U)
(declare-fun DatatypeTypeType () T@T)
(declare-fun BoxRank (T@U) Int)
(declare-fun DtRank (T@U) Int)
(declare-fun |ORD#Offset| (T@U) Int)
(declare-fun |ORD#FromNat| (Int) T@U)
(declare-fun |ORD#IsNat| (T@U) Bool)
(declare-fun |ORD#Less| (T@U T@U) Bool)
(declare-fun |ORD#LessThanLimit| (T@U T@U) Bool)
(declare-fun |ORD#Plus| (T@U T@U) T@U)
(declare-fun |ORD#Minus| (T@U T@U) T@U)
(declare-fun LayerTypeType () T@T)
(declare-fun AtLayer (T@U T@U) T@U)
(declare-fun $LS (T@U) T@U)
(declare-fun IndexField (Int) T@U)
(declare-fun FDim (T@U) Int)
(declare-fun IndexField_Inverse (T@U) Int)
(declare-fun MultiIndexField (T@U Int) T@U)
(declare-fun MultiIndexField_Inverse0 (T@U) T@U)
(declare-fun MultiIndexField_Inverse1 (T@U) Int)
(declare-fun FieldOfDecl (T@T T@U T@U) T@U)
(declare-fun DeclType (T@U) T@U)
(declare-fun DeclName (T@U) T@U)
(declare-fun $HeapSucc (T@U T@U) Bool)
(declare-fun $IsGhostField (T@U) Bool)
(declare-fun _System.array.Length (T@U) Int)
(declare-fun q@Int (Real) Int)
(declare-fun q@Real (Int) Real)
(declare-fun $OneHeap () T@U)
(declare-fun $IsGoodHeap (T@U) Bool)
(declare-fun $HeapSuccGhost (T@U T@U) Bool)
(declare-fun |Set#Card| (T@U) Int)
(declare-fun |Set#Empty| (T@T) T@U)
(declare-fun |Set#Singleton| (T@U) T@U)
(declare-fun |Set#UnionOne| (T@U T@U) T@U)
(declare-fun |Set#Union| (T@U T@U) T@U)
(declare-fun |Set#Difference| (T@U T@U) T@U)
(declare-fun |Set#Disjoint| (T@U T@U) Bool)
(declare-fun |Set#Intersection| (T@U T@U) T@U)
(declare-fun |Set#Subset| (T@U T@U) Bool)
(declare-fun |Set#Equal| (T@U T@U) Bool)
(declare-fun |ISet#Empty| (T@T) T@U)
(declare-fun |ISet#UnionOne| (T@U T@U) T@U)
(declare-fun |ISet#Union| (T@U T@U) T@U)
(declare-fun |ISet#Difference| (T@U T@U) T@U)
(declare-fun |ISet#Disjoint| (T@U T@U) Bool)
(declare-fun |ISet#Intersection| (T@U T@U) T@U)
(declare-fun |ISet#Subset| (T@U T@U) Bool)
(declare-fun |ISet#Equal| (T@U T@U) Bool)
(declare-fun |Math#min| (Int Int) Int)
(declare-fun |Math#clip| (Int) Int)
(declare-fun |MultiSet#Card| (T@U) Int)
(declare-fun |MultiSet#Empty| (T@T) T@U)
(declare-fun |MultiSet#Singleton| (T@U) T@U)
(declare-fun |MultiSet#UnionOne| (T@U T@U) T@U)
(declare-fun |MultiSet#Union| (T@U T@U) T@U)
(declare-fun |MultiSet#Intersection| (T@U T@U) T@U)
(declare-fun |MultiSet#Difference| (T@U T@U) T@U)
(declare-fun |MultiSet#Subset| (T@U T@U) Bool)
(declare-fun |MultiSet#Equal| (T@U T@U) Bool)
(declare-fun |MultiSet#Disjoint| (T@U T@U) Bool)
(declare-fun |MultiSet#FromSet| (T@U) T@U)
(declare-fun |MultiSet#FromSeq| (T@U) T@U)
(declare-fun |Seq#Build| (T@U T@U) T@U)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |Seq#Append| (T@U T@U) T@U)
(declare-fun |Seq#Update| (T@U Int T@U) T@U)
(declare-fun |Seq#Singleton| (T@U) T@U)
(declare-fun |Seq#Build_inv0| (T@U) T@U)
(declare-fun |Seq#Build_inv1| (T@U) T@U)
(declare-fun |Seq#Contains| (T@U T@U) Bool)
(declare-fun |Seq#Take| (T@U Int) T@U)
(declare-fun |Seq#Drop| (T@U Int) T@U)
(declare-fun |Seq#Equal| (T@U T@U) Bool)
(declare-fun |Seq#SameUntil| (T@U T@U Int) Bool)
(declare-fun |Seq#FromArray| (T@U T@U) T@U)
(declare-fun |Seq#Rank| (T@U) Int)
(declare-fun |Map#Card| (T@U) Int)
(declare-fun |Map#Values| (T@U) T@U)
(declare-fun |Map#Items| (T@U) T@U)
(declare-fun _System.Tuple2._0 (T@U) T@U)
(declare-fun _System.Tuple2._1 (T@U) T@U)
(declare-fun |Map#Empty| (T@T T@T) T@U)
(declare-fun |Map#Glue| (T@U T@U T@U) T@U)
(declare-fun |Map#Build| (T@U T@U T@U) T@U)
(declare-fun |Map#Equal| (T@U T@U) Bool)
(declare-fun |Map#Disjoint| (T@U T@U) Bool)
(declare-fun |IMap#Values| (T@U) T@U)
(declare-fun |IMap#Items| (T@U) T@U)
(declare-fun |IMap#Empty| (T@T T@T) T@U)
(declare-fun |IMap#Glue| (T@U T@U T@U) T@U)
(declare-fun |IMap#Build| (T@U T@U T@U) T@U)
(declare-fun |IMap#Equal| (T@U T@U) Bool)
(declare-fun INTERNAL_add_boogie (Int Int) Int)
(declare-fun INTERNAL_sub_boogie (Int Int) Int)
(declare-fun INTERNAL_mul_boogie (Int Int) Int)
(declare-fun INTERNAL_div_boogie (Int Int) Int)
(declare-fun INTERNAL_mod_boogie (Int Int) Int)
(declare-fun INTERNAL_lt_boogie (Int Int) Bool)
(declare-fun INTERNAL_le_boogie (Int Int) Bool)
(declare-fun INTERNAL_gt_boogie (Int Int) Bool)
(declare-fun INTERNAL_ge_boogie (Int Int) Bool)
(declare-fun Mul (Int Int) Int)
(declare-fun Div (Int Int) Int)
(declare-fun Mod (Int Int) Int)
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Tclass._System.nat () T@U)
(declare-fun null () T@U)
(declare-fun Tclass._System.object () T@U)
(declare-fun Tclass._System.array? (T@U) T@U)
(declare-fun Tclass._System.array?_0 (T@U) T@U)
(declare-fun dtype (T@U) T@U)
(declare-fun Tclass._System.array (T@U) T@U)
(declare-fun Tclass._System.array_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc0_0 (T@U) T@U)
(declare-fun HandleTypeType () T@T)
(declare-fun Apply0 (T@U T@U T@U) T@U)
(declare-fun Handle0 (T@U T@U T@U) T@U)
(declare-fun Requires0 (T@U T@U T@U) Bool)
(declare-fun Reads0 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc0_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hFunc2_2 (T@U) T@U)
(declare-fun MapType2Type (T@T T@T T@T T@T) T@T)
(declare-fun MapType2TypeInv0 (T@T) T@T)
(declare-fun MapType2TypeInv1 (T@T) T@T)
(declare-fun MapType2TypeInv2 (T@T) T@T)
(declare-fun MapType2TypeInv3 (T@T) T@T)
(declare-fun MapType2Select (T@U T@U T@U T@U) T@U)
(declare-fun MapType2Store (T@U T@U T@U T@U T@U) T@U)
(declare-fun Apply2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle2 (T@U T@U T@U) T@U)
(declare-fun Requires2 (T@U T@U T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads2 (T@U T@U T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc2_2 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2 (T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc2_2 (T@U) T@U)
(declare-fun |#_System._tuple#2._#Make2| (T@U T@U) T@U)
(declare-fun DatatypeCtorId (T@U) T@U)
(declare-fun _System.Tuple2.___hMake2_q (T@U) Bool)
(declare-fun Tclass._System.Tuple2 (T@U T@U) T@U)
(declare-fun Tclass._System.Tuple2_0 (T@U) T@U)
(declare-fun Tclass._System.Tuple2_1 (T@U) T@U)
(declare-fun |$IsA#_System.Tuple2| (T@U) Bool)
(declare-fun |_System.Tuple2#Equal| (T@U T@U) Bool)
(declare-fun Tclass._System.___hFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hFunc1_1 (T@U) T@U)
(declare-fun MapType3Type (T@T T@T T@T) T@T)
(declare-fun MapType3TypeInv0 (T@T) T@T)
(declare-fun MapType3TypeInv1 (T@T) T@T)
(declare-fun MapType3TypeInv2 (T@T) T@T)
(declare-fun MapType3Select (T@U T@U T@U) T@U)
(declare-fun MapType3Store (T@U T@U T@U T@U) T@U)
(declare-fun Apply1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun Handle1 (T@U T@U T@U) T@U)
(declare-fun Requires1 (T@U T@U T@U T@U T@U) Bool)
(declare-fun Reads1 (T@U T@U T@U T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hPartialFunc1_1 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1 (T@U T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_0 (T@U) T@U)
(declare-fun Tclass._System.___hTotalFunc1_1 (T@U) T@U)
(declare-fun |#_System._tuple#0._#Make0| () T@U)
(declare-fun _System.Tuple0.___hMake0_q (T@U) Bool)
(declare-fun Tclass._System.Tuple0 () T@U)
(declare-fun |$IsA#_System.Tuple0| (T@U) Bool)
(declare-fun |_System.Tuple0#Equal| (T@U T@U) Bool)
(declare-fun Tclass._module.__default () T@U)
(declare-fun _module.__default.exp (T@U Int Int) Int)
(declare-fun AsFuelBottom (T@U) T@U)
(declare-fun $LZ () T@U)
(declare-fun $FunctionContextHeight () Int)
(declare-fun |_module.__default.exp#canCall| (Int Int) Bool)
(declare-fun |_module.__default.exp#requires| (T@U Int Int) Bool)
(declare-fun MapType4Type (T@T T@T) T@T)
(declare-fun MapType4TypeInv0 (T@T) T@T)
(declare-fun MapType4TypeInv1 (T@T) T@T)
(declare-fun MapType4Select (T@U T@U T@U) T@U)
(declare-fun MapType4Store (T@U T@U T@U T@U) T@U)
(declare-fun |lambda#0| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#1| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#2| (T@U T@U T@U Bool) T@U)
(declare-fun |lambda#3| (T@U T@U T@U Bool) T@U)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor intType) 0) (= (Ctor realType) 1)) (= (Ctor boolType) 2)) (= (Ctor rmodeType) 3)) (forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))) (forall ((x T@U) ) (!  (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))) (forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@0 T@U) ) (!  (=> (= (type x@@0) realType) (= (real_2_U (U_2_real x@@0)) x@@0))
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@0))
))) (forall ((arg0@@2 Real) ) (! (= (type (real_2_U arg0@@2)) realType)
 :qid |funType:real_2_U|
 :pattern ( (real_2_U arg0@@2))
))) (forall ((arg0@@3 Bool) ) (! (= (U_2_bool (bool_2_U arg0@@3)) arg0@@3)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@3))
))) (forall ((x@@1 T@U) ) (!  (=> (= (type x@@1) boolType) (= (bool_2_U (U_2_bool x@@1)) x@@1))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@1))
))) (forall ((arg0@@4 Bool) ) (! (= (type (bool_2_U arg0@@4)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@4))
))) (forall ((arg0@@5 RoundingMode) ) (! (= (U_2_rmode (rmode_2_U arg0@@5)) arg0@@5)
 :qid |typeInv:U_2_rmode|
 :pattern ( (rmode_2_U arg0@@5))
))) (forall ((x@@2 T@U) ) (!  (=> (= (type x@@2) rmodeType) (= (rmode_2_U (U_2_rmode x@@2)) x@@2))
 :qid |cast:U_2_rmode|
 :pattern ( (U_2_rmode x@@2))
))) (forall ((arg0@@6 RoundingMode) ) (! (= (type (rmode_2_U arg0@@6)) rmodeType)
 :qid |funType:rmode_2_U|
 :pattern ( (rmode_2_U arg0@@6))
))))
(assert (forall ((x@@3 T@U) ) (! (UOrdering2 x@@3 x@@3)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@3)
 :no-pattern (U_2_bool x@@3)
)))
(assert (forall ((x@@4 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@4)))
 (=> (and (and (= (type y) alpha) (= (type z) alpha)) (and (UOrdering2 x@@4 y) (UOrdering2 y z))) (UOrdering2 x@@4 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@4 y) (UOrdering2 y z))
)))
(assert (forall ((x@@5 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@5)))
 (=> (= (type y@@0) alpha@@0) (=> (and (UOrdering2 x@@5 y@@0) (UOrdering2 y@@0 x@@5)) (= x@@5 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@5 y@@0) (UOrdering2 y@@0 x@@5))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (Ctor TyType) 4) (= (type TBool) TyType)) (= (type TChar) TyType)) (= (type TInt) TyType)) (= (type TReal) TyType)) (= (type TORDINAL) TyType)) (= (Ctor TyTagType) 5)) (= (type TagBool) TyTagType)) (= (type TagChar) TyTagType)) (= (type TagInt) TyTagType)) (= (type TagReal) TyTagType)) (= (type TagORDINAL) TyTagType)) (= (type TagSet) TyTagType)) (= (type TagISet) TyTagType)) (= (type TagMultiSet) TyTagType)) (= (type TagSeq) TyTagType)) (= (type TagMap) TyTagType)) (= (type TagIMap) TyTagType)) (= (type TagClass) TyTagType)) (= (Ctor ClassNameType) 6)) (= (type NoTraitAtAll) ClassNameType)) (= (type class._System.int) ClassNameType)) (= (type class._System.bool) ClassNameType)) (= (type class._System.set) ClassNameType)) (= (type class._System.seq) ClassNameType)) (= (type class._System.multiset) ClassNameType)) (forall ((arg0@@7 T@T) ) (! (= (Ctor (FieldType arg0@@7)) 7)
 :qid |ctor:FieldType|
))) (forall ((arg0@@8 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@8)) arg0@@8)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@8))
))) (= (type alloc) (FieldType boolType))) (= (Ctor NameFamilyType) 8)) (= (type allocName) NameFamilyType)) (= (type Tagclass._System.nat) TyTagType)) (= (type class._System.object?) ClassNameType)) (= (type Tagclass._System.object?) TyTagType)) (= (type Tagclass._System.object) TyTagType)) (= (type class._System.array?) ClassNameType)) (= (type Tagclass._System.array?) TyTagType)) (= (type Tagclass._System.array) TyTagType)) (= (type Tagclass._System.___hFunc0) TyTagType)) (= (type Tagclass._System.___hPartialFunc0) TyTagType)) (= (type Tagclass._System.___hTotalFunc0) TyTagType)) (= (type Tagclass._System.___hFunc2) TyTagType)) (= (type Tagclass._System.___hPartialFunc2) TyTagType)) (= (type Tagclass._System.___hTotalFunc2) TyTagType)) (= (type class._System.Tuple2) ClassNameType)) (= (Ctor DtCtorIdType) 9)) (= (type |##_System._tuple#2._#Make2|) DtCtorIdType)) (= (type Tagclass._System.Tuple2) TyTagType)) (= (type Tagclass._System.___hFunc1) TyTagType)) (= (type Tagclass._System.___hPartialFunc1) TyTagType)) (= (type Tagclass._System.___hTotalFunc1) TyTagType)) (= (type class._System.Tuple0) ClassNameType)) (= (type |##_System._tuple#0._#Make0|) DtCtorIdType)) (= (type Tagclass._System.Tuple0) TyTagType)) (= (type class._module.__default) ClassNameType)) (= (type Tagclass._module.__default) TyTagType)))
(assert (distinct TBool TChar TInt TReal TORDINAL TagBool TagChar TagInt TagReal TagORDINAL TagSet TagISet TagMultiSet TagSeq TagMap TagIMap TagClass NoTraitAtAll class._System.int class._System.bool class._System.set class._System.seq class._System.multiset alloc allocName Tagclass._System.nat class._System.object? Tagclass._System.object? Tagclass._System.object class._System.array? Tagclass._System.array? Tagclass._System.array Tagclass._System.___hFunc0 Tagclass._System.___hPartialFunc0 Tagclass._System.___hTotalFunc0 Tagclass._System.___hFunc2 Tagclass._System.___hPartialFunc2 Tagclass._System.___hTotalFunc2 class._System.Tuple2 |##_System._tuple#2._#Make2| Tagclass._System.Tuple2 Tagclass._System.___hFunc1 Tagclass._System.___hPartialFunc1 Tagclass._System.___hTotalFunc1 class._System.Tuple0 |##_System._tuple#0._#Make0| Tagclass._System.Tuple0 class._module.__default Tagclass._module.__default)
)
(assert $$Language$Dafny)
(assert (forall ((arg0@@9 Int) ) (! (= (type (TBitvector arg0@@9)) TyType)
 :qid |funType:TBitvector|
 :pattern ( (TBitvector arg0@@9))
)))
(assert (forall ((w Int) ) (! (= (Inv0_TBitvector (TBitvector w)) w)
 :qid |fastexpb.38:15|
 :skolemid |0|
 :pattern ( (TBitvector w))
)))
(assert  (and (forall ((arg0@@10 T@U) ) (! (= (type (TSet arg0@@10)) TyType)
 :qid |funType:TSet|
 :pattern ( (TSet arg0@@10))
)) (forall ((arg0@@11 T@U) ) (! (= (type (Inv0_TSet arg0@@11)) TyType)
 :qid |funType:Inv0_TSet|
 :pattern ( (Inv0_TSet arg0@@11))
))))
(assert (forall ((t T@U) ) (!  (=> (= (type t) TyType) (= (Inv0_TSet (TSet t)) t))
 :qid |fastexpb.42:15|
 :skolemid |1|
 :pattern ( (TSet t))
)))
(assert  (and (forall ((arg0@@12 T@U) ) (! (= (type (TISet arg0@@12)) TyType)
 :qid |funType:TISet|
 :pattern ( (TISet arg0@@12))
)) (forall ((arg0@@13 T@U) ) (! (= (type (Inv0_TISet arg0@@13)) TyType)
 :qid |funType:Inv0_TISet|
 :pattern ( (Inv0_TISet arg0@@13))
))))
(assert (forall ((t@@0 T@U) ) (!  (=> (= (type t@@0) TyType) (= (Inv0_TISet (TISet t@@0)) t@@0))
 :qid |fastexpb.46:15|
 :skolemid |2|
 :pattern ( (TISet t@@0))
)))
(assert  (and (forall ((arg0@@14 T@U) ) (! (= (type (TSeq arg0@@14)) TyType)
 :qid |funType:TSeq|
 :pattern ( (TSeq arg0@@14))
)) (forall ((arg0@@15 T@U) ) (! (= (type (Inv0_TSeq arg0@@15)) TyType)
 :qid |funType:Inv0_TSeq|
 :pattern ( (Inv0_TSeq arg0@@15))
))))
(assert (forall ((t@@1 T@U) ) (!  (=> (= (type t@@1) TyType) (= (Inv0_TSeq (TSeq t@@1)) t@@1))
 :qid |fastexpb.50:15|
 :skolemid |3|
 :pattern ( (TSeq t@@1))
)))
(assert  (and (forall ((arg0@@16 T@U) ) (! (= (type (TMultiSet arg0@@16)) TyType)
 :qid |funType:TMultiSet|
 :pattern ( (TMultiSet arg0@@16))
)) (forall ((arg0@@17 T@U) ) (! (= (type (Inv0_TMultiSet arg0@@17)) TyType)
 :qid |funType:Inv0_TMultiSet|
 :pattern ( (Inv0_TMultiSet arg0@@17))
))))
(assert (forall ((t@@2 T@U) ) (!  (=> (= (type t@@2) TyType) (= (Inv0_TMultiSet (TMultiSet t@@2)) t@@2))
 :qid |fastexpb.54:15|
 :skolemid |4|
 :pattern ( (TMultiSet t@@2))
)))
(assert  (and (forall ((arg0@@18 T@U) (arg1 T@U) ) (! (= (type (TMap arg0@@18 arg1)) TyType)
 :qid |funType:TMap|
 :pattern ( (TMap arg0@@18 arg1))
)) (forall ((arg0@@19 T@U) ) (! (= (type (Inv0_TMap arg0@@19)) TyType)
 :qid |funType:Inv0_TMap|
 :pattern ( (Inv0_TMap arg0@@19))
))))
(assert (forall ((t@@3 T@U) (u T@U) ) (!  (=> (and (= (type t@@3) TyType) (= (type u) TyType)) (= (Inv0_TMap (TMap t@@3 u)) t@@3))
 :qid |fastexpb.60:15|
 :skolemid |5|
 :pattern ( (TMap t@@3 u))
)))
(assert (forall ((arg0@@20 T@U) ) (! (= (type (Inv1_TMap arg0@@20)) TyType)
 :qid |funType:Inv1_TMap|
 :pattern ( (Inv1_TMap arg0@@20))
)))
(assert (forall ((t@@4 T@U) (u@@0 T@U) ) (!  (=> (and (= (type t@@4) TyType) (= (type u@@0) TyType)) (= (Inv1_TMap (TMap t@@4 u@@0)) u@@0))
 :qid |fastexpb.62:15|
 :skolemid |6|
 :pattern ( (TMap t@@4 u@@0))
)))
(assert  (and (forall ((arg0@@21 T@U) (arg1@@0 T@U) ) (! (= (type (TIMap arg0@@21 arg1@@0)) TyType)
 :qid |funType:TIMap|
 :pattern ( (TIMap arg0@@21 arg1@@0))
)) (forall ((arg0@@22 T@U) ) (! (= (type (Inv0_TIMap arg0@@22)) TyType)
 :qid |funType:Inv0_TIMap|
 :pattern ( (Inv0_TIMap arg0@@22))
))))
(assert (forall ((t@@5 T@U) (u@@1 T@U) ) (!  (=> (and (= (type t@@5) TyType) (= (type u@@1) TyType)) (= (Inv0_TIMap (TIMap t@@5 u@@1)) t@@5))
 :qid |fastexpb.68:15|
 :skolemid |7|
 :pattern ( (TIMap t@@5 u@@1))
)))
(assert (forall ((arg0@@23 T@U) ) (! (= (type (Inv1_TIMap arg0@@23)) TyType)
 :qid |funType:Inv1_TIMap|
 :pattern ( (Inv1_TIMap arg0@@23))
)))
(assert (forall ((t@@6 T@U) (u@@2 T@U) ) (!  (=> (and (= (type t@@6) TyType) (= (type u@@2) TyType)) (= (Inv1_TIMap (TIMap t@@6 u@@2)) u@@2))
 :qid |fastexpb.70:15|
 :skolemid |8|
 :pattern ( (TIMap t@@6 u@@2))
)))
(assert (forall ((arg0@@24 T@U) ) (! (= (type (Tag arg0@@24)) TyTagType)
 :qid |funType:Tag|
 :pattern ( (Tag arg0@@24))
)))
(assert (= (Tag TBool) TagBool))
(assert (= (Tag TChar) TagChar))
(assert (= (Tag TInt) TagInt))
(assert (= (Tag TReal) TagReal))
(assert (= (Tag TORDINAL) TagORDINAL))
(assert (forall ((t@@7 T@U) ) (!  (=> (= (type t@@7) TyType) (= (Tag (TSet t@@7)) TagSet))
 :qid |fastexpb.110:15|
 :skolemid |9|
 :pattern ( (TSet t@@7))
)))
(assert (forall ((t@@8 T@U) ) (!  (=> (= (type t@@8) TyType) (= (Tag (TISet t@@8)) TagISet))
 :qid |fastexpb.112:15|
 :skolemid |10|
 :pattern ( (TISet t@@8))
)))
(assert (forall ((t@@9 T@U) ) (!  (=> (= (type t@@9) TyType) (= (Tag (TMultiSet t@@9)) TagMultiSet))
 :qid |fastexpb.114:15|
 :skolemid |11|
 :pattern ( (TMultiSet t@@9))
)))
(assert (forall ((t@@10 T@U) ) (!  (=> (= (type t@@10) TyType) (= (Tag (TSeq t@@10)) TagSeq))
 :qid |fastexpb.116:15|
 :skolemid |12|
 :pattern ( (TSeq t@@10))
)))
(assert (forall ((t@@11 T@U) (u@@3 T@U) ) (!  (=> (and (= (type t@@11) TyType) (= (type u@@3) TyType)) (= (Tag (TMap t@@11 u@@3)) TagMap))
 :qid |fastexpb.118:15|
 :skolemid |13|
 :pattern ( (TMap t@@11 u@@3))
)))
(assert (forall ((t@@12 T@U) (u@@4 T@U) ) (!  (=> (and (= (type t@@12) TyType) (= (type u@@4) TyType)) (= (Tag (TIMap t@@12 u@@4)) TagIMap))
 :qid |fastexpb.120:15|
 :skolemid |14|
 :pattern ( (TIMap t@@12 u@@4))
)))
(assert (forall ((x@@6 Int) ) (! (= (LitInt x@@6) x@@6)
 :qid |fastexpb.124:15|
 :skolemid |15|
 :pattern ( (LitInt x@@6))
)))
(assert  (and (and (= (Ctor BoxType) 10) (forall ((arg0@@25 T@U) ) (! (= (type ($Box arg0@@25)) BoxType)
 :qid |funType:$Box|
 :pattern ( ($Box arg0@@25))
))) (forall ((arg0@@26 T@U) ) (! (let ((T (type arg0@@26)))
(= (type (Lit arg0@@26)) T))
 :qid |funType:Lit|
 :pattern ( (Lit arg0@@26))
))))
(assert (forall ((x@@7 Int) ) (! (= ($Box (int_2_U (LitInt x@@7))) (Lit ($Box (int_2_U x@@7))))
 :qid |fastexpb.126:15|
 :skolemid |16|
 :pattern ( ($Box (int_2_U (LitInt x@@7))))
)))
(assert (forall ((x@@8 Real) ) (! (= (LitReal x@@8) x@@8)
 :qid |fastexpb.130:15|
 :skolemid |17|
 :pattern ( (LitReal x@@8))
)))
(assert (forall ((x@@9 Real) ) (! (= ($Box (real_2_U (LitReal x@@9))) (Lit ($Box (real_2_U x@@9))))
 :qid |fastexpb.132:15|
 :skolemid |18|
 :pattern ( ($Box (real_2_U (LitReal x@@9))))
)))
(assert (forall ((x@@10 T@U) ) (! (= (Lit x@@10) x@@10)
 :qid |fastexpb.136:18|
 :skolemid |19|
 :pattern ( (Lit x@@10))
)))
(assert (forall ((x@@11 T@U) ) (! (= ($Box (Lit x@@11)) (Lit ($Box x@@11)))
 :qid |fastexpb.138:18|
 :skolemid |20|
 :pattern ( ($Box (Lit x@@11)))
)))
(assert  (and (= (Ctor charType) 11) (forall ((arg0@@27 Int) ) (! (= (type (|char#FromInt| arg0@@27)) charType)
 :qid |funType:char#FromInt|
 :pattern ( (|char#FromInt| arg0@@27))
))))
(assert (forall ((ch T@U) ) (!  (=> (= (type ch) charType) (and (and (= (|char#FromInt| (|char#ToInt| ch)) ch) (<= 0 (|char#ToInt| ch))) (< (|char#ToInt| ch) 65536)))
 :qid |fastexpb.146:15|
 :skolemid |21|
 :pattern ( (|char#ToInt| ch))
)))
(assert (forall ((n Int) ) (!  (=> (and (<= 0 n) (< n 65536)) (= (|char#ToInt| (|char#FromInt| n)) n))
 :qid |fastexpb.152:15|
 :skolemid |22|
 :pattern ( (|char#FromInt| n))
)))
(assert (forall ((arg0@@28 T@U) (arg1@@1 T@U) ) (! (= (type (|char#Plus| arg0@@28 arg1@@1)) charType)
 :qid |funType:char#Plus|
 :pattern ( (|char#Plus| arg0@@28 arg1@@1))
)))
(assert (forall ((a T@U) (b T@U) ) (!  (=> (and (= (type a) charType) (= (type b) charType)) (= (|char#Plus| a b) (|char#FromInt| (+ (|char#ToInt| a) (|char#ToInt| b)))))
 :qid |fastexpb.160:15|
 :skolemid |23|
 :pattern ( (|char#Plus| a b))
)))
(assert (forall ((arg0@@29 T@U) (arg1@@2 T@U) ) (! (= (type (|char#Minus| arg0@@29 arg1@@2)) charType)
 :qid |funType:char#Minus|
 :pattern ( (|char#Minus| arg0@@29 arg1@@2))
)))
(assert (forall ((a@@0 T@U) (b@@0 T@U) ) (!  (=> (and (= (type a@@0) charType) (= (type b@@0) charType)) (= (|char#Minus| a@@0 b@@0) (|char#FromInt| (- (|char#ToInt| a@@0) (|char#ToInt| b@@0)))))
 :qid |fastexpb.164:15|
 :skolemid |24|
 :pattern ( (|char#Minus| a@@0 b@@0))
)))
(assert (forall ((T@@0 T@T) (arg0@@30 T@U) ) (! (= (type ($Unbox T@@0 arg0@@30)) T@@0)
 :qid |funType:$Unbox|
 :pattern ( ($Unbox T@@0 arg0@@30))
)))
(assert (forall ((x@@12 T@U) ) (! (let ((T@@1 (type x@@12)))
(= ($Unbox T@@1 ($Box x@@12)) x@@12))
 :qid |fastexpb.184:18|
 :skolemid |25|
 :pattern ( ($Box x@@12))
)))
(assert (forall ((bx T@U) ) (!  (=> (and (= (type bx) BoxType) ($IsBox bx TInt)) (and (= ($Box ($Unbox intType bx)) bx) ($Is ($Unbox intType bx) TInt)))
 :qid |fastexpb.186:15|
 :skolemid |26|
 :pattern ( ($IsBox bx TInt))
)))
(assert (forall ((bx@@0 T@U) ) (!  (=> (and (= (type bx@@0) BoxType) ($IsBox bx@@0 TReal)) (and (= ($Box ($Unbox realType bx@@0)) bx@@0) ($Is ($Unbox realType bx@@0) TReal)))
 :qid |fastexpb.190:15|
 :skolemid |27|
 :pattern ( ($IsBox bx@@0 TReal))
)))
(assert (forall ((bx@@1 T@U) ) (!  (=> (and (= (type bx@@1) BoxType) ($IsBox bx@@1 TBool)) (and (= ($Box ($Unbox boolType bx@@1)) bx@@1) ($Is ($Unbox boolType bx@@1) TBool)))
 :qid |fastexpb.195:15|
 :skolemid |28|
 :pattern ( ($IsBox bx@@1 TBool))
)))
(assert (forall ((bx@@2 T@U) ) (!  (=> (and (= (type bx@@2) BoxType) ($IsBox bx@@2 TChar)) (and (= ($Box ($Unbox charType bx@@2)) bx@@2) ($Is ($Unbox charType bx@@2) TChar)))
 :qid |fastexpb.200:15|
 :skolemid |29|
 :pattern ( ($IsBox bx@@2 TChar))
)))
(assert  (and (and (and (and (and (and (forall ((arg0@@31 T@T) (arg1@@3 T@T) ) (! (= (Ctor (MapType0Type arg0@@31 arg1@@3)) 12)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@32 T@T) (arg1@@4 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@32 arg1@@4)) arg0@@32)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@32 arg1@@4))
))) (forall ((arg0@@33 T@T) (arg1@@5 T@T) ) (! (= (MapType0TypeInv1 (MapType0Type arg0@@33 arg1@@5)) arg1@@5)
 :qid |typeInv:MapType0TypeInv1|
 :pattern ( (MapType0Type arg0@@33 arg1@@5))
))) (forall ((arg0@@34 T@U) (arg1@@6 T@U) ) (! (let ((aVar1 (MapType0TypeInv1 (type arg0@@34))))
(= (type (MapType0Select arg0@@34 arg1@@6)) aVar1))
 :qid |funType:MapType0Select|
 :pattern ( (MapType0Select arg0@@34 arg1@@6))
))) (forall ((arg0@@35 T@U) (arg1@@7 T@U) (arg2 T@U) ) (! (let ((aVar1@@0 (type arg2)))
(let ((aVar0 (type arg1@@7)))
(= (type (MapType0Store arg0@@35 arg1@@7 arg2)) (MapType0Type aVar0 aVar1@@0))))
 :qid |funType:MapType0Store|
 :pattern ( (MapType0Store arg0@@35 arg1@@7 arg2))
))) (forall ((m T@U) (x0 T@U) (val T@U) ) (! (let ((aVar1@@1 (MapType0TypeInv1 (type m))))
 (=> (= (type val) aVar1@@1) (= (MapType0Select (MapType0Store m x0 val) x0) val)))
 :qid |mapAx0:MapType0Select|
 :weight 0
))) (and (forall ((val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (y0 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select (MapType0Store m@@0 x0@@0 val@@0) y0) (MapType0Select m@@0 y0)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (y0@@0 T@U) ) (!  (or true (= (MapType0Select (MapType0Store m@@1 x0@@1 val@@1) y0@@0) (MapType0Select m@@1 y0@@0)))
 :qid |mapAx2:MapType0Select|
 :weight 0
)))))
(assert (forall ((bx@@3 T@U) (t@@13 T@U) ) (!  (=> (and (and (= (type bx@@3) BoxType) (= (type t@@13) TyType)) ($IsBox bx@@3 (TSet t@@13))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@3)) bx@@3) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@3) (TSet t@@13))))
 :qid |fastexpb.205:15|
 :skolemid |30|
 :pattern ( ($IsBox bx@@3 (TSet t@@13)))
)))
(assert (forall ((bx@@4 T@U) (t@@14 T@U) ) (!  (=> (and (and (= (type bx@@4) BoxType) (= (type t@@14) TyType)) ($IsBox bx@@4 (TISet t@@14))) (and (= ($Box ($Unbox (MapType0Type BoxType boolType) bx@@4)) bx@@4) ($Is ($Unbox (MapType0Type BoxType boolType) bx@@4) (TISet t@@14))))
 :qid |fastexpb.210:15|
 :skolemid |31|
 :pattern ( ($IsBox bx@@4 (TISet t@@14)))
)))
(assert (forall ((bx@@5 T@U) (t@@15 T@U) ) (!  (=> (and (and (= (type bx@@5) BoxType) (= (type t@@15) TyType)) ($IsBox bx@@5 (TMultiSet t@@15))) (and (= ($Box ($Unbox (MapType0Type BoxType intType) bx@@5)) bx@@5) ($Is ($Unbox (MapType0Type BoxType intType) bx@@5) (TMultiSet t@@15))))
 :qid |fastexpb.215:15|
 :skolemid |32|
 :pattern ( ($IsBox bx@@5 (TMultiSet t@@15)))
)))
(assert  (and (forall ((arg0@@36 T@T) ) (! (= (Ctor (SeqType arg0@@36)) 13)
 :qid |ctor:SeqType|
)) (forall ((arg0@@37 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@37)) arg0@@37)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@37))
))))
(assert (forall ((bx@@6 T@U) (t@@16 T@U) ) (!  (=> (and (and (= (type bx@@6) BoxType) (= (type t@@16) TyType)) ($IsBox bx@@6 (TSeq t@@16))) (and (= ($Box ($Unbox (SeqType BoxType) bx@@6)) bx@@6) ($Is ($Unbox (SeqType BoxType) bx@@6) (TSeq t@@16))))
 :qid |fastexpb.221:15|
 :skolemid |33|
 :pattern ( ($IsBox bx@@6 (TSeq t@@16)))
)))
(assert  (and (and (forall ((arg0@@38 T@T) (arg1@@8 T@T) ) (! (= (Ctor (MapType arg0@@38 arg1@@8)) 14)
 :qid |ctor:MapType|
)) (forall ((arg0@@39 T@T) (arg1@@9 T@T) ) (! (= (MapTypeInv0 (MapType arg0@@39 arg1@@9)) arg0@@39)
 :qid |typeInv:MapTypeInv0|
 :pattern ( (MapType arg0@@39 arg1@@9))
))) (forall ((arg0@@40 T@T) (arg1@@10 T@T) ) (! (= (MapTypeInv1 (MapType arg0@@40 arg1@@10)) arg1@@10)
 :qid |typeInv:MapTypeInv1|
 :pattern ( (MapType arg0@@40 arg1@@10))
))))
(assert (forall ((bx@@7 T@U) (s T@U) (t@@17 T@U) ) (!  (=> (and (and (and (= (type bx@@7) BoxType) (= (type s) TyType)) (= (type t@@17) TyType)) ($IsBox bx@@7 (TMap s t@@17))) (and (= ($Box ($Unbox (MapType BoxType BoxType) bx@@7)) bx@@7) ($Is ($Unbox (MapType BoxType BoxType) bx@@7) (TMap s t@@17))))
 :qid |fastexpb.226:15|
 :skolemid |34|
 :pattern ( ($IsBox bx@@7 (TMap s t@@17)))
)))
(assert  (and (and (forall ((arg0@@41 T@T) (arg1@@11 T@T) ) (! (= (Ctor (IMapType arg0@@41 arg1@@11)) 15)
 :qid |ctor:IMapType|
)) (forall ((arg0@@42 T@T) (arg1@@12 T@T) ) (! (= (IMapTypeInv0 (IMapType arg0@@42 arg1@@12)) arg0@@42)
 :qid |typeInv:IMapTypeInv0|
 :pattern ( (IMapType arg0@@42 arg1@@12))
))) (forall ((arg0@@43 T@T) (arg1@@13 T@T) ) (! (= (IMapTypeInv1 (IMapType arg0@@43 arg1@@13)) arg1@@13)
 :qid |typeInv:IMapTypeInv1|
 :pattern ( (IMapType arg0@@43 arg1@@13))
))))
(assert (forall ((bx@@8 T@U) (s@@0 T@U) (t@@18 T@U) ) (!  (=> (and (and (and (= (type bx@@8) BoxType) (= (type s@@0) TyType)) (= (type t@@18) TyType)) ($IsBox bx@@8 (TIMap s@@0 t@@18))) (and (= ($Box ($Unbox (IMapType BoxType BoxType) bx@@8)) bx@@8) ($Is ($Unbox (IMapType BoxType BoxType) bx@@8) (TIMap s@@0 t@@18))))
 :qid |fastexpb.231:15|
 :skolemid |35|
 :pattern ( ($IsBox bx@@8 (TIMap s@@0 t@@18)))
)))
(assert (forall ((v T@U) (t@@19 T@U) ) (!  (=> (= (type t@@19) TyType) (and (=> ($IsBox ($Box v) t@@19) ($Is v t@@19)) (=> ($Is v t@@19) ($IsBox ($Box v) t@@19))))
 :qid |fastexpb.237:18|
 :skolemid |36|
 :pattern ( ($IsBox ($Box v) t@@19))
)))
(assert  (and (and (and (and (and (and (forall ((arg0@@44 T@T) ) (! (= (Ctor (MapType1Type arg0@@44)) 16)
 :qid |ctor:MapType1Type|
)) (forall ((arg0@@45 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@45)) arg0@@45)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@45))
))) (forall ((arg0@@46 T@U) (arg1@@14 T@U) (arg2@@0 T@U) ) (! (let ((alpha@@1 (FieldTypeInv0 (type arg2@@0))))
(= (type (MapType1Select arg0@@46 arg1@@14 arg2@@0)) alpha@@1))
 :qid |funType:MapType1Select|
 :pattern ( (MapType1Select arg0@@46 arg1@@14 arg2@@0))
))) (forall ((arg0@@47 T@U) (arg1@@15 T@U) (arg2@@1 T@U) (arg3 T@U) ) (! (let ((aVar0@@0 (type arg1@@15)))
(= (type (MapType1Store arg0@@47 arg1@@15 arg2@@1 arg3)) (MapType1Type aVar0@@0)))
 :qid |funType:MapType1Store|
 :pattern ( (MapType1Store arg0@@47 arg1@@15 arg2@@1 arg3))
))) (forall ((m@@2 T@U) (x0@@2 T@U) (x1 T@U) (val@@2 T@U) ) (! (let ((alpha@@2 (FieldTypeInv0 (type x1))))
 (=> (= (type val@@2) alpha@@2) (= (MapType1Select (MapType1Store m@@2 x0@@2 x1 val@@2) x0@@2 x1) val@@2)))
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (and (forall ((val@@3 T@U) (m@@3 T@U) (x0@@3 T@U) (x1@@0 T@U) (y0@@1 T@U) (y1 T@U) ) (!  (or (= x0@@3 y0@@1) (= (MapType1Select (MapType1Store m@@3 x0@@3 x1@@0 val@@3) y0@@1 y1) (MapType1Select m@@3 y0@@1 y1)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (x1@@1 T@U) (y0@@2 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType1Select (MapType1Store m@@4 x0@@4 x1@@1 val@@4) y0@@2 y1@@0) (MapType1Select m@@4 y0@@2 y1@@0)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
))) (forall ((val@@5 T@U) (m@@5 T@U) (x0@@5 T@U) (x1@@2 T@U) (y0@@3 T@U) (y1@@1 T@U) ) (!  (or true (= (MapType1Select (MapType1Store m@@5 x0@@5 x1@@2 val@@5) y0@@3 y1@@1) (MapType1Select m@@5 y0@@3 y1@@1)))
 :qid |mapAx2:MapType1Select|
 :weight 0
)))) (= (Ctor refType) 17)))
(assert (forall ((v@@0 T@U) (t@@20 T@U) (h T@U) ) (!  (=> (and (= (type t@@20) TyType) (= (type h) (MapType1Type refType))) (and (=> ($IsAllocBox ($Box v@@0) t@@20 h) ($IsAlloc v@@0 t@@20 h)) (=> ($IsAlloc v@@0 t@@20 h) ($IsAllocBox ($Box v@@0) t@@20 h))))
 :qid |fastexpb.241:18|
 :skolemid |37|
 :pattern ( ($IsAllocBox ($Box v@@0) t@@20 h))
)))
(assert (forall ((v@@1 T@U) ) (!  (=> (= (type v@@1) intType) ($Is v@@1 TInt))
 :qid |fastexpb.253:15|
 :skolemid |38|
 :pattern ( ($Is v@@1 TInt))
)))
(assert (forall ((v@@2 T@U) ) (!  (=> (= (type v@@2) realType) ($Is v@@2 TReal))
 :qid |fastexpb.255:15|
 :skolemid |39|
 :pattern ( ($Is v@@2 TReal))
)))
(assert (forall ((v@@3 T@U) ) (!  (=> (= (type v@@3) boolType) ($Is v@@3 TBool))
 :qid |fastexpb.257:15|
 :skolemid |40|
 :pattern ( ($Is v@@3 TBool))
)))
(assert (forall ((v@@4 T@U) ) (!  (=> (= (type v@@4) charType) ($Is v@@4 TChar))
 :qid |fastexpb.259:15|
 :skolemid |41|
 :pattern ( ($Is v@@4 TChar))
)))
(assert (forall ((v@@5 T@U) ) (!  (=> (= (type v@@5) BoxType) ($Is v@@5 TORDINAL))
 :qid |fastexpb.261:15|
 :skolemid |42|
 :pattern ( ($Is v@@5 TORDINAL))
)))
(assert (forall ((h@@0 T@U) (v@@6 T@U) ) (!  (=> (and (= (type h@@0) (MapType1Type refType)) (= (type v@@6) intType)) ($IsAlloc v@@6 TInt h@@0))
 :qid |fastexpb.263:15|
 :skolemid |43|
 :pattern ( ($IsAlloc v@@6 TInt h@@0))
)))
(assert (forall ((h@@1 T@U) (v@@7 T@U) ) (!  (=> (and (= (type h@@1) (MapType1Type refType)) (= (type v@@7) realType)) ($IsAlloc v@@7 TReal h@@1))
 :qid |fastexpb.265:15|
 :skolemid |44|
 :pattern ( ($IsAlloc v@@7 TReal h@@1))
)))
(assert (forall ((h@@2 T@U) (v@@8 T@U) ) (!  (=> (and (= (type h@@2) (MapType1Type refType)) (= (type v@@8) boolType)) ($IsAlloc v@@8 TBool h@@2))
 :qid |fastexpb.267:15|
 :skolemid |45|
 :pattern ( ($IsAlloc v@@8 TBool h@@2))
)))
(assert (forall ((h@@3 T@U) (v@@9 T@U) ) (!  (=> (and (= (type h@@3) (MapType1Type refType)) (= (type v@@9) charType)) ($IsAlloc v@@9 TChar h@@3))
 :qid |fastexpb.269:15|
 :skolemid |46|
 :pattern ( ($IsAlloc v@@9 TChar h@@3))
)))
(assert (forall ((h@@4 T@U) (v@@10 T@U) ) (!  (=> (and (= (type h@@4) (MapType1Type refType)) (= (type v@@10) BoxType)) ($IsAlloc v@@10 TORDINAL h@@4))
 :qid |fastexpb.271:15|
 :skolemid |47|
 :pattern ( ($IsAlloc v@@10 TORDINAL h@@4))
)))
(assert (forall ((v@@11 T@U) (t0 T@U) ) (!  (=> (and (= (type v@@11) (MapType0Type BoxType boolType)) (= (type t0) TyType)) (and (=> ($Is v@@11 (TSet t0)) (forall ((bx@@9 T@U) ) (!  (=> (and (= (type bx@@9) BoxType) (U_2_bool (MapType0Select v@@11 bx@@9))) ($IsBox bx@@9 t0))
 :qid |fastexpb.277:33|
 :skolemid |48|
 :pattern ( (MapType0Select v@@11 bx@@9))
))) (=> (forall ((bx@@10 T@U) ) (!  (=> (and (= (type bx@@10) BoxType) (U_2_bool (MapType0Select v@@11 bx@@10))) ($IsBox bx@@10 t0))
 :qid |fastexpb.277:33|
 :skolemid |48|
 :pattern ( (MapType0Select v@@11 bx@@10))
)) ($Is v@@11 (TSet t0)))))
 :qid |fastexpb.275:15|
 :skolemid |49|
 :pattern ( ($Is v@@11 (TSet t0)))
)))
(assert (forall ((v@@12 T@U) (t0@@0 T@U) ) (!  (=> (and (= (type v@@12) (MapType0Type BoxType boolType)) (= (type t0@@0) TyType)) (and (=> ($Is v@@12 (TISet t0@@0)) (forall ((bx@@11 T@U) ) (!  (=> (and (= (type bx@@11) BoxType) (U_2_bool (MapType0Select v@@12 bx@@11))) ($IsBox bx@@11 t0@@0))
 :qid |fastexpb.281:34|
 :skolemid |50|
 :pattern ( (MapType0Select v@@12 bx@@11))
))) (=> (forall ((bx@@12 T@U) ) (!  (=> (and (= (type bx@@12) BoxType) (U_2_bool (MapType0Select v@@12 bx@@12))) ($IsBox bx@@12 t0@@0))
 :qid |fastexpb.281:34|
 :skolemid |50|
 :pattern ( (MapType0Select v@@12 bx@@12))
)) ($Is v@@12 (TISet t0@@0)))))
 :qid |fastexpb.279:15|
 :skolemid |51|
 :pattern ( ($Is v@@12 (TISet t0@@0)))
)))
(assert (forall ((v@@13 T@U) (t0@@1 T@U) ) (!  (=> (and (= (type v@@13) (MapType0Type BoxType intType)) (= (type t0@@1) TyType)) (and (=> ($Is v@@13 (TMultiSet t0@@1)) (forall ((bx@@13 T@U) ) (!  (=> (and (= (type bx@@13) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@13)))) ($IsBox bx@@13 t0@@1))
 :qid |fastexpb.286:19|
 :skolemid |52|
 :pattern ( (MapType0Select v@@13 bx@@13))
))) (=> (forall ((bx@@14 T@U) ) (!  (=> (and (= (type bx@@14) BoxType) (< 0 (U_2_int (MapType0Select v@@13 bx@@14)))) ($IsBox bx@@14 t0@@1))
 :qid |fastexpb.286:19|
 :skolemid |52|
 :pattern ( (MapType0Select v@@13 bx@@14))
)) ($Is v@@13 (TMultiSet t0@@1)))))
 :qid |fastexpb.283:15|
 :skolemid |53|
 :pattern ( ($Is v@@13 (TMultiSet t0@@1)))
)))
(assert (forall ((v@@14 T@U) (t0@@2 T@U) ) (!  (=> (and (and (= (type v@@14) (MapType0Type BoxType intType)) (= (type t0@@2) TyType)) ($Is v@@14 (TMultiSet t0@@2))) ($IsGoodMultiSet v@@14))
 :qid |fastexpb.288:15|
 :skolemid |54|
 :pattern ( ($Is v@@14 (TMultiSet t0@@2)))
)))
(assert (forall ((arg0@@48 T@U) (arg1@@16 Int) ) (! (let ((T@@2 (SeqTypeInv0 (type arg0@@48))))
(= (type (|Seq#Index| arg0@@48 arg1@@16)) T@@2))
 :qid |funType:Seq#Index|
 :pattern ( (|Seq#Index| arg0@@48 arg1@@16))
)))
(assert (forall ((v@@15 T@U) (t0@@3 T@U) ) (!  (=> (and (= (type v@@15) (SeqType BoxType)) (= (type t0@@3) TyType)) (and (=> ($Is v@@15 (TSeq t0@@3)) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i) t0@@3))
 :qid |fastexpb.295:19|
 :skolemid |55|
 :pattern ( (|Seq#Index| v@@15 i))
))) (=> (forall ((i@@0 Int) ) (!  (=> (and (<= 0 i@@0) (< i@@0 (|Seq#Length| v@@15))) ($IsBox (|Seq#Index| v@@15 i@@0) t0@@3))
 :qid |fastexpb.295:19|
 :skolemid |55|
 :pattern ( (|Seq#Index| v@@15 i@@0))
)) ($Is v@@15 (TSeq t0@@3)))))
 :qid |fastexpb.292:15|
 :skolemid |56|
 :pattern ( ($Is v@@15 (TSeq t0@@3)))
)))
(assert (forall ((v@@16 T@U) (t0@@4 T@U) (h@@5 T@U) ) (!  (=> (and (and (= (type v@@16) (MapType0Type BoxType boolType)) (= (type t0@@4) TyType)) (= (type h@@5) (MapType1Type refType))) (and (=> ($IsAlloc v@@16 (TSet t0@@4) h@@5) (forall ((bx@@15 T@U) ) (!  (=> (and (= (type bx@@15) BoxType) (U_2_bool (MapType0Select v@@16 bx@@15))) ($IsAllocBox bx@@15 t0@@4 h@@5))
 :qid |fastexpb.302:19|
 :skolemid |57|
 :pattern ( (MapType0Select v@@16 bx@@15))
))) (=> (forall ((bx@@16 T@U) ) (!  (=> (and (= (type bx@@16) BoxType) (U_2_bool (MapType0Select v@@16 bx@@16))) ($IsAllocBox bx@@16 t0@@4 h@@5))
 :qid |fastexpb.302:19|
 :skolemid |57|
 :pattern ( (MapType0Select v@@16 bx@@16))
)) ($IsAlloc v@@16 (TSet t0@@4) h@@5))))
 :qid |fastexpb.299:15|
 :skolemid |58|
 :pattern ( ($IsAlloc v@@16 (TSet t0@@4) h@@5))
)))
(assert (forall ((v@@17 T@U) (t0@@5 T@U) (h@@6 T@U) ) (!  (=> (and (and (= (type v@@17) (MapType0Type BoxType boolType)) (= (type t0@@5) TyType)) (= (type h@@6) (MapType1Type refType))) (and (=> ($IsAlloc v@@17 (TISet t0@@5) h@@6) (forall ((bx@@17 T@U) ) (!  (=> (and (= (type bx@@17) BoxType) (U_2_bool (MapType0Select v@@17 bx@@17))) ($IsAllocBox bx@@17 t0@@5 h@@6))
 :qid |fastexpb.307:19|
 :skolemid |59|
 :pattern ( (MapType0Select v@@17 bx@@17))
))) (=> (forall ((bx@@18 T@U) ) (!  (=> (and (= (type bx@@18) BoxType) (U_2_bool (MapType0Select v@@17 bx@@18))) ($IsAllocBox bx@@18 t0@@5 h@@6))
 :qid |fastexpb.307:19|
 :skolemid |59|
 :pattern ( (MapType0Select v@@17 bx@@18))
)) ($IsAlloc v@@17 (TISet t0@@5) h@@6))))
 :qid |fastexpb.304:15|
 :skolemid |60|
 :pattern ( ($IsAlloc v@@17 (TISet t0@@5) h@@6))
)))
(assert (forall ((v@@18 T@U) (t0@@6 T@U) (h@@7 T@U) ) (!  (=> (and (and (= (type v@@18) (MapType0Type BoxType intType)) (= (type t0@@6) TyType)) (= (type h@@7) (MapType1Type refType))) (and (=> ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7) (forall ((bx@@19 T@U) ) (!  (=> (and (= (type bx@@19) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@19)))) ($IsAllocBox bx@@19 t0@@6 h@@7))
 :qid |fastexpb.312:19|
 :skolemid |61|
 :pattern ( (MapType0Select v@@18 bx@@19))
))) (=> (forall ((bx@@20 T@U) ) (!  (=> (and (= (type bx@@20) BoxType) (< 0 (U_2_int (MapType0Select v@@18 bx@@20)))) ($IsAllocBox bx@@20 t0@@6 h@@7))
 :qid |fastexpb.312:19|
 :skolemid |61|
 :pattern ( (MapType0Select v@@18 bx@@20))
)) ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))))
 :qid |fastexpb.309:15|
 :skolemid |62|
 :pattern ( ($IsAlloc v@@18 (TMultiSet t0@@6) h@@7))
)))
(assert (forall ((v@@19 T@U) (t0@@7 T@U) (h@@8 T@U) ) (!  (=> (and (and (= (type v@@19) (SeqType BoxType)) (= (type t0@@7) TyType)) (= (type h@@8) (MapType1Type refType))) (and (=> ($IsAlloc v@@19 (TSeq t0@@7) h@@8) (forall ((i@@1 Int) ) (!  (=> (and (<= 0 i@@1) (< i@@1 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@1) t0@@7 h@@8))
 :qid |fastexpb.317:19|
 :skolemid |63|
 :pattern ( (|Seq#Index| v@@19 i@@1))
))) (=> (forall ((i@@2 Int) ) (!  (=> (and (<= 0 i@@2) (< i@@2 (|Seq#Length| v@@19))) ($IsAllocBox (|Seq#Index| v@@19 i@@2) t0@@7 h@@8))
 :qid |fastexpb.317:19|
 :skolemid |63|
 :pattern ( (|Seq#Index| v@@19 i@@2))
)) ($IsAlloc v@@19 (TSeq t0@@7) h@@8))))
 :qid |fastexpb.314:15|
 :skolemid |64|
 :pattern ( ($IsAlloc v@@19 (TSeq t0@@7) h@@8))
)))
(assert  (and (forall ((arg0@@49 T@U) ) (! (let ((V (MapTypeInv1 (type arg0@@49))))
(let ((U (MapTypeInv0 (type arg0@@49))))
(= (type (|Map#Elements| arg0@@49)) (MapType0Type U V))))
 :qid |funType:Map#Elements|
 :pattern ( (|Map#Elements| arg0@@49))
)) (forall ((arg0@@50 T@U) ) (! (let ((U@@0 (MapTypeInv0 (type arg0@@50))))
(= (type (|Map#Domain| arg0@@50)) (MapType0Type U@@0 boolType)))
 :qid |funType:Map#Domain|
 :pattern ( (|Map#Domain| arg0@@50))
))))
(assert (forall ((v@@20 T@U) (t0@@8 T@U) (t1 T@U) ) (!  (=> (and (and (= (type v@@20) (MapType BoxType BoxType)) (= (type t0@@8) TyType)) (= (type t1) TyType)) (and (=> ($Is v@@20 (TMap t0@@8 t1)) (forall ((bx@@21 T@U) ) (!  (=> (and (= (type bx@@21) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@20) bx@@21))) (and ($IsBox (MapType0Select (|Map#Elements| v@@20) bx@@21) t1) ($IsBox bx@@21 t0@@8)))
 :qid |fastexpb.324:19|
 :skolemid |65|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@21))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@21))
))) (=> (forall ((bx@@22 T@U) ) (!  (=> (and (= (type bx@@22) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@20) bx@@22))) (and ($IsBox (MapType0Select (|Map#Elements| v@@20) bx@@22) t1) ($IsBox bx@@22 t0@@8)))
 :qid |fastexpb.324:19|
 :skolemid |65|
 :pattern ( (MapType0Select (|Map#Elements| v@@20) bx@@22))
 :pattern ( (MapType0Select (|Map#Domain| v@@20) bx@@22))
)) ($Is v@@20 (TMap t0@@8 t1)))))
 :qid |fastexpb.321:15|
 :skolemid |66|
 :pattern ( ($Is v@@20 (TMap t0@@8 t1)))
)))
(assert (forall ((v@@21 T@U) (t0@@9 T@U) (t1@@0 T@U) (h@@9 T@U) ) (!  (=> (and (and (and (= (type v@@21) (MapType BoxType BoxType)) (= (type t0@@9) TyType)) (= (type t1@@0) TyType)) (= (type h@@9) (MapType1Type refType))) (and (=> ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9) (forall ((bx@@23 T@U) ) (!  (=> (and (= (type bx@@23) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@23))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@23) t1@@0 h@@9) ($IsAllocBox bx@@23 t0@@9 h@@9)))
 :qid |fastexpb.331:19|
 :skolemid |67|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@23))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@23))
))) (=> (forall ((bx@@24 T@U) ) (!  (=> (and (= (type bx@@24) BoxType) (U_2_bool (MapType0Select (|Map#Domain| v@@21) bx@@24))) (and ($IsAllocBox (MapType0Select (|Map#Elements| v@@21) bx@@24) t1@@0 h@@9) ($IsAllocBox bx@@24 t0@@9 h@@9)))
 :qid |fastexpb.331:19|
 :skolemid |67|
 :pattern ( (MapType0Select (|Map#Elements| v@@21) bx@@24))
 :pattern ( (MapType0Select (|Map#Domain| v@@21) bx@@24))
)) ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9))))
 :qid |fastexpb.328:15|
 :skolemid |68|
 :pattern ( ($IsAlloc v@@21 (TMap t0@@9 t1@@0) h@@9))
)))
(assert  (and (forall ((arg0@@51 T@U) ) (! (let ((V@@0 (IMapTypeInv1 (type arg0@@51))))
(let ((U@@1 (IMapTypeInv0 (type arg0@@51))))
(= (type (|IMap#Elements| arg0@@51)) (MapType0Type U@@1 V@@0))))
 :qid |funType:IMap#Elements|
 :pattern ( (|IMap#Elements| arg0@@51))
)) (forall ((arg0@@52 T@U) ) (! (let ((U@@2 (IMapTypeInv0 (type arg0@@52))))
(= (type (|IMap#Domain| arg0@@52)) (MapType0Type U@@2 boolType)))
 :qid |funType:IMap#Domain|
 :pattern ( (|IMap#Domain| arg0@@52))
))))
(assert (forall ((v@@22 T@U) (t0@@10 T@U) (t1@@1 T@U) ) (!  (=> (and (and (= (type v@@22) (IMapType BoxType BoxType)) (= (type t0@@10) TyType)) (= (type t1@@1) TyType)) (and (=> ($Is v@@22 (TIMap t0@@10 t1@@1)) (forall ((bx@@25 T@U) ) (!  (=> (and (= (type bx@@25) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@22) bx@@25))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@22) bx@@25) t1@@1) ($IsBox bx@@25 t0@@10)))
 :qid |fastexpb.339:19|
 :skolemid |69|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@25))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@25))
))) (=> (forall ((bx@@26 T@U) ) (!  (=> (and (= (type bx@@26) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@22) bx@@26))) (and ($IsBox (MapType0Select (|IMap#Elements| v@@22) bx@@26) t1@@1) ($IsBox bx@@26 t0@@10)))
 :qid |fastexpb.339:19|
 :skolemid |69|
 :pattern ( (MapType0Select (|IMap#Elements| v@@22) bx@@26))
 :pattern ( (MapType0Select (|IMap#Domain| v@@22) bx@@26))
)) ($Is v@@22 (TIMap t0@@10 t1@@1)))))
 :qid |fastexpb.336:15|
 :skolemid |70|
 :pattern ( ($Is v@@22 (TIMap t0@@10 t1@@1)))
)))
(assert (forall ((v@@23 T@U) (t0@@11 T@U) (t1@@2 T@U) (h@@10 T@U) ) (!  (=> (and (and (and (= (type v@@23) (IMapType BoxType BoxType)) (= (type t0@@11) TyType)) (= (type t1@@2) TyType)) (= (type h@@10) (MapType1Type refType))) (and (=> ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10) (forall ((bx@@27 T@U) ) (!  (=> (and (= (type bx@@27) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@27))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@27) t1@@2 h@@10) ($IsAllocBox bx@@27 t0@@11 h@@10)))
 :qid |fastexpb.346:19|
 :skolemid |71|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@27))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@27))
))) (=> (forall ((bx@@28 T@U) ) (!  (=> (and (= (type bx@@28) BoxType) (U_2_bool (MapType0Select (|IMap#Domain| v@@23) bx@@28))) (and ($IsAllocBox (MapType0Select (|IMap#Elements| v@@23) bx@@28) t1@@2 h@@10) ($IsAllocBox bx@@28 t0@@11 h@@10)))
 :qid |fastexpb.346:19|
 :skolemid |71|
 :pattern ( (MapType0Select (|IMap#Elements| v@@23) bx@@28))
 :pattern ( (MapType0Select (|IMap#Domain| v@@23) bx@@28))
)) ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10))))
 :qid |fastexpb.343:15|
 :skolemid |72|
 :pattern ( ($IsAlloc v@@23 (TIMap t0@@11 t1@@2) h@@10))
)))
(assert  (and (and (forall ((arg0@@53 T@U) (arg1@@17 T@U) ) (! (= (type (TypeTuple arg0@@53 arg1@@17)) ClassNameType)
 :qid |funType:TypeTuple|
 :pattern ( (TypeTuple arg0@@53 arg1@@17))
)) (forall ((arg0@@54 T@U) ) (! (= (type (TypeTupleCar arg0@@54)) ClassNameType)
 :qid |funType:TypeTupleCar|
 :pattern ( (TypeTupleCar arg0@@54))
))) (forall ((arg0@@55 T@U) ) (! (= (type (TypeTupleCdr arg0@@55)) ClassNameType)
 :qid |funType:TypeTupleCdr|
 :pattern ( (TypeTupleCdr arg0@@55))
))))
(assert (forall ((a@@1 T@U) (b@@1 T@U) ) (!  (=> (and (= (type a@@1) ClassNameType) (= (type b@@1) ClassNameType)) (and (= (TypeTupleCar (TypeTuple a@@1 b@@1)) a@@1) (= (TypeTupleCdr (TypeTuple a@@1 b@@1)) b@@1)))
 :qid |fastexpb.373:15|
 :skolemid |73|
 :pattern ( (TypeTuple a@@1 b@@1))
)))
(assert (forall ((arg0@@56 T@U) ) (! (= (type (SetRef_to_SetBox arg0@@56)) (MapType0Type BoxType boolType))
 :qid |funType:SetRef_to_SetBox|
 :pattern ( (SetRef_to_SetBox arg0@@56))
)))
(assert (forall ((s@@1 T@U) (bx@@29 T@U) ) (!  (=> (and (= (type s@@1) (MapType0Type refType boolType)) (= (type bx@@29) BoxType)) (and (=> (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)) (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29)))) (=> (U_2_bool (MapType0Select s@@1 ($Unbox refType bx@@29))) (U_2_bool (MapType0Select (SetRef_to_SetBox s@@1) bx@@29)))))
 :qid |fastexpb.381:15|
 :skolemid |74|
 :pattern ( (MapType0Select (SetRef_to_SetBox s@@1) bx@@29))
)))
(assert (= (type Tclass._System.object?) TyType))
(assert (forall ((s@@2 T@U) ) (!  (=> (= (type s@@2) (MapType0Type refType boolType)) ($Is (SetRef_to_SetBox s@@2) (TSet Tclass._System.object?)))
 :qid |fastexpb.385:15|
 :skolemid |75|
 :pattern ( (SetRef_to_SetBox s@@2))
)))
(assert (= (Ctor DatatypeTypeType) 18))
(assert (forall ((d T@U) ) (!  (=> (= (type d) DatatypeTypeType) (= (BoxRank ($Box d)) (DtRank d)))
 :qid |fastexpb.399:15|
 :skolemid |76|
 :pattern ( (BoxRank ($Box d)))
)))
(assert (forall ((o T@U) ) (!  (=> (= (type o) BoxType) (<= 0 (|ORD#Offset| o)))
 :qid |fastexpb.407:15|
 :skolemid |77|
 :pattern ( (|ORD#Offset| o))
)))
(assert (forall ((arg0@@57 Int) ) (! (= (type (|ORD#FromNat| arg0@@57)) BoxType)
 :qid |funType:ORD#FromNat|
 :pattern ( (|ORD#FromNat| arg0@@57))
)))
(assert (forall ((n@@0 Int) ) (!  (=> (<= 0 n@@0) (and (|ORD#IsNat| (|ORD#FromNat| n@@0)) (= (|ORD#Offset| (|ORD#FromNat| n@@0)) n@@0)))
 :qid |fastexpb.421:15|
 :skolemid |78|
 :pattern ( (|ORD#FromNat| n@@0))
)))
(assert (forall ((o@@0 T@U) ) (!  (=> (and (= (type o@@0) BoxType) (|ORD#IsNat| o@@0)) (= o@@0 (|ORD#FromNat| (|ORD#Offset| o@@0))))
 :qid |fastexpb.425:15|
 :skolemid |79|
 :pattern ( (|ORD#Offset| o@@0))
 :pattern ( (|ORD#IsNat| o@@0))
)))
(assert (forall ((o@@1 T@U) (p T@U) ) (!  (=> (and (= (type o@@1) BoxType) (= (type p) BoxType)) (and (and (=> (|ORD#Less| o@@1 p) (not (= o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (not (|ORD#IsNat| p))) (|ORD#Less| o@@1 p))) (=> (and (|ORD#IsNat| o@@1) (|ORD#IsNat| p)) (and (=> (|ORD#Less| o@@1 p) (< (|ORD#Offset| o@@1) (|ORD#Offset| p))) (=> (< (|ORD#Offset| o@@1) (|ORD#Offset| p)) (|ORD#Less| o@@1 p))))))
 :qid |fastexpb.431:15|
 :skolemid |80|
 :pattern ( (|ORD#Less| o@@1 p))
)))
(assert (forall ((o@@2 T@U) (p@@0 T@U) ) (!  (=> (and (and (= (type o@@2) BoxType) (= (type p@@0) BoxType)) (|ORD#Less| o@@2 p@@0)) (not (= o@@2 p@@0)))
 :qid |fastexpb.438:15|
 :skolemid |81|
 :pattern ( (|ORD#Less| o@@2 p@@0))
)))
(assert (forall ((o@@3 T@U) (p@@1 T@U) ) (!  (=> (and (= (type o@@3) BoxType) (= (type p@@1) BoxType)) (or (or (|ORD#Less| o@@3 p@@1) (= o@@3 p@@1)) (|ORD#Less| p@@1 o@@3)))
 :qid |fastexpb.440:15|
 :skolemid |82|
 :pattern ( (|ORD#Less| o@@3 p@@1) (|ORD#Less| p@@1 o@@3))
)))
(assert (forall ((o@@4 T@U) (p@@2 T@U) (r T@U) ) (!  (=> (and (and (and (= (type o@@4) BoxType) (= (type p@@2) BoxType)) (= (type r) BoxType)) (and (|ORD#Less| o@@4 p@@2) (|ORD#Less| p@@2 r))) (|ORD#Less| o@@4 r))
 :qid |fastexpb.444:15|
 :skolemid |83|
 :pattern ( (|ORD#Less| o@@4 p@@2) (|ORD#Less| p@@2 r))
 :pattern ( (|ORD#Less| o@@4 p@@2) (|ORD#Less| o@@4 r))
)))
(assert (forall ((o@@5 T@U) (p@@3 T@U) ) (!  (=> (and (= (type o@@5) BoxType) (= (type p@@3) BoxType)) (and (=> (|ORD#LessThanLimit| o@@5 p@@3) (|ORD#Less| o@@5 p@@3)) (=> (|ORD#Less| o@@5 p@@3) (|ORD#LessThanLimit| o@@5 p@@3))))
 :qid |fastexpb.450:15|
 :skolemid |84|
 :pattern ( (|ORD#LessThanLimit| o@@5 p@@3))
)))
(assert (forall ((arg0@@58 T@U) (arg1@@18 T@U) ) (! (= (type (|ORD#Plus| arg0@@58 arg1@@18)) BoxType)
 :qid |funType:ORD#Plus|
 :pattern ( (|ORD#Plus| arg0@@58 arg1@@18))
)))
(assert (forall ((o@@6 T@U) (p@@4 T@U) ) (!  (=> (and (= (type o@@6) BoxType) (= (type p@@4) BoxType)) (and (=> (|ORD#IsNat| (|ORD#Plus| o@@6 p@@4)) (and (|ORD#IsNat| o@@6) (|ORD#IsNat| p@@4))) (=> (|ORD#IsNat| p@@4) (and (and (=> (|ORD#IsNat| (|ORD#Plus| o@@6 p@@4)) (|ORD#IsNat| o@@6)) (=> (|ORD#IsNat| o@@6) (|ORD#IsNat| (|ORD#Plus| o@@6 p@@4)))) (= (|ORD#Offset| (|ORD#Plus| o@@6 p@@4)) (+ (|ORD#Offset| o@@6) (|ORD#Offset| p@@4)))))))
 :qid |fastexpb.456:15|
 :skolemid |85|
 :pattern ( (|ORD#Plus| o@@6 p@@4))
)))
(assert (forall ((o@@7 T@U) (p@@5 T@U) ) (!  (=> (and (= (type o@@7) BoxType) (= (type p@@5) BoxType)) (and (or (= o@@7 (|ORD#Plus| o@@7 p@@5)) (|ORD#Less| o@@7 (|ORD#Plus| o@@7 p@@5))) (or (= p@@5 (|ORD#Plus| o@@7 p@@5)) (|ORD#Less| p@@5 (|ORD#Plus| o@@7 p@@5)))))
 :qid |fastexpb.463:15|
 :skolemid |86|
 :pattern ( (|ORD#Plus| o@@7 p@@5))
)))
(assert (forall ((o@@8 T@U) (p@@6 T@U) ) (!  (=> (and (= (type o@@8) BoxType) (= (type p@@6) BoxType)) (and (=> (= o@@8 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@8 p@@6) p@@6)) (=> (= p@@6 (|ORD#FromNat| 0)) (= (|ORD#Plus| o@@8 p@@6) o@@8))))
 :qid |fastexpb.468:15|
 :skolemid |87|
 :pattern ( (|ORD#Plus| o@@8 p@@6))
)))
(assert (forall ((arg0@@59 T@U) (arg1@@19 T@U) ) (! (= (type (|ORD#Minus| arg0@@59 arg1@@19)) BoxType)
 :qid |funType:ORD#Minus|
 :pattern ( (|ORD#Minus| arg0@@59 arg1@@19))
)))
(assert (forall ((o@@9 T@U) (p@@7 T@U) ) (!  (=> (and (and (= (type o@@9) BoxType) (= (type p@@7) BoxType)) (and (|ORD#IsNat| p@@7) (<= (|ORD#Offset| p@@7) (|ORD#Offset| o@@9)))) (and (and (=> (|ORD#IsNat| (|ORD#Minus| o@@9 p@@7)) (|ORD#IsNat| o@@9)) (=> (|ORD#IsNat| o@@9) (|ORD#IsNat| (|ORD#Minus| o@@9 p@@7)))) (= (|ORD#Offset| (|ORD#Minus| o@@9 p@@7)) (- (|ORD#Offset| o@@9) (|ORD#Offset| p@@7)))))
 :qid |fastexpb.475:15|
 :skolemid |88|
 :pattern ( (|ORD#Minus| o@@9 p@@7))
)))
(assert (forall ((o@@10 T@U) (p@@8 T@U) ) (!  (=> (and (and (= (type o@@10) BoxType) (= (type p@@8) BoxType)) (and (|ORD#IsNat| p@@8) (<= (|ORD#Offset| p@@8) (|ORD#Offset| o@@10)))) (or (and (= p@@8 (|ORD#FromNat| 0)) (= (|ORD#Minus| o@@10 p@@8) o@@10)) (and (not (= p@@8 (|ORD#FromNat| 0))) (|ORD#Less| (|ORD#Minus| o@@10 p@@8) o@@10))))
 :qid |fastexpb.481:15|
 :skolemid |89|
 :pattern ( (|ORD#Minus| o@@10 p@@8))
)))
(assert (forall ((o@@11 T@U) (m@@6 Int) (n@@1 Int) ) (!  (=> (= (type o@@11) BoxType) (=> (and (<= 0 m@@6) (<= 0 n@@1)) (= (|ORD#Plus| (|ORD#Plus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@1)) (|ORD#Plus| o@@11 (|ORD#FromNat| (+ m@@6 n@@1))))))
 :qid |fastexpb.487:15|
 :skolemid |90|
 :pattern ( (|ORD#Plus| (|ORD#Plus| o@@11 (|ORD#FromNat| m@@6)) (|ORD#FromNat| n@@1)))
)))
(assert (forall ((o@@12 T@U) (m@@7 Int) (n@@2 Int) ) (!  (=> (= (type o@@12) BoxType) (=> (and (and (<= 0 m@@7) (<= 0 n@@2)) (<= (+ m@@7 n@@2) (|ORD#Offset| o@@12))) (= (|ORD#Minus| (|ORD#Minus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@2)) (|ORD#Minus| o@@12 (|ORD#FromNat| (+ m@@7 n@@2))))))
 :qid |fastexpb.493:15|
 :skolemid |91|
 :pattern ( (|ORD#Minus| (|ORD#Minus| o@@12 (|ORD#FromNat| m@@7)) (|ORD#FromNat| n@@2)))
)))
(assert (forall ((o@@13 T@U) (m@@8 Int) (n@@3 Int) ) (!  (=> (= (type o@@13) BoxType) (=> (and (and (<= 0 m@@8) (<= 0 n@@3)) (<= n@@3 (+ (|ORD#Offset| o@@13) m@@8))) (and (=> (<= 0 (- m@@8 n@@3)) (= (|ORD#Minus| (|ORD#Plus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@3)) (|ORD#Plus| o@@13 (|ORD#FromNat| (- m@@8 n@@3))))) (=> (<= (- m@@8 n@@3) 0) (= (|ORD#Minus| (|ORD#Plus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@3)) (|ORD#Minus| o@@13 (|ORD#FromNat| (- n@@3 m@@8))))))))
 :qid |fastexpb.499:15|
 :skolemid |92|
 :pattern ( (|ORD#Minus| (|ORD#Plus| o@@13 (|ORD#FromNat| m@@8)) (|ORD#FromNat| n@@3)))
)))
(assert (forall ((o@@14 T@U) (m@@9 Int) (n@@4 Int) ) (!  (=> (= (type o@@14) BoxType) (=> (and (and (<= 0 m@@9) (<= 0 n@@4)) (<= n@@4 (+ (|ORD#Offset| o@@14) m@@9))) (and (=> (<= 0 (- m@@9 n@@4)) (= (|ORD#Plus| (|ORD#Minus| o@@14 (|ORD#FromNat| m@@9)) (|ORD#FromNat| n@@4)) (|ORD#Minus| o@@14 (|ORD#FromNat| (- m@@9 n@@4))))) (=> (<= (- m@@9 n@@4) 0) (= (|ORD#Plus| (|ORD#Minus| o@@14 (|ORD#FromNat| m@@9)) (|ORD#FromNat| n@@4)) (|ORD#Plus| o@@14 (|ORD#FromNat| (- n@@4 m@@9))))))))
 :qid |fastexpb.509:15|
 :skolemid |93|
 :pattern ( (|ORD#Plus| (|ORD#Minus| o@@14 (|ORD#FromNat| m@@9)) (|ORD#FromNat| n@@4)))
)))
(assert  (and (= (Ctor LayerTypeType) 19) (forall ((arg0@@60 T@U) (arg1@@20 T@U) ) (! (let ((A (MapType0TypeInv1 (type arg0@@60))))
(= (type (AtLayer arg0@@60 arg1@@20)) A))
 :qid |funType:AtLayer|
 :pattern ( (AtLayer arg0@@60 arg1@@20))
))))
(assert (forall ((f T@U) (ly T@U) ) (! (let ((A@@0 (MapType0TypeInv1 (type f))))
 (=> (and (= (type f) (MapType0Type LayerTypeType A@@0)) (= (type ly) LayerTypeType)) (= (AtLayer f ly) (MapType0Select f ly))))
 :qid |fastexpb.533:18|
 :skolemid |94|
 :pattern ( (AtLayer f ly))
)))
(assert (forall ((arg0@@61 T@U) ) (! (= (type ($LS arg0@@61)) LayerTypeType)
 :qid |funType:$LS|
 :pattern ( ($LS arg0@@61))
)))
(assert (forall ((f@@0 T@U) (ly@@0 T@U) ) (! (let ((A@@1 (MapType0TypeInv1 (type f@@0))))
 (=> (and (= (type f@@0) (MapType0Type LayerTypeType A@@1)) (= (type ly@@0) LayerTypeType)) (= (AtLayer f@@0 ($LS ly@@0)) (AtLayer f@@0 ly@@0))))
 :qid |fastexpb.537:18|
 :skolemid |95|
 :pattern ( (AtLayer f@@0 ($LS ly@@0)))
)))
(assert (forall ((arg0@@62 Int) ) (! (= (type (IndexField arg0@@62)) (FieldType BoxType))
 :qid |funType:IndexField|
 :pattern ( (IndexField arg0@@62))
)))
(assert (forall ((i@@3 Int) ) (! (= (FDim (IndexField i@@3)) 1)
 :qid |fastexpb.547:15|
 :skolemid |96|
 :pattern ( (IndexField i@@3))
)))
(assert (forall ((i@@4 Int) ) (! (= (IndexField_Inverse (IndexField i@@4)) i@@4)
 :qid |fastexpb.551:15|
 :skolemid |97|
 :pattern ( (IndexField i@@4))
)))
(assert (forall ((arg0@@63 T@U) (arg1@@21 Int) ) (! (= (type (MultiIndexField arg0@@63 arg1@@21)) (FieldType BoxType))
 :qid |funType:MultiIndexField|
 :pattern ( (MultiIndexField arg0@@63 arg1@@21))
)))
(assert (forall ((f@@1 T@U) (i@@5 Int) ) (!  (=> (= (type f@@1) (FieldType BoxType)) (= (FDim (MultiIndexField f@@1 i@@5)) (+ (FDim f@@1) 1)))
 :qid |fastexpb.555:15|
 :skolemid |98|
 :pattern ( (MultiIndexField f@@1 i@@5))
)))
(assert (forall ((arg0@@64 T@U) ) (! (let ((T@@3 (FieldTypeInv0 (type arg0@@64))))
(= (type (MultiIndexField_Inverse0 arg0@@64)) (FieldType T@@3)))
 :qid |funType:MultiIndexField_Inverse0|
 :pattern ( (MultiIndexField_Inverse0 arg0@@64))
)))
(assert (forall ((f@@2 T@U) (i@@6 Int) ) (!  (=> (= (type f@@2) (FieldType BoxType)) (and (= (MultiIndexField_Inverse0 (MultiIndexField f@@2 i@@6)) f@@2) (= (MultiIndexField_Inverse1 (MultiIndexField f@@2 i@@6)) i@@6)))
 :qid |fastexpb.563:15|
 :skolemid |99|
 :pattern ( (MultiIndexField f@@2 i@@6))
)))
(assert  (and (and (forall ((alpha@@3 T@T) (arg0@@65 T@U) (arg1@@22 T@U) ) (! (= (type (FieldOfDecl alpha@@3 arg0@@65 arg1@@22)) (FieldType alpha@@3))
 :qid |funType:FieldOfDecl|
 :pattern ( (FieldOfDecl alpha@@3 arg0@@65 arg1@@22))
)) (forall ((arg0@@66 T@U) ) (! (= (type (DeclType arg0@@66)) ClassNameType)
 :qid |funType:DeclType|
 :pattern ( (DeclType arg0@@66))
))) (forall ((arg0@@67 T@U) ) (! (= (type (DeclName arg0@@67)) NameFamilyType)
 :qid |funType:DeclName|
 :pattern ( (DeclName arg0@@67))
))))
(assert (forall ((cl T@U) (nm T@U) (T@@4 T@T) ) (!  (=> (and (= (type cl) ClassNameType) (= (type nm) NameFamilyType)) (and (= (DeclType (FieldOfDecl T@@4 cl nm)) cl) (= (DeclName (FieldOfDecl T@@4 cl nm)) nm)))
 :qid |fastexpb.576:18|
 :skolemid |100|
 :pattern ( (FieldOfDecl T@@4 cl nm))
)))
(assert (forall ((h@@11 T@U) (k T@U) (v@@24 T@U) (t@@21 T@U) ) (!  (=> (and (and (and (and (= (type h@@11) (MapType1Type refType)) (= (type k) (MapType1Type refType))) (= (type t@@21) TyType)) ($HeapSucc h@@11 k)) ($IsAlloc v@@24 t@@21 h@@11)) ($IsAlloc v@@24 t@@21 k))
 :qid |fastexpb.583:18|
 :skolemid |101|
 :pattern ( ($HeapSucc h@@11 k) ($IsAlloc v@@24 t@@21 h@@11))
)))
(assert (forall ((h@@12 T@U) (k@@0 T@U) (bx@@30 T@U) (t@@22 T@U) ) (!  (=> (and (and (and (and (and (= (type h@@12) (MapType1Type refType)) (= (type k@@0) (MapType1Type refType))) (= (type bx@@30) BoxType)) (= (type t@@22) TyType)) ($HeapSucc h@@12 k@@0)) ($IsAllocBox bx@@30 t@@22 h@@12)) ($IsAllocBox bx@@30 t@@22 k@@0))
 :qid |fastexpb.587:15|
 :skolemid |102|
 :pattern ( ($HeapSucc h@@12 k@@0) ($IsAllocBox bx@@30 t@@22 h@@12))
)))
(assert (= (FDim alloc) 0))
(assert (= (DeclName alloc) allocName))
(assert  (not ($IsGhostField alloc)))
(assert (forall ((o@@15 T@U) ) (!  (=> (= (type o@@15) refType) (<= 0 (_System.array.Length o@@15)))
 :qid |fastexpb.599:15|
 :skolemid |103|
 :no-pattern (type o@@15)
 :no-pattern (U_2_int o@@15)
 :no-pattern (U_2_bool o@@15)
)))
(assert (forall ((x@@13 Real) ) (! (= (q@Int x@@13) (to_int x@@13))
 :qid |fastexpb.603:15|
 :skolemid |104|
 :pattern ( (q@Int x@@13))
)))
(assert (forall ((x@@14 Int) ) (! (= (q@Real x@@14) (to_real x@@14))
 :qid |fastexpb.607:15|
 :skolemid |105|
 :pattern ( (q@Real x@@14))
)))
(assert (forall ((i@@7 Int) ) (! (= (q@Int (q@Real i@@7)) i@@7)
 :qid |fastexpb.609:15|
 :skolemid |106|
 :pattern ( (q@Int (q@Real i@@7)))
)))
(assert (= (type $OneHeap) (MapType1Type refType)))
(assert ($IsGoodHeap $OneHeap))
(assert (forall ((h@@13 T@U) (r@@0 T@U) (f@@3 T@U) (x@@15 T@U) ) (! (let ((alpha@@4 (type x@@15)))
 (=> (and (and (and (= (type h@@13) (MapType1Type refType)) (= (type r@@0) refType)) (= (type f@@3) (FieldType alpha@@4))) ($IsGoodHeap (MapType1Store h@@13 r@@0 f@@3 x@@15))) ($HeapSucc h@@13 (MapType1Store h@@13 r@@0 f@@3 x@@15))))
 :qid |fastexpb.640:22|
 :skolemid |107|
 :pattern ( (MapType1Store h@@13 r@@0 f@@3 x@@15))
)))
(assert (forall ((a@@2 T@U) (b@@2 T@U) (c T@U) ) (!  (=> (and (and (and (= (type a@@2) (MapType1Type refType)) (= (type b@@2) (MapType1Type refType))) (= (type c) (MapType1Type refType))) (and ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))) ($HeapSucc a@@2 c))
 :qid |fastexpb.644:15|
 :skolemid |108|
 :pattern ( ($HeapSucc a@@2 b@@2) ($HeapSucc b@@2 c))
)))
(assert (forall ((h@@14 T@U) (k@@1 T@U) ) (!  (=> (and (and (= (type h@@14) (MapType1Type refType)) (= (type k@@1) (MapType1Type refType))) ($HeapSucc h@@14 k@@1)) (forall ((o@@16 T@U) ) (!  (=> (and (= (type o@@16) refType) (U_2_bool (MapType1Select h@@14 o@@16 alloc))) (U_2_bool (MapType1Select k@@1 o@@16 alloc)))
 :qid |fastexpb.651:18|
 :skolemid |109|
 :pattern ( (MapType1Select k@@1 o@@16 alloc))
)))
 :qid |fastexpb.648:15|
 :skolemid |110|
 :pattern ( ($HeapSucc h@@14 k@@1))
)))
(assert (forall ((h@@15 T@U) (k@@2 T@U) ) (!  (=> (and (and (= (type h@@15) (MapType1Type refType)) (= (type k@@2) (MapType1Type refType))) ($HeapSuccGhost h@@15 k@@2)) (and ($HeapSucc h@@15 k@@2) (forall ((o@@17 T@U) (f@@4 T@U) ) (! (let ((alpha@@5 (FieldTypeInv0 (type f@@4))))
 (=> (and (and (= (type o@@17) refType) (= (type f@@4) (FieldType alpha@@5))) (not ($IsGhostField f@@4))) (= (MapType1Select h@@15 o@@17 f@@4) (MapType1Select k@@2 o@@17 f@@4))))
 :qid |fastexpb.659:26|
 :skolemid |111|
 :pattern ( (MapType1Select k@@2 o@@17 f@@4))
))))
 :qid |fastexpb.655:15|
 :skolemid |112|
 :pattern ( ($HeapSuccGhost h@@15 k@@2))
)))
(assert (forall ((s@@3 T@U) ) (! (let ((T@@5 (MapType0TypeInv0 (type s@@3))))
 (=> (= (type s@@3) (MapType0Type T@@5 boolType)) (<= 0 (|Set#Card| s@@3))))
 :qid |fastexpb.721:18|
 :skolemid |117|
 :pattern ( (|Set#Card| s@@3))
)))
(assert (forall ((T@@6 T@T) ) (! (= (type (|Set#Empty| T@@6)) (MapType0Type T@@6 boolType))
 :qid |funType:Set#Empty|
 :pattern ( (|Set#Empty| T@@6))
)))
(assert (forall ((o@@18 T@U) ) (! (let ((T@@7 (type o@@18)))
 (not (U_2_bool (MapType0Select (|Set#Empty| T@@7) o@@18))))
 :qid |fastexpb.725:18|
 :skolemid |118|
 :pattern ( (let ((T@@7 (type o@@18)))
(MapType0Select (|Set#Empty| T@@7) o@@18)))
)))
(assert (forall ((s@@4 T@U) ) (! (let ((T@@8 (MapType0TypeInv0 (type s@@4))))
 (=> (= (type s@@4) (MapType0Type T@@8 boolType)) (and (and (=> (= (|Set#Card| s@@4) 0) (= s@@4 (|Set#Empty| T@@8))) (=> (= s@@4 (|Set#Empty| T@@8)) (= (|Set#Card| s@@4) 0))) (=> (not (= (|Set#Card| s@@4) 0)) (exists ((x@@16 T@U) ) (!  (and (= (type x@@16) T@@8) (U_2_bool (MapType0Select s@@4 x@@16)))
 :qid |fastexpb.730:39|
 :skolemid |119|
 :no-pattern (type x@@16)
 :no-pattern (U_2_int x@@16)
 :no-pattern (U_2_bool x@@16)
))))))
 :qid |fastexpb.727:18|
 :skolemid |120|
 :pattern ( (|Set#Card| s@@4))
)))
(assert (forall ((arg0@@68 T@U) ) (! (let ((T@@9 (type arg0@@68)))
(= (type (|Set#Singleton| arg0@@68)) (MapType0Type T@@9 boolType)))
 :qid |funType:Set#Singleton|
 :pattern ( (|Set#Singleton| arg0@@68))
)))
(assert (forall ((r@@1 T@U) ) (! (U_2_bool (MapType0Select (|Set#Singleton| r@@1) r@@1))
 :qid |fastexpb.734:18|
 :skolemid |121|
 :pattern ( (|Set#Singleton| r@@1))
)))
(assert (forall ((r@@2 T@U) (o@@19 T@U) ) (! (let ((T@@10 (type r@@2)))
 (=> (= (type o@@19) T@@10) (and (=> (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@19)) (= r@@2 o@@19)) (=> (= r@@2 o@@19) (U_2_bool (MapType0Select (|Set#Singleton| r@@2) o@@19))))))
 :qid |fastexpb.736:18|
 :skolemid |122|
 :pattern ( (MapType0Select (|Set#Singleton| r@@2) o@@19))
)))
(assert (forall ((r@@3 T@U) ) (! (= (|Set#Card| (|Set#Singleton| r@@3)) 1)
 :qid |fastexpb.740:18|
 :skolemid |123|
 :pattern ( (|Set#Card| (|Set#Singleton| r@@3)))
)))
(assert (forall ((arg0@@69 T@U) (arg1@@23 T@U) ) (! (let ((T@@11 (type arg1@@23)))
(= (type (|Set#UnionOne| arg0@@69 arg1@@23)) (MapType0Type T@@11 boolType)))
 :qid |funType:Set#UnionOne|
 :pattern ( (|Set#UnionOne| arg0@@69 arg1@@23))
)))
(assert (forall ((a@@3 T@U) (x@@17 T@U) (o@@20 T@U) ) (! (let ((T@@12 (type x@@17)))
 (=> (and (= (type a@@3) (MapType0Type T@@12 boolType)) (= (type o@@20) T@@12)) (and (=> (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@17) o@@20)) (or (= o@@20 x@@17) (U_2_bool (MapType0Select a@@3 o@@20)))) (=> (or (= o@@20 x@@17) (U_2_bool (MapType0Select a@@3 o@@20))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@3 x@@17) o@@20))))))
 :qid |fastexpb.746:18|
 :skolemid |124|
 :pattern ( (MapType0Select (|Set#UnionOne| a@@3 x@@17) o@@20))
)))
(assert (forall ((a@@4 T@U) (x@@18 T@U) ) (! (let ((T@@13 (type x@@18)))
 (=> (= (type a@@4) (MapType0Type T@@13 boolType)) (U_2_bool (MapType0Select (|Set#UnionOne| a@@4 x@@18) x@@18))))
 :qid |fastexpb.750:18|
 :skolemid |125|
 :pattern ( (|Set#UnionOne| a@@4 x@@18))
)))
(assert (forall ((a@@5 T@U) (x@@19 T@U) (y@@1 T@U) ) (! (let ((T@@14 (type x@@19)))
 (=> (and (and (= (type a@@5) (MapType0Type T@@14 boolType)) (= (type y@@1) T@@14)) (U_2_bool (MapType0Select a@@5 y@@1))) (U_2_bool (MapType0Select (|Set#UnionOne| a@@5 x@@19) y@@1))))
 :qid |fastexpb.752:18|
 :skolemid |126|
 :pattern ( (|Set#UnionOne| a@@5 x@@19) (MapType0Select a@@5 y@@1))
)))
(assert (forall ((a@@6 T@U) (x@@20 T@U) ) (! (let ((T@@15 (type x@@20)))
 (=> (and (= (type a@@6) (MapType0Type T@@15 boolType)) (U_2_bool (MapType0Select a@@6 x@@20))) (= (|Set#Card| (|Set#UnionOne| a@@6 x@@20)) (|Set#Card| a@@6))))
 :qid |fastexpb.756:18|
 :skolemid |127|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@6 x@@20)))
)))
(assert (forall ((a@@7 T@U) (x@@21 T@U) ) (! (let ((T@@16 (type x@@21)))
 (=> (and (= (type a@@7) (MapType0Type T@@16 boolType)) (not (U_2_bool (MapType0Select a@@7 x@@21)))) (= (|Set#Card| (|Set#UnionOne| a@@7 x@@21)) (+ (|Set#Card| a@@7) 1))))
 :qid |fastexpb.760:18|
 :skolemid |128|
 :pattern ( (|Set#Card| (|Set#UnionOne| a@@7 x@@21)))
)))
(assert (forall ((arg0@@70 T@U) (arg1@@24 T@U) ) (! (let ((T@@17 (MapType0TypeInv0 (type arg0@@70))))
(= (type (|Set#Union| arg0@@70 arg1@@24)) (MapType0Type T@@17 boolType)))
 :qid |funType:Set#Union|
 :pattern ( (|Set#Union| arg0@@70 arg1@@24))
)))
(assert (forall ((a@@8 T@U) (b@@3 T@U) (o@@21 T@U) ) (! (let ((T@@18 (type o@@21)))
 (=> (and (= (type a@@8) (MapType0Type T@@18 boolType)) (= (type b@@3) (MapType0Type T@@18 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@21)) (or (U_2_bool (MapType0Select a@@8 o@@21)) (U_2_bool (MapType0Select b@@3 o@@21)))) (=> (or (U_2_bool (MapType0Select a@@8 o@@21)) (U_2_bool (MapType0Select b@@3 o@@21))) (U_2_bool (MapType0Select (|Set#Union| a@@8 b@@3) o@@21))))))
 :qid |fastexpb.766:18|
 :skolemid |129|
 :pattern ( (MapType0Select (|Set#Union| a@@8 b@@3) o@@21))
)))
(assert (forall ((a@@9 T@U) (b@@4 T@U) (y@@2 T@U) ) (! (let ((T@@19 (type y@@2)))
 (=> (and (and (= (type a@@9) (MapType0Type T@@19 boolType)) (= (type b@@4) (MapType0Type T@@19 boolType))) (U_2_bool (MapType0Select a@@9 y@@2))) (U_2_bool (MapType0Select (|Set#Union| a@@9 b@@4) y@@2))))
 :qid |fastexpb.770:18|
 :skolemid |130|
 :pattern ( (|Set#Union| a@@9 b@@4) (MapType0Select a@@9 y@@2))
)))
(assert (forall ((a@@10 T@U) (b@@5 T@U) (y@@3 T@U) ) (! (let ((T@@20 (type y@@3)))
 (=> (and (and (= (type a@@10) (MapType0Type T@@20 boolType)) (= (type b@@5) (MapType0Type T@@20 boolType))) (U_2_bool (MapType0Select b@@5 y@@3))) (U_2_bool (MapType0Select (|Set#Union| a@@10 b@@5) y@@3))))
 :qid |fastexpb.774:18|
 :skolemid |131|
 :pattern ( (|Set#Union| a@@10 b@@5) (MapType0Select b@@5 y@@3))
)))
(assert (forall ((arg0@@71 T@U) (arg1@@25 T@U) ) (! (let ((T@@21 (MapType0TypeInv0 (type arg0@@71))))
(= (type (|Set#Difference| arg0@@71 arg1@@25)) (MapType0Type T@@21 boolType)))
 :qid |funType:Set#Difference|
 :pattern ( (|Set#Difference| arg0@@71 arg1@@25))
)))
(assert (forall ((a@@11 T@U) (b@@6 T@U) ) (! (let ((T@@22 (MapType0TypeInv0 (type a@@11))))
 (=> (and (and (= (type a@@11) (MapType0Type T@@22 boolType)) (= (type b@@6) (MapType0Type T@@22 boolType))) (|Set#Disjoint| a@@11 b@@6)) (and (= (|Set#Difference| (|Set#Union| a@@11 b@@6) a@@11) b@@6) (= (|Set#Difference| (|Set#Union| a@@11 b@@6) b@@6) a@@11))))
 :qid |fastexpb.778:18|
 :skolemid |132|
 :pattern ( (|Set#Union| a@@11 b@@6))
)))
(assert (forall ((arg0@@72 T@U) (arg1@@26 T@U) ) (! (let ((T@@23 (MapType0TypeInv0 (type arg0@@72))))
(= (type (|Set#Intersection| arg0@@72 arg1@@26)) (MapType0Type T@@23 boolType)))
 :qid |funType:Set#Intersection|
 :pattern ( (|Set#Intersection| arg0@@72 arg1@@26))
)))
(assert (forall ((a@@12 T@U) (b@@7 T@U) (o@@22 T@U) ) (! (let ((T@@24 (type o@@22)))
 (=> (and (= (type a@@12) (MapType0Type T@@24 boolType)) (= (type b@@7) (MapType0Type T@@24 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@22)) (and (U_2_bool (MapType0Select a@@12 o@@22)) (U_2_bool (MapType0Select b@@7 o@@22)))) (=> (and (U_2_bool (MapType0Select a@@12 o@@22)) (U_2_bool (MapType0Select b@@7 o@@22))) (U_2_bool (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@22))))))
 :qid |fastexpb.786:18|
 :skolemid |133|
 :pattern ( (MapType0Select (|Set#Intersection| a@@12 b@@7) o@@22))
)))
(assert (forall ((a@@13 T@U) (b@@8 T@U) ) (! (let ((T@@25 (MapType0TypeInv0 (type a@@13))))
 (=> (and (= (type a@@13) (MapType0Type T@@25 boolType)) (= (type b@@8) (MapType0Type T@@25 boolType))) (= (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8) (|Set#Union| a@@13 b@@8))))
 :qid |fastexpb.790:18|
 :skolemid |134|
 :pattern ( (|Set#Union| (|Set#Union| a@@13 b@@8) b@@8))
)))
(assert (forall ((a@@14 T@U) (b@@9 T@U) ) (! (let ((T@@26 (MapType0TypeInv0 (type a@@14))))
 (=> (and (= (type a@@14) (MapType0Type T@@26 boolType)) (= (type b@@9) (MapType0Type T@@26 boolType))) (= (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)) (|Set#Union| a@@14 b@@9))))
 :qid |fastexpb.794:18|
 :skolemid |135|
 :pattern ( (|Set#Union| a@@14 (|Set#Union| a@@14 b@@9)))
)))
(assert (forall ((a@@15 T@U) (b@@10 T@U) ) (! (let ((T@@27 (MapType0TypeInv0 (type a@@15))))
 (=> (and (= (type a@@15) (MapType0Type T@@27 boolType)) (= (type b@@10) (MapType0Type T@@27 boolType))) (= (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10) (|Set#Intersection| a@@15 b@@10))))
 :qid |fastexpb.798:18|
 :skolemid |136|
 :pattern ( (|Set#Intersection| (|Set#Intersection| a@@15 b@@10) b@@10))
)))
(assert (forall ((a@@16 T@U) (b@@11 T@U) ) (! (let ((T@@28 (MapType0TypeInv0 (type a@@16))))
 (=> (and (= (type a@@16) (MapType0Type T@@28 boolType)) (= (type b@@11) (MapType0Type T@@28 boolType))) (= (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)) (|Set#Intersection| a@@16 b@@11))))
 :qid |fastexpb.802:18|
 :skolemid |137|
 :pattern ( (|Set#Intersection| a@@16 (|Set#Intersection| a@@16 b@@11)))
)))
(assert (forall ((a@@17 T@U) (b@@12 T@U) ) (! (let ((T@@29 (MapType0TypeInv0 (type a@@17))))
 (=> (and (= (type a@@17) (MapType0Type T@@29 boolType)) (= (type b@@12) (MapType0Type T@@29 boolType))) (= (+ (|Set#Card| (|Set#Union| a@@17 b@@12)) (|Set#Card| (|Set#Intersection| a@@17 b@@12))) (+ (|Set#Card| a@@17) (|Set#Card| b@@12)))))
 :qid |fastexpb.806:18|
 :skolemid |138|
 :pattern ( (|Set#Card| (|Set#Union| a@@17 b@@12)))
 :pattern ( (|Set#Card| (|Set#Intersection| a@@17 b@@12)))
)))
(assert (forall ((a@@18 T@U) (b@@13 T@U) (o@@23 T@U) ) (! (let ((T@@30 (type o@@23)))
 (=> (and (= (type a@@18) (MapType0Type T@@30 boolType)) (= (type b@@13) (MapType0Type T@@30 boolType))) (and (=> (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@23)) (and (U_2_bool (MapType0Select a@@18 o@@23)) (not (U_2_bool (MapType0Select b@@13 o@@23))))) (=> (and (U_2_bool (MapType0Select a@@18 o@@23)) (not (U_2_bool (MapType0Select b@@13 o@@23)))) (U_2_bool (MapType0Select (|Set#Difference| a@@18 b@@13) o@@23))))))
 :qid |fastexpb.813:18|
 :skolemid |139|
 :pattern ( (MapType0Select (|Set#Difference| a@@18 b@@13) o@@23))
)))
(assert (forall ((a@@19 T@U) (b@@14 T@U) (y@@4 T@U) ) (! (let ((T@@31 (type y@@4)))
 (=> (and (and (= (type a@@19) (MapType0Type T@@31 boolType)) (= (type b@@14) (MapType0Type T@@31 boolType))) (U_2_bool (MapType0Select b@@14 y@@4))) (not (U_2_bool (MapType0Select (|Set#Difference| a@@19 b@@14) y@@4)))))
 :qid |fastexpb.817:18|
 :skolemid |140|
 :pattern ( (|Set#Difference| a@@19 b@@14) (MapType0Select b@@14 y@@4))
)))
(assert (forall ((a@@20 T@U) (b@@15 T@U) ) (! (let ((T@@32 (MapType0TypeInv0 (type a@@20))))
 (=> (and (= (type a@@20) (MapType0Type T@@32 boolType)) (= (type b@@15) (MapType0Type T@@32 boolType))) (and (= (+ (+ (|Set#Card| (|Set#Difference| a@@20 b@@15)) (|Set#Card| (|Set#Difference| b@@15 a@@20))) (|Set#Card| (|Set#Intersection| a@@20 b@@15))) (|Set#Card| (|Set#Union| a@@20 b@@15))) (= (|Set#Card| (|Set#Difference| a@@20 b@@15)) (- (|Set#Card| a@@20) (|Set#Card| (|Set#Intersection| a@@20 b@@15)))))))
 :qid |fastexpb.821:18|
 :skolemid |141|
 :pattern ( (|Set#Card| (|Set#Difference| a@@20 b@@15)))
)))
(assert (forall ((a@@21 T@U) (b@@16 T@U) ) (! (let ((T@@33 (MapType0TypeInv0 (type a@@21))))
 (=> (and (= (type a@@21) (MapType0Type T@@33 boolType)) (= (type b@@16) (MapType0Type T@@33 boolType))) (and (=> (|Set#Subset| a@@21 b@@16) (forall ((o@@24 T@U) ) (!  (=> (and (= (type o@@24) T@@33) (U_2_bool (MapType0Select a@@21 o@@24))) (U_2_bool (MapType0Select b@@16 o@@24)))
 :qid |fastexpb.833:33|
 :skolemid |142|
 :pattern ( (MapType0Select a@@21 o@@24))
 :pattern ( (MapType0Select b@@16 o@@24))
))) (=> (forall ((o@@25 T@U) ) (!  (=> (and (= (type o@@25) T@@33) (U_2_bool (MapType0Select a@@21 o@@25))) (U_2_bool (MapType0Select b@@16 o@@25)))
 :qid |fastexpb.833:33|
 :skolemid |142|
 :pattern ( (MapType0Select a@@21 o@@25))
 :pattern ( (MapType0Select b@@16 o@@25))
)) (|Set#Subset| a@@21 b@@16)))))
 :qid |fastexpb.831:18|
 :skolemid |143|
 :pattern ( (|Set#Subset| a@@21 b@@16))
)))
(assert (forall ((a@@22 T@U) (b@@17 T@U) ) (! (let ((T@@34 (MapType0TypeInv0 (type a@@22))))
 (=> (and (= (type a@@22) (MapType0Type T@@34 boolType)) (= (type b@@17) (MapType0Type T@@34 boolType))) (and (=> (|Set#Equal| a@@22 b@@17) (forall ((o@@26 T@U) ) (!  (=> (= (type o@@26) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@26)) (U_2_bool (MapType0Select b@@17 o@@26))) (=> (U_2_bool (MapType0Select b@@17 o@@26)) (U_2_bool (MapType0Select a@@22 o@@26)))))
 :qid |fastexpb.839:32|
 :skolemid |144|
 :pattern ( (MapType0Select a@@22 o@@26))
 :pattern ( (MapType0Select b@@17 o@@26))
))) (=> (forall ((o@@27 T@U) ) (!  (=> (= (type o@@27) T@@34) (and (=> (U_2_bool (MapType0Select a@@22 o@@27)) (U_2_bool (MapType0Select b@@17 o@@27))) (=> (U_2_bool (MapType0Select b@@17 o@@27)) (U_2_bool (MapType0Select a@@22 o@@27)))))
 :qid |fastexpb.839:32|
 :skolemid |144|
 :pattern ( (MapType0Select a@@22 o@@27))
 :pattern ( (MapType0Select b@@17 o@@27))
)) (|Set#Equal| a@@22 b@@17)))))
 :qid |fastexpb.837:18|
 :skolemid |145|
 :pattern ( (|Set#Equal| a@@22 b@@17))
)))
(assert (forall ((a@@23 T@U) (b@@18 T@U) ) (! (let ((T@@35 (MapType0TypeInv0 (type a@@23))))
 (=> (and (and (= (type a@@23) (MapType0Type T@@35 boolType)) (= (type b@@18) (MapType0Type T@@35 boolType))) (|Set#Equal| a@@23 b@@18)) (= a@@23 b@@18)))
 :qid |fastexpb.841:18|
 :skolemid |146|
 :pattern ( (|Set#Equal| a@@23 b@@18))
)))
(assert (forall ((a@@24 T@U) (b@@19 T@U) ) (! (let ((T@@36 (MapType0TypeInv0 (type a@@24))))
 (=> (and (= (type a@@24) (MapType0Type T@@36 boolType)) (= (type b@@19) (MapType0Type T@@36 boolType))) (and (=> (|Set#Disjoint| a@@24 b@@19) (forall ((o@@28 T@U) ) (!  (=> (= (type o@@28) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@28))) (not (U_2_bool (MapType0Select b@@19 o@@28)))))
 :qid |fastexpb.847:35|
 :skolemid |147|
 :pattern ( (MapType0Select a@@24 o@@28))
 :pattern ( (MapType0Select b@@19 o@@28))
))) (=> (forall ((o@@29 T@U) ) (!  (=> (= (type o@@29) T@@36) (or (not (U_2_bool (MapType0Select a@@24 o@@29))) (not (U_2_bool (MapType0Select b@@19 o@@29)))))
 :qid |fastexpb.847:35|
 :skolemid |147|
 :pattern ( (MapType0Select a@@24 o@@29))
 :pattern ( (MapType0Select b@@19 o@@29))
)) (|Set#Disjoint| a@@24 b@@19)))))
 :qid |fastexpb.845:18|
 :skolemid |148|
 :pattern ( (|Set#Disjoint| a@@24 b@@19))
)))
(assert (forall ((T@@37 T@T) ) (! (= (type (|ISet#Empty| T@@37)) (MapType0Type T@@37 boolType))
 :qid |funType:ISet#Empty|
 :pattern ( (|ISet#Empty| T@@37))
)))
(assert (forall ((o@@30 T@U) ) (! (let ((T@@38 (type o@@30)))
 (not (U_2_bool (MapType0Select (|ISet#Empty| T@@38) o@@30))))
 :qid |fastexpb.853:18|
 :skolemid |149|
 :pattern ( (let ((T@@38 (type o@@30)))
(MapType0Select (|ISet#Empty| T@@38) o@@30)))
)))
(assert (forall ((arg0@@73 T@U) (arg1@@27 T@U) ) (! (let ((T@@39 (type arg1@@27)))
(= (type (|ISet#UnionOne| arg0@@73 arg1@@27)) (MapType0Type T@@39 boolType)))
 :qid |funType:ISet#UnionOne|
 :pattern ( (|ISet#UnionOne| arg0@@73 arg1@@27))
)))
(assert (forall ((a@@25 T@U) (x@@22 T@U) (o@@31 T@U) ) (! (let ((T@@40 (type x@@22)))
 (=> (and (= (type a@@25) (MapType0Type T@@40 boolType)) (= (type o@@31) T@@40)) (and (=> (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@22) o@@31)) (or (= o@@31 x@@22) (U_2_bool (MapType0Select a@@25 o@@31)))) (=> (or (= o@@31 x@@22) (U_2_bool (MapType0Select a@@25 o@@31))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@25 x@@22) o@@31))))))
 :qid |fastexpb.857:18|
 :skolemid |150|
 :pattern ( (MapType0Select (|ISet#UnionOne| a@@25 x@@22) o@@31))
)))
(assert (forall ((a@@26 T@U) (x@@23 T@U) ) (! (let ((T@@41 (type x@@23)))
 (=> (= (type a@@26) (MapType0Type T@@41 boolType)) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@26 x@@23) x@@23))))
 :qid |fastexpb.861:18|
 :skolemid |151|
 :pattern ( (|ISet#UnionOne| a@@26 x@@23))
)))
(assert (forall ((a@@27 T@U) (x@@24 T@U) (y@@5 T@U) ) (! (let ((T@@42 (type x@@24)))
 (=> (and (and (= (type a@@27) (MapType0Type T@@42 boolType)) (= (type y@@5) T@@42)) (U_2_bool (MapType0Select a@@27 y@@5))) (U_2_bool (MapType0Select (|ISet#UnionOne| a@@27 x@@24) y@@5))))
 :qid |fastexpb.863:18|
 :skolemid |152|
 :pattern ( (|ISet#UnionOne| a@@27 x@@24) (MapType0Select a@@27 y@@5))
)))
(assert (forall ((arg0@@74 T@U) (arg1@@28 T@U) ) (! (let ((T@@43 (MapType0TypeInv0 (type arg0@@74))))
(= (type (|ISet#Union| arg0@@74 arg1@@28)) (MapType0Type T@@43 boolType)))
 :qid |funType:ISet#Union|
 :pattern ( (|ISet#Union| arg0@@74 arg1@@28))
)))
(assert (forall ((a@@28 T@U) (b@@20 T@U) (o@@32 T@U) ) (! (let ((T@@44 (type o@@32)))
 (=> (and (= (type a@@28) (MapType0Type T@@44 boolType)) (= (type b@@20) (MapType0Type T@@44 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@32)) (or (U_2_bool (MapType0Select a@@28 o@@32)) (U_2_bool (MapType0Select b@@20 o@@32)))) (=> (or (U_2_bool (MapType0Select a@@28 o@@32)) (U_2_bool (MapType0Select b@@20 o@@32))) (U_2_bool (MapType0Select (|ISet#Union| a@@28 b@@20) o@@32))))))
 :qid |fastexpb.869:18|
 :skolemid |153|
 :pattern ( (MapType0Select (|ISet#Union| a@@28 b@@20) o@@32))
)))
(assert (forall ((a@@29 T@U) (b@@21 T@U) (y@@6 T@U) ) (! (let ((T@@45 (type y@@6)))
 (=> (and (and (= (type a@@29) (MapType0Type T@@45 boolType)) (= (type b@@21) (MapType0Type T@@45 boolType))) (U_2_bool (MapType0Select a@@29 y@@6))) (U_2_bool (MapType0Select (|ISet#Union| a@@29 b@@21) y@@6))))
 :qid |fastexpb.873:18|
 :skolemid |154|
 :pattern ( (|ISet#Union| a@@29 b@@21) (MapType0Select a@@29 y@@6))
)))
(assert (forall ((a@@30 T@U) (b@@22 T@U) (y@@7 T@U) ) (! (let ((T@@46 (type y@@7)))
 (=> (and (and (= (type a@@30) (MapType0Type T@@46 boolType)) (= (type b@@22) (MapType0Type T@@46 boolType))) (U_2_bool (MapType0Select b@@22 y@@7))) (U_2_bool (MapType0Select (|ISet#Union| a@@30 b@@22) y@@7))))
 :qid |fastexpb.877:18|
 :skolemid |155|
 :pattern ( (|ISet#Union| a@@30 b@@22) (MapType0Select b@@22 y@@7))
)))
(assert (forall ((arg0@@75 T@U) (arg1@@29 T@U) ) (! (let ((T@@47 (MapType0TypeInv0 (type arg0@@75))))
(= (type (|ISet#Difference| arg0@@75 arg1@@29)) (MapType0Type T@@47 boolType)))
 :qid |funType:ISet#Difference|
 :pattern ( (|ISet#Difference| arg0@@75 arg1@@29))
)))
(assert (forall ((a@@31 T@U) (b@@23 T@U) ) (! (let ((T@@48 (MapType0TypeInv0 (type a@@31))))
 (=> (and (and (= (type a@@31) (MapType0Type T@@48 boolType)) (= (type b@@23) (MapType0Type T@@48 boolType))) (|ISet#Disjoint| a@@31 b@@23)) (and (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) a@@31) b@@23) (= (|ISet#Difference| (|ISet#Union| a@@31 b@@23) b@@23) a@@31))))
 :qid |fastexpb.881:18|
 :skolemid |156|
 :pattern ( (|ISet#Union| a@@31 b@@23))
)))
(assert (forall ((arg0@@76 T@U) (arg1@@30 T@U) ) (! (let ((T@@49 (MapType0TypeInv0 (type arg0@@76))))
(= (type (|ISet#Intersection| arg0@@76 arg1@@30)) (MapType0Type T@@49 boolType)))
 :qid |funType:ISet#Intersection|
 :pattern ( (|ISet#Intersection| arg0@@76 arg1@@30))
)))
(assert (forall ((a@@32 T@U) (b@@24 T@U) (o@@33 T@U) ) (! (let ((T@@50 (type o@@33)))
 (=> (and (= (type a@@32) (MapType0Type T@@50 boolType)) (= (type b@@24) (MapType0Type T@@50 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@33)) (and (U_2_bool (MapType0Select a@@32 o@@33)) (U_2_bool (MapType0Select b@@24 o@@33)))) (=> (and (U_2_bool (MapType0Select a@@32 o@@33)) (U_2_bool (MapType0Select b@@24 o@@33))) (U_2_bool (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@33))))))
 :qid |fastexpb.889:18|
 :skolemid |157|
 :pattern ( (MapType0Select (|ISet#Intersection| a@@32 b@@24) o@@33))
)))
(assert (forall ((a@@33 T@U) (b@@25 T@U) ) (! (let ((T@@51 (MapType0TypeInv0 (type a@@33))))
 (=> (and (= (type a@@33) (MapType0Type T@@51 boolType)) (= (type b@@25) (MapType0Type T@@51 boolType))) (= (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25) (|ISet#Union| a@@33 b@@25))))
 :qid |fastexpb.893:18|
 :skolemid |158|
 :pattern ( (|ISet#Union| (|ISet#Union| a@@33 b@@25) b@@25))
)))
(assert (forall ((a@@34 T@U) (b@@26 T@U) ) (! (let ((T@@52 (MapType0TypeInv0 (type a@@34))))
 (=> (and (= (type a@@34) (MapType0Type T@@52 boolType)) (= (type b@@26) (MapType0Type T@@52 boolType))) (= (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)) (|ISet#Union| a@@34 b@@26))))
 :qid |fastexpb.897:18|
 :skolemid |159|
 :pattern ( (|ISet#Union| a@@34 (|ISet#Union| a@@34 b@@26)))
)))
(assert (forall ((a@@35 T@U) (b@@27 T@U) ) (! (let ((T@@53 (MapType0TypeInv0 (type a@@35))))
 (=> (and (= (type a@@35) (MapType0Type T@@53 boolType)) (= (type b@@27) (MapType0Type T@@53 boolType))) (= (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27) (|ISet#Intersection| a@@35 b@@27))))
 :qid |fastexpb.901:18|
 :skolemid |160|
 :pattern ( (|ISet#Intersection| (|ISet#Intersection| a@@35 b@@27) b@@27))
)))
(assert (forall ((a@@36 T@U) (b@@28 T@U) ) (! (let ((T@@54 (MapType0TypeInv0 (type a@@36))))
 (=> (and (= (type a@@36) (MapType0Type T@@54 boolType)) (= (type b@@28) (MapType0Type T@@54 boolType))) (= (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)) (|ISet#Intersection| a@@36 b@@28))))
 :qid |fastexpb.905:18|
 :skolemid |161|
 :pattern ( (|ISet#Intersection| a@@36 (|ISet#Intersection| a@@36 b@@28)))
)))
(assert (forall ((a@@37 T@U) (b@@29 T@U) (o@@34 T@U) ) (! (let ((T@@55 (type o@@34)))
 (=> (and (= (type a@@37) (MapType0Type T@@55 boolType)) (= (type b@@29) (MapType0Type T@@55 boolType))) (and (=> (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@34)) (and (U_2_bool (MapType0Select a@@37 o@@34)) (not (U_2_bool (MapType0Select b@@29 o@@34))))) (=> (and (U_2_bool (MapType0Select a@@37 o@@34)) (not (U_2_bool (MapType0Select b@@29 o@@34)))) (U_2_bool (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@34))))))
 :qid |fastexpb.911:18|
 :skolemid |162|
 :pattern ( (MapType0Select (|ISet#Difference| a@@37 b@@29) o@@34))
)))
(assert (forall ((a@@38 T@U) (b@@30 T@U) (y@@8 T@U) ) (! (let ((T@@56 (type y@@8)))
 (=> (and (and (= (type a@@38) (MapType0Type T@@56 boolType)) (= (type b@@30) (MapType0Type T@@56 boolType))) (U_2_bool (MapType0Select b@@30 y@@8))) (not (U_2_bool (MapType0Select (|ISet#Difference| a@@38 b@@30) y@@8)))))
 :qid |fastexpb.915:18|
 :skolemid |163|
 :pattern ( (|ISet#Difference| a@@38 b@@30) (MapType0Select b@@30 y@@8))
)))
(assert (forall ((a@@39 T@U) (b@@31 T@U) ) (! (let ((T@@57 (MapType0TypeInv0 (type a@@39))))
 (=> (and (= (type a@@39) (MapType0Type T@@57 boolType)) (= (type b@@31) (MapType0Type T@@57 boolType))) (and (=> (|ISet#Subset| a@@39 b@@31) (forall ((o@@35 T@U) ) (!  (=> (and (= (type o@@35) T@@57) (U_2_bool (MapType0Select a@@39 o@@35))) (U_2_bool (MapType0Select b@@31 o@@35)))
 :qid |fastexpb.923:34|
 :skolemid |164|
 :pattern ( (MapType0Select a@@39 o@@35))
 :pattern ( (MapType0Select b@@31 o@@35))
))) (=> (forall ((o@@36 T@U) ) (!  (=> (and (= (type o@@36) T@@57) (U_2_bool (MapType0Select a@@39 o@@36))) (U_2_bool (MapType0Select b@@31 o@@36)))
 :qid |fastexpb.923:34|
 :skolemid |164|
 :pattern ( (MapType0Select a@@39 o@@36))
 :pattern ( (MapType0Select b@@31 o@@36))
)) (|ISet#Subset| a@@39 b@@31)))))
 :qid |fastexpb.921:18|
 :skolemid |165|
 :pattern ( (|ISet#Subset| a@@39 b@@31))
)))
(assert (forall ((a@@40 T@U) (b@@32 T@U) ) (! (let ((T@@58 (MapType0TypeInv0 (type a@@40))))
 (=> (and (= (type a@@40) (MapType0Type T@@58 boolType)) (= (type b@@32) (MapType0Type T@@58 boolType))) (and (=> (|ISet#Equal| a@@40 b@@32) (forall ((o@@37 T@U) ) (!  (=> (= (type o@@37) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@37)) (U_2_bool (MapType0Select b@@32 o@@37))) (=> (U_2_bool (MapType0Select b@@32 o@@37)) (U_2_bool (MapType0Select a@@40 o@@37)))))
 :qid |fastexpb.929:33|
 :skolemid |166|
 :pattern ( (MapType0Select a@@40 o@@37))
 :pattern ( (MapType0Select b@@32 o@@37))
))) (=> (forall ((o@@38 T@U) ) (!  (=> (= (type o@@38) T@@58) (and (=> (U_2_bool (MapType0Select a@@40 o@@38)) (U_2_bool (MapType0Select b@@32 o@@38))) (=> (U_2_bool (MapType0Select b@@32 o@@38)) (U_2_bool (MapType0Select a@@40 o@@38)))))
 :qid |fastexpb.929:33|
 :skolemid |166|
 :pattern ( (MapType0Select a@@40 o@@38))
 :pattern ( (MapType0Select b@@32 o@@38))
)) (|ISet#Equal| a@@40 b@@32)))))
 :qid |fastexpb.927:18|
 :skolemid |167|
 :pattern ( (|ISet#Equal| a@@40 b@@32))
)))
(assert (forall ((a@@41 T@U) (b@@33 T@U) ) (! (let ((T@@59 (MapType0TypeInv0 (type a@@41))))
 (=> (and (and (= (type a@@41) (MapType0Type T@@59 boolType)) (= (type b@@33) (MapType0Type T@@59 boolType))) (|ISet#Equal| a@@41 b@@33)) (= a@@41 b@@33)))
 :qid |fastexpb.931:18|
 :skolemid |168|
 :pattern ( (|ISet#Equal| a@@41 b@@33))
)))
(assert (forall ((a@@42 T@U) (b@@34 T@U) ) (! (let ((T@@60 (MapType0TypeInv0 (type a@@42))))
 (=> (and (= (type a@@42) (MapType0Type T@@60 boolType)) (= (type b@@34) (MapType0Type T@@60 boolType))) (and (=> (|ISet#Disjoint| a@@42 b@@34) (forall ((o@@39 T@U) ) (!  (=> (= (type o@@39) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@39))) (not (U_2_bool (MapType0Select b@@34 o@@39)))))
 :qid |fastexpb.939:36|
 :skolemid |169|
 :pattern ( (MapType0Select a@@42 o@@39))
 :pattern ( (MapType0Select b@@34 o@@39))
))) (=> (forall ((o@@40 T@U) ) (!  (=> (= (type o@@40) T@@60) (or (not (U_2_bool (MapType0Select a@@42 o@@40))) (not (U_2_bool (MapType0Select b@@34 o@@40)))))
 :qid |fastexpb.939:36|
 :skolemid |169|
 :pattern ( (MapType0Select a@@42 o@@40))
 :pattern ( (MapType0Select b@@34 o@@40))
)) (|ISet#Disjoint| a@@42 b@@34)))))
 :qid |fastexpb.937:18|
 :skolemid |170|
 :pattern ( (|ISet#Disjoint| a@@42 b@@34))
)))
(assert (forall ((a@@43 Int) (b@@35 Int) ) (!  (and (=> (<= a@@43 b@@35) (= (|Math#min| a@@43 b@@35) a@@43)) (=> (= (|Math#min| a@@43 b@@35) a@@43) (<= a@@43 b@@35)))
 :qid |fastexpb.943:15|
 :skolemid |171|
 :pattern ( (|Math#min| a@@43 b@@35))
)))
(assert (forall ((a@@44 Int) (b@@36 Int) ) (!  (and (=> (<= b@@36 a@@44) (= (|Math#min| a@@44 b@@36) b@@36)) (=> (= (|Math#min| a@@44 b@@36) b@@36) (<= b@@36 a@@44)))
 :qid |fastexpb.945:15|
 :skolemid |172|
 :pattern ( (|Math#min| a@@44 b@@36))
)))
(assert (forall ((a@@45 Int) (b@@37 Int) ) (!  (or (= (|Math#min| a@@45 b@@37) a@@45) (= (|Math#min| a@@45 b@@37) b@@37))
 :qid |fastexpb.947:15|
 :skolemid |173|
 :pattern ( (|Math#min| a@@45 b@@37))
)))
(assert (forall ((a@@46 Int) ) (!  (=> (<= 0 a@@46) (= (|Math#clip| a@@46) a@@46))
 :qid |fastexpb.953:15|
 :skolemid |174|
 :pattern ( (|Math#clip| a@@46))
)))
(assert (forall ((a@@47 Int) ) (!  (=> (< a@@47 0) (= (|Math#clip| a@@47) 0))
 :qid |fastexpb.955:15|
 :skolemid |175|
 :pattern ( (|Math#clip| a@@47))
)))
(assert (forall ((ms T@U) ) (! (let ((T@@61 (MapType0TypeInv0 (type ms))))
 (=> (= (type ms) (MapType0Type T@@61 intType)) (and (=> ($IsGoodMultiSet ms) (forall ((bx@@31 T@U) ) (!  (=> (= (type bx@@31) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@31))) (<= (U_2_int (MapType0Select ms bx@@31)) (|MultiSet#Card| ms))))
 :qid |fastexpb.964:19|
 :skolemid |176|
 :pattern ( (MapType0Select ms bx@@31))
))) (=> (forall ((bx@@32 T@U) ) (!  (=> (= (type bx@@32) T@@61) (and (<= 0 (U_2_int (MapType0Select ms bx@@32))) (<= (U_2_int (MapType0Select ms bx@@32)) (|MultiSet#Card| ms))))
 :qid |fastexpb.964:19|
 :skolemid |176|
 :pattern ( (MapType0Select ms bx@@32))
)) ($IsGoodMultiSet ms)))))
 :qid |fastexpb.961:18|
 :skolemid |177|
 :pattern ( ($IsGoodMultiSet ms))
)))
(assert (forall ((s@@5 T@U) ) (! (let ((T@@62 (MapType0TypeInv0 (type s@@5))))
 (=> (= (type s@@5) (MapType0Type T@@62 intType)) (<= 0 (|MultiSet#Card| s@@5))))
 :qid |fastexpb.968:18|
 :skolemid |178|
 :pattern ( (|MultiSet#Card| s@@5))
)))
(assert (forall ((s@@6 T@U) (x@@25 T@U) (n@@5 T@U) ) (! (let ((T@@63 (type x@@25)))
 (=> (and (and (= (type s@@6) (MapType0Type T@@63 intType)) (= (type n@@5) intType)) (<= 0 (U_2_int n@@5))) (= (|MultiSet#Card| (MapType0Store s@@6 x@@25 n@@5)) (+ (- (|MultiSet#Card| s@@6) (U_2_int (MapType0Select s@@6 x@@25))) (U_2_int n@@5)))))
 :qid |fastexpb.970:18|
 :skolemid |179|
 :pattern ( (|MultiSet#Card| (MapType0Store s@@6 x@@25 n@@5)))
)))
(assert (forall ((T@@64 T@T) ) (! (= (type (|MultiSet#Empty| T@@64)) (MapType0Type T@@64 intType))
 :qid |funType:MultiSet#Empty|
 :pattern ( (|MultiSet#Empty| T@@64))
)))
(assert (forall ((o@@41 T@U) ) (! (let ((T@@65 (type o@@41)))
(= (U_2_int (MapType0Select (|MultiSet#Empty| T@@65) o@@41)) 0))
 :qid |fastexpb.976:18|
 :skolemid |180|
 :pattern ( (let ((T@@65 (type o@@41)))
(MapType0Select (|MultiSet#Empty| T@@65) o@@41)))
)))
(assert (forall ((s@@7 T@U) ) (! (let ((T@@66 (MapType0TypeInv0 (type s@@7))))
 (=> (= (type s@@7) (MapType0Type T@@66 intType)) (and (and (=> (= (|MultiSet#Card| s@@7) 0) (= s@@7 (|MultiSet#Empty| T@@66))) (=> (= s@@7 (|MultiSet#Empty| T@@66)) (= (|MultiSet#Card| s@@7) 0))) (=> (not (= (|MultiSet#Card| s@@7) 0)) (exists ((x@@26 T@U) ) (!  (and (= (type x@@26) T@@66) (< 0 (U_2_int (MapType0Select s@@7 x@@26))))
 :qid |fastexpb.981:44|
 :skolemid |181|
 :no-pattern (type x@@26)
 :no-pattern (U_2_int x@@26)
 :no-pattern (U_2_bool x@@26)
))))))
 :qid |fastexpb.978:18|
 :skolemid |182|
 :pattern ( (|MultiSet#Card| s@@7))
)))
(assert (forall ((arg0@@77 T@U) ) (! (let ((T@@67 (type arg0@@77)))
(= (type (|MultiSet#Singleton| arg0@@77)) (MapType0Type T@@67 intType)))
 :qid |funType:MultiSet#Singleton|
 :pattern ( (|MultiSet#Singleton| arg0@@77))
)))
(assert (forall ((r@@4 T@U) (o@@42 T@U) ) (! (let ((T@@68 (type r@@4)))
 (=> (= (type o@@42) T@@68) (and (and (=> (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@42)) 1) (= r@@4 o@@42)) (=> (= r@@4 o@@42) (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@42)) 1))) (and (=> (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@42)) 0) (not (= r@@4 o@@42))) (=> (not (= r@@4 o@@42)) (= (U_2_int (MapType0Select (|MultiSet#Singleton| r@@4) o@@42)) 0))))))
 :qid |fastexpb.985:18|
 :skolemid |183|
 :pattern ( (MapType0Select (|MultiSet#Singleton| r@@4) o@@42))
)))
(assert (forall ((arg0@@78 T@U) (arg1@@31 T@U) ) (! (let ((T@@69 (type arg1@@31)))
(= (type (|MultiSet#UnionOne| arg0@@78 arg1@@31)) (MapType0Type T@@69 intType)))
 :qid |funType:MultiSet#UnionOne|
 :pattern ( (|MultiSet#UnionOne| arg0@@78 arg1@@31))
)))
(assert (forall ((r@@5 T@U) ) (! (let ((T@@70 (type r@@5)))
(= (|MultiSet#Singleton| r@@5) (|MultiSet#UnionOne| (|MultiSet#Empty| T@@70) r@@5)))
 :qid |fastexpb.990:18|
 :skolemid |184|
 :pattern ( (|MultiSet#Singleton| r@@5))
)))
(assert (forall ((a@@48 T@U) (x@@27 T@U) (o@@43 T@U) ) (! (let ((T@@71 (type x@@27)))
 (=> (and (= (type a@@48) (MapType0Type T@@71 intType)) (= (type o@@43) T@@71)) (and (=> (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@27) o@@43))) (or (= o@@43 x@@27) (< 0 (U_2_int (MapType0Select a@@48 o@@43))))) (=> (or (= o@@43 x@@27) (< 0 (U_2_int (MapType0Select a@@48 o@@43)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@48 x@@27) o@@43)))))))
 :qid |fastexpb.996:18|
 :skolemid |185|
 :pattern ( (MapType0Select (|MultiSet#UnionOne| a@@48 x@@27) o@@43))
)))
(assert (forall ((a@@49 T@U) (x@@28 T@U) ) (! (let ((T@@72 (type x@@28)))
 (=> (= (type a@@49) (MapType0Type T@@72 intType)) (= (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@49 x@@28) x@@28)) (+ (U_2_int (MapType0Select a@@49 x@@28)) 1))))
 :qid |fastexpb.1000:18|
 :skolemid |186|
 :pattern ( (|MultiSet#UnionOne| a@@49 x@@28))
)))
(assert (forall ((a@@50 T@U) (x@@29 T@U) (y@@9 T@U) ) (! (let ((T@@73 (type x@@29)))
 (=> (and (and (= (type a@@50) (MapType0Type T@@73 intType)) (= (type y@@9) T@@73)) (< 0 (U_2_int (MapType0Select a@@50 y@@9)))) (< 0 (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@50 x@@29) y@@9)))))
 :qid |fastexpb.1004:18|
 :skolemid |187|
 :pattern ( (|MultiSet#UnionOne| a@@50 x@@29) (MapType0Select a@@50 y@@9))
)))
(assert (forall ((a@@51 T@U) (x@@30 T@U) (y@@10 T@U) ) (! (let ((T@@74 (type x@@30)))
 (=> (and (and (= (type a@@51) (MapType0Type T@@74 intType)) (= (type y@@10) T@@74)) (not (= x@@30 y@@10))) (= (U_2_int (MapType0Select a@@51 y@@10)) (U_2_int (MapType0Select (|MultiSet#UnionOne| a@@51 x@@30) y@@10)))))
 :qid |fastexpb.1008:18|
 :skolemid |188|
 :pattern ( (|MultiSet#UnionOne| a@@51 x@@30) (MapType0Select a@@51 y@@10))
)))
(assert (forall ((a@@52 T@U) (x@@31 T@U) ) (! (let ((T@@75 (type x@@31)))
 (=> (= (type a@@52) (MapType0Type T@@75 intType)) (= (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@31)) (+ (|MultiSet#Card| a@@52) 1))))
 :qid |fastexpb.1012:18|
 :skolemid |189|
 :pattern ( (|MultiSet#Card| (|MultiSet#UnionOne| a@@52 x@@31)))
)))
(assert (forall ((arg0@@79 T@U) (arg1@@32 T@U) ) (! (let ((T@@76 (MapType0TypeInv0 (type arg0@@79))))
(= (type (|MultiSet#Union| arg0@@79 arg1@@32)) (MapType0Type T@@76 intType)))
 :qid |funType:MultiSet#Union|
 :pattern ( (|MultiSet#Union| arg0@@79 arg1@@32))
)))
(assert (forall ((a@@53 T@U) (b@@38 T@U) (o@@44 T@U) ) (! (let ((T@@77 (type o@@44)))
 (=> (and (= (type a@@53) (MapType0Type T@@77 intType)) (= (type b@@38) (MapType0Type T@@77 intType))) (= (U_2_int (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@44)) (+ (U_2_int (MapType0Select a@@53 o@@44)) (U_2_int (MapType0Select b@@38 o@@44))))))
 :qid |fastexpb.1018:18|
 :skolemid |190|
 :pattern ( (MapType0Select (|MultiSet#Union| a@@53 b@@38) o@@44))
)))
(assert (forall ((a@@54 T@U) (b@@39 T@U) ) (! (let ((T@@78 (MapType0TypeInv0 (type a@@54))))
 (=> (and (= (type a@@54) (MapType0Type T@@78 intType)) (= (type b@@39) (MapType0Type T@@78 intType))) (= (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)) (+ (|MultiSet#Card| a@@54) (|MultiSet#Card| b@@39)))))
 :qid |fastexpb.1022:18|
 :skolemid |191|
 :pattern ( (|MultiSet#Card| (|MultiSet#Union| a@@54 b@@39)))
)))
(assert (forall ((arg0@@80 T@U) (arg1@@33 T@U) ) (! (let ((T@@79 (MapType0TypeInv0 (type arg0@@80))))
(= (type (|MultiSet#Intersection| arg0@@80 arg1@@33)) (MapType0Type T@@79 intType)))
 :qid |funType:MultiSet#Intersection|
 :pattern ( (|MultiSet#Intersection| arg0@@80 arg1@@33))
)))
(assert (forall ((a@@55 T@U) (b@@40 T@U) (o@@45 T@U) ) (! (let ((T@@80 (type o@@45)))
 (=> (and (= (type a@@55) (MapType0Type T@@80 intType)) (= (type b@@40) (MapType0Type T@@80 intType))) (= (U_2_int (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@45)) (|Math#min| (U_2_int (MapType0Select a@@55 o@@45)) (U_2_int (MapType0Select b@@40 o@@45))))))
 :qid |fastexpb.1028:18|
 :skolemid |192|
 :pattern ( (MapType0Select (|MultiSet#Intersection| a@@55 b@@40) o@@45))
)))
(assert (forall ((a@@56 T@U) (b@@41 T@U) ) (! (let ((T@@81 (MapType0TypeInv0 (type a@@56))))
 (=> (and (= (type a@@56) (MapType0Type T@@81 intType)) (= (type b@@41) (MapType0Type T@@81 intType))) (= (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41) (|MultiSet#Intersection| a@@56 b@@41))))
 :qid |fastexpb.1032:18|
 :skolemid |193|
 :pattern ( (|MultiSet#Intersection| (|MultiSet#Intersection| a@@56 b@@41) b@@41))
)))
(assert (forall ((a@@57 T@U) (b@@42 T@U) ) (! (let ((T@@82 (MapType0TypeInv0 (type a@@57))))
 (=> (and (= (type a@@57) (MapType0Type T@@82 intType)) (= (type b@@42) (MapType0Type T@@82 intType))) (= (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)) (|MultiSet#Intersection| a@@57 b@@42))))
 :qid |fastexpb.1037:18|
 :skolemid |194|
 :pattern ( (|MultiSet#Intersection| a@@57 (|MultiSet#Intersection| a@@57 b@@42)))
)))
(assert (forall ((arg0@@81 T@U) (arg1@@34 T@U) ) (! (let ((T@@83 (MapType0TypeInv0 (type arg0@@81))))
(= (type (|MultiSet#Difference| arg0@@81 arg1@@34)) (MapType0Type T@@83 intType)))
 :qid |funType:MultiSet#Difference|
 :pattern ( (|MultiSet#Difference| arg0@@81 arg1@@34))
)))
(assert (forall ((a@@58 T@U) (b@@43 T@U) (o@@46 T@U) ) (! (let ((T@@84 (type o@@46)))
 (=> (and (= (type a@@58) (MapType0Type T@@84 intType)) (= (type b@@43) (MapType0Type T@@84 intType))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@46)) (|Math#clip| (- (U_2_int (MapType0Select a@@58 o@@46)) (U_2_int (MapType0Select b@@43 o@@46)))))))
 :qid |fastexpb.1044:18|
 :skolemid |195|
 :pattern ( (MapType0Select (|MultiSet#Difference| a@@58 b@@43) o@@46))
)))
(assert (forall ((a@@59 T@U) (b@@44 T@U) (y@@11 T@U) ) (! (let ((T@@85 (type y@@11)))
 (=> (and (and (= (type a@@59) (MapType0Type T@@85 intType)) (= (type b@@44) (MapType0Type T@@85 intType))) (<= (U_2_int (MapType0Select a@@59 y@@11)) (U_2_int (MapType0Select b@@44 y@@11)))) (= (U_2_int (MapType0Select (|MultiSet#Difference| a@@59 b@@44) y@@11)) 0)))
 :qid |fastexpb.1048:18|
 :skolemid |196|
 :pattern ( (|MultiSet#Difference| a@@59 b@@44) (MapType0Select b@@44 y@@11) (MapType0Select a@@59 y@@11))
)))
(assert (forall ((a@@60 T@U) (b@@45 T@U) ) (! (let ((T@@86 (MapType0TypeInv0 (type a@@60))))
 (=> (and (= (type a@@60) (MapType0Type T@@86 intType)) (= (type b@@45) (MapType0Type T@@86 intType))) (and (= (+ (+ (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (|MultiSet#Card| (|MultiSet#Difference| b@@45 a@@60))) (* 2 (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))) (|MultiSet#Card| (|MultiSet#Union| a@@60 b@@45))) (= (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)) (- (|MultiSet#Card| a@@60) (|MultiSet#Card| (|MultiSet#Intersection| a@@60 b@@45)))))))
 :qid |fastexpb.1052:18|
 :skolemid |197|
 :pattern ( (|MultiSet#Card| (|MultiSet#Difference| a@@60 b@@45)))
)))
(assert (forall ((a@@61 T@U) (b@@46 T@U) ) (! (let ((T@@87 (MapType0TypeInv0 (type a@@61))))
 (=> (and (= (type a@@61) (MapType0Type T@@87 intType)) (= (type b@@46) (MapType0Type T@@87 intType))) (and (=> (|MultiSet#Subset| a@@61 b@@46) (forall ((o@@47 T@U) ) (!  (=> (= (type o@@47) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@47)) (U_2_int (MapType0Select b@@46 o@@47))))
 :qid |fastexpb.1065:38|
 :skolemid |198|
 :pattern ( (MapType0Select a@@61 o@@47))
 :pattern ( (MapType0Select b@@46 o@@47))
))) (=> (forall ((o@@48 T@U) ) (!  (=> (= (type o@@48) T@@87) (<= (U_2_int (MapType0Select a@@61 o@@48)) (U_2_int (MapType0Select b@@46 o@@48))))
 :qid |fastexpb.1065:38|
 :skolemid |198|
 :pattern ( (MapType0Select a@@61 o@@48))
 :pattern ( (MapType0Select b@@46 o@@48))
)) (|MultiSet#Subset| a@@61 b@@46)))))
 :qid |fastexpb.1063:18|
 :skolemid |199|
 :pattern ( (|MultiSet#Subset| a@@61 b@@46))
)))
(assert (forall ((a@@62 T@U) (b@@47 T@U) ) (! (let ((T@@88 (MapType0TypeInv0 (type a@@62))))
 (=> (and (= (type a@@62) (MapType0Type T@@88 intType)) (= (type b@@47) (MapType0Type T@@88 intType))) (and (=> (|MultiSet#Equal| a@@62 b@@47) (forall ((o@@49 T@U) ) (!  (=> (= (type o@@49) T@@88) (= (U_2_int (MapType0Select a@@62 o@@49)) (U_2_int (MapType0Select b@@47 o@@49))))
 :qid |fastexpb.1071:37|
 :skolemid |200|
 :pattern ( (MapType0Select a@@62 o@@49))
 :pattern ( (MapType0Select b@@47 o@@49))
))) (=> (forall ((o@@50 T@U) ) (!  (=> (= (type o@@50) T@@88) (= (U_2_int (MapType0Select a@@62 o@@50)) (U_2_int (MapType0Select b@@47 o@@50))))
 :qid |fastexpb.1071:37|
 :skolemid |200|
 :pattern ( (MapType0Select a@@62 o@@50))
 :pattern ( (MapType0Select b@@47 o@@50))
)) (|MultiSet#Equal| a@@62 b@@47)))))
 :qid |fastexpb.1069:18|
 :skolemid |201|
 :pattern ( (|MultiSet#Equal| a@@62 b@@47))
)))
(assert (forall ((a@@63 T@U) (b@@48 T@U) ) (! (let ((T@@89 (MapType0TypeInv0 (type a@@63))))
 (=> (and (and (= (type a@@63) (MapType0Type T@@89 intType)) (= (type b@@48) (MapType0Type T@@89 intType))) (|MultiSet#Equal| a@@63 b@@48)) (= a@@63 b@@48)))
 :qid |fastexpb.1073:18|
 :skolemid |202|
 :pattern ( (|MultiSet#Equal| a@@63 b@@48))
)))
(assert (forall ((a@@64 T@U) (b@@49 T@U) ) (! (let ((T@@90 (MapType0TypeInv0 (type a@@64))))
 (=> (and (= (type a@@64) (MapType0Type T@@90 intType)) (= (type b@@49) (MapType0Type T@@90 intType))) (and (=> (|MultiSet#Disjoint| a@@64 b@@49) (forall ((o@@51 T@U) ) (!  (=> (= (type o@@51) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@51)) 0) (= (U_2_int (MapType0Select b@@49 o@@51)) 0)))
 :qid |fastexpb.1082:19|
 :skolemid |203|
 :pattern ( (MapType0Select a@@64 o@@51))
 :pattern ( (MapType0Select b@@49 o@@51))
))) (=> (forall ((o@@52 T@U) ) (!  (=> (= (type o@@52) T@@90) (or (= (U_2_int (MapType0Select a@@64 o@@52)) 0) (= (U_2_int (MapType0Select b@@49 o@@52)) 0)))
 :qid |fastexpb.1082:19|
 :skolemid |203|
 :pattern ( (MapType0Select a@@64 o@@52))
 :pattern ( (MapType0Select b@@49 o@@52))
)) (|MultiSet#Disjoint| a@@64 b@@49)))))
 :qid |fastexpb.1079:18|
 :skolemid |204|
 :pattern ( (|MultiSet#Disjoint| a@@64 b@@49))
)))
(assert (forall ((arg0@@82 T@U) ) (! (let ((T@@91 (MapType0TypeInv0 (type arg0@@82))))
(= (type (|MultiSet#FromSet| arg0@@82)) (MapType0Type T@@91 intType)))
 :qid |funType:MultiSet#FromSet|
 :pattern ( (|MultiSet#FromSet| arg0@@82))
)))
(assert (forall ((s@@8 T@U) (a@@65 T@U) ) (! (let ((T@@92 (type a@@65)))
 (=> (= (type s@@8) (MapType0Type T@@92 boolType)) (and (and (=> (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 0) (not (U_2_bool (MapType0Select s@@8 a@@65)))) (=> (not (U_2_bool (MapType0Select s@@8 a@@65))) (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 0))) (and (=> (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 1) (U_2_bool (MapType0Select s@@8 a@@65))) (=> (U_2_bool (MapType0Select s@@8 a@@65)) (= (U_2_int (MapType0Select (|MultiSet#FromSet| s@@8) a@@65)) 1))))))
 :qid |fastexpb.1086:18|
 :skolemid |205|
 :pattern ( (MapType0Select (|MultiSet#FromSet| s@@8) a@@65))
)))
(assert (forall ((s@@9 T@U) ) (! (let ((T@@93 (MapType0TypeInv0 (type s@@9))))
 (=> (= (type s@@9) (MapType0Type T@@93 boolType)) (= (|MultiSet#Card| (|MultiSet#FromSet| s@@9)) (|Set#Card| s@@9))))
 :qid |fastexpb.1091:18|
 :skolemid |206|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSet| s@@9)))
)))
(assert (forall ((arg0@@83 T@U) ) (! (let ((T@@94 (SeqTypeInv0 (type arg0@@83))))
(= (type (|MultiSet#FromSeq| arg0@@83)) (MapType0Type T@@94 intType)))
 :qid |funType:MultiSet#FromSeq|
 :pattern ( (|MultiSet#FromSeq| arg0@@83))
)))
(assert (forall ((s@@10 T@U) ) (! (let ((T@@95 (SeqTypeInv0 (type s@@10))))
 (=> (= (type s@@10) (SeqType T@@95)) ($IsGoodMultiSet (|MultiSet#FromSeq| s@@10))))
 :qid |fastexpb.1097:18|
 :skolemid |207|
 :pattern ( (|MultiSet#FromSeq| s@@10))
)))
(assert (forall ((s@@11 T@U) ) (! (let ((T@@96 (SeqTypeInv0 (type s@@11))))
 (=> (= (type s@@11) (SeqType T@@96)) (= (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)) (|Seq#Length| s@@11))))
 :qid |fastexpb.1101:18|
 :skolemid |208|
 :pattern ( (|MultiSet#Card| (|MultiSet#FromSeq| s@@11)))
)))
(assert (forall ((arg0@@84 T@U) (arg1@@35 T@U) ) (! (let ((T@@97 (type arg1@@35)))
(= (type (|Seq#Build| arg0@@84 arg1@@35)) (SeqType T@@97)))
 :qid |funType:Seq#Build|
 :pattern ( (|Seq#Build| arg0@@84 arg1@@35))
)))
(assert (forall ((s@@12 T@U) (v@@25 T@U) ) (! (let ((T@@98 (type v@@25)))
 (=> (= (type s@@12) (SeqType T@@98)) (= (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@25)) (|MultiSet#UnionOne| (|MultiSet#FromSeq| s@@12) v@@25))))
 :qid |fastexpb.1105:18|
 :skolemid |209|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Build| s@@12 v@@25)))
)))
(assert (forall ((T@@99 T@T) ) (! (= (type (|Seq#Empty| T@@99)) (SeqType T@@99))
 :qid |funType:Seq#Empty|
 :pattern ( (|Seq#Empty| T@@99))
)))
(assert (forall ((T@@100 T@T) ) (! (= (|MultiSet#FromSeq| (|Seq#Empty| T@@100)) (|MultiSet#Empty| T@@100))
 :skolemid |210|
)))
(assert (forall ((arg0@@85 T@U) (arg1@@36 T@U) ) (! (let ((T@@101 (SeqTypeInv0 (type arg0@@85))))
(= (type (|Seq#Append| arg0@@85 arg1@@36)) (SeqType T@@101)))
 :qid |funType:Seq#Append|
 :pattern ( (|Seq#Append| arg0@@85 arg1@@36))
)))
(assert (forall ((a@@66 T@U) (b@@50 T@U) ) (! (let ((T@@102 (SeqTypeInv0 (type a@@66))))
 (=> (and (= (type a@@66) (SeqType T@@102)) (= (type b@@50) (SeqType T@@102))) (= (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)) (|MultiSet#Union| (|MultiSet#FromSeq| a@@66) (|MultiSet#FromSeq| b@@50)))))
 :qid |fastexpb.1112:18|
 :skolemid |211|
 :pattern ( (|MultiSet#FromSeq| (|Seq#Append| a@@66 b@@50)))
)))
(assert (forall ((arg0@@86 T@U) (arg1@@37 Int) (arg2@@2 T@U) ) (! (let ((T@@103 (type arg2@@2)))
(= (type (|Seq#Update| arg0@@86 arg1@@37 arg2@@2)) (SeqType T@@103)))
 :qid |funType:Seq#Update|
 :pattern ( (|Seq#Update| arg0@@86 arg1@@37 arg2@@2))
)))
(assert (forall ((s@@13 T@U) (i@@8 Int) (v@@26 T@U) (x@@32 T@U) ) (! (let ((T@@104 (type v@@26)))
 (=> (and (and (= (type s@@13) (SeqType T@@104)) (= (type x@@32) T@@104)) (and (<= 0 i@@8) (< i@@8 (|Seq#Length| s@@13)))) (= (U_2_int (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@32)) (U_2_int (MapType0Select (|MultiSet#Union| (|MultiSet#Difference| (|MultiSet#FromSeq| s@@13) (|MultiSet#Singleton| (|Seq#Index| s@@13 i@@8))) (|MultiSet#Singleton| v@@26)) x@@32)))))
 :qid |fastexpb.1117:18|
 :skolemid |212|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| (|Seq#Update| s@@13 i@@8 v@@26)) x@@32))
)))
(assert (forall ((s@@14 T@U) (x@@33 T@U) ) (! (let ((T@@105 (type x@@33)))
 (=> (= (type s@@14) (SeqType T@@105)) (and (=> (exists ((i@@9 Int) ) (!  (and (and (<= 0 i@@9) (< i@@9 (|Seq#Length| s@@14))) (= x@@33 (|Seq#Index| s@@14 i@@9)))
 :qid |fastexpb.1126:11|
 :skolemid |213|
 :pattern ( (|Seq#Index| s@@14 i@@9))
)) (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@33)))) (=> (< 0 (U_2_int (MapType0Select (|MultiSet#FromSeq| s@@14) x@@33))) (exists ((i@@10 Int) ) (!  (and (and (<= 0 i@@10) (< i@@10 (|Seq#Length| s@@14))) (= x@@33 (|Seq#Index| s@@14 i@@10)))
 :qid |fastexpb.1126:11|
 :skolemid |213|
 :pattern ( (|Seq#Index| s@@14 i@@10))
))))))
 :qid |fastexpb.1124:18|
 :skolemid |214|
 :pattern ( (MapType0Select (|MultiSet#FromSeq| s@@14) x@@33))
)))
(assert (forall ((s@@15 T@U) ) (! (let ((T@@106 (SeqTypeInv0 (type s@@15))))
 (=> (= (type s@@15) (SeqType T@@106)) (<= 0 (|Seq#Length| s@@15))))
 :qid |fastexpb.1135:18|
 :skolemid |215|
 :pattern ( (|Seq#Length| s@@15))
)))
(assert (forall ((T@@107 T@T) ) (! (= (|Seq#Length| (|Seq#Empty| T@@107)) 0)
 :skolemid |216|
 :pattern ( (|Seq#Empty| T@@107))
)))
(assert (forall ((s@@16 T@U) ) (! (let ((T@@108 (SeqTypeInv0 (type s@@16))))
 (=> (and (= (type s@@16) (SeqType T@@108)) (= (|Seq#Length| s@@16) 0)) (= s@@16 (|Seq#Empty| T@@108))))
 :qid |fastexpb.1141:18|
 :skolemid |217|
 :pattern ( (|Seq#Length| s@@16))
)))
(assert (forall ((t@@23 T@U) (T@@109 T@T) ) (!  (=> (= (type t@@23) TyType) ($Is (|Seq#Empty| T@@109) t@@23))
 :qid |fastexpb.1145:18|
 :skolemid |218|
 :pattern ( ($Is (|Seq#Empty| T@@109) t@@23))
)))
(assert (forall ((arg0@@87 T@U) ) (! (let ((T@@110 (type arg0@@87)))
(= (type (|Seq#Singleton| arg0@@87)) (SeqType T@@110)))
 :qid |funType:Seq#Singleton|
 :pattern ( (|Seq#Singleton| arg0@@87))
)))
(assert (forall ((t@@24 T@U) ) (! (= (|Seq#Length| (|Seq#Singleton| t@@24)) 1)
 :qid |fastexpb.1149:18|
 :skolemid |219|
 :pattern ( (|Seq#Length| (|Seq#Singleton| t@@24)))
)))
(assert  (and (forall ((arg0@@88 T@U) ) (! (let ((T@@111 (SeqTypeInv0 (type arg0@@88))))
(= (type (|Seq#Build_inv0| arg0@@88)) (SeqType T@@111)))
 :qid |funType:Seq#Build_inv0|
 :pattern ( (|Seq#Build_inv0| arg0@@88))
)) (forall ((arg0@@89 T@U) ) (! (let ((T@@112 (SeqTypeInv0 (type arg0@@89))))
(= (type (|Seq#Build_inv1| arg0@@89)) T@@112))
 :qid |funType:Seq#Build_inv1|
 :pattern ( (|Seq#Build_inv1| arg0@@89))
))))
(assert (forall ((s@@17 T@U) (val@@6 T@U) ) (! (let ((T@@113 (type val@@6)))
 (=> (= (type s@@17) (SeqType T@@113)) (and (= (|Seq#Build_inv0| (|Seq#Build| s@@17 val@@6)) s@@17) (= (|Seq#Build_inv1| (|Seq#Build| s@@17 val@@6)) val@@6))))
 :qid |fastexpb.1159:18|
 :skolemid |220|
 :pattern ( (|Seq#Build| s@@17 val@@6))
)))
(assert (forall ((s@@18 T@U) (v@@27 T@U) ) (! (let ((T@@114 (type v@@27)))
 (=> (= (type s@@18) (SeqType T@@114)) (= (|Seq#Length| (|Seq#Build| s@@18 v@@27)) (+ 1 (|Seq#Length| s@@18)))))
 :qid |fastexpb.1164:18|
 :skolemid |221|
 :pattern ( (|Seq#Build| s@@18 v@@27))
)))
(assert (forall ((s@@19 T@U) (i@@11 Int) (v@@28 T@U) ) (! (let ((T@@115 (type v@@28)))
 (=> (= (type s@@19) (SeqType T@@115)) (and (=> (= i@@11 (|Seq#Length| s@@19)) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) v@@28)) (=> (not (= i@@11 (|Seq#Length| s@@19))) (= (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11) (|Seq#Index| s@@19 i@@11))))))
 :qid |fastexpb.1168:18|
 :skolemid |222|
 :pattern ( (|Seq#Index| (|Seq#Build| s@@19 v@@28) i@@11))
)))
(assert (forall ((s@@20 T@U) (bx@@33 T@U) (t@@25 T@U) ) (!  (=> (and (and (and (= (type s@@20) (SeqType BoxType)) (= (type bx@@33) BoxType)) (= (type t@@25) TyType)) (and ($Is s@@20 (TSeq t@@25)) ($IsBox bx@@33 t@@25))) ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
 :qid |fastexpb.1173:15|
 :skolemid |223|
 :pattern ( ($Is (|Seq#Build| s@@20 bx@@33) (TSeq t@@25)))
)))
(assert (forall ((s0 T@U) (s1 T@U) ) (! (let ((T@@116 (SeqTypeInv0 (type s0))))
 (=> (and (= (type s0) (SeqType T@@116)) (= (type s1) (SeqType T@@116))) (= (|Seq#Length| (|Seq#Append| s0 s1)) (+ (|Seq#Length| s0) (|Seq#Length| s1)))))
 :qid |fastexpb.1179:18|
 :skolemid |224|
 :pattern ( (|Seq#Length| (|Seq#Append| s0 s1)))
)))
(assert (forall ((s0@@0 T@U) (s1@@0 T@U) (t@@26 T@U) ) (!  (=> (and (and (and (= (type s0@@0) (SeqType BoxType)) (= (type s1@@0) (SeqType BoxType))) (= (type t@@26) TyType)) (and ($Is s0@@0 t@@26) ($Is s1@@0 t@@26))) ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
 :qid |fastexpb.1183:15|
 :skolemid |225|
 :pattern ( ($Is (|Seq#Append| s0@@0 s1@@0) t@@26))
)))
(assert (forall ((t@@27 T@U) ) (! (= (|Seq#Index| (|Seq#Singleton| t@@27) 0) t@@27)
 :qid |fastexpb.1189:18|
 :skolemid |226|
 :pattern ( (|Seq#Index| (|Seq#Singleton| t@@27) 0))
)))
(assert (forall ((s0@@1 T@U) (s1@@1 T@U) (n@@6 Int) ) (! (let ((T@@117 (SeqTypeInv0 (type s0@@1))))
 (=> (and (= (type s0@@1) (SeqType T@@117)) (= (type s1@@1) (SeqType T@@117))) (and (=> (< n@@6 (|Seq#Length| s0@@1)) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s0@@1 n@@6))) (=> (<= (|Seq#Length| s0@@1) n@@6) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6) (|Seq#Index| s1@@1 (- n@@6 (|Seq#Length| s0@@1))))))))
 :qid |fastexpb.1193:18|
 :skolemid |227|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@6))
)))
(assert (forall ((s@@21 T@U) (i@@12 Int) (v@@29 T@U) ) (! (let ((T@@118 (type v@@29)))
 (=> (= (type s@@21) (SeqType T@@118)) (=> (and (<= 0 i@@12) (< i@@12 (|Seq#Length| s@@21))) (= (|Seq#Length| (|Seq#Update| s@@21 i@@12 v@@29)) (|Seq#Length| s@@21)))))
 :qid |fastexpb.1201:18|
 :skolemid |228|
 :pattern ( (|Seq#Length| (|Seq#Update| s@@21 i@@12 v@@29)))
)))
(assert (forall ((s@@22 T@U) (i@@13 Int) (v@@30 T@U) (n@@7 Int) ) (! (let ((T@@119 (type v@@30)))
 (=> (= (type s@@22) (SeqType T@@119)) (=> (and (<= 0 n@@7) (< n@@7 (|Seq#Length| s@@22))) (and (=> (= i@@13 n@@7) (= (|Seq#Index| (|Seq#Update| s@@22 i@@13 v@@30) n@@7) v@@30)) (=> (not (= i@@13 n@@7)) (= (|Seq#Index| (|Seq#Update| s@@22 i@@13 v@@30) n@@7) (|Seq#Index| s@@22 n@@7)))))))
 :qid |fastexpb.1205:18|
 :skolemid |229|
 :pattern ( (|Seq#Index| (|Seq#Update| s@@22 i@@13 v@@30) n@@7))
)))
(assert (forall ((s@@23 T@U) (x@@34 T@U) ) (! (let ((T@@120 (type x@@34)))
 (=> (= (type s@@23) (SeqType T@@120)) (and (=> (|Seq#Contains| s@@23 x@@34) (exists ((i@@14 Int) ) (!  (and (and (<= 0 i@@14) (< i@@14 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@14) x@@34))
 :qid |fastexpb.1216:19|
 :skolemid |230|
 :pattern ( (|Seq#Index| s@@23 i@@14))
))) (=> (exists ((i@@15 Int) ) (!  (and (and (<= 0 i@@15) (< i@@15 (|Seq#Length| s@@23))) (= (|Seq#Index| s@@23 i@@15) x@@34))
 :qid |fastexpb.1216:19|
 :skolemid |230|
 :pattern ( (|Seq#Index| s@@23 i@@15))
)) (|Seq#Contains| s@@23 x@@34)))))
 :qid |fastexpb.1213:18|
 :skolemid |231|
 :pattern ( (|Seq#Contains| s@@23 x@@34))
)))
(assert (forall ((x@@35 T@U) ) (! (let ((T@@121 (type x@@35)))
 (not (|Seq#Contains| (|Seq#Empty| T@@121) x@@35)))
 :qid |fastexpb.1220:18|
 :skolemid |232|
 :pattern ( (let ((T@@121 (type x@@35)))
(|Seq#Contains| (|Seq#Empty| T@@121) x@@35)))
)))
(assert (forall ((s0@@2 T@U) (s1@@2 T@U) (x@@36 T@U) ) (! (let ((T@@122 (type x@@36)))
 (=> (and (= (type s0@@2) (SeqType T@@122)) (= (type s1@@2) (SeqType T@@122))) (and (=> (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@36) (or (|Seq#Contains| s0@@2 x@@36) (|Seq#Contains| s1@@2 x@@36))) (=> (or (|Seq#Contains| s0@@2 x@@36) (|Seq#Contains| s1@@2 x@@36)) (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@36)))))
 :qid |fastexpb.1224:18|
 :skolemid |233|
 :pattern ( (|Seq#Contains| (|Seq#Append| s0@@2 s1@@2) x@@36))
)))
(assert (forall ((s@@24 T@U) (v@@31 T@U) (x@@37 T@U) ) (! (let ((T@@123 (type v@@31)))
 (=> (and (= (type s@@24) (SeqType T@@123)) (= (type x@@37) T@@123)) (and (=> (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@37) (or (= v@@31 x@@37) (|Seq#Contains| s@@24 x@@37))) (=> (or (= v@@31 x@@37) (|Seq#Contains| s@@24 x@@37)) (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@37)))))
 :qid |fastexpb.1229:18|
 :skolemid |234|
 :pattern ( (|Seq#Contains| (|Seq#Build| s@@24 v@@31) x@@37))
)))
(assert (forall ((arg0@@90 T@U) (arg1@@38 Int) ) (! (let ((T@@124 (SeqTypeInv0 (type arg0@@90))))
(= (type (|Seq#Take| arg0@@90 arg1@@38)) (SeqType T@@124)))
 :qid |funType:Seq#Take|
 :pattern ( (|Seq#Take| arg0@@90 arg1@@38))
)))
(assert (forall ((s@@25 T@U) (n@@8 Int) (x@@38 T@U) ) (! (let ((T@@125 (type x@@38)))
 (=> (= (type s@@25) (SeqType T@@125)) (and (=> (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@38) (exists ((i@@16 Int) ) (!  (and (and (and (<= 0 i@@16) (< i@@16 n@@8)) (< i@@16 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@16) x@@38))
 :qid |fastexpb.1236:19|
 :skolemid |235|
 :pattern ( (|Seq#Index| s@@25 i@@16))
))) (=> (exists ((i@@17 Int) ) (!  (and (and (and (<= 0 i@@17) (< i@@17 n@@8)) (< i@@17 (|Seq#Length| s@@25))) (= (|Seq#Index| s@@25 i@@17) x@@38))
 :qid |fastexpb.1236:19|
 :skolemid |235|
 :pattern ( (|Seq#Index| s@@25 i@@17))
)) (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@38)))))
 :qid |fastexpb.1233:18|
 :skolemid |236|
 :pattern ( (|Seq#Contains| (|Seq#Take| s@@25 n@@8) x@@38))
)))
(assert (forall ((arg0@@91 T@U) (arg1@@39 Int) ) (! (let ((T@@126 (SeqTypeInv0 (type arg0@@91))))
(= (type (|Seq#Drop| arg0@@91 arg1@@39)) (SeqType T@@126)))
 :qid |funType:Seq#Drop|
 :pattern ( (|Seq#Drop| arg0@@91 arg1@@39))
)))
(assert (forall ((s@@26 T@U) (n@@9 Int) (x@@39 T@U) ) (! (let ((T@@127 (type x@@39)))
 (=> (= (type s@@26) (SeqType T@@127)) (and (=> (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@39) (exists ((i@@18 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@18)) (< i@@18 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@18) x@@39))
 :qid |fastexpb.1243:19|
 :skolemid |237|
 :pattern ( (|Seq#Index| s@@26 i@@18))
))) (=> (exists ((i@@19 Int) ) (!  (and (and (and (<= 0 n@@9) (<= n@@9 i@@19)) (< i@@19 (|Seq#Length| s@@26))) (= (|Seq#Index| s@@26 i@@19) x@@39))
 :qid |fastexpb.1243:19|
 :skolemid |237|
 :pattern ( (|Seq#Index| s@@26 i@@19))
)) (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@39)))))
 :qid |fastexpb.1240:18|
 :skolemid |238|
 :pattern ( (|Seq#Contains| (|Seq#Drop| s@@26 n@@9) x@@39))
)))
(assert (forall ((s0@@3 T@U) (s1@@3 T@U) ) (! (let ((T@@128 (SeqTypeInv0 (type s0@@3))))
 (=> (and (= (type s0@@3) (SeqType T@@128)) (= (type s1@@3) (SeqType T@@128))) (and (=> (|Seq#Equal| s0@@3 s1@@3) (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j Int) ) (!  (=> (and (<= 0 j) (< j (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j) (|Seq#Index| s1@@3 j)))
 :qid |fastexpb.1253:19|
 :skolemid |239|
 :pattern ( (|Seq#Index| s0@@3 j))
 :pattern ( (|Seq#Index| s1@@3 j))
)))) (=> (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j@@0 Int) ) (!  (=> (and (<= 0 j@@0) (< j@@0 (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j@@0) (|Seq#Index| s1@@3 j@@0)))
 :qid |fastexpb.1253:19|
 :skolemid |239|
 :pattern ( (|Seq#Index| s0@@3 j@@0))
 :pattern ( (|Seq#Index| s1@@3 j@@0))
))) (|Seq#Equal| s0@@3 s1@@3)))))
 :qid |fastexpb.1249:18|
 :skolemid |240|
 :pattern ( (|Seq#Equal| s0@@3 s1@@3))
)))
(assert (forall ((a@@67 T@U) (b@@51 T@U) ) (! (let ((T@@129 (SeqTypeInv0 (type a@@67))))
 (=> (and (and (= (type a@@67) (SeqType T@@129)) (= (type b@@51) (SeqType T@@129))) (|Seq#Equal| a@@67 b@@51)) (= a@@67 b@@51)))
 :qid |fastexpb.1257:18|
 :skolemid |241|
 :pattern ( (|Seq#Equal| a@@67 b@@51))
)))
(assert (forall ((s0@@4 T@U) (s1@@4 T@U) (n@@10 Int) ) (! (let ((T@@130 (SeqTypeInv0 (type s0@@4))))
 (=> (and (= (type s0@@4) (SeqType T@@130)) (= (type s1@@4) (SeqType T@@130))) (and (=> (|Seq#SameUntil| s0@@4 s1@@4 n@@10) (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 n@@10)) (= (|Seq#Index| s0@@4 j@@1) (|Seq#Index| s1@@4 j@@1)))
 :qid |fastexpb.1264:19|
 :skolemid |242|
 :pattern ( (|Seq#Index| s0@@4 j@@1))
 :pattern ( (|Seq#Index| s1@@4 j@@1))
))) (=> (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 n@@10)) (= (|Seq#Index| s0@@4 j@@2) (|Seq#Index| s1@@4 j@@2)))
 :qid |fastexpb.1264:19|
 :skolemid |242|
 :pattern ( (|Seq#Index| s0@@4 j@@2))
 :pattern ( (|Seq#Index| s1@@4 j@@2))
)) (|Seq#SameUntil| s0@@4 s1@@4 n@@10)))))
 :qid |fastexpb.1261:18|
 :skolemid |243|
 :pattern ( (|Seq#SameUntil| s0@@4 s1@@4 n@@10))
)))
(assert (forall ((s@@27 T@U) (n@@11 Int) ) (! (let ((T@@131 (SeqTypeInv0 (type s@@27))))
 (=> (= (type s@@27) (SeqType T@@131)) (=> (and (<= 0 n@@11) (<= n@@11 (|Seq#Length| s@@27))) (= (|Seq#Length| (|Seq#Take| s@@27 n@@11)) n@@11))))
 :qid |fastexpb.1270:18|
 :skolemid |244|
 :pattern ( (|Seq#Length| (|Seq#Take| s@@27 n@@11)))
)))
(assert (forall ((s@@28 T@U) (n@@12 Int) (j@@3 Int) ) (! (let ((T@@132 (SeqTypeInv0 (type s@@28))))
 (=> (= (type s@@28) (SeqType T@@132)) (=> (and (and (<= 0 j@@3) (< j@@3 n@@12)) (< j@@3 (|Seq#Length| s@@28))) (= (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3) (|Seq#Index| s@@28 j@@3)))))
 :qid |fastexpb.1274:18|
 :weight 25
 :skolemid |245|
 :pattern ( (|Seq#Index| (|Seq#Take| s@@28 n@@12) j@@3))
 :pattern ( (|Seq#Index| s@@28 j@@3) (|Seq#Take| s@@28 n@@12))
)))
(assert (forall ((s@@29 T@U) (n@@13 Int) ) (! (let ((T@@133 (SeqTypeInv0 (type s@@29))))
 (=> (= (type s@@29) (SeqType T@@133)) (=> (and (<= 0 n@@13) (<= n@@13 (|Seq#Length| s@@29))) (= (|Seq#Length| (|Seq#Drop| s@@29 n@@13)) (- (|Seq#Length| s@@29) n@@13)))))
 :qid |fastexpb.1281:18|
 :skolemid |246|
 :pattern ( (|Seq#Length| (|Seq#Drop| s@@29 n@@13)))
)))
(assert (forall ((s@@30 T@U) (n@@14 Int) (j@@4 Int) ) (! (let ((T@@134 (SeqTypeInv0 (type s@@30))))
 (=> (= (type s@@30) (SeqType T@@134)) (=> (and (and (<= 0 n@@14) (<= 0 j@@4)) (< j@@4 (- (|Seq#Length| s@@30) n@@14))) (= (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4) (|Seq#Index| s@@30 (+ j@@4 n@@14))))))
 :qid |fastexpb.1285:18|
 :weight 25
 :skolemid |247|
 :pattern ( (|Seq#Index| (|Seq#Drop| s@@30 n@@14) j@@4))
)))
(assert (forall ((s@@31 T@U) (n@@15 Int) (k@@3 Int) ) (! (let ((T@@135 (SeqTypeInv0 (type s@@31))))
 (=> (= (type s@@31) (SeqType T@@135)) (=> (and (and (<= 0 n@@15) (<= n@@15 k@@3)) (< k@@3 (|Seq#Length| s@@31))) (= (|Seq#Index| (|Seq#Drop| s@@31 n@@15) (- k@@3 n@@15)) (|Seq#Index| s@@31 k@@3)))))
 :qid |fastexpb.1290:18|
 :weight 25
 :skolemid |248|
 :pattern ( (|Seq#Index| s@@31 k@@3) (|Seq#Drop| s@@31 n@@15))
)))
(assert (forall ((s@@32 T@U) (t@@28 T@U) (n@@16 Int) ) (! (let ((T@@136 (SeqTypeInv0 (type s@@32))))
 (=> (and (and (= (type s@@32) (SeqType T@@136)) (= (type t@@28) (SeqType T@@136))) (= n@@16 (|Seq#Length| s@@32))) (and (= (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16) s@@32) (= (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16) t@@28))))
 :qid |fastexpb.1295:18|
 :skolemid |249|
 :pattern ( (|Seq#Take| (|Seq#Append| s@@32 t@@28) n@@16))
 :pattern ( (|Seq#Drop| (|Seq#Append| s@@32 t@@28) n@@16))
)))
(assert (forall ((arg0@@92 T@U) (arg1@@40 T@U) ) (! (= (type (|Seq#FromArray| arg0@@92 arg1@@40)) (SeqType BoxType))
 :qid |funType:Seq#FromArray|
 :pattern ( (|Seq#FromArray| arg0@@92 arg1@@40))
)))
(assert (forall ((h@@16 T@U) (a@@68 T@U) ) (!  (=> (and (= (type h@@16) (MapType1Type refType)) (= (type a@@68) refType)) (= (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)) (_System.array.Length a@@68)))
 :qid |fastexpb.1302:15|
 :skolemid |250|
 :pattern ( (|Seq#Length| (|Seq#FromArray| h@@16 a@@68)))
)))
(assert (forall ((h@@17 T@U) (a@@69 T@U) ) (!  (=> (and (= (type h@@17) (MapType1Type refType)) (= (type a@@69) refType)) (forall ((i@@20 Int) ) (!  (=> (and (<= 0 i@@20) (< i@@20 (|Seq#Length| (|Seq#FromArray| h@@17 a@@69)))) (= (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@20) (MapType1Select h@@17 a@@69 (IndexField i@@20))))
 :qid |fastexpb.1308:11|
 :skolemid |251|
 :pattern ( (MapType1Select h@@17 a@@69 (IndexField i@@20)))
 :pattern ( (|Seq#Index| (|Seq#FromArray| h@@17 a@@69) i@@20))
)))
 :qid |fastexpb.1306:15|
 :skolemid |252|
 :pattern ( (|Seq#FromArray| h@@17 a@@69))
)))
(assert (forall ((h0 T@U) (h1 T@U) (a@@70 T@U) ) (!  (=> (and (and (= (type h0) (MapType1Type refType)) (= (type h1) (MapType1Type refType))) (= (type a@@70) refType)) (=> (and (and (and ($IsGoodHeap h0) ($IsGoodHeap h1)) ($HeapSucc h0 h1)) (forall ((i@@21 Int) ) (!  (=> (and (<= 0 i@@21) (< i@@21 (_System.array.Length a@@70))) (= (MapType1Select h0 a@@70 (IndexField i@@21)) (MapType1Select h1 a@@70 (IndexField i@@21))))
 :qid |fastexpb.1318:19|
 :skolemid |253|
))) (= (|Seq#FromArray| h0 a@@70) (|Seq#FromArray| h1 a@@70))))
 :qid |fastexpb.1313:15|
 :skolemid |254|
 :pattern ( (|Seq#FromArray| h1 a@@70) ($HeapSucc h0 h1))
)))
(assert (forall ((h@@18 T@U) (i@@22 Int) (v@@32 T@U) (a@@71 T@U) ) (!  (=> (and (and (and (= (type h@@18) (MapType1Type refType)) (= (type v@@32) BoxType)) (= (type a@@71) refType)) (and (<= 0 i@@22) (< i@@22 (_System.array.Length a@@71)))) (= (|Seq#FromArray| (MapType1Store h@@18 a@@71 (IndexField i@@22) v@@32) a@@71) (|Seq#Update| (|Seq#FromArray| h@@18 a@@71) i@@22 v@@32)))
 :qid |fastexpb.1323:15|
 :skolemid |255|
 :pattern ( (|Seq#FromArray| (MapType1Store h@@18 a@@71 (IndexField i@@22) v@@32) a@@71))
)))
(assert (forall ((s@@33 T@U) (i@@23 Int) (v@@33 T@U) (n@@17 Int) ) (! (let ((T@@137 (type v@@33)))
 (=> (= (type s@@33) (SeqType T@@137)) (=> (and (and (<= 0 i@@23) (< i@@23 n@@17)) (<= n@@17 (|Seq#Length| s@@33))) (= (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17) (|Seq#Update| (|Seq#Take| s@@33 n@@17) i@@23 v@@33)))))
 :qid |fastexpb.1329:18|
 :skolemid |256|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@33 i@@23 v@@33) n@@17))
)))
(assert (forall ((s@@34 T@U) (i@@24 Int) (v@@34 T@U) (n@@18 Int) ) (! (let ((T@@138 (type v@@34)))
 (=> (= (type s@@34) (SeqType T@@138)) (=> (and (<= n@@18 i@@24) (< i@@24 (|Seq#Length| s@@34))) (= (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18) (|Seq#Take| s@@34 n@@18)))))
 :qid |fastexpb.1334:18|
 :skolemid |257|
 :pattern ( (|Seq#Take| (|Seq#Update| s@@34 i@@24 v@@34) n@@18))
)))
(assert (forall ((s@@35 T@U) (i@@25 Int) (v@@35 T@U) (n@@19 Int) ) (! (let ((T@@139 (type v@@35)))
 (=> (= (type s@@35) (SeqType T@@139)) (=> (and (and (<= 0 n@@19) (<= n@@19 i@@25)) (< i@@25 (|Seq#Length| s@@35))) (= (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19) (|Seq#Update| (|Seq#Drop| s@@35 n@@19) (- i@@25 n@@19) v@@35)))))
 :qid |fastexpb.1339:18|
 :skolemid |258|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@35 i@@25 v@@35) n@@19))
)))
(assert (forall ((s@@36 T@U) (i@@26 Int) (v@@36 T@U) (n@@20 Int) ) (! (let ((T@@140 (type v@@36)))
 (=> (= (type s@@36) (SeqType T@@140)) (=> (and (and (<= 0 i@@26) (< i@@26 n@@20)) (< n@@20 (|Seq#Length| s@@36))) (= (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20) (|Seq#Drop| s@@36 n@@20)))))
 :qid |fastexpb.1344:18|
 :skolemid |259|
 :pattern ( (|Seq#Drop| (|Seq#Update| s@@36 i@@26 v@@36) n@@20))
)))
(assert (forall ((h@@19 T@U) (a@@72 T@U) (n0 Int) (n1 Int) ) (!  (=> (and (= (type h@@19) (MapType1Type refType)) (= (type a@@72) refType)) (=> (and (and (= (+ n0 1) n1) (<= 0 n0)) (<= n1 (_System.array.Length a@@72))) (= (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1) (|Seq#Build| (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (MapType1Select h@@19 a@@72 (IndexField n0))))))
 :qid |fastexpb.1349:15|
 :skolemid |260|
 :pattern ( (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n0) (|Seq#Take| (|Seq#FromArray| h@@19 a@@72) n1))
)))
(assert (forall ((s@@37 T@U) (v@@37 T@U) (n@@21 Int) ) (! (let ((T@@141 (type v@@37)))
 (=> (= (type s@@37) (SeqType T@@141)) (=> (and (<= 0 n@@21) (<= n@@21 (|Seq#Length| s@@37))) (= (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21) (|Seq#Build| (|Seq#Drop| s@@37 n@@21) v@@37)))))
 :qid |fastexpb.1355:18|
 :skolemid |261|
 :pattern ( (|Seq#Drop| (|Seq#Build| s@@37 v@@37) n@@21))
)))
(assert (forall ((s@@38 T@U) (i@@27 Int) ) (!  (=> (= (type s@@38) (SeqType BoxType)) (=> (and (<= 0 i@@27) (< i@@27 (|Seq#Length| s@@38))) (< (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))) (|Seq#Rank| s@@38))))
 :qid |fastexpb.1362:15|
 :skolemid |262|
 :pattern ( (DtRank ($Unbox DatatypeTypeType (|Seq#Index| s@@38 i@@27))))
)))
(assert (forall ((s@@39 T@U) (i@@28 Int) ) (! (let ((T@@142 (SeqTypeInv0 (type s@@39))))
 (=> (= (type s@@39) (SeqType T@@142)) (=> (and (< 0 i@@28) (<= i@@28 (|Seq#Length| s@@39))) (< (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)) (|Seq#Rank| s@@39)))))
 :qid |fastexpb.1367:18|
 :skolemid |263|
 :pattern ( (|Seq#Rank| (|Seq#Drop| s@@39 i@@28)))
)))
(assert (forall ((s@@40 T@U) (i@@29 Int) ) (! (let ((T@@143 (SeqTypeInv0 (type s@@40))))
 (=> (= (type s@@40) (SeqType T@@143)) (=> (and (<= 0 i@@29) (< i@@29 (|Seq#Length| s@@40))) (< (|Seq#Rank| (|Seq#Take| s@@40 i@@29)) (|Seq#Rank| s@@40)))))
 :qid |fastexpb.1371:18|
 :skolemid |264|
 :pattern ( (|Seq#Rank| (|Seq#Take| s@@40 i@@29)))
)))
(assert (forall ((s@@41 T@U) (i@@30 Int) (j@@5 Int) ) (! (let ((T@@144 (SeqTypeInv0 (type s@@41))))
 (=> (= (type s@@41) (SeqType T@@144)) (=> (and (and (<= 0 i@@30) (< i@@30 j@@5)) (<= j@@5 (|Seq#Length| s@@41))) (< (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))) (|Seq#Rank| s@@41)))))
 :qid |fastexpb.1375:18|
 :skolemid |265|
 :pattern ( (|Seq#Rank| (|Seq#Append| (|Seq#Take| s@@41 i@@30) (|Seq#Drop| s@@41 j@@5))))
)))
(assert (forall ((s@@42 T@U) (n@@22 Int) ) (! (let ((T@@145 (SeqTypeInv0 (type s@@42))))
 (=> (and (= (type s@@42) (SeqType T@@145)) (= n@@22 0)) (= (|Seq#Drop| s@@42 n@@22) s@@42)))
 :qid |fastexpb.1380:18|
 :skolemid |266|
 :pattern ( (|Seq#Drop| s@@42 n@@22))
)))
(assert (forall ((s@@43 T@U) (n@@23 Int) ) (! (let ((T@@146 (SeqTypeInv0 (type s@@43))))
 (=> (and (= (type s@@43) (SeqType T@@146)) (= n@@23 0)) (= (|Seq#Take| s@@43 n@@23) (|Seq#Empty| T@@146))))
 :qid |fastexpb.1384:18|
 :skolemid |267|
 :pattern ( (|Seq#Take| s@@43 n@@23))
)))
(assert (forall ((s@@44 T@U) (m@@10 Int) (n@@24 Int) ) (! (let ((T@@147 (SeqTypeInv0 (type s@@44))))
 (=> (= (type s@@44) (SeqType T@@147)) (=> (and (and (<= 0 m@@10) (<= 0 n@@24)) (<= (+ m@@10 n@@24) (|Seq#Length| s@@44))) (= (|Seq#Drop| (|Seq#Drop| s@@44 m@@10) n@@24) (|Seq#Drop| s@@44 (+ m@@10 n@@24))))))
 :qid |fastexpb.1388:18|
 :skolemid |268|
 :pattern ( (|Seq#Drop| (|Seq#Drop| s@@44 m@@10) n@@24))
)))
(assert (forall ((m@@11 T@U) ) (! (let ((V@@1 (MapTypeInv1 (type m@@11))))
(let ((U@@3 (MapTypeInv0 (type m@@11))))
 (=> (= (type m@@11) (MapType U@@3 V@@1)) (<= 0 (|Map#Card| m@@11)))))
 :qid |fastexpb.1401:20|
 :skolemid |269|
 :pattern ( (|Map#Card| m@@11))
)))
(assert (forall ((m@@12 T@U) ) (! (let ((V@@2 (MapTypeInv1 (type m@@12))))
(let ((U@@4 (MapTypeInv0 (type m@@12))))
 (=> (= (type m@@12) (MapType U@@4 V@@2)) (= (|Set#Card| (|Map#Domain| m@@12)) (|Map#Card| m@@12)))))
 :qid |fastexpb.1403:20|
 :skolemid |270|
 :pattern ( (|Set#Card| (|Map#Domain| m@@12)))
)))
(assert (forall ((arg0@@93 T@U) ) (! (let ((V@@3 (MapTypeInv1 (type arg0@@93))))
(= (type (|Map#Values| arg0@@93)) (MapType0Type V@@3 boolType)))
 :qid |funType:Map#Values|
 :pattern ( (|Map#Values| arg0@@93))
)))
(assert (forall ((m@@13 T@U) (v@@38 T@U) ) (! (let ((V@@4 (type v@@38)))
(let ((U@@5 (MapTypeInv0 (type m@@13))))
 (=> (= (type m@@13) (MapType U@@5 V@@4)) (and (=> (U_2_bool (MapType0Select (|Map#Values| m@@13) v@@38)) (exists ((u@@5 T@U) ) (!  (and (= (type u@@5) U@@5) (and (U_2_bool (MapType0Select (|Map#Domain| m@@13) u@@5)) (= v@@38 (MapType0Select (|Map#Elements| m@@13) u@@5))))
 :qid |fastexpb.1412:17|
 :skolemid |271|
 :pattern ( (MapType0Select (|Map#Domain| m@@13) u@@5))
 :pattern ( (MapType0Select (|Map#Elements| m@@13) u@@5))
))) (=> (exists ((u@@6 T@U) ) (!  (and (= (type u@@6) U@@5) (and (U_2_bool (MapType0Select (|Map#Domain| m@@13) u@@6)) (= v@@38 (MapType0Select (|Map#Elements| m@@13) u@@6))))
 :qid |fastexpb.1412:17|
 :skolemid |271|
 :pattern ( (MapType0Select (|Map#Domain| m@@13) u@@6))
 :pattern ( (MapType0Select (|Map#Elements| m@@13) u@@6))
)) (U_2_bool (MapType0Select (|Map#Values| m@@13) v@@38)))))))
 :qid |fastexpb.1409:20|
 :skolemid |272|
 :pattern ( (MapType0Select (|Map#Values| m@@13) v@@38))
)))
(assert (forall ((arg0@@94 T@U) ) (! (= (type (|Map#Items| arg0@@94)) (MapType0Type BoxType boolType))
 :qid |funType:Map#Items|
 :pattern ( (|Map#Items| arg0@@94))
)))
(assert (forall ((m@@14 T@U) ) (! (let ((V@@5 (MapTypeInv1 (type m@@14))))
(let ((U@@6 (MapTypeInv0 (type m@@14))))
 (=> (= (type m@@14) (MapType U@@6 V@@5)) (= (|Set#Card| (|Map#Items| m@@14)) (|Map#Card| m@@14)))))
 :qid |fastexpb.1422:20|
 :skolemid |273|
 :pattern ( (|Set#Card| (|Map#Items| m@@14)))
)))
(assert  (and (forall ((arg0@@95 T@U) ) (! (= (type (_System.Tuple2._0 arg0@@95)) BoxType)
 :qid |funType:_System.Tuple2._0|
 :pattern ( (_System.Tuple2._0 arg0@@95))
)) (forall ((arg0@@96 T@U) ) (! (= (type (_System.Tuple2._1 arg0@@96)) BoxType)
 :qid |funType:_System.Tuple2._1|
 :pattern ( (_System.Tuple2._1 arg0@@96))
))))
(assert (forall ((m@@15 T@U) (item T@U) ) (!  (=> (and (= (type m@@15) (MapType BoxType BoxType)) (= (type item) BoxType)) (and (=> (U_2_bool (MapType0Select (|Map#Items| m@@15) item)) (and (U_2_bool (MapType0Select (|Map#Domain| m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select (|Map#Elements| m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item))))) (=> (and (U_2_bool (MapType0Select (|Map#Domain| m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item)))) (= (MapType0Select (|Map#Elements| m@@15) (_System.Tuple2._0 ($Unbox DatatypeTypeType item))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item)))) (U_2_bool (MapType0Select (|Map#Items| m@@15) item)))))
 :qid |fastexpb.1426:15|
 :skolemid |274|
 :pattern ( (MapType0Select (|Map#Items| m@@15) item))
)))
(assert (forall ((U@@7 T@T) (V@@6 T@T) ) (! (= (type (|Map#Empty| U@@7 V@@6)) (MapType U@@7 V@@6))
 :qid |funType:Map#Empty|
 :pattern ( (|Map#Empty| U@@7 V@@6))
)))
(assert (forall ((u@@7 T@U) (V@@7 T@T) ) (! (let ((U@@8 (type u@@7)))
 (not (U_2_bool (MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7))))
 :qid |fastexpb.1435:20|
 :skolemid |275|
 :pattern ( (let ((U@@8 (type u@@7)))
(MapType0Select (|Map#Domain| (|Map#Empty| U@@8 V@@7)) u@@7)))
)))
(assert (forall ((m@@16 T@U) ) (! (let ((V@@8 (MapTypeInv1 (type m@@16))))
(let ((U@@9 (MapTypeInv0 (type m@@16))))
 (=> (= (type m@@16) (MapType U@@9 V@@8)) (and (and (=> (= (|Map#Card| m@@16) 0) (= m@@16 (|Map#Empty| U@@9 V@@8))) (=> (= m@@16 (|Map#Empty| U@@9 V@@8)) (= (|Map#Card| m@@16) 0))) (=> (not (= (|Map#Card| m@@16) 0)) (exists ((x@@40 T@U) ) (!  (and (= (type x@@40) U@@9) (U_2_bool (MapType0Select (|Map#Domain| m@@16) x@@40)))
 :qid |fastexpb.1442:39|
 :skolemid |276|
 :no-pattern (type x@@40)
 :no-pattern (U_2_int x@@40)
 :no-pattern (U_2_bool x@@40)
)))))))
 :qid |fastexpb.1439:20|
 :skolemid |277|
 :pattern ( (|Map#Card| m@@16))
)))
(assert (forall ((arg0@@97 T@U) (arg1@@41 T@U) (arg2@@3 T@U) ) (! (let ((V@@9 (MapType0TypeInv1 (type arg1@@41))))
(let ((U@@10 (MapType0TypeInv0 (type arg0@@97))))
(= (type (|Map#Glue| arg0@@97 arg1@@41 arg2@@3)) (MapType U@@10 V@@9))))
 :qid |funType:Map#Glue|
 :pattern ( (|Map#Glue| arg0@@97 arg1@@41 arg2@@3))
)))
(assert (forall ((a@@73 T@U) (b@@52 T@U) (t@@29 T@U) ) (! (let ((V@@10 (MapType0TypeInv1 (type b@@52))))
(let ((U@@11 (MapType0TypeInv0 (type a@@73))))
 (=> (and (and (= (type a@@73) (MapType0Type U@@11 boolType)) (= (type b@@52) (MapType0Type U@@11 V@@10))) (= (type t@@29) TyType)) (= (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@29)) a@@73))))
 :qid |fastexpb.1446:20|
 :skolemid |278|
 :pattern ( (|Map#Domain| (|Map#Glue| a@@73 b@@52 t@@29)))
)))
(assert (forall ((a@@74 T@U) (b@@53 T@U) (t@@30 T@U) ) (! (let ((V@@11 (MapType0TypeInv1 (type b@@53))))
(let ((U@@12 (MapType0TypeInv0 (type a@@74))))
 (=> (and (and (= (type a@@74) (MapType0Type U@@12 boolType)) (= (type b@@53) (MapType0Type U@@12 V@@11))) (= (type t@@30) TyType)) (= (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)) b@@53))))
 :qid |fastexpb.1450:20|
 :skolemid |279|
 :pattern ( (|Map#Elements| (|Map#Glue| a@@74 b@@53 t@@30)))
)))
(assert (forall ((a@@75 T@U) (b@@54 T@U) (t@@31 T@U) ) (! (let ((V@@12 (MapType0TypeInv1 (type b@@54))))
(let ((U@@13 (MapType0TypeInv0 (type a@@75))))
 (=> (and (and (= (type a@@75) (MapType0Type U@@13 boolType)) (= (type b@@54) (MapType0Type U@@13 V@@12))) (= (type t@@31) TyType)) ($Is (|Map#Glue| a@@75 b@@54 t@@31) t@@31))))
 :qid |fastexpb.1454:20|
 :skolemid |280|
 :pattern ( ($Is (|Map#Glue| a@@75 b@@54 t@@31) t@@31))
)))
(assert (forall ((arg0@@98 T@U) (arg1@@42 T@U) (arg2@@4 T@U) ) (! (let ((V@@13 (type arg2@@4)))
(let ((U@@14 (type arg1@@42)))
(= (type (|Map#Build| arg0@@98 arg1@@42 arg2@@4)) (MapType U@@14 V@@13))))
 :qid |funType:Map#Build|
 :pattern ( (|Map#Build| arg0@@98 arg1@@42 arg2@@4))
)))
(assert (forall ((m@@17 T@U) (u@@8 T@U) (|u'| T@U) (v@@39 T@U) ) (! (let ((V@@14 (type v@@39)))
(let ((U@@15 (type u@@8)))
 (=> (and (= (type m@@17) (MapType U@@15 V@@14)) (= (type |u'|) U@@15)) (and (=> (= |u'| u@@8) (and (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@17 u@@8 v@@39)) |u'|)) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@17 u@@8 v@@39)) |u'|) v@@39))) (=> (not (= |u'| u@@8)) (and (and (=> (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@17 u@@8 v@@39)) |u'|)) (U_2_bool (MapType0Select (|Map#Domain| m@@17) |u'|))) (=> (U_2_bool (MapType0Select (|Map#Domain| m@@17) |u'|)) (U_2_bool (MapType0Select (|Map#Domain| (|Map#Build| m@@17 u@@8 v@@39)) |u'|)))) (= (MapType0Select (|Map#Elements| (|Map#Build| m@@17 u@@8 v@@39)) |u'|) (MapType0Select (|Map#Elements| m@@17) |u'|))))))))
 :qid |fastexpb.1460:20|
 :skolemid |281|
 :pattern ( (MapType0Select (|Map#Domain| (|Map#Build| m@@17 u@@8 v@@39)) |u'|))
 :pattern ( (MapType0Select (|Map#Elements| (|Map#Build| m@@17 u@@8 v@@39)) |u'|))
)))
(assert (forall ((m@@18 T@U) (u@@9 T@U) (v@@40 T@U) ) (! (let ((V@@15 (type v@@40)))
(let ((U@@16 (type u@@9)))
 (=> (and (= (type m@@18) (MapType U@@16 V@@15)) (U_2_bool (MapType0Select (|Map#Domain| m@@18) u@@9))) (= (|Map#Card| (|Map#Build| m@@18 u@@9 v@@40)) (|Map#Card| m@@18)))))
 :qid |fastexpb.1468:20|
 :skolemid |282|
 :pattern ( (|Map#Card| (|Map#Build| m@@18 u@@9 v@@40)))
)))
(assert (forall ((m@@19 T@U) (u@@10 T@U) (v@@41 T@U) ) (! (let ((V@@16 (type v@@41)))
(let ((U@@17 (type u@@10)))
 (=> (and (= (type m@@19) (MapType U@@17 V@@16)) (not (U_2_bool (MapType0Select (|Map#Domain| m@@19) u@@10)))) (= (|Map#Card| (|Map#Build| m@@19 u@@10 v@@41)) (+ (|Map#Card| m@@19) 1)))))
 :qid |fastexpb.1472:20|
 :skolemid |283|
 :pattern ( (|Map#Card| (|Map#Build| m@@19 u@@10 v@@41)))
)))
(assert (forall ((m@@20 T@U) (|m'| T@U) ) (! (let ((V@@17 (MapTypeInv1 (type m@@20))))
(let ((U@@18 (MapTypeInv0 (type m@@20))))
 (=> (and (= (type m@@20) (MapType U@@18 V@@17)) (= (type |m'|) (MapType U@@18 V@@17))) (and (=> (|Map#Equal| m@@20 |m'|) (and (forall ((u@@11 T@U) ) (!  (=> (= (type u@@11) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@11)) (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@11)))))
 :qid |fastexpb.1481:19|
 :skolemid |284|
 :no-pattern (type u@@11)
 :no-pattern (U_2_int u@@11)
 :no-pattern (U_2_bool u@@11)
)) (forall ((u@@12 T@U) ) (!  (=> (and (= (type u@@12) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@12))) (= (MapType0Select (|Map#Elements| m@@20) u@@12) (MapType0Select (|Map#Elements| |m'|) u@@12)))
 :qid |fastexpb.1482:19|
 :skolemid |285|
 :no-pattern (type u@@12)
 :no-pattern (U_2_int u@@12)
 :no-pattern (U_2_bool u@@12)
)))) (=> (and (forall ((u@@13 T@U) ) (!  (=> (= (type u@@13) U@@18) (and (=> (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13))) (=> (U_2_bool (MapType0Select (|Map#Domain| |m'|) u@@13)) (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@13)))))
 :qid |fastexpb.1481:19|
 :skolemid |284|
 :no-pattern (type u@@13)
 :no-pattern (U_2_int u@@13)
 :no-pattern (U_2_bool u@@13)
)) (forall ((u@@14 T@U) ) (!  (=> (and (= (type u@@14) U@@18) (U_2_bool (MapType0Select (|Map#Domain| m@@20) u@@14))) (= (MapType0Select (|Map#Elements| m@@20) u@@14) (MapType0Select (|Map#Elements| |m'|) u@@14)))
 :qid |fastexpb.1482:19|
 :skolemid |285|
 :no-pattern (type u@@14)
 :no-pattern (U_2_int u@@14)
 :no-pattern (U_2_bool u@@14)
))) (|Map#Equal| m@@20 |m'|))))))
 :qid |fastexpb.1478:20|
 :skolemid |286|
 :pattern ( (|Map#Equal| m@@20 |m'|))
)))
(assert (forall ((m@@21 T@U) (|m'@@0| T@U) ) (! (let ((V@@18 (MapTypeInv1 (type m@@21))))
(let ((U@@19 (MapTypeInv0 (type m@@21))))
 (=> (and (and (= (type m@@21) (MapType U@@19 V@@18)) (= (type |m'@@0|) (MapType U@@19 V@@18))) (|Map#Equal| m@@21 |m'@@0|)) (= m@@21 |m'@@0|))))
 :qid |fastexpb.1484:20|
 :skolemid |287|
 :pattern ( (|Map#Equal| m@@21 |m'@@0|))
)))
(assert (forall ((m@@22 T@U) (|m'@@1| T@U) ) (! (let ((V@@19 (MapTypeInv1 (type m@@22))))
(let ((U@@20 (MapTypeInv0 (type m@@22))))
 (=> (and (= (type m@@22) (MapType U@@20 V@@19)) (= (type |m'@@1|) (MapType U@@20 V@@19))) (and (=> (|Map#Disjoint| m@@22 |m'@@1|) (forall ((o@@53 T@U) ) (!  (=> (= (type o@@53) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@22) o@@53))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@53)))))
 :qid |fastexpb.1493:19|
 :skolemid |288|
 :pattern ( (MapType0Select (|Map#Domain| m@@22) o@@53))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@53))
))) (=> (forall ((o@@54 T@U) ) (!  (=> (= (type o@@54) U@@20) (or (not (U_2_bool (MapType0Select (|Map#Domain| m@@22) o@@54))) (not (U_2_bool (MapType0Select (|Map#Domain| |m'@@1|) o@@54)))))
 :qid |fastexpb.1493:19|
 :skolemid |288|
 :pattern ( (MapType0Select (|Map#Domain| m@@22) o@@54))
 :pattern ( (MapType0Select (|Map#Domain| |m'@@1|) o@@54))
)) (|Map#Disjoint| m@@22 |m'@@1|))))))
 :qid |fastexpb.1490:20|
 :skolemid |289|
 :pattern ( (|Map#Disjoint| m@@22 |m'@@1|))
)))
(assert (forall ((arg0@@99 T@U) ) (! (let ((V@@20 (IMapTypeInv1 (type arg0@@99))))
(= (type (|IMap#Values| arg0@@99)) (MapType0Type V@@20 boolType)))
 :qid |funType:IMap#Values|
 :pattern ( (|IMap#Values| arg0@@99))
)))
(assert (forall ((m@@23 T@U) (v@@42 T@U) ) (! (let ((V@@21 (type v@@42)))
(let ((U@@21 (IMapTypeInv0 (type m@@23))))
 (=> (= (type m@@23) (IMapType U@@21 V@@21)) (and (=> (U_2_bool (MapType0Select (|IMap#Values| m@@23) v@@42)) (exists ((u@@15 T@U) ) (!  (and (= (type u@@15) U@@21) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) u@@15)) (= v@@42 (MapType0Select (|IMap#Elements| m@@23) u@@15))))
 :qid |fastexpb.1508:17|
 :skolemid |290|
 :pattern ( (MapType0Select (|IMap#Domain| m@@23) u@@15))
 :pattern ( (MapType0Select (|IMap#Elements| m@@23) u@@15))
))) (=> (exists ((u@@16 T@U) ) (!  (and (= (type u@@16) U@@21) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@23) u@@16)) (= v@@42 (MapType0Select (|IMap#Elements| m@@23) u@@16))))
 :qid |fastexpb.1508:17|
 :skolemid |290|
 :pattern ( (MapType0Select (|IMap#Domain| m@@23) u@@16))
 :pattern ( (MapType0Select (|IMap#Elements| m@@23) u@@16))
)) (U_2_bool (MapType0Select (|IMap#Values| m@@23) v@@42)))))))
 :qid |fastexpb.1505:20|
 :skolemid |291|
 :pattern ( (MapType0Select (|IMap#Values| m@@23) v@@42))
)))
(assert (forall ((arg0@@100 T@U) ) (! (= (type (|IMap#Items| arg0@@100)) (MapType0Type BoxType boolType))
 :qid |funType:IMap#Items|
 :pattern ( (|IMap#Items| arg0@@100))
)))
(assert (forall ((m@@24 T@U) (item@@0 T@U) ) (!  (=> (and (= (type m@@24) (IMapType BoxType BoxType)) (= (type item@@0) BoxType)) (and (=> (U_2_bool (MapType0Select (|IMap#Items| m@@24) item@@0)) (and (U_2_bool (MapType0Select (|IMap#Domain| m@@24) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@24) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0))))) (=> (and (U_2_bool (MapType0Select (|IMap#Domain| m@@24) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0)))) (= (MapType0Select (|IMap#Elements| m@@24) (_System.Tuple2._0 ($Unbox DatatypeTypeType item@@0))) (_System.Tuple2._1 ($Unbox DatatypeTypeType item@@0)))) (U_2_bool (MapType0Select (|IMap#Items| m@@24) item@@0)))))
 :qid |fastexpb.1514:15|
 :skolemid |292|
 :pattern ( (MapType0Select (|IMap#Items| m@@24) item@@0))
)))
(assert (forall ((U@@22 T@T) (V@@22 T@T) ) (! (= (type (|IMap#Empty| U@@22 V@@22)) (IMapType U@@22 V@@22))
 :qid |funType:IMap#Empty|
 :pattern ( (|IMap#Empty| U@@22 V@@22))
)))
(assert (forall ((u@@17 T@U) (V@@23 T@T) ) (! (let ((U@@23 (type u@@17)))
 (not (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Empty| U@@23 V@@23)) u@@17))))
 :qid |fastexpb.1523:20|
 :skolemid |293|
 :pattern ( (let ((U@@23 (type u@@17)))
(MapType0Select (|IMap#Domain| (|IMap#Empty| U@@23 V@@23)) u@@17)))
)))
(assert (forall ((arg0@@101 T@U) (arg1@@43 T@U) (arg2@@5 T@U) ) (! (let ((V@@24 (MapType0TypeInv1 (type arg1@@43))))
(let ((U@@24 (MapType0TypeInv0 (type arg0@@101))))
(= (type (|IMap#Glue| arg0@@101 arg1@@43 arg2@@5)) (IMapType U@@24 V@@24))))
 :qid |funType:IMap#Glue|
 :pattern ( (|IMap#Glue| arg0@@101 arg1@@43 arg2@@5))
)))
(assert (forall ((a@@76 T@U) (b@@55 T@U) (t@@32 T@U) ) (! (let ((V@@25 (MapType0TypeInv1 (type b@@55))))
(let ((U@@25 (MapType0TypeInv0 (type a@@76))))
 (=> (and (and (= (type a@@76) (MapType0Type U@@25 boolType)) (= (type b@@55) (MapType0Type U@@25 V@@25))) (= (type t@@32) TyType)) (= (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@32)) a@@76))))
 :qid |fastexpb.1529:20|
 :skolemid |294|
 :pattern ( (|IMap#Domain| (|IMap#Glue| a@@76 b@@55 t@@32)))
)))
(assert (forall ((a@@77 T@U) (b@@56 T@U) (t@@33 T@U) ) (! (let ((V@@26 (MapType0TypeInv1 (type b@@56))))
(let ((U@@26 (MapType0TypeInv0 (type a@@77))))
 (=> (and (and (= (type a@@77) (MapType0Type U@@26 boolType)) (= (type b@@56) (MapType0Type U@@26 V@@26))) (= (type t@@33) TyType)) (= (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)) b@@56))))
 :qid |fastexpb.1533:20|
 :skolemid |295|
 :pattern ( (|IMap#Elements| (|IMap#Glue| a@@77 b@@56 t@@33)))
)))
(assert (forall ((a@@78 T@U) (b@@57 T@U) (t@@34 T@U) ) (! (let ((V@@27 (MapType0TypeInv1 (type b@@57))))
(let ((U@@27 (MapType0TypeInv0 (type a@@78))))
 (=> (and (and (= (type a@@78) (MapType0Type U@@27 boolType)) (= (type b@@57) (MapType0Type U@@27 V@@27))) (= (type t@@34) TyType)) ($Is (|IMap#Glue| a@@78 b@@57 t@@34) t@@34))))
 :qid |fastexpb.1537:20|
 :skolemid |296|
 :pattern ( ($Is (|IMap#Glue| a@@78 b@@57 t@@34) t@@34))
)))
(assert (forall ((arg0@@102 T@U) (arg1@@44 T@U) (arg2@@6 T@U) ) (! (let ((V@@28 (type arg2@@6)))
(let ((U@@28 (type arg1@@44)))
(= (type (|IMap#Build| arg0@@102 arg1@@44 arg2@@6)) (IMapType U@@28 V@@28))))
 :qid |funType:IMap#Build|
 :pattern ( (|IMap#Build| arg0@@102 arg1@@44 arg2@@6))
)))
(assert (forall ((m@@25 T@U) (u@@18 T@U) (|u'@@0| T@U) (v@@43 T@U) ) (! (let ((V@@29 (type v@@43)))
(let ((U@@29 (type u@@18)))
 (=> (and (= (type m@@25) (IMapType U@@29 V@@29)) (= (type |u'@@0|) U@@29)) (and (=> (= |u'@@0| u@@18) (and (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|)) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|) v@@43))) (=> (not (= |u'@@0| u@@18)) (and (and (=> (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|)) (U_2_bool (MapType0Select (|IMap#Domain| m@@25) |u'@@0|))) (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@25) |u'@@0|)) (U_2_bool (MapType0Select (|IMap#Domain| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|)))) (= (MapType0Select (|IMap#Elements| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|) (MapType0Select (|IMap#Elements| m@@25) |u'@@0|))))))))
 :qid |fastexpb.1543:20|
 :skolemid |297|
 :pattern ( (MapType0Select (|IMap#Domain| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|))
 :pattern ( (MapType0Select (|IMap#Elements| (|IMap#Build| m@@25 u@@18 v@@43)) |u'@@0|))
)))
(assert (forall ((m@@26 T@U) (|m'@@2| T@U) ) (! (let ((V@@30 (IMapTypeInv1 (type m@@26))))
(let ((U@@30 (IMapTypeInv0 (type m@@26))))
 (=> (and (= (type m@@26) (IMapType U@@30 V@@30)) (= (type |m'@@2|) (IMapType U@@30 V@@30))) (and (=> (|IMap#Equal| m@@26 |m'@@2|) (and (forall ((u@@19 T@U) ) (!  (=> (= (type u@@19) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@19)) (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@19)))))
 :qid |fastexpb.1558:19|
 :skolemid |298|
 :no-pattern (type u@@19)
 :no-pattern (U_2_int u@@19)
 :no-pattern (U_2_bool u@@19)
)) (forall ((u@@20 T@U) ) (!  (=> (and (= (type u@@20) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@20))) (= (MapType0Select (|IMap#Elements| m@@26) u@@20) (MapType0Select (|IMap#Elements| |m'@@2|) u@@20)))
 :qid |fastexpb.1559:19|
 :skolemid |299|
 :no-pattern (type u@@20)
 :no-pattern (U_2_int u@@20)
 :no-pattern (U_2_bool u@@20)
)))) (=> (and (forall ((u@@21 T@U) ) (!  (=> (= (type u@@21) U@@30) (and (=> (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21))) (=> (U_2_bool (MapType0Select (|IMap#Domain| |m'@@2|) u@@21)) (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@21)))))
 :qid |fastexpb.1558:19|
 :skolemid |298|
 :no-pattern (type u@@21)
 :no-pattern (U_2_int u@@21)
 :no-pattern (U_2_bool u@@21)
)) (forall ((u@@22 T@U) ) (!  (=> (and (= (type u@@22) U@@30) (U_2_bool (MapType0Select (|IMap#Domain| m@@26) u@@22))) (= (MapType0Select (|IMap#Elements| m@@26) u@@22) (MapType0Select (|IMap#Elements| |m'@@2|) u@@22)))
 :qid |fastexpb.1559:19|
 :skolemid |299|
 :no-pattern (type u@@22)
 :no-pattern (U_2_int u@@22)
 :no-pattern (U_2_bool u@@22)
))) (|IMap#Equal| m@@26 |m'@@2|))))))
 :qid |fastexpb.1555:20|
 :skolemid |300|
 :pattern ( (|IMap#Equal| m@@26 |m'@@2|))
)))
(assert (forall ((m@@27 T@U) (|m'@@3| T@U) ) (! (let ((V@@31 (IMapTypeInv1 (type m@@27))))
(let ((U@@31 (IMapTypeInv0 (type m@@27))))
 (=> (and (and (= (type m@@27) (IMapType U@@31 V@@31)) (= (type |m'@@3|) (IMapType U@@31 V@@31))) (|IMap#Equal| m@@27 |m'@@3|)) (= m@@27 |m'@@3|))))
 :qid |fastexpb.1562:20|
 :skolemid |301|
 :pattern ( (|IMap#Equal| m@@27 |m'@@3|))
)))
(assert (forall ((x@@41 Int) (y@@12 Int) ) (! (= (INTERNAL_add_boogie x@@41 y@@12) (+ x@@41 y@@12))
 :qid |fastexpb.1568:15|
 :skolemid |302|
 :pattern ( (INTERNAL_add_boogie x@@41 y@@12))
)))
(assert (forall ((x@@42 Int) (y@@13 Int) ) (! (= (INTERNAL_sub_boogie x@@42 y@@13) (- x@@42 y@@13))
 :qid |fastexpb.1574:15|
 :skolemid |303|
 :pattern ( (INTERNAL_sub_boogie x@@42 y@@13))
)))
(assert (forall ((x@@43 Int) (y@@14 Int) ) (! (= (INTERNAL_mul_boogie x@@43 y@@14) (* x@@43 y@@14))
 :qid |fastexpb.1580:15|
 :skolemid |304|
 :pattern ( (INTERNAL_mul_boogie x@@43 y@@14))
)))
(assert (forall ((x@@44 Int) (y@@15 Int) ) (! (= (INTERNAL_div_boogie x@@44 y@@15) (div x@@44 y@@15))
 :qid |fastexpb.1586:15|
 :skolemid |305|
 :pattern ( (INTERNAL_div_boogie x@@44 y@@15))
)))
(assert (forall ((x@@45 Int) (y@@16 Int) ) (! (= (INTERNAL_mod_boogie x@@45 y@@16) (mod x@@45 y@@16))
 :qid |fastexpb.1592:15|
 :skolemid |306|
 :pattern ( (INTERNAL_mod_boogie x@@45 y@@16))
)))
(assert (forall ((x@@46 Int) (y@@17 Int) ) (!  (and (=> (INTERNAL_lt_boogie x@@46 y@@17) (< x@@46 y@@17)) (=> (< x@@46 y@@17) (INTERNAL_lt_boogie x@@46 y@@17)))
 :qid |fastexpb.1598:15|
 :skolemid |307|
 :pattern ( (INTERNAL_lt_boogie x@@46 y@@17))
)))
(assert (forall ((x@@47 Int) (y@@18 Int) ) (!  (and (=> (INTERNAL_le_boogie x@@47 y@@18) (<= x@@47 y@@18)) (=> (<= x@@47 y@@18) (INTERNAL_le_boogie x@@47 y@@18)))
 :qid |fastexpb.1604:15|
 :skolemid |308|
 :pattern ( (INTERNAL_le_boogie x@@47 y@@18))
)))
(assert (forall ((x@@48 Int) (y@@19 Int) ) (!  (and (=> (INTERNAL_gt_boogie x@@48 y@@19) (> x@@48 y@@19)) (=> (> x@@48 y@@19) (INTERNAL_gt_boogie x@@48 y@@19)))
 :qid |fastexpb.1610:15|
 :skolemid |309|
 :pattern ( (INTERNAL_gt_boogie x@@48 y@@19))
)))
(assert (forall ((x@@49 Int) (y@@20 Int) ) (!  (and (=> (INTERNAL_ge_boogie x@@49 y@@20) (>= x@@49 y@@20)) (=> (>= x@@49 y@@20) (INTERNAL_ge_boogie x@@49 y@@20)))
 :qid |fastexpb.1616:15|
 :skolemid |310|
 :pattern ( (INTERNAL_ge_boogie x@@49 y@@20))
)))
(assert (forall ((x@@50 Int) (y@@21 Int) ) (! (= (Mul x@@50 y@@21) (* x@@50 y@@21))
 :qid |fastexpb.1622:15|
 :skolemid |311|
 :pattern ( (Mul x@@50 y@@21))
)))
(assert (forall ((x@@51 Int) (y@@22 Int) ) (! (= (Div x@@51 y@@22) (div x@@51 y@@22))
 :qid |fastexpb.1626:15|
 :skolemid |312|
 :pattern ( (Div x@@51 y@@22))
)))
(assert (forall ((x@@52 Int) (y@@23 Int) ) (! (= (Mod x@@52 y@@23) (mod x@@52 y@@23))
 :qid |fastexpb.1630:15|
 :skolemid |313|
 :pattern ( (Mod x@@52 y@@23))
)))
(assert (forall ((x@@53 Int) (y@@24 Int) ) (! (= (Add x@@53 y@@24) (+ x@@53 y@@24))
 :qid |fastexpb.1634:15|
 :skolemid |314|
 :pattern ( (Add x@@53 y@@24))
)))
(assert (forall ((x@@54 Int) (y@@25 Int) ) (! (= (Sub x@@54 y@@25) (- x@@54 y@@25))
 :qid |fastexpb.1638:15|
 :skolemid |315|
 :pattern ( (Sub x@@54 y@@25))
)))
(assert (= (type Tclass._System.nat) TyType))
(assert (= (Tag Tclass._System.nat) Tagclass._System.nat))
(assert (forall ((bx@@34 T@U) ) (!  (=> (and (= (type bx@@34) BoxType) ($IsBox bx@@34 Tclass._System.nat)) (and (= ($Box ($Unbox intType bx@@34)) bx@@34) ($Is ($Unbox intType bx@@34) Tclass._System.nat)))
 :qid |fastexpb.1648:15|
 :skolemid |316|
 :pattern ( ($IsBox bx@@34 Tclass._System.nat))
)))
(assert (forall ((|x#0| T@U) ) (!  (=> (= (type |x#0|) intType) (and (=> ($Is |x#0| Tclass._System.nat) (<= (LitInt 0) (U_2_int |x#0|))) (=> (<= (LitInt 0) (U_2_int |x#0|)) ($Is |x#0| Tclass._System.nat))))
 :qid |fastexpb.1654:15|
 :skolemid |317|
 :pattern ( ($Is |x#0| Tclass._System.nat))
)))
(assert (forall ((|x#0@@0| T@U) ($h T@U) ) (!  (=> (and (= (type |x#0@@0|) intType) (= (type $h) (MapType1Type refType))) ($IsAlloc |x#0@@0| Tclass._System.nat $h))
 :qid |fastexpb.1659:15|
 :skolemid |318|
 :pattern ( ($IsAlloc |x#0@@0| Tclass._System.nat $h))
)))
(assert (= (Tag Tclass._System.object?) Tagclass._System.object?))
(assert (forall ((bx@@35 T@U) ) (!  (=> (and (= (type bx@@35) BoxType) ($IsBox bx@@35 Tclass._System.object?)) (and (= ($Box ($Unbox refType bx@@35)) bx@@35) ($Is ($Unbox refType bx@@35) Tclass._System.object?)))
 :qid |fastexpb.1671:15|
 :skolemid |319|
 :pattern ( ($IsBox bx@@35 Tclass._System.object?))
)))
(assert (forall (($o T@U) ) (!  (=> (= (type $o) refType) ($Is $o Tclass._System.object?))
 :qid |fastexpb.1677:15|
 :skolemid |320|
 :pattern ( ($Is $o Tclass._System.object?))
)))
(assert (= (type null) refType))
(assert (forall (($o@@0 T@U) ($h@@0 T@U) ) (!  (=> (and (= (type $o@@0) refType) (= (type $h@@0) (MapType1Type refType))) (and (=> ($IsAlloc $o@@0 Tclass._System.object? $h@@0) (or (= $o@@0 null) (U_2_bool (MapType1Select $h@@0 $o@@0 alloc)))) (=> (or (= $o@@0 null) (U_2_bool (MapType1Select $h@@0 $o@@0 alloc))) ($IsAlloc $o@@0 Tclass._System.object? $h@@0))))
 :qid |fastexpb.1682:15|
 :skolemid |321|
 :pattern ( ($IsAlloc $o@@0 Tclass._System.object? $h@@0))
)))
(assert (= (type Tclass._System.object) TyType))
(assert (= (Tag Tclass._System.object) Tagclass._System.object))
(assert (forall ((bx@@36 T@U) ) (!  (=> (and (= (type bx@@36) BoxType) ($IsBox bx@@36 Tclass._System.object)) (and (= ($Box ($Unbox refType bx@@36)) bx@@36) ($Is ($Unbox refType bx@@36) Tclass._System.object)))
 :qid |fastexpb.1697:15|
 :skolemid |322|
 :pattern ( ($IsBox bx@@36 Tclass._System.object))
)))
(assert (forall ((|c#0| T@U) ) (!  (=> (= (type |c#0|) refType) (and (=> ($Is |c#0| Tclass._System.object) (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null)))) (=> (and ($Is |c#0| Tclass._System.object?) (not (= |c#0| null))) ($Is |c#0| Tclass._System.object))))
 :qid |fastexpb.1703:15|
 :skolemid |323|
 :pattern ( ($Is |c#0| Tclass._System.object))
)))
(assert (forall ((|c#0@@0| T@U) ($h@@1 T@U) ) (!  (=> (and (= (type |c#0@@0|) refType) (= (type $h@@1) (MapType1Type refType))) (and (=> ($IsAlloc |c#0@@0| Tclass._System.object $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1)) (=> ($IsAlloc |c#0@@0| Tclass._System.object? $h@@1) ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))))
 :qid |fastexpb.1709:15|
 :skolemid |324|
 :pattern ( ($IsAlloc |c#0@@0| Tclass._System.object $h@@1))
)))
(assert (forall ((arg0@@103 T@U) ) (! (= (type (Tclass._System.array? arg0@@103)) TyType)
 :qid |funType:Tclass._System.array?|
 :pattern ( (Tclass._System.array? arg0@@103))
)))
(assert (forall ((|#$arg| T@U) ) (!  (=> (= (type |#$arg|) TyType) (= (Tag (Tclass._System.array? |#$arg|)) Tagclass._System.array?))
 :qid |fastexpb.1719:15|
 :skolemid |325|
 :pattern ( (Tclass._System.array? |#$arg|))
)))
(assert (forall ((arg0@@104 T@U) ) (! (= (type (Tclass._System.array?_0 arg0@@104)) TyType)
 :qid |funType:Tclass._System.array?_0|
 :pattern ( (Tclass._System.array?_0 arg0@@104))
)))
(assert (forall ((|#$arg@@0| T@U) ) (!  (=> (= (type |#$arg@@0|) TyType) (= (Tclass._System.array?_0 (Tclass._System.array? |#$arg@@0|)) |#$arg@@0|))
 :qid |fastexpb.1726:15|
 :skolemid |326|
 :pattern ( (Tclass._System.array? |#$arg@@0|))
)))
(assert (forall ((|#$arg@@1| T@U) (bx@@37 T@U) ) (!  (=> (and (and (= (type |#$arg@@1|) TyType) (= (type bx@@37) BoxType)) ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|))) (and (= ($Box ($Unbox refType bx@@37)) bx@@37) ($Is ($Unbox refType bx@@37) (Tclass._System.array? |#$arg@@1|))))
 :qid |fastexpb.1733:15|
 :skolemid |327|
 :pattern ( ($IsBox bx@@37 (Tclass._System.array? |#$arg@@1|)))
)))
(assert (forall ((arg0@@105 T@U) ) (! (= (type (dtype arg0@@105)) TyType)
 :qid |funType:dtype|
 :pattern ( (dtype arg0@@105))
)))
(assert (forall ((|#$arg@@2| T@U) ($h@@2 T@U) ($o@@1 T@U) ($i0 Int) ) (!  (=> (and (and (= (type |#$arg@@2|) TyType) (= (type $h@@2) (MapType1Type refType))) (= (type $o@@1) refType)) (=> (and (and (and (and ($IsGoodHeap $h@@2) (not (= $o@@1 null))) (= (dtype $o@@1) (Tclass._System.array? |#$arg@@2|))) (<= 0 $i0)) (< $i0 (_System.array.Length $o@@1))) ($IsBox (MapType1Select $h@@2 $o@@1 (IndexField $i0)) |#$arg@@2|)))
 :qid |fastexpb.1740:15|
 :skolemid |328|
 :pattern ( (MapType1Select $h@@2 $o@@1 (IndexField $i0)) (Tclass._System.array? |#$arg@@2|))
)))
(assert (forall ((|#$arg@@3| T@U) ($h@@3 T@U) ($o@@2 T@U) ($i0@@0 Int) ) (!  (=> (and (and (= (type |#$arg@@3|) TyType) (= (type $h@@3) (MapType1Type refType))) (= (type $o@@2) refType)) (=> (and (and (and (and (and ($IsGoodHeap $h@@3) (not (= $o@@2 null))) (= (dtype $o@@2) (Tclass._System.array? |#$arg@@3|))) (<= 0 $i0@@0)) (< $i0@@0 (_System.array.Length $o@@2))) (U_2_bool (MapType1Select $h@@3 $o@@2 alloc))) ($IsAllocBox (MapType1Select $h@@3 $o@@2 (IndexField $i0@@0)) |#$arg@@3| $h@@3)))
 :qid |fastexpb.1752:15|
 :skolemid |329|
 :pattern ( (MapType1Select $h@@3 $o@@2 (IndexField $i0@@0)) (Tclass._System.array? |#$arg@@3|))
)))
(assert (forall ((|#$arg@@4| T@U) ($o@@3 T@U) ) (!  (=> (and (= (type |#$arg@@4|) TyType) (= (type $o@@3) refType)) (and (=> ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)) (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|)))) (=> (or (= $o@@3 null) (= (dtype $o@@3) (Tclass._System.array? |#$arg@@4|))) ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))))
 :qid |fastexpb.1765:15|
 :skolemid |330|
 :pattern ( ($Is $o@@3 (Tclass._System.array? |#$arg@@4|)))
)))
(assert (forall ((|#$arg@@5| T@U) ($o@@4 T@U) ($h@@4 T@U) ) (!  (=> (and (and (= (type |#$arg@@5|) TyType) (= (type $o@@4) refType)) (= (type $h@@4) (MapType1Type refType))) (and (=> ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4) (or (= $o@@4 null) (U_2_bool (MapType1Select $h@@4 $o@@4 alloc)))) (=> (or (= $o@@4 null) (U_2_bool (MapType1Select $h@@4 $o@@4 alloc))) ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))))
 :qid |fastexpb.1771:15|
 :skolemid |331|
 :pattern ( ($IsAlloc $o@@4 (Tclass._System.array? |#$arg@@5|) $h@@4))
)))
(assert (forall ((|#$arg@@6| T@U) ($o@@5 T@U) ) (!  (=> (and (and (= (type |#$arg@@6|) TyType) (= (type $o@@5) refType)) (and (not (= $o@@5 null)) (= (dtype $o@@5) (Tclass._System.array? |#$arg@@6|)))) ($Is (int_2_U (_System.array.Length $o@@5)) TInt))
 :qid |fastexpb.1777:15|
 :skolemid |332|
 :pattern ( (_System.array.Length $o@@5) (Tclass._System.array? |#$arg@@6|))
)))
(assert (forall ((|#$arg@@7| T@U) ($h@@5 T@U) ($o@@6 T@U) ) (!  (=> (and (and (= (type |#$arg@@7|) TyType) (= (type $h@@5) (MapType1Type refType))) (= (type $o@@6) refType)) (=> (and (and (and ($IsGoodHeap $h@@5) (not (= $o@@6 null))) (= (dtype $o@@6) (Tclass._System.array? |#$arg@@7|))) (U_2_bool (MapType1Select $h@@5 $o@@6 alloc))) ($IsAlloc (int_2_U (_System.array.Length $o@@6)) TInt $h@@5)))
 :qid |fastexpb.1783:15|
 :skolemid |333|
 :pattern ( (_System.array.Length $o@@6) (MapType1Select $h@@5 $o@@6 alloc) (Tclass._System.array? |#$arg@@7|))
)))
(assert (forall ((arg0@@106 T@U) ) (! (= (type (Tclass._System.array arg0@@106)) TyType)
 :qid |funType:Tclass._System.array|
 :pattern ( (Tclass._System.array arg0@@106))
)))
(assert (forall ((_System.array$arg T@U) ) (!  (=> (= (type _System.array$arg) TyType) (= (Tag (Tclass._System.array _System.array$arg)) Tagclass._System.array))
 :qid |fastexpb.1795:15|
 :skolemid |334|
 :pattern ( (Tclass._System.array _System.array$arg))
)))
(assert (forall ((arg0@@107 T@U) ) (! (= (type (Tclass._System.array_0 arg0@@107)) TyType)
 :qid |funType:Tclass._System.array_0|
 :pattern ( (Tclass._System.array_0 arg0@@107))
)))
(assert (forall ((_System.array$arg@@0 T@U) ) (!  (=> (= (type _System.array$arg@@0) TyType) (= (Tclass._System.array_0 (Tclass._System.array _System.array$arg@@0)) _System.array$arg@@0))
 :qid |fastexpb.1802:15|
 :skolemid |335|
 :pattern ( (Tclass._System.array _System.array$arg@@0))
)))
(assert (forall ((_System.array$arg@@1 T@U) (bx@@38 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@1) TyType) (= (type bx@@38) BoxType)) ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1))) (and (= ($Box ($Unbox refType bx@@38)) bx@@38) ($Is ($Unbox refType bx@@38) (Tclass._System.array _System.array$arg@@1))))
 :qid |fastexpb.1810:15|
 :skolemid |336|
 :pattern ( ($IsBox bx@@38 (Tclass._System.array _System.array$arg@@1)))
)))
(assert (forall ((_System.array$arg@@2 T@U) (|c#0@@1| T@U) ) (!  (=> (and (= (type _System.array$arg@@2) TyType) (= (type |c#0@@1|) refType)) (and (=> ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)) (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null)))) (=> (and ($Is |c#0@@1| (Tclass._System.array? _System.array$arg@@2)) (not (= |c#0@@1| null))) ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))))
 :qid |fastexpb.1817:15|
 :skolemid |337|
 :pattern ( ($Is |c#0@@1| (Tclass._System.array _System.array$arg@@2)))
)))
(assert (forall ((_System.array$arg@@3 T@U) (|c#0@@2| T@U) ($h@@6 T@U) ) (!  (=> (and (and (= (type _System.array$arg@@3) TyType) (= (type |c#0@@2|) refType)) (= (type $h@@6) (MapType1Type refType))) (and (=> ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6)) (=> ($IsAlloc |c#0@@2| (Tclass._System.array? _System.array$arg@@3) $h@@6) ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))))
 :qid |fastexpb.1823:15|
 :skolemid |338|
 :pattern ( ($IsAlloc |c#0@@2| (Tclass._System.array _System.array$arg@@3) $h@@6))
)))
(assert (forall ((arg0@@108 T@U) ) (! (= (type (Tclass._System.___hFunc0 arg0@@108)) TyType)
 :qid |funType:Tclass._System.___hFunc0|
 :pattern ( (Tclass._System.___hFunc0 arg0@@108))
)))
(assert (forall ((|#$R| T@U) ) (!  (=> (= (type |#$R|) TyType) (= (Tag (Tclass._System.___hFunc0 |#$R|)) Tagclass._System.___hFunc0))
 :qid |fastexpb.1831:15|
 :skolemid |339|
 :pattern ( (Tclass._System.___hFunc0 |#$R|))
)))
(assert (forall ((arg0@@109 T@U) ) (! (= (type (Tclass._System.___hFunc0_0 arg0@@109)) TyType)
 :qid |funType:Tclass._System.___hFunc0_0|
 :pattern ( (Tclass._System.___hFunc0_0 arg0@@109))
)))
(assert (forall ((|#$R@@0| T@U) ) (!  (=> (= (type |#$R@@0|) TyType) (= (Tclass._System.___hFunc0_0 (Tclass._System.___hFunc0 |#$R@@0|)) |#$R@@0|))
 :qid |fastexpb.1838:15|
 :skolemid |340|
 :pattern ( (Tclass._System.___hFunc0 |#$R@@0|))
)))
(assert (= (Ctor HandleTypeType) 20))
(assert (forall ((|#$R@@1| T@U) (bx@@39 T@U) ) (!  (=> (and (and (= (type |#$R@@1|) TyType) (= (type bx@@39) BoxType)) ($IsBox bx@@39 (Tclass._System.___hFunc0 |#$R@@1|))) (and (= ($Box ($Unbox HandleTypeType bx@@39)) bx@@39) ($Is ($Unbox HandleTypeType bx@@39) (Tclass._System.___hFunc0 |#$R@@1|))))
 :qid |fastexpb.1845:15|
 :skolemid |341|
 :pattern ( ($IsBox bx@@39 (Tclass._System.___hFunc0 |#$R@@1|)))
)))
(assert  (and (forall ((arg0@@110 T@U) (arg1@@45 T@U) (arg2@@7 T@U) ) (! (= (type (Apply0 arg0@@110 arg1@@45 arg2@@7)) BoxType)
 :qid |funType:Apply0|
 :pattern ( (Apply0 arg0@@110 arg1@@45 arg2@@7))
)) (forall ((arg0@@111 T@U) (arg1@@46 T@U) (arg2@@8 T@U) ) (! (= (type (Handle0 arg0@@111 arg1@@46 arg2@@8)) HandleTypeType)
 :qid |funType:Handle0|
 :pattern ( (Handle0 arg0@@111 arg1@@46 arg2@@8))
))))
(assert (forall ((t0@@12 T@U) (heap T@U) (h@@20 T@U) (r@@6 T@U) (rd T@U) ) (!  (=> (and (and (and (and (= (type t0@@12) TyType) (= (type heap) (MapType1Type refType))) (= (type h@@20) (MapType0Type (MapType1Type refType) BoxType))) (= (type r@@6) (MapType0Type (MapType1Type refType) boolType))) (= (type rd) (MapType0Type (MapType1Type refType) (MapType0Type BoxType boolType)))) (= (Apply0 t0@@12 heap (Handle0 h@@20 r@@6 rd)) (MapType0Select h@@20 heap)))
 :qid |fastexpb.1859:15|
 :skolemid |342|
 :pattern ( (Apply0 t0@@12 heap (Handle0 h@@20 r@@6 rd)))
)))
(assert (forall ((t0@@13 T@U) (heap@@0 T@U) (h@@21 T@U) (r@@7 T@U) (rd@@0 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@13) TyType) (= (type heap@@0) (MapType1Type refType))) (= (type h@@21) (MapType0Type (MapType1Type refType) BoxType))) (= (type r@@7) (MapType0Type (MapType1Type refType) boolType))) (= (type rd@@0) (MapType0Type (MapType1Type refType) (MapType0Type BoxType boolType)))) (U_2_bool (MapType0Select r@@7 heap@@0))) (Requires0 t0@@13 heap@@0 (Handle0 h@@21 r@@7 rd@@0)))
 :qid |fastexpb.1863:15|
 :skolemid |343|
 :pattern ( (Requires0 t0@@13 heap@@0 (Handle0 h@@21 r@@7 rd@@0)))
)))
(assert (forall ((arg0@@112 T@U) (arg1@@47 T@U) (arg2@@9 T@U) ) (! (= (type (Reads0 arg0@@112 arg1@@47 arg2@@9)) (MapType0Type BoxType boolType))
 :qid |funType:Reads0|
 :pattern ( (Reads0 arg0@@112 arg1@@47 arg2@@9))
)))
(assert (forall ((t0@@14 T@U) (heap@@1 T@U) (h@@22 T@U) (r@@8 T@U) (rd@@1 T@U) (bx@@40 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@14) TyType) (= (type heap@@1) (MapType1Type refType))) (= (type h@@22) (MapType0Type (MapType1Type refType) BoxType))) (= (type r@@8) (MapType0Type (MapType1Type refType) boolType))) (= (type rd@@1) (MapType0Type (MapType1Type refType) (MapType0Type BoxType boolType)))) (= (type bx@@40) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads0 t0@@14 heap@@1 (Handle0 h@@22 r@@8 rd@@1)) bx@@40)) (U_2_bool (MapType0Select (MapType0Select rd@@1 heap@@1) bx@@40))) (=> (U_2_bool (MapType0Select (MapType0Select rd@@1 heap@@1) bx@@40)) (U_2_bool (MapType0Select (Reads0 t0@@14 heap@@1 (Handle0 h@@22 r@@8 rd@@1)) bx@@40)))))
 :qid |fastexpb.1867:15|
 :skolemid |344|
 :pattern ( (MapType0Select (Reads0 t0@@14 heap@@1 (Handle0 h@@22 r@@8 rd@@1)) bx@@40))
)))
(assert (forall ((t0@@15 T@U) (h0@@0 T@U) (h1@@0 T@U) (f@@5 T@U) ) (!  (=> (and (and (and (= (type t0@@15) TyType) (= (type h0@@0) (MapType1Type refType))) (= (type h1@@0) (MapType1Type refType))) (= (type f@@5) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@0 h1@@0) ($IsGoodHeap h0@@0)) ($IsGoodHeap h1@@0)) ($Is f@@5 (Tclass._System.___hFunc0 t0@@15))) (forall ((o@@55 T@U) (fld T@U) ) (! (let ((a@@79 (FieldTypeInv0 (type fld))))
 (=> (and (and (= (type o@@55) refType) (= (type fld) (FieldType a@@79))) (and (not (= o@@55 null)) (U_2_bool (MapType0Select (Reads0 t0@@15 h0@@0 f@@5) ($Box o@@55))))) (= (MapType1Select h0@@0 o@@55 fld) (MapType1Select h1@@0 o@@55 fld))))
 :qid |fastexpb.1889:22|
 :skolemid |345|
 :no-pattern (type o@@55)
 :no-pattern (type fld)
 :no-pattern (U_2_int o@@55)
 :no-pattern (U_2_bool o@@55)
 :no-pattern (U_2_int fld)
 :no-pattern (U_2_bool fld)
))) (= (Reads0 t0@@15 h0@@0 f@@5) (Reads0 t0@@15 h1@@0 f@@5))))
 :qid |fastexpb.1882:15|
 :skolemid |346|
 :pattern ( ($HeapSucc h0@@0 h1@@0) (Reads0 t0@@15 h1@@0 f@@5))
)))
(assert (forall ((t0@@16 T@U) (h0@@1 T@U) (h1@@1 T@U) (f@@6 T@U) ) (!  (=> (and (and (and (= (type t0@@16) TyType) (= (type h0@@1) (MapType1Type refType))) (= (type h1@@1) (MapType1Type refType))) (= (type f@@6) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@1 h1@@1) ($IsGoodHeap h0@@1)) ($IsGoodHeap h1@@1)) ($Is f@@6 (Tclass._System.___hFunc0 t0@@16))) (forall ((o@@56 T@U) (fld@@0 T@U) ) (! (let ((a@@80 (FieldTypeInv0 (type fld@@0))))
 (=> (and (and (= (type o@@56) refType) (= (type fld@@0) (FieldType a@@80))) (and (not (= o@@56 null)) (U_2_bool (MapType0Select (Reads0 t0@@16 h1@@1 f@@6) ($Box o@@56))))) (= (MapType1Select h0@@1 o@@56 fld@@0) (MapType1Select h1@@1 o@@56 fld@@0))))
 :qid |fastexpb.1901:22|
 :skolemid |347|
 :no-pattern (type o@@56)
 :no-pattern (type fld@@0)
 :no-pattern (U_2_int o@@56)
 :no-pattern (U_2_bool o@@56)
 :no-pattern (U_2_int fld@@0)
 :no-pattern (U_2_bool fld@@0)
))) (= (Reads0 t0@@16 h0@@1 f@@6) (Reads0 t0@@16 h1@@1 f@@6))))
 :qid |fastexpb.1894:15|
 :skolemid |348|
 :pattern ( ($HeapSucc h0@@1 h1@@1) (Reads0 t0@@16 h1@@1 f@@6))
)))
(assert (forall ((t0@@17 T@U) (h0@@2 T@U) (h1@@2 T@U) (f@@7 T@U) ) (!  (=> (and (and (and (= (type t0@@17) TyType) (= (type h0@@2) (MapType1Type refType))) (= (type h1@@2) (MapType1Type refType))) (= (type f@@7) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@2 h1@@2) ($IsGoodHeap h0@@2)) ($IsGoodHeap h1@@2)) ($Is f@@7 (Tclass._System.___hFunc0 t0@@17))) (forall ((o@@57 T@U) (fld@@1 T@U) ) (! (let ((a@@81 (FieldTypeInv0 (type fld@@1))))
 (=> (and (and (= (type o@@57) refType) (= (type fld@@1) (FieldType a@@81))) (and (not (= o@@57 null)) (U_2_bool (MapType0Select (Reads0 t0@@17 h0@@2 f@@7) ($Box o@@57))))) (= (MapType1Select h0@@2 o@@57 fld@@1) (MapType1Select h1@@2 o@@57 fld@@1))))
 :qid |fastexpb.1913:22|
 :skolemid |349|
 :no-pattern (type o@@57)
 :no-pattern (type fld@@1)
 :no-pattern (U_2_int o@@57)
 :no-pattern (U_2_bool o@@57)
 :no-pattern (U_2_int fld@@1)
 :no-pattern (U_2_bool fld@@1)
))) (and (=> (Requires0 t0@@17 h0@@2 f@@7) (Requires0 t0@@17 h1@@2 f@@7)) (=> (Requires0 t0@@17 h1@@2 f@@7) (Requires0 t0@@17 h0@@2 f@@7)))))
 :qid |fastexpb.1906:15|
 :skolemid |350|
 :pattern ( ($HeapSucc h0@@2 h1@@2) (Requires0 t0@@17 h1@@2 f@@7))
)))
(assert (forall ((t0@@18 T@U) (h0@@3 T@U) (h1@@3 T@U) (f@@8 T@U) ) (!  (=> (and (and (and (= (type t0@@18) TyType) (= (type h0@@3) (MapType1Type refType))) (= (type h1@@3) (MapType1Type refType))) (= (type f@@8) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@3 h1@@3) ($IsGoodHeap h0@@3)) ($IsGoodHeap h1@@3)) ($Is f@@8 (Tclass._System.___hFunc0 t0@@18))) (forall ((o@@58 T@U) (fld@@2 T@U) ) (! (let ((a@@82 (FieldTypeInv0 (type fld@@2))))
 (=> (and (and (= (type o@@58) refType) (= (type fld@@2) (FieldType a@@82))) (and (not (= o@@58 null)) (U_2_bool (MapType0Select (Reads0 t0@@18 h1@@3 f@@8) ($Box o@@58))))) (= (MapType1Select h0@@3 o@@58 fld@@2) (MapType1Select h1@@3 o@@58 fld@@2))))
 :qid |fastexpb.1925:22|
 :skolemid |351|
 :no-pattern (type o@@58)
 :no-pattern (type fld@@2)
 :no-pattern (U_2_int o@@58)
 :no-pattern (U_2_bool o@@58)
 :no-pattern (U_2_int fld@@2)
 :no-pattern (U_2_bool fld@@2)
))) (and (=> (Requires0 t0@@18 h0@@3 f@@8) (Requires0 t0@@18 h1@@3 f@@8)) (=> (Requires0 t0@@18 h1@@3 f@@8) (Requires0 t0@@18 h0@@3 f@@8)))))
 :qid |fastexpb.1918:15|
 :skolemid |352|
 :pattern ( ($HeapSucc h0@@3 h1@@3) (Requires0 t0@@18 h1@@3 f@@8))
)))
(assert (forall ((t0@@19 T@U) (h0@@4 T@U) (h1@@4 T@U) (f@@9 T@U) ) (!  (=> (and (and (and (= (type t0@@19) TyType) (= (type h0@@4) (MapType1Type refType))) (= (type h1@@4) (MapType1Type refType))) (= (type f@@9) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@4 h1@@4) ($IsGoodHeap h0@@4)) ($IsGoodHeap h1@@4)) ($Is f@@9 (Tclass._System.___hFunc0 t0@@19))) (forall ((o@@59 T@U) (fld@@3 T@U) ) (! (let ((a@@83 (FieldTypeInv0 (type fld@@3))))
 (=> (and (and (= (type o@@59) refType) (= (type fld@@3) (FieldType a@@83))) (and (not (= o@@59 null)) (U_2_bool (MapType0Select (Reads0 t0@@19 h0@@4 f@@9) ($Box o@@59))))) (= (MapType1Select h0@@4 o@@59 fld@@3) (MapType1Select h1@@4 o@@59 fld@@3))))
 :qid |fastexpb.1937:22|
 :skolemid |353|
 :no-pattern (type o@@59)
 :no-pattern (type fld@@3)
 :no-pattern (U_2_int o@@59)
 :no-pattern (U_2_bool o@@59)
 :no-pattern (U_2_int fld@@3)
 :no-pattern (U_2_bool fld@@3)
))) (= (Apply0 t0@@19 h0@@4 f@@9) (Apply0 t0@@19 h1@@4 f@@9))))
 :qid |fastexpb.1930:15|
 :skolemid |354|
 :pattern ( ($HeapSucc h0@@4 h1@@4) (Apply0 t0@@19 h1@@4 f@@9))
)))
(assert (forall ((t0@@20 T@U) (h0@@5 T@U) (h1@@5 T@U) (f@@10 T@U) ) (!  (=> (and (and (and (= (type t0@@20) TyType) (= (type h0@@5) (MapType1Type refType))) (= (type h1@@5) (MapType1Type refType))) (= (type f@@10) HandleTypeType)) (=> (and (and (and (and ($HeapSucc h0@@5 h1@@5) ($IsGoodHeap h0@@5)) ($IsGoodHeap h1@@5)) ($Is f@@10 (Tclass._System.___hFunc0 t0@@20))) (forall ((o@@60 T@U) (fld@@4 T@U) ) (! (let ((a@@84 (FieldTypeInv0 (type fld@@4))))
 (=> (and (and (= (type o@@60) refType) (= (type fld@@4) (FieldType a@@84))) (and (not (= o@@60 null)) (U_2_bool (MapType0Select (Reads0 t0@@20 h1@@5 f@@10) ($Box o@@60))))) (= (MapType1Select h0@@5 o@@60 fld@@4) (MapType1Select h1@@5 o@@60 fld@@4))))
 :qid |fastexpb.1949:22|
 :skolemid |355|
 :no-pattern (type o@@60)
 :no-pattern (type fld@@4)
 :no-pattern (U_2_int o@@60)
 :no-pattern (U_2_bool o@@60)
 :no-pattern (U_2_int fld@@4)
 :no-pattern (U_2_bool fld@@4)
))) (= (Apply0 t0@@20 h0@@5 f@@10) (Apply0 t0@@20 h1@@5 f@@10))))
 :qid |fastexpb.1942:15|
 :skolemid |356|
 :pattern ( ($HeapSucc h0@@5 h1@@5) (Apply0 t0@@20 h1@@5 f@@10))
)))
(assert (forall ((t0@@21 T@U) (heap@@2 T@U) (f@@11 T@U) ) (!  (=> (and (and (and (= (type t0@@21) TyType) (= (type heap@@2) (MapType1Type refType))) (= (type f@@11) HandleTypeType)) (and ($IsGoodHeap heap@@2) ($Is f@@11 (Tclass._System.___hFunc0 t0@@21)))) (and (=> (|Set#Equal| (Reads0 t0@@21 $OneHeap f@@11) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@21 heap@@2 f@@11) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads0 t0@@21 heap@@2 f@@11) (|Set#Empty| BoxType)) (|Set#Equal| (Reads0 t0@@21 $OneHeap f@@11) (|Set#Empty| BoxType)))))
 :qid |fastexpb.1954:15|
 :skolemid |357|
 :pattern ( (Reads0 t0@@21 $OneHeap f@@11) ($IsGoodHeap heap@@2))
 :pattern ( (Reads0 t0@@21 heap@@2 f@@11))
)))
(assert (forall ((t0@@22 T@U) (heap@@3 T@U) (f@@12 T@U) ) (!  (=> (and (and (and (= (type t0@@22) TyType) (= (type heap@@3) (MapType1Type refType))) (= (type f@@12) HandleTypeType)) (and (and ($IsGoodHeap heap@@3) ($Is f@@12 (Tclass._System.___hFunc0 t0@@22))) (|Set#Equal| (Reads0 t0@@22 $OneHeap f@@12) (|Set#Empty| BoxType)))) (and (=> (Requires0 t0@@22 $OneHeap f@@12) (Requires0 t0@@22 heap@@3 f@@12)) (=> (Requires0 t0@@22 heap@@3 f@@12) (Requires0 t0@@22 $OneHeap f@@12))))
 :qid |fastexpb.1961:15|
 :skolemid |358|
 :pattern ( (Requires0 t0@@22 $OneHeap f@@12) ($IsGoodHeap heap@@3))
 :pattern ( (Requires0 t0@@22 heap@@3 f@@12))
)))
(assert (forall ((f@@13 T@U) (t0@@23 T@U) ) (!  (=> (and (= (type f@@13) HandleTypeType) (= (type t0@@23) TyType)) (and (=> ($Is f@@13 (Tclass._System.___hFunc0 t0@@23)) (forall ((h@@23 T@U) ) (!  (=> (= (type h@@23) (MapType1Type refType)) (=> (and ($IsGoodHeap h@@23) (Requires0 t0@@23 h@@23 f@@13)) ($IsBox (Apply0 t0@@23 h@@23 f@@13) t0@@23)))
 :qid |fastexpb.1971:19|
 :skolemid |359|
 :pattern ( (Apply0 t0@@23 h@@23 f@@13))
))) (=> (forall ((h@@24 T@U) ) (!  (=> (= (type h@@24) (MapType1Type refType)) (=> (and ($IsGoodHeap h@@24) (Requires0 t0@@23 h@@24 f@@13)) ($IsBox (Apply0 t0@@23 h@@24 f@@13) t0@@23)))
 :qid |fastexpb.1971:19|
 :skolemid |359|
 :pattern ( (Apply0 t0@@23 h@@24 f@@13))
)) ($Is f@@13 (Tclass._System.___hFunc0 t0@@23)))))
 :qid |fastexpb.1968:15|
 :skolemid |360|
 :pattern ( ($Is f@@13 (Tclass._System.___hFunc0 t0@@23)))
)))
(assert (forall ((f@@14 T@U) (t0@@24 T@U) (u0 T@U) ) (!  (=> (and (and (and (= (type f@@14) HandleTypeType) (= (type t0@@24) TyType)) (= (type u0) TyType)) (and ($Is f@@14 (Tclass._System.___hFunc0 t0@@24)) (forall ((bx@@41 T@U) ) (!  (=> (and (= (type bx@@41) BoxType) ($IsBox bx@@41 t0@@24)) ($IsBox bx@@41 u0))
 :qid |fastexpb.1978:19|
 :skolemid |361|
 :pattern ( ($IsBox bx@@41 t0@@24))
 :pattern ( ($IsBox bx@@41 u0))
)))) ($Is f@@14 (Tclass._System.___hFunc0 u0)))
 :qid |fastexpb.1975:15|
 :skolemid |362|
 :pattern ( ($Is f@@14 (Tclass._System.___hFunc0 t0@@24)) ($Is f@@14 (Tclass._System.___hFunc0 u0)))
)))
(assert (forall ((f@@15 T@U) (t0@@25 T@U) (h@@25 T@U) ) (!  (=> (and (and (and (= (type f@@15) HandleTypeType) (= (type t0@@25) TyType)) (= (type h@@25) (MapType1Type refType))) ($IsGoodHeap h@@25)) (and (=> ($IsAlloc f@@15 (Tclass._System.___hFunc0 t0@@25) h@@25) (=> (Requires0 t0@@25 h@@25 f@@15) (forall ((r@@9 T@U) ) (!  (=> (= (type r@@9) refType) (=> (and (not (= r@@9 null)) (U_2_bool (MapType0Select (Reads0 t0@@25 h@@25 f@@15) ($Box r@@9)))) (U_2_bool (MapType1Select h@@25 r@@9 alloc))))
 :qid |fastexpb.1988:22|
 :skolemid |363|
 :pattern ( (MapType0Select (Reads0 t0@@25 h@@25 f@@15) ($Box r@@9)))
)))) (=> (=> (Requires0 t0@@25 h@@25 f@@15) (forall ((r@@10 T@U) ) (!  (=> (= (type r@@10) refType) (=> (and (not (= r@@10 null)) (U_2_bool (MapType0Select (Reads0 t0@@25 h@@25 f@@15) ($Box r@@10)))) (U_2_bool (MapType1Select h@@25 r@@10 alloc))))
 :qid |fastexpb.1988:22|
 :skolemid |363|
 :pattern ( (MapType0Select (Reads0 t0@@25 h@@25 f@@15) ($Box r@@10)))
))) ($IsAlloc f@@15 (Tclass._System.___hFunc0 t0@@25) h@@25))))
 :qid |fastexpb.1983:15|
 :skolemid |364|
 :pattern ( ($IsAlloc f@@15 (Tclass._System.___hFunc0 t0@@25) h@@25))
)))
(assert (forall ((f@@16 T@U) (t0@@26 T@U) (h@@26 T@U) ) (!  (=> (and (and (and (and (= (type f@@16) HandleTypeType) (= (type t0@@26) TyType)) (= (type h@@26) (MapType1Type refType))) (and ($IsGoodHeap h@@26) ($IsAlloc f@@16 (Tclass._System.___hFunc0 t0@@26) h@@26))) (Requires0 t0@@26 h@@26 f@@16)) ($IsAllocBox (Apply0 t0@@26 h@@26 f@@16) t0@@26 h@@26))
 :qid |fastexpb.1992:15|
 :skolemid |365|
 :pattern ( ($IsAlloc f@@16 (Tclass._System.___hFunc0 t0@@26) h@@26))
)))
(assert (forall ((arg0@@113 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0 arg0@@113)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0|
 :pattern ( (Tclass._System.___hPartialFunc0 arg0@@113))
)))
(assert (forall ((|#$R@@2| T@U) ) (!  (=> (= (type |#$R@@2|) TyType) (= (Tag (Tclass._System.___hPartialFunc0 |#$R@@2|)) Tagclass._System.___hPartialFunc0))
 :qid |fastexpb.2002:15|
 :skolemid |366|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@2|))
)))
(assert (forall ((arg0@@114 T@U) ) (! (= (type (Tclass._System.___hPartialFunc0_0 arg0@@114)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc0_0|
 :pattern ( (Tclass._System.___hPartialFunc0_0 arg0@@114))
)))
(assert (forall ((|#$R@@3| T@U) ) (!  (=> (= (type |#$R@@3|) TyType) (= (Tclass._System.___hPartialFunc0_0 (Tclass._System.___hPartialFunc0 |#$R@@3|)) |#$R@@3|))
 :qid |fastexpb.2009:15|
 :skolemid |367|
 :pattern ( (Tclass._System.___hPartialFunc0 |#$R@@3|))
)))
(assert (forall ((|#$R@@4| T@U) (bx@@42 T@U) ) (!  (=> (and (and (= (type |#$R@@4|) TyType) (= (type bx@@42) BoxType)) ($IsBox bx@@42 (Tclass._System.___hPartialFunc0 |#$R@@4|))) (and (= ($Box ($Unbox HandleTypeType bx@@42)) bx@@42) ($Is ($Unbox HandleTypeType bx@@42) (Tclass._System.___hPartialFunc0 |#$R@@4|))))
 :qid |fastexpb.2016:15|
 :skolemid |368|
 :pattern ( ($IsBox bx@@42 (Tclass._System.___hPartialFunc0 |#$R@@4|)))
)))
(assert (forall ((|#$R@@5| T@U) (|f#0| T@U) ) (!  (=> (and (= (type |#$R@@5|) TyType) (= (type |f#0|) HandleTypeType)) (and (=> ($Is |f#0| (Tclass._System.___hPartialFunc0 |#$R@@5|)) (and ($Is |f#0| (Tclass._System.___hFunc0 |#$R@@5|)) (|Set#Equal| (Reads0 |#$R@@5| $OneHeap |f#0|) (|Set#Empty| BoxType)))) (=> (and ($Is |f#0| (Tclass._System.___hFunc0 |#$R@@5|)) (|Set#Equal| (Reads0 |#$R@@5| $OneHeap |f#0|) (|Set#Empty| BoxType))) ($Is |f#0| (Tclass._System.___hPartialFunc0 |#$R@@5|)))))
 :qid |fastexpb.2023:15|
 :skolemid |369|
 :pattern ( ($Is |f#0| (Tclass._System.___hPartialFunc0 |#$R@@5|)))
)))
(assert (forall ((|#$R@@6| T@U) (|f#0@@0| T@U) ($h@@7 T@U) ) (!  (=> (and (and (= (type |#$R@@6|) TyType) (= (type |f#0@@0|) HandleTypeType)) (= (type $h@@7) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc0 |#$R@@6|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hFunc0 |#$R@@6|) $h@@7)) (=> ($IsAlloc |f#0@@0| (Tclass._System.___hFunc0 |#$R@@6|) $h@@7) ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc0 |#$R@@6|) $h@@7))))
 :qid |fastexpb.2030:15|
 :skolemid |370|
 :pattern ( ($IsAlloc |f#0@@0| (Tclass._System.___hPartialFunc0 |#$R@@6|) $h@@7))
)))
(assert (forall ((arg0@@115 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0 arg0@@115)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0|
 :pattern ( (Tclass._System.___hTotalFunc0 arg0@@115))
)))
(assert (forall ((|#$R@@7| T@U) ) (!  (=> (= (type |#$R@@7|) TyType) (= (Tag (Tclass._System.___hTotalFunc0 |#$R@@7|)) Tagclass._System.___hTotalFunc0))
 :qid |fastexpb.2038:15|
 :skolemid |371|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@7|))
)))
(assert (forall ((arg0@@116 T@U) ) (! (= (type (Tclass._System.___hTotalFunc0_0 arg0@@116)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc0_0|
 :pattern ( (Tclass._System.___hTotalFunc0_0 arg0@@116))
)))
(assert (forall ((|#$R@@8| T@U) ) (!  (=> (= (type |#$R@@8|) TyType) (= (Tclass._System.___hTotalFunc0_0 (Tclass._System.___hTotalFunc0 |#$R@@8|)) |#$R@@8|))
 :qid |fastexpb.2045:15|
 :skolemid |372|
 :pattern ( (Tclass._System.___hTotalFunc0 |#$R@@8|))
)))
(assert (forall ((|#$R@@9| T@U) (bx@@43 T@U) ) (!  (=> (and (and (= (type |#$R@@9|) TyType) (= (type bx@@43) BoxType)) ($IsBox bx@@43 (Tclass._System.___hTotalFunc0 |#$R@@9|))) (and (= ($Box ($Unbox HandleTypeType bx@@43)) bx@@43) ($Is ($Unbox HandleTypeType bx@@43) (Tclass._System.___hTotalFunc0 |#$R@@9|))))
 :qid |fastexpb.2052:15|
 :skolemid |373|
 :pattern ( ($IsBox bx@@43 (Tclass._System.___hTotalFunc0 |#$R@@9|)))
)))
(assert (forall ((|#$R@@10| T@U) (|f#0@@1| T@U) ) (!  (=> (and (= (type |#$R@@10|) TyType) (= (type |f#0@@1|) HandleTypeType)) (and (=> ($Is |f#0@@1| (Tclass._System.___hTotalFunc0 |#$R@@10|)) (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc0 |#$R@@10|)) (Requires0 |#$R@@10| $OneHeap |f#0@@1|))) (=> (and ($Is |f#0@@1| (Tclass._System.___hPartialFunc0 |#$R@@10|)) (Requires0 |#$R@@10| $OneHeap |f#0@@1|)) ($Is |f#0@@1| (Tclass._System.___hTotalFunc0 |#$R@@10|)))))
 :qid |fastexpb.2059:15|
 :skolemid |374|
 :pattern ( ($Is |f#0@@1| (Tclass._System.___hTotalFunc0 |#$R@@10|)))
)))
(assert (forall ((|#$R@@11| T@U) (|f#0@@2| T@U) ($h@@8 T@U) ) (!  (=> (and (and (= (type |#$R@@11|) TyType) (= (type |f#0@@2|) HandleTypeType)) (= (type $h@@8) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc0 |#$R@@11|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc0 |#$R@@11|) $h@@8)) (=> ($IsAlloc |f#0@@2| (Tclass._System.___hPartialFunc0 |#$R@@11|) $h@@8) ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc0 |#$R@@11|) $h@@8))))
 :qid |fastexpb.2065:15|
 :skolemid |375|
 :pattern ( ($IsAlloc |f#0@@2| (Tclass._System.___hTotalFunc0 |#$R@@11|) $h@@8))
)))
(assert (forall ((arg0@@117 T@U) (arg1@@48 T@U) (arg2@@10 T@U) ) (! (= (type (Tclass._System.___hFunc2 arg0@@117 arg1@@48 arg2@@10)) TyType)
 :qid |funType:Tclass._System.___hFunc2|
 :pattern ( (Tclass._System.___hFunc2 arg0@@117 arg1@@48 arg2@@10))
)))
(assert (forall ((|#$T0| T@U) (|#$T1| T@U) (|#$R@@12| T@U) ) (!  (=> (and (and (= (type |#$T0|) TyType) (= (type |#$T1|) TyType)) (= (type |#$R@@12|) TyType)) (= (Tag (Tclass._System.___hFunc2 |#$T0| |#$T1| |#$R@@12|)) Tagclass._System.___hFunc2))
 :qid |fastexpb.2073:15|
 :skolemid |376|
 :pattern ( (Tclass._System.___hFunc2 |#$T0| |#$T1| |#$R@@12|))
)))
(assert (forall ((arg0@@118 T@U) ) (! (= (type (Tclass._System.___hFunc2_0 arg0@@118)) TyType)
 :qid |funType:Tclass._System.___hFunc2_0|
 :pattern ( (Tclass._System.___hFunc2_0 arg0@@118))
)))
(assert (forall ((|#$T0@@0| T@U) (|#$T1@@0| T@U) (|#$R@@13| T@U) ) (!  (=> (and (and (= (type |#$T0@@0|) TyType) (= (type |#$T1@@0|) TyType)) (= (type |#$R@@13|) TyType)) (= (Tclass._System.___hFunc2_0 (Tclass._System.___hFunc2 |#$T0@@0| |#$T1@@0| |#$R@@13|)) |#$T0@@0|))
 :qid |fastexpb.2080:15|
 :skolemid |377|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@0| |#$T1@@0| |#$R@@13|))
)))
(assert (forall ((arg0@@119 T@U) ) (! (= (type (Tclass._System.___hFunc2_1 arg0@@119)) TyType)
 :qid |funType:Tclass._System.___hFunc2_1|
 :pattern ( (Tclass._System.___hFunc2_1 arg0@@119))
)))
(assert (forall ((|#$T0@@1| T@U) (|#$T1@@1| T@U) (|#$R@@14| T@U) ) (!  (=> (and (and (= (type |#$T0@@1|) TyType) (= (type |#$T1@@1|) TyType)) (= (type |#$R@@14|) TyType)) (= (Tclass._System.___hFunc2_1 (Tclass._System.___hFunc2 |#$T0@@1| |#$T1@@1| |#$R@@14|)) |#$T1@@1|))
 :qid |fastexpb.2087:15|
 :skolemid |378|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@1| |#$T1@@1| |#$R@@14|))
)))
(assert (forall ((arg0@@120 T@U) ) (! (= (type (Tclass._System.___hFunc2_2 arg0@@120)) TyType)
 :qid |funType:Tclass._System.___hFunc2_2|
 :pattern ( (Tclass._System.___hFunc2_2 arg0@@120))
)))
(assert (forall ((|#$T0@@2| T@U) (|#$T1@@2| T@U) (|#$R@@15| T@U) ) (!  (=> (and (and (= (type |#$T0@@2|) TyType) (= (type |#$T1@@2|) TyType)) (= (type |#$R@@15|) TyType)) (= (Tclass._System.___hFunc2_2 (Tclass._System.___hFunc2 |#$T0@@2| |#$T1@@2| |#$R@@15|)) |#$R@@15|))
 :qid |fastexpb.2094:15|
 :skolemid |379|
 :pattern ( (Tclass._System.___hFunc2 |#$T0@@2| |#$T1@@2| |#$R@@15|))
)))
(assert (forall ((|#$T0@@3| T@U) (|#$T1@@3| T@U) (|#$R@@16| T@U) (bx@@44 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@3|) TyType) (= (type |#$T1@@3|) TyType)) (= (type |#$R@@16|) TyType)) (= (type bx@@44) BoxType)) ($IsBox bx@@44 (Tclass._System.___hFunc2 |#$T0@@3| |#$T1@@3| |#$R@@16|))) (and (= ($Box ($Unbox HandleTypeType bx@@44)) bx@@44) ($Is ($Unbox HandleTypeType bx@@44) (Tclass._System.___hFunc2 |#$T0@@3| |#$T1@@3| |#$R@@16|))))
 :qid |fastexpb.2101:15|
 :skolemid |380|
 :pattern ( ($IsBox bx@@44 (Tclass._System.___hFunc2 |#$T0@@3| |#$T1@@3| |#$R@@16|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@121 T@T) (arg1@@49 T@T) (arg2@@11 T@T) (arg3@@0 T@T) ) (! (= (Ctor (MapType2Type arg0@@121 arg1@@49 arg2@@11 arg3@@0)) 21)
 :qid |ctor:MapType2Type|
)) (forall ((arg0@@122 T@T) (arg1@@50 T@T) (arg2@@12 T@T) (arg3@@1 T@T) ) (! (= (MapType2TypeInv0 (MapType2Type arg0@@122 arg1@@50 arg2@@12 arg3@@1)) arg0@@122)
 :qid |typeInv:MapType2TypeInv0|
 :pattern ( (MapType2Type arg0@@122 arg1@@50 arg2@@12 arg3@@1))
))) (forall ((arg0@@123 T@T) (arg1@@51 T@T) (arg2@@13 T@T) (arg3@@2 T@T) ) (! (= (MapType2TypeInv1 (MapType2Type arg0@@123 arg1@@51 arg2@@13 arg3@@2)) arg1@@51)
 :qid |typeInv:MapType2TypeInv1|
 :pattern ( (MapType2Type arg0@@123 arg1@@51 arg2@@13 arg3@@2))
))) (forall ((arg0@@124 T@T) (arg1@@52 T@T) (arg2@@14 T@T) (arg3@@3 T@T) ) (! (= (MapType2TypeInv2 (MapType2Type arg0@@124 arg1@@52 arg2@@14 arg3@@3)) arg2@@14)
 :qid |typeInv:MapType2TypeInv2|
 :pattern ( (MapType2Type arg0@@124 arg1@@52 arg2@@14 arg3@@3))
))) (forall ((arg0@@125 T@T) (arg1@@53 T@T) (arg2@@15 T@T) (arg3@@4 T@T) ) (! (= (MapType2TypeInv3 (MapType2Type arg0@@125 arg1@@53 arg2@@15 arg3@@4)) arg3@@4)
 :qid |typeInv:MapType2TypeInv3|
 :pattern ( (MapType2Type arg0@@125 arg1@@53 arg2@@15 arg3@@4))
))) (forall ((arg0@@126 T@U) (arg1@@54 T@U) (arg2@@16 T@U) (arg3@@5 T@U) ) (! (let ((aVar3 (MapType2TypeInv3 (type arg0@@126))))
(= (type (MapType2Select arg0@@126 arg1@@54 arg2@@16 arg3@@5)) aVar3))
 :qid |funType:MapType2Select|
 :pattern ( (MapType2Select arg0@@126 arg1@@54 arg2@@16 arg3@@5))
))) (forall ((arg0@@127 T@U) (arg1@@55 T@U) (arg2@@17 T@U) (arg3@@6 T@U) (arg4 T@U) ) (! (let ((aVar3@@0 (type arg4)))
(let ((aVar2 (type arg3@@6)))
(let ((aVar1@@2 (type arg2@@17)))
(let ((aVar0@@1 (type arg1@@55)))
(= (type (MapType2Store arg0@@127 arg1@@55 arg2@@17 arg3@@6 arg4)) (MapType2Type aVar0@@1 aVar1@@2 aVar2 aVar3@@0))))))
 :qid |funType:MapType2Store|
 :pattern ( (MapType2Store arg0@@127 arg1@@55 arg2@@17 arg3@@6 arg4))
))) (forall ((m@@28 T@U) (x0@@6 T@U) (x1@@3 T@U) (x2 T@U) (val@@7 T@U) ) (! (let ((aVar3@@1 (MapType2TypeInv3 (type m@@28))))
 (=> (= (type val@@7) aVar3@@1) (= (MapType2Select (MapType2Store m@@28 x0@@6 x1@@3 x2 val@@7) x0@@6 x1@@3 x2) val@@7)))
 :qid |mapAx0:MapType2Select|
 :weight 0
))) (and (and (and (forall ((val@@8 T@U) (m@@29 T@U) (x0@@7 T@U) (x1@@4 T@U) (x2@@0 T@U) (y0@@4 T@U) (y1@@2 T@U) (y2 T@U) ) (!  (or (= x0@@7 y0@@4) (= (MapType2Select (MapType2Store m@@29 x0@@7 x1@@4 x2@@0 val@@8) y0@@4 y1@@2 y2) (MapType2Select m@@29 y0@@4 y1@@2 y2)))
 :qid |mapAx1:MapType2Select:0|
 :weight 0
)) (forall ((val@@9 T@U) (m@@30 T@U) (x0@@8 T@U) (x1@@5 T@U) (x2@@1 T@U) (y0@@5 T@U) (y1@@3 T@U) (y2@@0 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType2Select (MapType2Store m@@30 x0@@8 x1@@5 x2@@1 val@@9) y0@@5 y1@@3 y2@@0) (MapType2Select m@@30 y0@@5 y1@@3 y2@@0)))
 :qid |mapAx1:MapType2Select:1|
 :weight 0
))) (forall ((val@@10 T@U) (m@@31 T@U) (x0@@9 T@U) (x1@@6 T@U) (x2@@2 T@U) (y0@@6 T@U) (y1@@4 T@U) (y2@@1 T@U) ) (!  (or (= x2@@2 y2@@1) (= (MapType2Select (MapType2Store m@@31 x0@@9 x1@@6 x2@@2 val@@10) y0@@6 y1@@4 y2@@1) (MapType2Select m@@31 y0@@6 y1@@4 y2@@1)))
 :qid |mapAx1:MapType2Select:2|
 :weight 0
))) (forall ((val@@11 T@U) (m@@32 T@U) (x0@@10 T@U) (x1@@7 T@U) (x2@@3 T@U) (y0@@7 T@U) (y1@@5 T@U) (y2@@2 T@U) ) (!  (or true (= (MapType2Select (MapType2Store m@@32 x0@@10 x1@@7 x2@@3 val@@11) y0@@7 y1@@5 y2@@2) (MapType2Select m@@32 y0@@7 y1@@5 y2@@2)))
 :qid |mapAx2:MapType2Select|
 :weight 0
)))) (forall ((arg0@@128 T@U) (arg1@@56 T@U) (arg2@@18 T@U) (arg3@@7 T@U) (arg4@@0 T@U) (arg5 T@U) (arg6 T@U) ) (! (= (type (Apply2 arg0@@128 arg1@@56 arg2@@18 arg3@@7 arg4@@0 arg5 arg6)) BoxType)
 :qid |funType:Apply2|
 :pattern ( (Apply2 arg0@@128 arg1@@56 arg2@@18 arg3@@7 arg4@@0 arg5 arg6))
))) (forall ((arg0@@129 T@U) (arg1@@57 T@U) (arg2@@19 T@U) ) (! (= (type (Handle2 arg0@@129 arg1@@57 arg2@@19)) HandleTypeType)
 :qid |funType:Handle2|
 :pattern ( (Handle2 arg0@@129 arg1@@57 arg2@@19))
))))
(assert (forall ((t0@@27 T@U) (t1@@3 T@U) (t2 T@U) (heap@@4 T@U) (h@@27 T@U) (r@@11 T@U) (rd@@2 T@U) (bx0 T@U) (bx1 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@27) TyType) (= (type t1@@3) TyType)) (= (type t2) TyType)) (= (type heap@@4) (MapType1Type refType))) (= (type h@@27) (MapType2Type (MapType1Type refType) BoxType BoxType BoxType))) (= (type r@@11) (MapType2Type (MapType1Type refType) BoxType BoxType boolType))) (= (type rd@@2) (MapType2Type (MapType1Type refType) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0) BoxType)) (= (type bx1) BoxType)) (= (Apply2 t0@@27 t1@@3 t2 heap@@4 (Handle2 h@@27 r@@11 rd@@2) bx0 bx1) (MapType2Select h@@27 heap@@4 bx0 bx1)))
 :qid |fastexpb.2115:15|
 :skolemid |381|
 :pattern ( (Apply2 t0@@27 t1@@3 t2 heap@@4 (Handle2 h@@27 r@@11 rd@@2) bx0 bx1))
)))
(assert (forall ((t0@@28 T@U) (t1@@4 T@U) (t2@@0 T@U) (heap@@5 T@U) (h@@28 T@U) (r@@12 T@U) (rd@@3 T@U) (bx0@@0 T@U) (bx1@@0 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@28) TyType) (= (type t1@@4) TyType)) (= (type t2@@0) TyType)) (= (type heap@@5) (MapType1Type refType))) (= (type h@@28) (MapType2Type (MapType1Type refType) BoxType BoxType BoxType))) (= (type r@@12) (MapType2Type (MapType1Type refType) BoxType BoxType boolType))) (= (type rd@@3) (MapType2Type (MapType1Type refType) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@0) BoxType)) (= (type bx1@@0) BoxType)) (U_2_bool (MapType2Select r@@12 heap@@5 bx0@@0 bx1@@0))) (Requires2 t0@@28 t1@@4 t2@@0 heap@@5 (Handle2 h@@28 r@@12 rd@@3) bx0@@0 bx1@@0))
 :qid |fastexpb.2127:15|
 :skolemid |382|
 :pattern ( (Requires2 t0@@28 t1@@4 t2@@0 heap@@5 (Handle2 h@@28 r@@12 rd@@3) bx0@@0 bx1@@0))
)))
(assert (forall ((arg0@@130 T@U) (arg1@@58 T@U) (arg2@@20 T@U) (arg3@@8 T@U) (arg4@@1 T@U) (arg5@@0 T@U) (arg6@@0 T@U) ) (! (= (type (Reads2 arg0@@130 arg1@@58 arg2@@20 arg3@@8 arg4@@1 arg5@@0 arg6@@0)) (MapType0Type BoxType boolType))
 :qid |funType:Reads2|
 :pattern ( (Reads2 arg0@@130 arg1@@58 arg2@@20 arg3@@8 arg4@@1 arg5@@0 arg6@@0))
)))
(assert (forall ((t0@@29 T@U) (t1@@5 T@U) (t2@@1 T@U) (heap@@6 T@U) (h@@29 T@U) (r@@13 T@U) (rd@@4 T@U) (bx0@@1 T@U) (bx1@@1 T@U) (bx@@45 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (and (= (type t0@@29) TyType) (= (type t1@@5) TyType)) (= (type t2@@1) TyType)) (= (type heap@@6) (MapType1Type refType))) (= (type h@@29) (MapType2Type (MapType1Type refType) BoxType BoxType BoxType))) (= (type r@@13) (MapType2Type (MapType1Type refType) BoxType BoxType boolType))) (= (type rd@@4) (MapType2Type (MapType1Type refType) BoxType BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@1) BoxType)) (= (type bx1@@1) BoxType)) (= (type bx@@45) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads2 t0@@29 t1@@5 t2@@1 heap@@6 (Handle2 h@@29 r@@13 rd@@4) bx0@@1 bx1@@1) bx@@45)) (U_2_bool (MapType0Select (MapType2Select rd@@4 heap@@6 bx0@@1 bx1@@1) bx@@45))) (=> (U_2_bool (MapType0Select (MapType2Select rd@@4 heap@@6 bx0@@1 bx1@@1) bx@@45)) (U_2_bool (MapType0Select (Reads2 t0@@29 t1@@5 t2@@1 heap@@6 (Handle2 h@@29 r@@13 rd@@4) bx0@@1 bx1@@1) bx@@45)))))
 :qid |fastexpb.2139:15|
 :skolemid |383|
 :pattern ( (MapType0Select (Reads2 t0@@29 t1@@5 t2@@1 heap@@6 (Handle2 h@@29 r@@13 rd@@4) bx0@@1 bx1@@1) bx@@45))
)))
(assert (forall ((t0@@30 T@U) (t1@@6 T@U) (t2@@2 T@U) (h0@@6 T@U) (h1@@6 T@U) (f@@17 T@U) (bx0@@2 T@U) (bx1@@2 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@30) TyType) (= (type t1@@6) TyType)) (= (type t2@@2) TyType)) (= (type h0@@6) (MapType1Type refType))) (= (type h1@@6) (MapType1Type refType))) (= (type f@@17) HandleTypeType)) (= (type bx0@@2) BoxType)) (= (type bx1@@2) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@6 h1@@6) ($IsGoodHeap h0@@6)) ($IsGoodHeap h1@@6)) ($IsBox bx0@@2 t0@@30)) ($IsBox bx1@@2 t1@@6)) ($Is f@@17 (Tclass._System.___hFunc2 t0@@30 t1@@6 t2@@2))) (forall ((o@@61 T@U) (fld@@5 T@U) ) (! (let ((a@@85 (FieldTypeInv0 (type fld@@5))))
 (=> (and (and (= (type o@@61) refType) (= (type fld@@5) (FieldType a@@85))) (and (not (= o@@61 null)) (U_2_bool (MapType0Select (Reads2 t0@@30 t1@@6 t2@@2 h0@@6 f@@17 bx0@@2 bx1@@2) ($Box o@@61))))) (= (MapType1Select h0@@6 o@@61 fld@@5) (MapType1Select h1@@6 o@@61 fld@@5))))
 :qid |fastexpb.2174:22|
 :skolemid |384|
 :no-pattern (type o@@61)
 :no-pattern (type fld@@5)
 :no-pattern (U_2_int o@@61)
 :no-pattern (U_2_bool o@@61)
 :no-pattern (U_2_int fld@@5)
 :no-pattern (U_2_bool fld@@5)
)))) (= (Reads2 t0@@30 t1@@6 t2@@2 h0@@6 f@@17 bx0@@2 bx1@@2) (Reads2 t0@@30 t1@@6 t2@@2 h1@@6 f@@17 bx0@@2 bx1@@2)))
 :qid |fastexpb.2164:15|
 :skolemid |385|
 :pattern ( ($HeapSucc h0@@6 h1@@6) (Reads2 t0@@30 t1@@6 t2@@2 h1@@6 f@@17 bx0@@2 bx1@@2))
)))
(assert (forall ((t0@@31 T@U) (t1@@7 T@U) (t2@@3 T@U) (h0@@7 T@U) (h1@@7 T@U) (f@@18 T@U) (bx0@@3 T@U) (bx1@@3 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@31) TyType) (= (type t1@@7) TyType)) (= (type t2@@3) TyType)) (= (type h0@@7) (MapType1Type refType))) (= (type h1@@7) (MapType1Type refType))) (= (type f@@18) HandleTypeType)) (= (type bx0@@3) BoxType)) (= (type bx1@@3) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@7 h1@@7) ($IsGoodHeap h0@@7)) ($IsGoodHeap h1@@7)) ($IsBox bx0@@3 t0@@31)) ($IsBox bx1@@3 t1@@7)) ($Is f@@18 (Tclass._System.___hFunc2 t0@@31 t1@@7 t2@@3))) (forall ((o@@62 T@U) (fld@@6 T@U) ) (! (let ((a@@86 (FieldTypeInv0 (type fld@@6))))
 (=> (and (and (= (type o@@62) refType) (= (type fld@@6) (FieldType a@@86))) (and (not (= o@@62 null)) (U_2_bool (MapType0Select (Reads2 t0@@31 t1@@7 t2@@3 h1@@7 f@@18 bx0@@3 bx1@@3) ($Box o@@62))))) (= (MapType1Select h0@@7 o@@62 fld@@6) (MapType1Select h1@@7 o@@62 fld@@6))))
 :qid |fastexpb.2190:22|
 :skolemid |386|
 :no-pattern (type o@@62)
 :no-pattern (type fld@@6)
 :no-pattern (U_2_int o@@62)
 :no-pattern (U_2_bool o@@62)
 :no-pattern (U_2_int fld@@6)
 :no-pattern (U_2_bool fld@@6)
)))) (= (Reads2 t0@@31 t1@@7 t2@@3 h0@@7 f@@18 bx0@@3 bx1@@3) (Reads2 t0@@31 t1@@7 t2@@3 h1@@7 f@@18 bx0@@3 bx1@@3)))
 :qid |fastexpb.2180:15|
 :skolemid |387|
 :pattern ( ($HeapSucc h0@@7 h1@@7) (Reads2 t0@@31 t1@@7 t2@@3 h1@@7 f@@18 bx0@@3 bx1@@3))
)))
(assert (forall ((t0@@32 T@U) (t1@@8 T@U) (t2@@4 T@U) (h0@@8 T@U) (h1@@8 T@U) (f@@19 T@U) (bx0@@4 T@U) (bx1@@4 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@32) TyType) (= (type t1@@8) TyType)) (= (type t2@@4) TyType)) (= (type h0@@8) (MapType1Type refType))) (= (type h1@@8) (MapType1Type refType))) (= (type f@@19) HandleTypeType)) (= (type bx0@@4) BoxType)) (= (type bx1@@4) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@8 h1@@8) ($IsGoodHeap h0@@8)) ($IsGoodHeap h1@@8)) ($IsBox bx0@@4 t0@@32)) ($IsBox bx1@@4 t1@@8)) ($Is f@@19 (Tclass._System.___hFunc2 t0@@32 t1@@8 t2@@4))) (forall ((o@@63 T@U) (fld@@7 T@U) ) (! (let ((a@@87 (FieldTypeInv0 (type fld@@7))))
 (=> (and (and (= (type o@@63) refType) (= (type fld@@7) (FieldType a@@87))) (and (not (= o@@63 null)) (U_2_bool (MapType0Select (Reads2 t0@@32 t1@@8 t2@@4 h0@@8 f@@19 bx0@@4 bx1@@4) ($Box o@@63))))) (= (MapType1Select h0@@8 o@@63 fld@@7) (MapType1Select h1@@8 o@@63 fld@@7))))
 :qid |fastexpb.2206:22|
 :skolemid |388|
 :no-pattern (type o@@63)
 :no-pattern (type fld@@7)
 :no-pattern (U_2_int o@@63)
 :no-pattern (U_2_bool o@@63)
 :no-pattern (U_2_int fld@@7)
 :no-pattern (U_2_bool fld@@7)
)))) (and (=> (Requires2 t0@@32 t1@@8 t2@@4 h0@@8 f@@19 bx0@@4 bx1@@4) (Requires2 t0@@32 t1@@8 t2@@4 h1@@8 f@@19 bx0@@4 bx1@@4)) (=> (Requires2 t0@@32 t1@@8 t2@@4 h1@@8 f@@19 bx0@@4 bx1@@4) (Requires2 t0@@32 t1@@8 t2@@4 h0@@8 f@@19 bx0@@4 bx1@@4))))
 :qid |fastexpb.2196:15|
 :skolemid |389|
 :pattern ( ($HeapSucc h0@@8 h1@@8) (Requires2 t0@@32 t1@@8 t2@@4 h1@@8 f@@19 bx0@@4 bx1@@4))
)))
(assert (forall ((t0@@33 T@U) (t1@@9 T@U) (t2@@5 T@U) (h0@@9 T@U) (h1@@9 T@U) (f@@20 T@U) (bx0@@5 T@U) (bx1@@5 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@33) TyType) (= (type t1@@9) TyType)) (= (type t2@@5) TyType)) (= (type h0@@9) (MapType1Type refType))) (= (type h1@@9) (MapType1Type refType))) (= (type f@@20) HandleTypeType)) (= (type bx0@@5) BoxType)) (= (type bx1@@5) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@9 h1@@9) ($IsGoodHeap h0@@9)) ($IsGoodHeap h1@@9)) ($IsBox bx0@@5 t0@@33)) ($IsBox bx1@@5 t1@@9)) ($Is f@@20 (Tclass._System.___hFunc2 t0@@33 t1@@9 t2@@5))) (forall ((o@@64 T@U) (fld@@8 T@U) ) (! (let ((a@@88 (FieldTypeInv0 (type fld@@8))))
 (=> (and (and (= (type o@@64) refType) (= (type fld@@8) (FieldType a@@88))) (and (not (= o@@64 null)) (U_2_bool (MapType0Select (Reads2 t0@@33 t1@@9 t2@@5 h1@@9 f@@20 bx0@@5 bx1@@5) ($Box o@@64))))) (= (MapType1Select h0@@9 o@@64 fld@@8) (MapType1Select h1@@9 o@@64 fld@@8))))
 :qid |fastexpb.2222:22|
 :skolemid |390|
 :no-pattern (type o@@64)
 :no-pattern (type fld@@8)
 :no-pattern (U_2_int o@@64)
 :no-pattern (U_2_bool o@@64)
 :no-pattern (U_2_int fld@@8)
 :no-pattern (U_2_bool fld@@8)
)))) (and (=> (Requires2 t0@@33 t1@@9 t2@@5 h0@@9 f@@20 bx0@@5 bx1@@5) (Requires2 t0@@33 t1@@9 t2@@5 h1@@9 f@@20 bx0@@5 bx1@@5)) (=> (Requires2 t0@@33 t1@@9 t2@@5 h1@@9 f@@20 bx0@@5 bx1@@5) (Requires2 t0@@33 t1@@9 t2@@5 h0@@9 f@@20 bx0@@5 bx1@@5))))
 :qid |fastexpb.2212:15|
 :skolemid |391|
 :pattern ( ($HeapSucc h0@@9 h1@@9) (Requires2 t0@@33 t1@@9 t2@@5 h1@@9 f@@20 bx0@@5 bx1@@5))
)))
(assert (forall ((t0@@34 T@U) (t1@@10 T@U) (t2@@6 T@U) (h0@@10 T@U) (h1@@10 T@U) (f@@21 T@U) (bx0@@6 T@U) (bx1@@6 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@34) TyType) (= (type t1@@10) TyType)) (= (type t2@@6) TyType)) (= (type h0@@10) (MapType1Type refType))) (= (type h1@@10) (MapType1Type refType))) (= (type f@@21) HandleTypeType)) (= (type bx0@@6) BoxType)) (= (type bx1@@6) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@10 h1@@10) ($IsGoodHeap h0@@10)) ($IsGoodHeap h1@@10)) ($IsBox bx0@@6 t0@@34)) ($IsBox bx1@@6 t1@@10)) ($Is f@@21 (Tclass._System.___hFunc2 t0@@34 t1@@10 t2@@6))) (forall ((o@@65 T@U) (fld@@9 T@U) ) (! (let ((a@@89 (FieldTypeInv0 (type fld@@9))))
 (=> (and (and (= (type o@@65) refType) (= (type fld@@9) (FieldType a@@89))) (and (not (= o@@65 null)) (U_2_bool (MapType0Select (Reads2 t0@@34 t1@@10 t2@@6 h0@@10 f@@21 bx0@@6 bx1@@6) ($Box o@@65))))) (= (MapType1Select h0@@10 o@@65 fld@@9) (MapType1Select h1@@10 o@@65 fld@@9))))
 :qid |fastexpb.2238:22|
 :skolemid |392|
 :no-pattern (type o@@65)
 :no-pattern (type fld@@9)
 :no-pattern (U_2_int o@@65)
 :no-pattern (U_2_bool o@@65)
 :no-pattern (U_2_int fld@@9)
 :no-pattern (U_2_bool fld@@9)
)))) (= (Apply2 t0@@34 t1@@10 t2@@6 h0@@10 f@@21 bx0@@6 bx1@@6) (Apply2 t0@@34 t1@@10 t2@@6 h1@@10 f@@21 bx0@@6 bx1@@6)))
 :qid |fastexpb.2228:15|
 :skolemid |393|
 :pattern ( ($HeapSucc h0@@10 h1@@10) (Apply2 t0@@34 t1@@10 t2@@6 h1@@10 f@@21 bx0@@6 bx1@@6))
)))
(assert (forall ((t0@@35 T@U) (t1@@11 T@U) (t2@@7 T@U) (h0@@11 T@U) (h1@@11 T@U) (f@@22 T@U) (bx0@@7 T@U) (bx1@@7 T@U) ) (!  (=> (and (and (and (and (and (and (and (and (= (type t0@@35) TyType) (= (type t1@@11) TyType)) (= (type t2@@7) TyType)) (= (type h0@@11) (MapType1Type refType))) (= (type h1@@11) (MapType1Type refType))) (= (type f@@22) HandleTypeType)) (= (type bx0@@7) BoxType)) (= (type bx1@@7) BoxType)) (and (and (and (and (and (and ($HeapSucc h0@@11 h1@@11) ($IsGoodHeap h0@@11)) ($IsGoodHeap h1@@11)) ($IsBox bx0@@7 t0@@35)) ($IsBox bx1@@7 t1@@11)) ($Is f@@22 (Tclass._System.___hFunc2 t0@@35 t1@@11 t2@@7))) (forall ((o@@66 T@U) (fld@@10 T@U) ) (! (let ((a@@90 (FieldTypeInv0 (type fld@@10))))
 (=> (and (and (= (type o@@66) refType) (= (type fld@@10) (FieldType a@@90))) (and (not (= o@@66 null)) (U_2_bool (MapType0Select (Reads2 t0@@35 t1@@11 t2@@7 h1@@11 f@@22 bx0@@7 bx1@@7) ($Box o@@66))))) (= (MapType1Select h0@@11 o@@66 fld@@10) (MapType1Select h1@@11 o@@66 fld@@10))))
 :qid |fastexpb.2254:22|
 :skolemid |394|
 :no-pattern (type o@@66)
 :no-pattern (type fld@@10)
 :no-pattern (U_2_int o@@66)
 :no-pattern (U_2_bool o@@66)
 :no-pattern (U_2_int fld@@10)
 :no-pattern (U_2_bool fld@@10)
)))) (= (Apply2 t0@@35 t1@@11 t2@@7 h0@@11 f@@22 bx0@@7 bx1@@7) (Apply2 t0@@35 t1@@11 t2@@7 h1@@11 f@@22 bx0@@7 bx1@@7)))
 :qid |fastexpb.2244:15|
 :skolemid |395|
 :pattern ( ($HeapSucc h0@@11 h1@@11) (Apply2 t0@@35 t1@@11 t2@@7 h1@@11 f@@22 bx0@@7 bx1@@7))
)))
(assert (forall ((t0@@36 T@U) (t1@@12 T@U) (t2@@8 T@U) (heap@@7 T@U) (f@@23 T@U) (bx0@@8 T@U) (bx1@@8 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@36) TyType) (= (type t1@@12) TyType)) (= (type t2@@8) TyType)) (= (type heap@@7) (MapType1Type refType))) (= (type f@@23) HandleTypeType)) (= (type bx0@@8) BoxType)) (= (type bx1@@8) BoxType)) (and (and (and ($IsGoodHeap heap@@7) ($IsBox bx0@@8 t0@@36)) ($IsBox bx1@@8 t1@@12)) ($Is f@@23 (Tclass._System.___hFunc2 t0@@36 t1@@12 t2@@8)))) (and (=> (|Set#Equal| (Reads2 t0@@36 t1@@12 t2@@8 $OneHeap f@@23 bx0@@8 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@36 t1@@12 t2@@8 heap@@7 f@@23 bx0@@8 bx1@@8) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads2 t0@@36 t1@@12 t2@@8 heap@@7 f@@23 bx0@@8 bx1@@8) (|Set#Empty| BoxType)) (|Set#Equal| (Reads2 t0@@36 t1@@12 t2@@8 $OneHeap f@@23 bx0@@8 bx1@@8) (|Set#Empty| BoxType)))))
 :qid |fastexpb.2260:15|
 :skolemid |396|
 :pattern ( (Reads2 t0@@36 t1@@12 t2@@8 $OneHeap f@@23 bx0@@8 bx1@@8) ($IsGoodHeap heap@@7))
 :pattern ( (Reads2 t0@@36 t1@@12 t2@@8 heap@@7 f@@23 bx0@@8 bx1@@8))
)))
(assert (forall ((t0@@37 T@U) (t1@@13 T@U) (t2@@9 T@U) (heap@@8 T@U) (f@@24 T@U) (bx0@@9 T@U) (bx1@@9 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@37) TyType) (= (type t1@@13) TyType)) (= (type t2@@9) TyType)) (= (type heap@@8) (MapType1Type refType))) (= (type f@@24) HandleTypeType)) (= (type bx0@@9) BoxType)) (= (type bx1@@9) BoxType)) (and (and (and (and ($IsGoodHeap heap@@8) ($IsBox bx0@@9 t0@@37)) ($IsBox bx1@@9 t1@@13)) ($Is f@@24 (Tclass._System.___hFunc2 t0@@37 t1@@13 t2@@9))) (|Set#Equal| (Reads2 t0@@37 t1@@13 t2@@9 $OneHeap f@@24 bx0@@9 bx1@@9) (|Set#Empty| BoxType)))) (and (=> (Requires2 t0@@37 t1@@13 t2@@9 $OneHeap f@@24 bx0@@9 bx1@@9) (Requires2 t0@@37 t1@@13 t2@@9 heap@@8 f@@24 bx0@@9 bx1@@9)) (=> (Requires2 t0@@37 t1@@13 t2@@9 heap@@8 f@@24 bx0@@9 bx1@@9) (Requires2 t0@@37 t1@@13 t2@@9 $OneHeap f@@24 bx0@@9 bx1@@9))))
 :qid |fastexpb.2272:15|
 :skolemid |397|
 :pattern ( (Requires2 t0@@37 t1@@13 t2@@9 $OneHeap f@@24 bx0@@9 bx1@@9) ($IsGoodHeap heap@@8))
 :pattern ( (Requires2 t0@@37 t1@@13 t2@@9 heap@@8 f@@24 bx0@@9 bx1@@9))
)))
(assert (forall ((f@@25 T@U) (t0@@38 T@U) (t1@@14 T@U) (t2@@10 T@U) ) (!  (=> (and (and (and (= (type f@@25) HandleTypeType) (= (type t0@@38) TyType)) (= (type t1@@14) TyType)) (= (type t2@@10) TyType)) (and (=> ($Is f@@25 (Tclass._System.___hFunc2 t0@@38 t1@@14 t2@@10)) (forall ((h@@30 T@U) (bx0@@10 T@U) (bx1@@10 T@U) ) (!  (=> (and (and (= (type h@@30) (MapType1Type refType)) (= (type bx0@@10) BoxType)) (= (type bx1@@10) BoxType)) (=> (and (and (and ($IsGoodHeap h@@30) ($IsBox bx0@@10 t0@@38)) ($IsBox bx1@@10 t1@@14)) (Requires2 t0@@38 t1@@14 t2@@10 h@@30 f@@25 bx0@@10 bx1@@10)) ($IsBox (Apply2 t0@@38 t1@@14 t2@@10 h@@30 f@@25 bx0@@10 bx1@@10) t2@@10)))
 :qid |fastexpb.2287:19|
 :skolemid |398|
 :pattern ( (Apply2 t0@@38 t1@@14 t2@@10 h@@30 f@@25 bx0@@10 bx1@@10))
))) (=> (forall ((h@@31 T@U) (bx0@@11 T@U) (bx1@@11 T@U) ) (!  (=> (and (and (= (type h@@31) (MapType1Type refType)) (= (type bx0@@11) BoxType)) (= (type bx1@@11) BoxType)) (=> (and (and (and ($IsGoodHeap h@@31) ($IsBox bx0@@11 t0@@38)) ($IsBox bx1@@11 t1@@14)) (Requires2 t0@@38 t1@@14 t2@@10 h@@31 f@@25 bx0@@11 bx1@@11)) ($IsBox (Apply2 t0@@38 t1@@14 t2@@10 h@@31 f@@25 bx0@@11 bx1@@11) t2@@10)))
 :qid |fastexpb.2287:19|
 :skolemid |398|
 :pattern ( (Apply2 t0@@38 t1@@14 t2@@10 h@@31 f@@25 bx0@@11 bx1@@11))
)) ($Is f@@25 (Tclass._System.___hFunc2 t0@@38 t1@@14 t2@@10)))))
 :qid |fastexpb.2284:15|
 :skolemid |399|
 :pattern ( ($Is f@@25 (Tclass._System.___hFunc2 t0@@38 t1@@14 t2@@10)))
)))
(assert (forall ((f@@26 T@U) (t0@@39 T@U) (t1@@15 T@U) (t2@@11 T@U) (u0@@0 T@U) (u1 T@U) (u2 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type f@@26) HandleTypeType) (= (type t0@@39) TyType)) (= (type t1@@15) TyType)) (= (type t2@@11) TyType)) (= (type u0@@0) TyType)) (= (type u1) TyType)) (= (type u2) TyType)) (and (and (and ($Is f@@26 (Tclass._System.___hFunc2 t0@@39 t1@@15 t2@@11)) (forall ((bx@@46 T@U) ) (!  (=> (and (= (type bx@@46) BoxType) ($IsBox bx@@46 u0@@0)) ($IsBox bx@@46 t0@@39))
 :qid |fastexpb.2299:19|
 :skolemid |400|
 :pattern ( ($IsBox bx@@46 u0@@0))
 :pattern ( ($IsBox bx@@46 t0@@39))
))) (forall ((bx@@47 T@U) ) (!  (=> (and (= (type bx@@47) BoxType) ($IsBox bx@@47 u1)) ($IsBox bx@@47 t1@@15))
 :qid |fastexpb.2302:19|
 :skolemid |401|
 :pattern ( ($IsBox bx@@47 u1))
 :pattern ( ($IsBox bx@@47 t1@@15))
))) (forall ((bx@@48 T@U) ) (!  (=> (and (= (type bx@@48) BoxType) ($IsBox bx@@48 t2@@11)) ($IsBox bx@@48 u2))
 :qid |fastexpb.2305:19|
 :skolemid |402|
 :pattern ( ($IsBox bx@@48 t2@@11))
 :pattern ( ($IsBox bx@@48 u2))
)))) ($Is f@@26 (Tclass._System.___hFunc2 u0@@0 u1 u2)))
 :qid |fastexpb.2296:15|
 :skolemid |403|
 :pattern ( ($Is f@@26 (Tclass._System.___hFunc2 t0@@39 t1@@15 t2@@11)) ($Is f@@26 (Tclass._System.___hFunc2 u0@@0 u1 u2)))
)))
(assert (forall ((f@@27 T@U) (t0@@40 T@U) (t1@@16 T@U) (t2@@12 T@U) (h@@32 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@27) HandleTypeType) (= (type t0@@40) TyType)) (= (type t1@@16) TyType)) (= (type t2@@12) TyType)) (= (type h@@32) (MapType1Type refType))) ($IsGoodHeap h@@32)) (and (=> ($IsAlloc f@@27 (Tclass._System.___hFunc2 t0@@40 t1@@16 t2@@12) h@@32) (forall ((bx0@@12 T@U) (bx1@@12 T@U) ) (!  (=> (and (= (type bx0@@12) BoxType) (= (type bx1@@12) BoxType)) (=> (and (and (and (and ($IsBox bx0@@12 t0@@40) ($IsAllocBox bx0@@12 t0@@40 h@@32)) ($IsBox bx1@@12 t1@@16)) ($IsAllocBox bx1@@12 t1@@16 h@@32)) (Requires2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@12 bx1@@12)) (forall ((r@@14 T@U) ) (!  (=> (= (type r@@14) refType) (=> (and (not (= r@@14 null)) (U_2_bool (MapType0Select (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@12 bx1@@12) ($Box r@@14)))) (U_2_bool (MapType1Select h@@32 r@@14 alloc))))
 :qid |fastexpb.2322:24|
 :skolemid |404|
 :pattern ( (MapType0Select (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@12 bx1@@12) ($Box r@@14)))
))))
 :qid |fastexpb.2314:21|
 :skolemid |405|
 :pattern ( (Apply2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@12 bx1@@12))
 :pattern ( (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@12 bx1@@12))
))) (=> (forall ((bx0@@13 T@U) (bx1@@13 T@U) ) (!  (=> (and (= (type bx0@@13) BoxType) (= (type bx1@@13) BoxType)) (=> (and (and (and (and ($IsBox bx0@@13 t0@@40) ($IsAllocBox bx0@@13 t0@@40 h@@32)) ($IsBox bx1@@13 t1@@16)) ($IsAllocBox bx1@@13 t1@@16 h@@32)) (Requires2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@13 bx1@@13)) (forall ((r@@15 T@U) ) (!  (=> (= (type r@@15) refType) (=> (and (not (= r@@15 null)) (U_2_bool (MapType0Select (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@13 bx1@@13) ($Box r@@15)))) (U_2_bool (MapType1Select h@@32 r@@15 alloc))))
 :qid |fastexpb.2322:24|
 :skolemid |404|
 :pattern ( (MapType0Select (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@13 bx1@@13) ($Box r@@15)))
))))
 :qid |fastexpb.2314:21|
 :skolemid |405|
 :pattern ( (Apply2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@13 bx1@@13))
 :pattern ( (Reads2 t0@@40 t1@@16 t2@@12 h@@32 f@@27 bx0@@13 bx1@@13))
)) ($IsAlloc f@@27 (Tclass._System.___hFunc2 t0@@40 t1@@16 t2@@12) h@@32))))
 :qid |fastexpb.2310:15|
 :skolemid |406|
 :pattern ( ($IsAlloc f@@27 (Tclass._System.___hFunc2 t0@@40 t1@@16 t2@@12) h@@32))
)))
(assert (forall ((f@@28 T@U) (t0@@41 T@U) (t1@@17 T@U) (t2@@13 T@U) (h@@33 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@28) HandleTypeType) (= (type t0@@41) TyType)) (= (type t1@@17) TyType)) (= (type t2@@13) TyType)) (= (type h@@33) (MapType1Type refType))) (and ($IsGoodHeap h@@33) ($IsAlloc f@@28 (Tclass._System.___hFunc2 t0@@41 t1@@17 t2@@13) h@@33))) (forall ((bx0@@14 T@U) (bx1@@14 T@U) ) (!  (=> (and (= (type bx0@@14) BoxType) (= (type bx1@@14) BoxType)) (=> (and (and ($IsAllocBox bx0@@14 t0@@41 h@@33) ($IsAllocBox bx1@@14 t1@@17 h@@33)) (Requires2 t0@@41 t1@@17 t2@@13 h@@33 f@@28 bx0@@14 bx1@@14)) ($IsAllocBox (Apply2 t0@@41 t1@@17 t2@@13 h@@33 f@@28 bx0@@14 bx1@@14) t2@@13 h@@33)))
 :qid |fastexpb.2329:18|
 :skolemid |407|
 :pattern ( (Apply2 t0@@41 t1@@17 t2@@13 h@@33 f@@28 bx0@@14 bx1@@14))
)))
 :qid |fastexpb.2326:15|
 :skolemid |408|
 :pattern ( ($IsAlloc f@@28 (Tclass._System.___hFunc2 t0@@41 t1@@17 t2@@13) h@@33))
)))
(assert (forall ((arg0@@131 T@U) (arg1@@59 T@U) (arg2@@21 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2 arg0@@131 arg1@@59 arg2@@21)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2|
 :pattern ( (Tclass._System.___hPartialFunc2 arg0@@131 arg1@@59 arg2@@21))
)))
(assert (forall ((|#$T0@@4| T@U) (|#$T1@@4| T@U) (|#$R@@17| T@U) ) (!  (=> (and (and (= (type |#$T0@@4|) TyType) (= (type |#$T1@@4|) TyType)) (= (type |#$R@@17|) TyType)) (= (Tag (Tclass._System.___hPartialFunc2 |#$T0@@4| |#$T1@@4| |#$R@@17|)) Tagclass._System.___hPartialFunc2))
 :qid |fastexpb.2339:15|
 :skolemid |409|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@4| |#$T1@@4| |#$R@@17|))
)))
(assert (forall ((arg0@@132 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_0 arg0@@132)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_0|
 :pattern ( (Tclass._System.___hPartialFunc2_0 arg0@@132))
)))
(assert (forall ((|#$T0@@5| T@U) (|#$T1@@5| T@U) (|#$R@@18| T@U) ) (!  (=> (and (and (= (type |#$T0@@5|) TyType) (= (type |#$T1@@5|) TyType)) (= (type |#$R@@18|) TyType)) (= (Tclass._System.___hPartialFunc2_0 (Tclass._System.___hPartialFunc2 |#$T0@@5| |#$T1@@5| |#$R@@18|)) |#$T0@@5|))
 :qid |fastexpb.2347:15|
 :skolemid |410|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@5| |#$T1@@5| |#$R@@18|))
)))
(assert (forall ((arg0@@133 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_1 arg0@@133)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_1|
 :pattern ( (Tclass._System.___hPartialFunc2_1 arg0@@133))
)))
(assert (forall ((|#$T0@@6| T@U) (|#$T1@@6| T@U) (|#$R@@19| T@U) ) (!  (=> (and (and (= (type |#$T0@@6|) TyType) (= (type |#$T1@@6|) TyType)) (= (type |#$R@@19|) TyType)) (= (Tclass._System.___hPartialFunc2_1 (Tclass._System.___hPartialFunc2 |#$T0@@6| |#$T1@@6| |#$R@@19|)) |#$T1@@6|))
 :qid |fastexpb.2355:15|
 :skolemid |411|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@6| |#$T1@@6| |#$R@@19|))
)))
(assert (forall ((arg0@@134 T@U) ) (! (= (type (Tclass._System.___hPartialFunc2_2 arg0@@134)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc2_2|
 :pattern ( (Tclass._System.___hPartialFunc2_2 arg0@@134))
)))
(assert (forall ((|#$T0@@7| T@U) (|#$T1@@7| T@U) (|#$R@@20| T@U) ) (!  (=> (and (and (= (type |#$T0@@7|) TyType) (= (type |#$T1@@7|) TyType)) (= (type |#$R@@20|) TyType)) (= (Tclass._System.___hPartialFunc2_2 (Tclass._System.___hPartialFunc2 |#$T0@@7| |#$T1@@7| |#$R@@20|)) |#$R@@20|))
 :qid |fastexpb.2363:15|
 :skolemid |412|
 :pattern ( (Tclass._System.___hPartialFunc2 |#$T0@@7| |#$T1@@7| |#$R@@20|))
)))
(assert (forall ((|#$T0@@8| T@U) (|#$T1@@8| T@U) (|#$R@@21| T@U) (bx@@49 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@8|) TyType) (= (type |#$T1@@8|) TyType)) (= (type |#$R@@21|) TyType)) (= (type bx@@49) BoxType)) ($IsBox bx@@49 (Tclass._System.___hPartialFunc2 |#$T0@@8| |#$T1@@8| |#$R@@21|))) (and (= ($Box ($Unbox HandleTypeType bx@@49)) bx@@49) ($Is ($Unbox HandleTypeType bx@@49) (Tclass._System.___hPartialFunc2 |#$T0@@8| |#$T1@@8| |#$R@@21|))))
 :qid |fastexpb.2371:15|
 :skolemid |413|
 :pattern ( ($IsBox bx@@49 (Tclass._System.___hPartialFunc2 |#$T0@@8| |#$T1@@8| |#$R@@21|)))
)))
(assert (forall ((|#$T0@@9| T@U) (|#$T1@@9| T@U) (|#$R@@22| T@U) (|f#0@@3| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@9|) TyType) (= (type |#$T1@@9|) TyType)) (= (type |#$R@@22|) TyType)) (= (type |f#0@@3|) HandleTypeType)) (and (=> ($Is |f#0@@3| (Tclass._System.___hPartialFunc2 |#$T0@@9| |#$T1@@9| |#$R@@22|)) (and ($Is |f#0@@3| (Tclass._System.___hFunc2 |#$T0@@9| |#$T1@@9| |#$R@@22|)) (forall ((|x0#0| T@U) (|x1#0| T@U) ) (!  (=> (and (and (= (type |x0#0|) BoxType) (= (type |x1#0|) BoxType)) (and ($IsBox |x0#0| |#$T0@@9|) ($IsBox |x1#0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@9| |#$T1@@9| |#$R@@22| $OneHeap |f#0@@3| |x0#0| |x1#0|) (|Set#Empty| BoxType)))
 :qid |fastexpb.2382:19|
 :skolemid |414|
 :no-pattern (type |x0#0|)
 :no-pattern (type |x1#0|)
 :no-pattern (U_2_int |x0#0|)
 :no-pattern (U_2_bool |x0#0|)
 :no-pattern (U_2_int |x1#0|)
 :no-pattern (U_2_bool |x1#0|)
)))) (=> (and ($Is |f#0@@3| (Tclass._System.___hFunc2 |#$T0@@9| |#$T1@@9| |#$R@@22|)) (forall ((|x0#0@@0| T@U) (|x1#0@@0| T@U) ) (!  (=> (and (and (= (type |x0#0@@0|) BoxType) (= (type |x1#0@@0|) BoxType)) (and ($IsBox |x0#0@@0| |#$T0@@9|) ($IsBox |x1#0@@0| |#$T1@@9|))) (|Set#Equal| (Reads2 |#$T0@@9| |#$T1@@9| |#$R@@22| $OneHeap |f#0@@3| |x0#0@@0| |x1#0@@0|) (|Set#Empty| BoxType)))
 :qid |fastexpb.2382:19|
 :skolemid |414|
 :no-pattern (type |x0#0@@0|)
 :no-pattern (type |x1#0@@0|)
 :no-pattern (U_2_int |x0#0@@0|)
 :no-pattern (U_2_bool |x0#0@@0|)
 :no-pattern (U_2_int |x1#0@@0|)
 :no-pattern (U_2_bool |x1#0@@0|)
))) ($Is |f#0@@3| (Tclass._System.___hPartialFunc2 |#$T0@@9| |#$T1@@9| |#$R@@22|)))))
 :qid |fastexpb.2378:15|
 :skolemid |415|
 :pattern ( ($Is |f#0@@3| (Tclass._System.___hPartialFunc2 |#$T0@@9| |#$T1@@9| |#$R@@22|)))
)))
(assert (forall ((|#$T0@@10| T@U) (|#$T1@@10| T@U) (|#$R@@23| T@U) (|f#0@@4| T@U) ($h@@9 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@10|) TyType) (= (type |#$T1@@10|) TyType)) (= (type |#$R@@23|) TyType)) (= (type |f#0@@4|) HandleTypeType)) (= (type $h@@9) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc2 |#$T0@@10| |#$T1@@10| |#$R@@23|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hFunc2 |#$T0@@10| |#$T1@@10| |#$R@@23|) $h@@9)) (=> ($IsAlloc |f#0@@4| (Tclass._System.___hFunc2 |#$T0@@10| |#$T1@@10| |#$R@@23|) $h@@9) ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc2 |#$T0@@10| |#$T1@@10| |#$R@@23|) $h@@9))))
 :qid |fastexpb.2387:15|
 :skolemid |416|
 :pattern ( ($IsAlloc |f#0@@4| (Tclass._System.___hPartialFunc2 |#$T0@@10| |#$T1@@10| |#$R@@23|) $h@@9))
)))
(assert (forall ((arg0@@135 T@U) (arg1@@60 T@U) (arg2@@22 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2 arg0@@135 arg1@@60 arg2@@22)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2|
 :pattern ( (Tclass._System.___hTotalFunc2 arg0@@135 arg1@@60 arg2@@22))
)))
(assert (forall ((|#$T0@@11| T@U) (|#$T1@@11| T@U) (|#$R@@24| T@U) ) (!  (=> (and (and (= (type |#$T0@@11|) TyType) (= (type |#$T1@@11|) TyType)) (= (type |#$R@@24|) TyType)) (= (Tag (Tclass._System.___hTotalFunc2 |#$T0@@11| |#$T1@@11| |#$R@@24|)) Tagclass._System.___hTotalFunc2))
 :qid |fastexpb.2395:15|
 :skolemid |417|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@11| |#$T1@@11| |#$R@@24|))
)))
(assert (forall ((arg0@@136 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_0 arg0@@136)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_0|
 :pattern ( (Tclass._System.___hTotalFunc2_0 arg0@@136))
)))
(assert (forall ((|#$T0@@12| T@U) (|#$T1@@12| T@U) (|#$R@@25| T@U) ) (!  (=> (and (and (= (type |#$T0@@12|) TyType) (= (type |#$T1@@12|) TyType)) (= (type |#$R@@25|) TyType)) (= (Tclass._System.___hTotalFunc2_0 (Tclass._System.___hTotalFunc2 |#$T0@@12| |#$T1@@12| |#$R@@25|)) |#$T0@@12|))
 :qid |fastexpb.2403:15|
 :skolemid |418|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@12| |#$T1@@12| |#$R@@25|))
)))
(assert (forall ((arg0@@137 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_1 arg0@@137)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_1|
 :pattern ( (Tclass._System.___hTotalFunc2_1 arg0@@137))
)))
(assert (forall ((|#$T0@@13| T@U) (|#$T1@@13| T@U) (|#$R@@26| T@U) ) (!  (=> (and (and (= (type |#$T0@@13|) TyType) (= (type |#$T1@@13|) TyType)) (= (type |#$R@@26|) TyType)) (= (Tclass._System.___hTotalFunc2_1 (Tclass._System.___hTotalFunc2 |#$T0@@13| |#$T1@@13| |#$R@@26|)) |#$T1@@13|))
 :qid |fastexpb.2411:15|
 :skolemid |419|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@13| |#$T1@@13| |#$R@@26|))
)))
(assert (forall ((arg0@@138 T@U) ) (! (= (type (Tclass._System.___hTotalFunc2_2 arg0@@138)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc2_2|
 :pattern ( (Tclass._System.___hTotalFunc2_2 arg0@@138))
)))
(assert (forall ((|#$T0@@14| T@U) (|#$T1@@14| T@U) (|#$R@@27| T@U) ) (!  (=> (and (and (= (type |#$T0@@14|) TyType) (= (type |#$T1@@14|) TyType)) (= (type |#$R@@27|) TyType)) (= (Tclass._System.___hTotalFunc2_2 (Tclass._System.___hTotalFunc2 |#$T0@@14| |#$T1@@14| |#$R@@27|)) |#$R@@27|))
 :qid |fastexpb.2419:15|
 :skolemid |420|
 :pattern ( (Tclass._System.___hTotalFunc2 |#$T0@@14| |#$T1@@14| |#$R@@27|))
)))
(assert (forall ((|#$T0@@15| T@U) (|#$T1@@15| T@U) (|#$R@@28| T@U) (bx@@50 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@15|) TyType) (= (type |#$T1@@15|) TyType)) (= (type |#$R@@28|) TyType)) (= (type bx@@50) BoxType)) ($IsBox bx@@50 (Tclass._System.___hTotalFunc2 |#$T0@@15| |#$T1@@15| |#$R@@28|))) (and (= ($Box ($Unbox HandleTypeType bx@@50)) bx@@50) ($Is ($Unbox HandleTypeType bx@@50) (Tclass._System.___hTotalFunc2 |#$T0@@15| |#$T1@@15| |#$R@@28|))))
 :qid |fastexpb.2427:15|
 :skolemid |421|
 :pattern ( ($IsBox bx@@50 (Tclass._System.___hTotalFunc2 |#$T0@@15| |#$T1@@15| |#$R@@28|)))
)))
(assert (forall ((|#$T0@@16| T@U) (|#$T1@@16| T@U) (|#$R@@29| T@U) (|f#0@@5| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@16|) TyType) (= (type |#$T1@@16|) TyType)) (= (type |#$R@@29|) TyType)) (= (type |f#0@@5|) HandleTypeType)) (and (=> ($Is |f#0@@5| (Tclass._System.___hTotalFunc2 |#$T0@@16| |#$T1@@16| |#$R@@29|)) (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc2 |#$T0@@16| |#$T1@@16| |#$R@@29|)) (forall ((|x0#0@@1| T@U) (|x1#0@@1| T@U) ) (!  (=> (and (and (= (type |x0#0@@1|) BoxType) (= (type |x1#0@@1|) BoxType)) (and ($IsBox |x0#0@@1| |#$T0@@16|) ($IsBox |x1#0@@1| |#$T1@@16|))) (Requires2 |#$T0@@16| |#$T1@@16| |#$R@@29| $OneHeap |f#0@@5| |x0#0@@1| |x1#0@@1|))
 :qid |fastexpb.2438:19|
 :skolemid |422|
 :no-pattern (type |x0#0@@1|)
 :no-pattern (type |x1#0@@1|)
 :no-pattern (U_2_int |x0#0@@1|)
 :no-pattern (U_2_bool |x0#0@@1|)
 :no-pattern (U_2_int |x1#0@@1|)
 :no-pattern (U_2_bool |x1#0@@1|)
)))) (=> (and ($Is |f#0@@5| (Tclass._System.___hPartialFunc2 |#$T0@@16| |#$T1@@16| |#$R@@29|)) (forall ((|x0#0@@2| T@U) (|x1#0@@2| T@U) ) (!  (=> (and (and (= (type |x0#0@@2|) BoxType) (= (type |x1#0@@2|) BoxType)) (and ($IsBox |x0#0@@2| |#$T0@@16|) ($IsBox |x1#0@@2| |#$T1@@16|))) (Requires2 |#$T0@@16| |#$T1@@16| |#$R@@29| $OneHeap |f#0@@5| |x0#0@@2| |x1#0@@2|))
 :qid |fastexpb.2438:19|
 :skolemid |422|
 :no-pattern (type |x0#0@@2|)
 :no-pattern (type |x1#0@@2|)
 :no-pattern (U_2_int |x0#0@@2|)
 :no-pattern (U_2_bool |x0#0@@2|)
 :no-pattern (U_2_int |x1#0@@2|)
 :no-pattern (U_2_bool |x1#0@@2|)
))) ($Is |f#0@@5| (Tclass._System.___hTotalFunc2 |#$T0@@16| |#$T1@@16| |#$R@@29|)))))
 :qid |fastexpb.2434:15|
 :skolemid |423|
 :pattern ( ($Is |f#0@@5| (Tclass._System.___hTotalFunc2 |#$T0@@16| |#$T1@@16| |#$R@@29|)))
)))
(assert (forall ((|#$T0@@17| T@U) (|#$T1@@17| T@U) (|#$R@@30| T@U) (|f#0@@6| T@U) ($h@@10 T@U) ) (!  (=> (and (and (and (and (= (type |#$T0@@17|) TyType) (= (type |#$T1@@17|) TyType)) (= (type |#$R@@30|) TyType)) (= (type |f#0@@6|) HandleTypeType)) (= (type $h@@10) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc2 |#$T0@@17| |#$T1@@17| |#$R@@30|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc2 |#$T0@@17| |#$T1@@17| |#$R@@30|) $h@@10)) (=> ($IsAlloc |f#0@@6| (Tclass._System.___hPartialFunc2 |#$T0@@17| |#$T1@@17| |#$R@@30|) $h@@10) ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc2 |#$T0@@17| |#$T1@@17| |#$R@@30|) $h@@10))))
 :qid |fastexpb.2443:15|
 :skolemid |424|
 :pattern ( ($IsAlloc |f#0@@6| (Tclass._System.___hTotalFunc2 |#$T0@@17| |#$T1@@17| |#$R@@30|) $h@@10))
)))
(assert  (and (forall ((arg0@@139 T@U) (arg1@@61 T@U) ) (! (= (type (|#_System._tuple#2._#Make2| arg0@@139 arg1@@61)) DatatypeTypeType)
 :qid |funType:#_System._tuple#2._#Make2|
 :pattern ( (|#_System._tuple#2._#Make2| arg0@@139 arg1@@61))
)) (forall ((arg0@@140 T@U) ) (! (= (type (DatatypeCtorId arg0@@140)) DtCtorIdType)
 :qid |funType:DatatypeCtorId|
 :pattern ( (DatatypeCtorId arg0@@140))
))))
(assert (forall ((|a#0#0#0| T@U) (|a#0#1#0| T@U) ) (!  (=> (and (= (type |a#0#0#0|) BoxType) (= (type |a#0#1#0|) BoxType)) (= (DatatypeCtorId (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|)) |##_System._tuple#2._#Make2|))
 :qid |fastexpb.2456:15|
 :skolemid |425|
 :pattern ( (|#_System._tuple#2._#Make2| |a#0#0#0| |a#0#1#0|))
)))
(assert (forall ((d@@0 T@U) ) (!  (=> (= (type d@@0) DatatypeTypeType) (and (=> (_System.Tuple2.___hMake2_q d@@0) (= (DatatypeCtorId d@@0) |##_System._tuple#2._#Make2|)) (=> (= (DatatypeCtorId d@@0) |##_System._tuple#2._#Make2|) (_System.Tuple2.___hMake2_q d@@0))))
 :qid |fastexpb.2464:15|
 :skolemid |426|
 :pattern ( (_System.Tuple2.___hMake2_q d@@0))
)))
(assert (forall ((d@@1 T@U) ) (!  (=> (and (= (type d@@1) DatatypeTypeType) (_System.Tuple2.___hMake2_q d@@1)) (exists ((|a#1#0#0| T@U) (|a#1#1#0| T@U) ) (!  (and (and (= (type |a#1#0#0|) BoxType) (= (type |a#1#1#0|) BoxType)) (= d@@1 (|#_System._tuple#2._#Make2| |a#1#0#0| |a#1#1#0|)))
 :qid |fastexpb.2473:18|
 :skolemid |427|
 :no-pattern (type |a#1#0#0|)
 :no-pattern (type |a#1#1#0|)
 :no-pattern (U_2_int |a#1#0#0|)
 :no-pattern (U_2_bool |a#1#0#0|)
 :no-pattern (U_2_int |a#1#1#0|)
 :no-pattern (U_2_bool |a#1#1#0|)
)))
 :qid |fastexpb.2470:15|
 :skolemid |428|
 :pattern ( (_System.Tuple2.___hMake2_q d@@1))
)))
(assert (forall ((arg0@@141 T@U) (arg1@@62 T@U) ) (! (= (type (Tclass._System.Tuple2 arg0@@141 arg1@@62)) TyType)
 :qid |funType:Tclass._System.Tuple2|
 :pattern ( (Tclass._System.Tuple2 arg0@@141 arg1@@62))
)))
(assert (forall ((|#$T0@@18| T@U) (|#$T1@@18| T@U) ) (!  (=> (and (= (type |#$T0@@18|) TyType) (= (type |#$T1@@18|) TyType)) (= (Tag (Tclass._System.Tuple2 |#$T0@@18| |#$T1@@18|)) Tagclass._System.Tuple2))
 :qid |fastexpb.2479:15|
 :skolemid |429|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@18| |#$T1@@18|))
)))
(assert (forall ((arg0@@142 T@U) ) (! (= (type (Tclass._System.Tuple2_0 arg0@@142)) TyType)
 :qid |funType:Tclass._System.Tuple2_0|
 :pattern ( (Tclass._System.Tuple2_0 arg0@@142))
)))
(assert (forall ((|#$T0@@19| T@U) (|#$T1@@19| T@U) ) (!  (=> (and (= (type |#$T0@@19|) TyType) (= (type |#$T1@@19|) TyType)) (= (Tclass._System.Tuple2_0 (Tclass._System.Tuple2 |#$T0@@19| |#$T1@@19|)) |#$T0@@19|))
 :qid |fastexpb.2486:15|
 :skolemid |430|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@19| |#$T1@@19|))
)))
(assert (forall ((arg0@@143 T@U) ) (! (= (type (Tclass._System.Tuple2_1 arg0@@143)) TyType)
 :qid |funType:Tclass._System.Tuple2_1|
 :pattern ( (Tclass._System.Tuple2_1 arg0@@143))
)))
(assert (forall ((|#$T0@@20| T@U) (|#$T1@@20| T@U) ) (!  (=> (and (= (type |#$T0@@20|) TyType) (= (type |#$T1@@20|) TyType)) (= (Tclass._System.Tuple2_1 (Tclass._System.Tuple2 |#$T0@@20| |#$T1@@20|)) |#$T1@@20|))
 :qid |fastexpb.2493:15|
 :skolemid |431|
 :pattern ( (Tclass._System.Tuple2 |#$T0@@20| |#$T1@@20|))
)))
(assert (forall ((|#$T0@@21| T@U) (|#$T1@@21| T@U) (bx@@51 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@21|) TyType) (= (type |#$T1@@21|) TyType)) (= (type bx@@51) BoxType)) ($IsBox bx@@51 (Tclass._System.Tuple2 |#$T0@@21| |#$T1@@21|))) (and (= ($Box ($Unbox DatatypeTypeType bx@@51)) bx@@51) ($Is ($Unbox DatatypeTypeType bx@@51) (Tclass._System.Tuple2 |#$T0@@21| |#$T1@@21|))))
 :qid |fastexpb.2500:15|
 :skolemid |432|
 :pattern ( ($IsBox bx@@51 (Tclass._System.Tuple2 |#$T0@@21| |#$T1@@21|)))
)))
(assert (forall ((|#$T0@@22| T@U) (|#$T1@@22| T@U) (|a#2#0#0| T@U) (|a#2#1#0| T@U) ) (!  (=> (and (and (and (= (type |#$T0@@22|) TyType) (= (type |#$T1@@22|) TyType)) (= (type |a#2#0#0|) BoxType)) (= (type |a#2#1#0|) BoxType)) (and (=> ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@22| |#$T1@@22|)) (and ($IsBox |a#2#0#0| |#$T0@@22|) ($IsBox |a#2#1#0| |#$T1@@22|))) (=> (and ($IsBox |a#2#0#0| |#$T0@@22|) ($IsBox |a#2#1#0| |#$T1@@22|)) ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@22| |#$T1@@22|)))))
 :qid |fastexpb.2507:15|
 :skolemid |433|
 :pattern ( ($Is (|#_System._tuple#2._#Make2| |a#2#0#0| |a#2#1#0|) (Tclass._System.Tuple2 |#$T0@@22| |#$T1@@22|)))
)))
(assert (forall ((|#$T0@@23| T@U) (|#$T1@@23| T@U) (|a#3#0#0| T@U) (|a#3#1#0| T@U) ($h@@11 T@U) ) (!  (=> (and (and (and (and (and (= (type |#$T0@@23|) TyType) (= (type |#$T1@@23|) TyType)) (= (type |a#3#0#0|) BoxType)) (= (type |a#3#1#0|) BoxType)) (= (type $h@@11) (MapType1Type refType))) ($IsGoodHeap $h@@11)) (and (=> ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@23| |#$T1@@23|) $h@@11) (and ($IsAllocBox |a#3#0#0| |#$T0@@23| $h@@11) ($IsAllocBox |a#3#1#0| |#$T1@@23| $h@@11))) (=> (and ($IsAllocBox |a#3#0#0| |#$T0@@23| $h@@11) ($IsAllocBox |a#3#1#0| |#$T1@@23| $h@@11)) ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@23| |#$T1@@23|) $h@@11))))
 :qid |fastexpb.2513:15|
 :skolemid |434|
 :pattern ( ($IsAlloc (|#_System._tuple#2._#Make2| |a#3#0#0| |a#3#1#0|) (Tclass._System.Tuple2 |#$T0@@23| |#$T1@@23|) $h@@11))
)))
(assert (forall ((d@@2 T@U) (|#$T0@@24| T@U) ($h@@12 T@U) ) (!  (=> (and (and (and (= (type d@@2) DatatypeTypeType) (= (type |#$T0@@24|) TyType)) (= (type $h@@12) (MapType1Type refType))) (and (and ($IsGoodHeap $h@@12) (_System.Tuple2.___hMake2_q d@@2)) (exists ((|#$T1@@24| T@U) ) (!  (and (= (type |#$T1@@24|) TyType) ($IsAlloc d@@2 (Tclass._System.Tuple2 |#$T0@@24| |#$T1@@24|) $h@@12))
 :qid |fastexpb.2529:19|
 :skolemid |435|
 :pattern ( ($IsAlloc d@@2 (Tclass._System.Tuple2 |#$T0@@24| |#$T1@@24|) $h@@12))
)))) ($IsAllocBox (_System.Tuple2._0 d@@2) |#$T0@@24| $h@@12))
 :qid |fastexpb.2524:15|
 :skolemid |436|
 :pattern ( ($IsAllocBox (_System.Tuple2._0 d@@2) |#$T0@@24| $h@@12))
)))
(assert (forall ((d@@3 T@U) (|#$T1@@25| T@U) ($h@@13 T@U) ) (!  (=> (and (and (and (= (type d@@3) DatatypeTypeType) (= (type |#$T1@@25|) TyType)) (= (type $h@@13) (MapType1Type refType))) (and (and ($IsGoodHeap $h@@13) (_System.Tuple2.___hMake2_q d@@3)) (exists ((|#$T0@@25| T@U) ) (!  (and (= (type |#$T0@@25|) TyType) ($IsAlloc d@@3 (Tclass._System.Tuple2 |#$T0@@25| |#$T1@@25|) $h@@13))
 :qid |fastexpb.2540:19|
 :skolemid |437|
 :pattern ( ($IsAlloc d@@3 (Tclass._System.Tuple2 |#$T0@@25| |#$T1@@25|) $h@@13))
)))) ($IsAllocBox (_System.Tuple2._1 d@@3) |#$T1@@25| $h@@13))
 :qid |fastexpb.2535:15|
 :skolemid |438|
 :pattern ( ($IsAllocBox (_System.Tuple2._1 d@@3) |#$T1@@25| $h@@13))
)))
(assert (forall ((|a#4#0#0| T@U) (|a#4#1#0| T@U) ) (!  (=> (and (= (type |a#4#0#0|) BoxType) (= (type |a#4#1#0|) BoxType)) (= (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)) (Lit (|#_System._tuple#2._#Make2| |a#4#0#0| |a#4#1#0|))))
 :qid |fastexpb.2546:15|
 :skolemid |439|
 :pattern ( (|#_System._tuple#2._#Make2| (Lit |a#4#0#0|) (Lit |a#4#1#0|)))
)))
(assert (forall ((|a#5#0#0| T@U) (|a#5#1#0| T@U) ) (!  (=> (and (= (type |a#5#0#0|) BoxType) (= (type |a#5#1#0|) BoxType)) (= (_System.Tuple2._0 (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|)) |a#5#0#0|))
 :qid |fastexpb.2552:15|
 :skolemid |440|
 :pattern ( (|#_System._tuple#2._#Make2| |a#5#0#0| |a#5#1#0|))
)))
(assert (forall ((|a#6#0#0| T@U) (|a#6#1#0| T@U) ) (!  (=> (and (= (type |a#6#0#0|) BoxType) (= (type |a#6#1#0|) BoxType)) (< (BoxRank |a#6#0#0|) (DtRank (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))))
 :qid |fastexpb.2557:15|
 :skolemid |441|
 :pattern ( (|#_System._tuple#2._#Make2| |a#6#0#0| |a#6#1#0|))
)))
(assert (forall ((|a#7#0#0| T@U) (|a#7#1#0| T@U) ) (!  (=> (and (= (type |a#7#0#0|) BoxType) (= (type |a#7#1#0|) BoxType)) (= (_System.Tuple2._1 (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|)) |a#7#1#0|))
 :qid |fastexpb.2562:15|
 :skolemid |442|
 :pattern ( (|#_System._tuple#2._#Make2| |a#7#0#0| |a#7#1#0|))
)))
(assert (forall ((|a#8#0#0| T@U) (|a#8#1#0| T@U) ) (!  (=> (and (= (type |a#8#0#0|) BoxType) (= (type |a#8#1#0|) BoxType)) (< (BoxRank |a#8#1#0|) (DtRank (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))))
 :qid |fastexpb.2567:15|
 :skolemid |443|
 :pattern ( (|#_System._tuple#2._#Make2| |a#8#0#0| |a#8#1#0|))
)))
(assert (forall ((d@@4 T@U) ) (!  (=> (and (= (type d@@4) DatatypeTypeType) (|$IsA#_System.Tuple2| d@@4)) (_System.Tuple2.___hMake2_q d@@4))
 :qid |fastexpb.2575:15|
 :skolemid |444|
 :pattern ( (|$IsA#_System.Tuple2| d@@4))
)))
(assert (forall ((|#$T0@@26| T@U) (|#$T1@@26| T@U) (d@@5 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@26|) TyType) (= (type |#$T1@@26|) TyType)) (= (type d@@5) DatatypeTypeType)) ($Is d@@5 (Tclass._System.Tuple2 |#$T0@@26| |#$T1@@26|))) (_System.Tuple2.___hMake2_q d@@5))
 :qid |fastexpb.2580:15|
 :skolemid |445|
 :pattern ( (_System.Tuple2.___hMake2_q d@@5) ($Is d@@5 (Tclass._System.Tuple2 |#$T0@@26| |#$T1@@26|)))
)))
(assert (forall ((a@@91 T@U) (b@@58 T@U) ) (!  (=> (and (and (= (type a@@91) DatatypeTypeType) (= (type b@@58) DatatypeTypeType)) true) (and (=> (|_System.Tuple2#Equal| a@@91 b@@58) (and (= (_System.Tuple2._0 a@@91) (_System.Tuple2._0 b@@58)) (= (_System.Tuple2._1 a@@91) (_System.Tuple2._1 b@@58)))) (=> (and (= (_System.Tuple2._0 a@@91) (_System.Tuple2._0 b@@58)) (= (_System.Tuple2._1 a@@91) (_System.Tuple2._1 b@@58))) (|_System.Tuple2#Equal| a@@91 b@@58))))
 :qid |fastexpb.2588:15|
 :skolemid |446|
 :pattern ( (|_System.Tuple2#Equal| a@@91 b@@58))
)))
(assert (forall ((a@@92 T@U) (b@@59 T@U) ) (!  (=> (and (= (type a@@92) DatatypeTypeType) (= (type b@@59) DatatypeTypeType)) (and (=> (|_System.Tuple2#Equal| a@@92 b@@59) (= a@@92 b@@59)) (=> (= a@@92 b@@59) (|_System.Tuple2#Equal| a@@92 b@@59))))
 :qid |fastexpb.2596:15|
 :skolemid |447|
 :pattern ( (|_System.Tuple2#Equal| a@@92 b@@59))
)))
(assert (forall ((arg0@@144 T@U) (arg1@@63 T@U) ) (! (= (type (Tclass._System.___hFunc1 arg0@@144 arg1@@63)) TyType)
 :qid |funType:Tclass._System.___hFunc1|
 :pattern ( (Tclass._System.___hFunc1 arg0@@144 arg1@@63))
)))
(assert (forall ((|#$T0@@27| T@U) (|#$R@@31| T@U) ) (!  (=> (and (= (type |#$T0@@27|) TyType) (= (type |#$R@@31|) TyType)) (= (Tag (Tclass._System.___hFunc1 |#$T0@@27| |#$R@@31|)) Tagclass._System.___hFunc1))
 :qid |fastexpb.2603:15|
 :skolemid |448|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@27| |#$R@@31|))
)))
(assert (forall ((arg0@@145 T@U) ) (! (= (type (Tclass._System.___hFunc1_0 arg0@@145)) TyType)
 :qid |funType:Tclass._System.___hFunc1_0|
 :pattern ( (Tclass._System.___hFunc1_0 arg0@@145))
)))
(assert (forall ((|#$T0@@28| T@U) (|#$R@@32| T@U) ) (!  (=> (and (= (type |#$T0@@28|) TyType) (= (type |#$R@@32|) TyType)) (= (Tclass._System.___hFunc1_0 (Tclass._System.___hFunc1 |#$T0@@28| |#$R@@32|)) |#$T0@@28|))
 :qid |fastexpb.2610:15|
 :skolemid |449|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@28| |#$R@@32|))
)))
(assert (forall ((arg0@@146 T@U) ) (! (= (type (Tclass._System.___hFunc1_1 arg0@@146)) TyType)
 :qid |funType:Tclass._System.___hFunc1_1|
 :pattern ( (Tclass._System.___hFunc1_1 arg0@@146))
)))
(assert (forall ((|#$T0@@29| T@U) (|#$R@@33| T@U) ) (!  (=> (and (= (type |#$T0@@29|) TyType) (= (type |#$R@@33|) TyType)) (= (Tclass._System.___hFunc1_1 (Tclass._System.___hFunc1 |#$T0@@29| |#$R@@33|)) |#$R@@33|))
 :qid |fastexpb.2617:15|
 :skolemid |450|
 :pattern ( (Tclass._System.___hFunc1 |#$T0@@29| |#$R@@33|))
)))
(assert (forall ((|#$T0@@30| T@U) (|#$R@@34| T@U) (bx@@52 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@30|) TyType) (= (type |#$R@@34|) TyType)) (= (type bx@@52) BoxType)) ($IsBox bx@@52 (Tclass._System.___hFunc1 |#$T0@@30| |#$R@@34|))) (and (= ($Box ($Unbox HandleTypeType bx@@52)) bx@@52) ($Is ($Unbox HandleTypeType bx@@52) (Tclass._System.___hFunc1 |#$T0@@30| |#$R@@34|))))
 :qid |fastexpb.2624:15|
 :skolemid |451|
 :pattern ( ($IsBox bx@@52 (Tclass._System.___hFunc1 |#$T0@@30| |#$R@@34|)))
)))
(assert  (and (and (and (and (and (and (and (and (and (forall ((arg0@@147 T@T) (arg1@@64 T@T) (arg2@@23 T@T) ) (! (= (Ctor (MapType3Type arg0@@147 arg1@@64 arg2@@23)) 22)
 :qid |ctor:MapType3Type|
)) (forall ((arg0@@148 T@T) (arg1@@65 T@T) (arg2@@24 T@T) ) (! (= (MapType3TypeInv0 (MapType3Type arg0@@148 arg1@@65 arg2@@24)) arg0@@148)
 :qid |typeInv:MapType3TypeInv0|
 :pattern ( (MapType3Type arg0@@148 arg1@@65 arg2@@24))
))) (forall ((arg0@@149 T@T) (arg1@@66 T@T) (arg2@@25 T@T) ) (! (= (MapType3TypeInv1 (MapType3Type arg0@@149 arg1@@66 arg2@@25)) arg1@@66)
 :qid |typeInv:MapType3TypeInv1|
 :pattern ( (MapType3Type arg0@@149 arg1@@66 arg2@@25))
))) (forall ((arg0@@150 T@T) (arg1@@67 T@T) (arg2@@26 T@T) ) (! (= (MapType3TypeInv2 (MapType3Type arg0@@150 arg1@@67 arg2@@26)) arg2@@26)
 :qid |typeInv:MapType3TypeInv2|
 :pattern ( (MapType3Type arg0@@150 arg1@@67 arg2@@26))
))) (forall ((arg0@@151 T@U) (arg1@@68 T@U) (arg2@@27 T@U) ) (! (let ((aVar2@@0 (MapType3TypeInv2 (type arg0@@151))))
(= (type (MapType3Select arg0@@151 arg1@@68 arg2@@27)) aVar2@@0))
 :qid |funType:MapType3Select|
 :pattern ( (MapType3Select arg0@@151 arg1@@68 arg2@@27))
))) (forall ((arg0@@152 T@U) (arg1@@69 T@U) (arg2@@28 T@U) (arg3@@9 T@U) ) (! (let ((aVar2@@1 (type arg3@@9)))
(let ((aVar1@@3 (type arg2@@28)))
(let ((aVar0@@2 (type arg1@@69)))
(= (type (MapType3Store arg0@@152 arg1@@69 arg2@@28 arg3@@9)) (MapType3Type aVar0@@2 aVar1@@3 aVar2@@1)))))
 :qid |funType:MapType3Store|
 :pattern ( (MapType3Store arg0@@152 arg1@@69 arg2@@28 arg3@@9))
))) (forall ((m@@33 T@U) (x0@@11 T@U) (x1@@8 T@U) (val@@12 T@U) ) (! (let ((aVar2@@2 (MapType3TypeInv2 (type m@@33))))
 (=> (= (type val@@12) aVar2@@2) (= (MapType3Select (MapType3Store m@@33 x0@@11 x1@@8 val@@12) x0@@11 x1@@8) val@@12)))
 :qid |mapAx0:MapType3Select|
 :weight 0
))) (and (and (forall ((val@@13 T@U) (m@@34 T@U) (x0@@12 T@U) (x1@@9 T@U) (y0@@8 T@U) (y1@@6 T@U) ) (!  (or (= x0@@12 y0@@8) (= (MapType3Select (MapType3Store m@@34 x0@@12 x1@@9 val@@13) y0@@8 y1@@6) (MapType3Select m@@34 y0@@8 y1@@6)))
 :qid |mapAx1:MapType3Select:0|
 :weight 0
)) (forall ((val@@14 T@U) (m@@35 T@U) (x0@@13 T@U) (x1@@10 T@U) (y0@@9 T@U) (y1@@7 T@U) ) (!  (or (= x1@@10 y1@@7) (= (MapType3Select (MapType3Store m@@35 x0@@13 x1@@10 val@@14) y0@@9 y1@@7) (MapType3Select m@@35 y0@@9 y1@@7)))
 :qid |mapAx1:MapType3Select:1|
 :weight 0
))) (forall ((val@@15 T@U) (m@@36 T@U) (x0@@14 T@U) (x1@@11 T@U) (y0@@10 T@U) (y1@@8 T@U) ) (!  (or true (= (MapType3Select (MapType3Store m@@36 x0@@14 x1@@11 val@@15) y0@@10 y1@@8) (MapType3Select m@@36 y0@@10 y1@@8)))
 :qid |mapAx2:MapType3Select|
 :weight 0
)))) (forall ((arg0@@153 T@U) (arg1@@70 T@U) (arg2@@29 T@U) (arg3@@10 T@U) (arg4@@2 T@U) ) (! (= (type (Apply1 arg0@@153 arg1@@70 arg2@@29 arg3@@10 arg4@@2)) BoxType)
 :qid |funType:Apply1|
 :pattern ( (Apply1 arg0@@153 arg1@@70 arg2@@29 arg3@@10 arg4@@2))
))) (forall ((arg0@@154 T@U) (arg1@@71 T@U) (arg2@@30 T@U) ) (! (= (type (Handle1 arg0@@154 arg1@@71 arg2@@30)) HandleTypeType)
 :qid |funType:Handle1|
 :pattern ( (Handle1 arg0@@154 arg1@@71 arg2@@30))
))))
(assert (forall ((t0@@42 T@U) (t1@@18 T@U) (heap@@9 T@U) (h@@34 T@U) (r@@16 T@U) (rd@@5 T@U) (bx0@@15 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@42) TyType) (= (type t1@@18) TyType)) (= (type heap@@9) (MapType1Type refType))) (= (type h@@34) (MapType3Type (MapType1Type refType) BoxType BoxType))) (= (type r@@16) (MapType3Type (MapType1Type refType) BoxType boolType))) (= (type rd@@5) (MapType3Type (MapType1Type refType) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@15) BoxType)) (= (Apply1 t0@@42 t1@@18 heap@@9 (Handle1 h@@34 r@@16 rd@@5) bx0@@15) (MapType3Select h@@34 heap@@9 bx0@@15)))
 :qid |fastexpb.2638:15|
 :skolemid |452|
 :pattern ( (Apply1 t0@@42 t1@@18 heap@@9 (Handle1 h@@34 r@@16 rd@@5) bx0@@15))
)))
(assert (forall ((t0@@43 T@U) (t1@@19 T@U) (heap@@10 T@U) (h@@35 T@U) (r@@17 T@U) (rd@@6 T@U) (bx0@@16 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@43) TyType) (= (type t1@@19) TyType)) (= (type heap@@10) (MapType1Type refType))) (= (type h@@35) (MapType3Type (MapType1Type refType) BoxType BoxType))) (= (type r@@17) (MapType3Type (MapType1Type refType) BoxType boolType))) (= (type rd@@6) (MapType3Type (MapType1Type refType) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@16) BoxType)) (U_2_bool (MapType3Select r@@17 heap@@10 bx0@@16))) (Requires1 t0@@43 t1@@19 heap@@10 (Handle1 h@@35 r@@17 rd@@6) bx0@@16))
 :qid |fastexpb.2648:15|
 :skolemid |453|
 :pattern ( (Requires1 t0@@43 t1@@19 heap@@10 (Handle1 h@@35 r@@17 rd@@6) bx0@@16))
)))
(assert (forall ((arg0@@155 T@U) (arg1@@72 T@U) (arg2@@31 T@U) (arg3@@11 T@U) (arg4@@3 T@U) ) (! (= (type (Reads1 arg0@@155 arg1@@72 arg2@@31 arg3@@11 arg4@@3)) (MapType0Type BoxType boolType))
 :qid |funType:Reads1|
 :pattern ( (Reads1 arg0@@155 arg1@@72 arg2@@31 arg3@@11 arg4@@3))
)))
(assert (forall ((t0@@44 T@U) (t1@@20 T@U) (heap@@11 T@U) (h@@36 T@U) (r@@18 T@U) (rd@@7 T@U) (bx0@@17 T@U) (bx@@53 T@U) ) (!  (=> (and (and (and (and (and (and (and (= (type t0@@44) TyType) (= (type t1@@20) TyType)) (= (type heap@@11) (MapType1Type refType))) (= (type h@@36) (MapType3Type (MapType1Type refType) BoxType BoxType))) (= (type r@@18) (MapType3Type (MapType1Type refType) BoxType boolType))) (= (type rd@@7) (MapType3Type (MapType1Type refType) BoxType (MapType0Type BoxType boolType)))) (= (type bx0@@17) BoxType)) (= (type bx@@53) BoxType)) (and (=> (U_2_bool (MapType0Select (Reads1 t0@@44 t1@@20 heap@@11 (Handle1 h@@36 r@@18 rd@@7) bx0@@17) bx@@53)) (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@11 bx0@@17) bx@@53))) (=> (U_2_bool (MapType0Select (MapType3Select rd@@7 heap@@11 bx0@@17) bx@@53)) (U_2_bool (MapType0Select (Reads1 t0@@44 t1@@20 heap@@11 (Handle1 h@@36 r@@18 rd@@7) bx0@@17) bx@@53)))))
 :qid |fastexpb.2658:15|
 :skolemid |454|
 :pattern ( (MapType0Select (Reads1 t0@@44 t1@@20 heap@@11 (Handle1 h@@36 r@@18 rd@@7) bx0@@17) bx@@53))
)))
(assert (forall ((t0@@45 T@U) (t1@@21 T@U) (h0@@12 T@U) (h1@@12 T@U) (f@@29 T@U) (bx0@@18 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@45) TyType) (= (type t1@@21) TyType)) (= (type h0@@12) (MapType1Type refType))) (= (type h1@@12) (MapType1Type refType))) (= (type f@@29) HandleTypeType)) (= (type bx0@@18) BoxType)) (and (and (and (and (and ($HeapSucc h0@@12 h1@@12) ($IsGoodHeap h0@@12)) ($IsGoodHeap h1@@12)) ($IsBox bx0@@18 t0@@45)) ($Is f@@29 (Tclass._System.___hFunc1 t0@@45 t1@@21))) (forall ((o@@67 T@U) (fld@@11 T@U) ) (! (let ((a@@93 (FieldTypeInv0 (type fld@@11))))
 (=> (and (and (= (type o@@67) refType) (= (type fld@@11) (FieldType a@@93))) (and (not (= o@@67 null)) (U_2_bool (MapType0Select (Reads1 t0@@45 t1@@21 h0@@12 f@@29 bx0@@18) ($Box o@@67))))) (= (MapType1Select h0@@12 o@@67 fld@@11) (MapType1Select h1@@12 o@@67 fld@@11))))
 :qid |fastexpb.2689:22|
 :skolemid |455|
 :no-pattern (type o@@67)
 :no-pattern (type fld@@11)
 :no-pattern (U_2_int o@@67)
 :no-pattern (U_2_bool o@@67)
 :no-pattern (U_2_int fld@@11)
 :no-pattern (U_2_bool fld@@11)
)))) (= (Reads1 t0@@45 t1@@21 h0@@12 f@@29 bx0@@18) (Reads1 t0@@45 t1@@21 h1@@12 f@@29 bx0@@18)))
 :qid |fastexpb.2680:15|
 :skolemid |456|
 :pattern ( ($HeapSucc h0@@12 h1@@12) (Reads1 t0@@45 t1@@21 h1@@12 f@@29 bx0@@18))
)))
(assert (forall ((t0@@46 T@U) (t1@@22 T@U) (h0@@13 T@U) (h1@@13 T@U) (f@@30 T@U) (bx0@@19 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@46) TyType) (= (type t1@@22) TyType)) (= (type h0@@13) (MapType1Type refType))) (= (type h1@@13) (MapType1Type refType))) (= (type f@@30) HandleTypeType)) (= (type bx0@@19) BoxType)) (and (and (and (and (and ($HeapSucc h0@@13 h1@@13) ($IsGoodHeap h0@@13)) ($IsGoodHeap h1@@13)) ($IsBox bx0@@19 t0@@46)) ($Is f@@30 (Tclass._System.___hFunc1 t0@@46 t1@@22))) (forall ((o@@68 T@U) (fld@@12 T@U) ) (! (let ((a@@94 (FieldTypeInv0 (type fld@@12))))
 (=> (and (and (= (type o@@68) refType) (= (type fld@@12) (FieldType a@@94))) (and (not (= o@@68 null)) (U_2_bool (MapType0Select (Reads1 t0@@46 t1@@22 h1@@13 f@@30 bx0@@19) ($Box o@@68))))) (= (MapType1Select h0@@13 o@@68 fld@@12) (MapType1Select h1@@13 o@@68 fld@@12))))
 :qid |fastexpb.2704:22|
 :skolemid |457|
 :no-pattern (type o@@68)
 :no-pattern (type fld@@12)
 :no-pattern (U_2_int o@@68)
 :no-pattern (U_2_bool o@@68)
 :no-pattern (U_2_int fld@@12)
 :no-pattern (U_2_bool fld@@12)
)))) (= (Reads1 t0@@46 t1@@22 h0@@13 f@@30 bx0@@19) (Reads1 t0@@46 t1@@22 h1@@13 f@@30 bx0@@19)))
 :qid |fastexpb.2695:15|
 :skolemid |458|
 :pattern ( ($HeapSucc h0@@13 h1@@13) (Reads1 t0@@46 t1@@22 h1@@13 f@@30 bx0@@19))
)))
(assert (forall ((t0@@47 T@U) (t1@@23 T@U) (h0@@14 T@U) (h1@@14 T@U) (f@@31 T@U) (bx0@@20 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@47) TyType) (= (type t1@@23) TyType)) (= (type h0@@14) (MapType1Type refType))) (= (type h1@@14) (MapType1Type refType))) (= (type f@@31) HandleTypeType)) (= (type bx0@@20) BoxType)) (and (and (and (and (and ($HeapSucc h0@@14 h1@@14) ($IsGoodHeap h0@@14)) ($IsGoodHeap h1@@14)) ($IsBox bx0@@20 t0@@47)) ($Is f@@31 (Tclass._System.___hFunc1 t0@@47 t1@@23))) (forall ((o@@69 T@U) (fld@@13 T@U) ) (! (let ((a@@95 (FieldTypeInv0 (type fld@@13))))
 (=> (and (and (= (type o@@69) refType) (= (type fld@@13) (FieldType a@@95))) (and (not (= o@@69 null)) (U_2_bool (MapType0Select (Reads1 t0@@47 t1@@23 h0@@14 f@@31 bx0@@20) ($Box o@@69))))) (= (MapType1Select h0@@14 o@@69 fld@@13) (MapType1Select h1@@14 o@@69 fld@@13))))
 :qid |fastexpb.2719:22|
 :skolemid |459|
 :no-pattern (type o@@69)
 :no-pattern (type fld@@13)
 :no-pattern (U_2_int o@@69)
 :no-pattern (U_2_bool o@@69)
 :no-pattern (U_2_int fld@@13)
 :no-pattern (U_2_bool fld@@13)
)))) (and (=> (Requires1 t0@@47 t1@@23 h0@@14 f@@31 bx0@@20) (Requires1 t0@@47 t1@@23 h1@@14 f@@31 bx0@@20)) (=> (Requires1 t0@@47 t1@@23 h1@@14 f@@31 bx0@@20) (Requires1 t0@@47 t1@@23 h0@@14 f@@31 bx0@@20))))
 :qid |fastexpb.2710:15|
 :skolemid |460|
 :pattern ( ($HeapSucc h0@@14 h1@@14) (Requires1 t0@@47 t1@@23 h1@@14 f@@31 bx0@@20))
)))
(assert (forall ((t0@@48 T@U) (t1@@24 T@U) (h0@@15 T@U) (h1@@15 T@U) (f@@32 T@U) (bx0@@21 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@48) TyType) (= (type t1@@24) TyType)) (= (type h0@@15) (MapType1Type refType))) (= (type h1@@15) (MapType1Type refType))) (= (type f@@32) HandleTypeType)) (= (type bx0@@21) BoxType)) (and (and (and (and (and ($HeapSucc h0@@15 h1@@15) ($IsGoodHeap h0@@15)) ($IsGoodHeap h1@@15)) ($IsBox bx0@@21 t0@@48)) ($Is f@@32 (Tclass._System.___hFunc1 t0@@48 t1@@24))) (forall ((o@@70 T@U) (fld@@14 T@U) ) (! (let ((a@@96 (FieldTypeInv0 (type fld@@14))))
 (=> (and (and (= (type o@@70) refType) (= (type fld@@14) (FieldType a@@96))) (and (not (= o@@70 null)) (U_2_bool (MapType0Select (Reads1 t0@@48 t1@@24 h1@@15 f@@32 bx0@@21) ($Box o@@70))))) (= (MapType1Select h0@@15 o@@70 fld@@14) (MapType1Select h1@@15 o@@70 fld@@14))))
 :qid |fastexpb.2734:22|
 :skolemid |461|
 :no-pattern (type o@@70)
 :no-pattern (type fld@@14)
 :no-pattern (U_2_int o@@70)
 :no-pattern (U_2_bool o@@70)
 :no-pattern (U_2_int fld@@14)
 :no-pattern (U_2_bool fld@@14)
)))) (and (=> (Requires1 t0@@48 t1@@24 h0@@15 f@@32 bx0@@21) (Requires1 t0@@48 t1@@24 h1@@15 f@@32 bx0@@21)) (=> (Requires1 t0@@48 t1@@24 h1@@15 f@@32 bx0@@21) (Requires1 t0@@48 t1@@24 h0@@15 f@@32 bx0@@21))))
 :qid |fastexpb.2725:15|
 :skolemid |462|
 :pattern ( ($HeapSucc h0@@15 h1@@15) (Requires1 t0@@48 t1@@24 h1@@15 f@@32 bx0@@21))
)))
(assert (forall ((t0@@49 T@U) (t1@@25 T@U) (h0@@16 T@U) (h1@@16 T@U) (f@@33 T@U) (bx0@@22 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@49) TyType) (= (type t1@@25) TyType)) (= (type h0@@16) (MapType1Type refType))) (= (type h1@@16) (MapType1Type refType))) (= (type f@@33) HandleTypeType)) (= (type bx0@@22) BoxType)) (and (and (and (and (and ($HeapSucc h0@@16 h1@@16) ($IsGoodHeap h0@@16)) ($IsGoodHeap h1@@16)) ($IsBox bx0@@22 t0@@49)) ($Is f@@33 (Tclass._System.___hFunc1 t0@@49 t1@@25))) (forall ((o@@71 T@U) (fld@@15 T@U) ) (! (let ((a@@97 (FieldTypeInv0 (type fld@@15))))
 (=> (and (and (= (type o@@71) refType) (= (type fld@@15) (FieldType a@@97))) (and (not (= o@@71 null)) (U_2_bool (MapType0Select (Reads1 t0@@49 t1@@25 h0@@16 f@@33 bx0@@22) ($Box o@@71))))) (= (MapType1Select h0@@16 o@@71 fld@@15) (MapType1Select h1@@16 o@@71 fld@@15))))
 :qid |fastexpb.2749:22|
 :skolemid |463|
 :no-pattern (type o@@71)
 :no-pattern (type fld@@15)
 :no-pattern (U_2_int o@@71)
 :no-pattern (U_2_bool o@@71)
 :no-pattern (U_2_int fld@@15)
 :no-pattern (U_2_bool fld@@15)
)))) (= (Apply1 t0@@49 t1@@25 h0@@16 f@@33 bx0@@22) (Apply1 t0@@49 t1@@25 h1@@16 f@@33 bx0@@22)))
 :qid |fastexpb.2740:15|
 :skolemid |464|
 :pattern ( ($HeapSucc h0@@16 h1@@16) (Apply1 t0@@49 t1@@25 h1@@16 f@@33 bx0@@22))
)))
(assert (forall ((t0@@50 T@U) (t1@@26 T@U) (h0@@17 T@U) (h1@@17 T@U) (f@@34 T@U) (bx0@@23 T@U) ) (!  (=> (and (and (and (and (and (and (= (type t0@@50) TyType) (= (type t1@@26) TyType)) (= (type h0@@17) (MapType1Type refType))) (= (type h1@@17) (MapType1Type refType))) (= (type f@@34) HandleTypeType)) (= (type bx0@@23) BoxType)) (and (and (and (and (and ($HeapSucc h0@@17 h1@@17) ($IsGoodHeap h0@@17)) ($IsGoodHeap h1@@17)) ($IsBox bx0@@23 t0@@50)) ($Is f@@34 (Tclass._System.___hFunc1 t0@@50 t1@@26))) (forall ((o@@72 T@U) (fld@@16 T@U) ) (! (let ((a@@98 (FieldTypeInv0 (type fld@@16))))
 (=> (and (and (= (type o@@72) refType) (= (type fld@@16) (FieldType a@@98))) (and (not (= o@@72 null)) (U_2_bool (MapType0Select (Reads1 t0@@50 t1@@26 h1@@17 f@@34 bx0@@23) ($Box o@@72))))) (= (MapType1Select h0@@17 o@@72 fld@@16) (MapType1Select h1@@17 o@@72 fld@@16))))
 :qid |fastexpb.2764:22|
 :skolemid |465|
 :no-pattern (type o@@72)
 :no-pattern (type fld@@16)
 :no-pattern (U_2_int o@@72)
 :no-pattern (U_2_bool o@@72)
 :no-pattern (U_2_int fld@@16)
 :no-pattern (U_2_bool fld@@16)
)))) (= (Apply1 t0@@50 t1@@26 h0@@17 f@@34 bx0@@23) (Apply1 t0@@50 t1@@26 h1@@17 f@@34 bx0@@23)))
 :qid |fastexpb.2755:15|
 :skolemid |466|
 :pattern ( ($HeapSucc h0@@17 h1@@17) (Apply1 t0@@50 t1@@26 h1@@17 f@@34 bx0@@23))
)))
(assert (forall ((t0@@51 T@U) (t1@@27 T@U) (heap@@12 T@U) (f@@35 T@U) (bx0@@24 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@51) TyType) (= (type t1@@27) TyType)) (= (type heap@@12) (MapType1Type refType))) (= (type f@@35) HandleTypeType)) (= (type bx0@@24) BoxType)) (and (and ($IsGoodHeap heap@@12) ($IsBox bx0@@24 t0@@51)) ($Is f@@35 (Tclass._System.___hFunc1 t0@@51 t1@@27)))) (and (=> (|Set#Equal| (Reads1 t0@@51 t1@@27 $OneHeap f@@35 bx0@@24) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@51 t1@@27 heap@@12 f@@35 bx0@@24) (|Set#Empty| BoxType))) (=> (|Set#Equal| (Reads1 t0@@51 t1@@27 heap@@12 f@@35 bx0@@24) (|Set#Empty| BoxType)) (|Set#Equal| (Reads1 t0@@51 t1@@27 $OneHeap f@@35 bx0@@24) (|Set#Empty| BoxType)))))
 :qid |fastexpb.2770:15|
 :skolemid |467|
 :pattern ( (Reads1 t0@@51 t1@@27 $OneHeap f@@35 bx0@@24) ($IsGoodHeap heap@@12))
 :pattern ( (Reads1 t0@@51 t1@@27 heap@@12 f@@35 bx0@@24))
)))
(assert (forall ((t0@@52 T@U) (t1@@28 T@U) (heap@@13 T@U) (f@@36 T@U) (bx0@@25 T@U) ) (!  (=> (and (and (and (and (and (= (type t0@@52) TyType) (= (type t1@@28) TyType)) (= (type heap@@13) (MapType1Type refType))) (= (type f@@36) HandleTypeType)) (= (type bx0@@25) BoxType)) (and (and (and ($IsGoodHeap heap@@13) ($IsBox bx0@@25 t0@@52)) ($Is f@@36 (Tclass._System.___hFunc1 t0@@52 t1@@28))) (|Set#Equal| (Reads1 t0@@52 t1@@28 $OneHeap f@@36 bx0@@25) (|Set#Empty| BoxType)))) (and (=> (Requires1 t0@@52 t1@@28 $OneHeap f@@36 bx0@@25) (Requires1 t0@@52 t1@@28 heap@@13 f@@36 bx0@@25)) (=> (Requires1 t0@@52 t1@@28 heap@@13 f@@36 bx0@@25) (Requires1 t0@@52 t1@@28 $OneHeap f@@36 bx0@@25))))
 :qid |fastexpb.2778:15|
 :skolemid |468|
 :pattern ( (Requires1 t0@@52 t1@@28 $OneHeap f@@36 bx0@@25) ($IsGoodHeap heap@@13))
 :pattern ( (Requires1 t0@@52 t1@@28 heap@@13 f@@36 bx0@@25))
)))
(assert (forall ((f@@37 T@U) (t0@@53 T@U) (t1@@29 T@U) ) (!  (=> (and (and (= (type f@@37) HandleTypeType) (= (type t0@@53) TyType)) (= (type t1@@29) TyType)) (and (=> ($Is f@@37 (Tclass._System.___hFunc1 t0@@53 t1@@29)) (forall ((h@@37 T@U) (bx0@@26 T@U) ) (!  (=> (and (= (type h@@37) (MapType1Type refType)) (= (type bx0@@26) BoxType)) (=> (and (and ($IsGoodHeap h@@37) ($IsBox bx0@@26 t0@@53)) (Requires1 t0@@53 t1@@29 h@@37 f@@37 bx0@@26)) ($IsBox (Apply1 t0@@53 t1@@29 h@@37 f@@37 bx0@@26) t1@@29)))
 :qid |fastexpb.2791:19|
 :skolemid |469|
 :pattern ( (Apply1 t0@@53 t1@@29 h@@37 f@@37 bx0@@26))
))) (=> (forall ((h@@38 T@U) (bx0@@27 T@U) ) (!  (=> (and (= (type h@@38) (MapType1Type refType)) (= (type bx0@@27) BoxType)) (=> (and (and ($IsGoodHeap h@@38) ($IsBox bx0@@27 t0@@53)) (Requires1 t0@@53 t1@@29 h@@38 f@@37 bx0@@27)) ($IsBox (Apply1 t0@@53 t1@@29 h@@38 f@@37 bx0@@27) t1@@29)))
 :qid |fastexpb.2791:19|
 :skolemid |469|
 :pattern ( (Apply1 t0@@53 t1@@29 h@@38 f@@37 bx0@@27))
)) ($Is f@@37 (Tclass._System.___hFunc1 t0@@53 t1@@29)))))
 :qid |fastexpb.2788:15|
 :skolemid |470|
 :pattern ( ($Is f@@37 (Tclass._System.___hFunc1 t0@@53 t1@@29)))
)))
(assert (forall ((f@@38 T@U) (t0@@54 T@U) (t1@@30 T@U) (u0@@1 T@U) (u1@@0 T@U) ) (!  (=> (and (and (and (and (and (= (type f@@38) HandleTypeType) (= (type t0@@54) TyType)) (= (type t1@@30) TyType)) (= (type u0@@1) TyType)) (= (type u1@@0) TyType)) (and (and ($Is f@@38 (Tclass._System.___hFunc1 t0@@54 t1@@30)) (forall ((bx@@54 T@U) ) (!  (=> (and (= (type bx@@54) BoxType) ($IsBox bx@@54 u0@@1)) ($IsBox bx@@54 t0@@54))
 :qid |fastexpb.2799:19|
 :skolemid |471|
 :pattern ( ($IsBox bx@@54 u0@@1))
 :pattern ( ($IsBox bx@@54 t0@@54))
))) (forall ((bx@@55 T@U) ) (!  (=> (and (= (type bx@@55) BoxType) ($IsBox bx@@55 t1@@30)) ($IsBox bx@@55 u1@@0))
 :qid |fastexpb.2802:19|
 :skolemid |472|
 :pattern ( ($IsBox bx@@55 t1@@30))
 :pattern ( ($IsBox bx@@55 u1@@0))
)))) ($Is f@@38 (Tclass._System.___hFunc1 u0@@1 u1@@0)))
 :qid |fastexpb.2796:15|
 :skolemid |473|
 :pattern ( ($Is f@@38 (Tclass._System.___hFunc1 t0@@54 t1@@30)) ($Is f@@38 (Tclass._System.___hFunc1 u0@@1 u1@@0)))
)))
(assert (forall ((f@@39 T@U) (t0@@55 T@U) (t1@@31 T@U) (h@@39 T@U) ) (!  (=> (and (and (and (and (= (type f@@39) HandleTypeType) (= (type t0@@55) TyType)) (= (type t1@@31) TyType)) (= (type h@@39) (MapType1Type refType))) ($IsGoodHeap h@@39)) (and (=> ($IsAlloc f@@39 (Tclass._System.___hFunc1 t0@@55 t1@@31) h@@39) (forall ((bx0@@28 T@U) ) (!  (=> (= (type bx0@@28) BoxType) (=> (and (and ($IsBox bx0@@28 t0@@55) ($IsAllocBox bx0@@28 t0@@55 h@@39)) (Requires1 t0@@55 t1@@31 h@@39 f@@39 bx0@@28)) (forall ((r@@19 T@U) ) (!  (=> (= (type r@@19) refType) (=> (and (not (= r@@19 null)) (U_2_bool (MapType0Select (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@28) ($Box r@@19)))) (U_2_bool (MapType1Select h@@39 r@@19 alloc))))
 :qid |fastexpb.2814:24|
 :skolemid |474|
 :pattern ( (MapType0Select (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@28) ($Box r@@19)))
))))
 :qid |fastexpb.2811:21|
 :skolemid |475|
 :pattern ( (Apply1 t0@@55 t1@@31 h@@39 f@@39 bx0@@28))
 :pattern ( (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@28))
))) (=> (forall ((bx0@@29 T@U) ) (!  (=> (= (type bx0@@29) BoxType) (=> (and (and ($IsBox bx0@@29 t0@@55) ($IsAllocBox bx0@@29 t0@@55 h@@39)) (Requires1 t0@@55 t1@@31 h@@39 f@@39 bx0@@29)) (forall ((r@@20 T@U) ) (!  (=> (= (type r@@20) refType) (=> (and (not (= r@@20 null)) (U_2_bool (MapType0Select (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@29) ($Box r@@20)))) (U_2_bool (MapType1Select h@@39 r@@20 alloc))))
 :qid |fastexpb.2814:24|
 :skolemid |474|
 :pattern ( (MapType0Select (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@29) ($Box r@@20)))
))))
 :qid |fastexpb.2811:21|
 :skolemid |475|
 :pattern ( (Apply1 t0@@55 t1@@31 h@@39 f@@39 bx0@@29))
 :pattern ( (Reads1 t0@@55 t1@@31 h@@39 f@@39 bx0@@29))
)) ($IsAlloc f@@39 (Tclass._System.___hFunc1 t0@@55 t1@@31) h@@39))))
 :qid |fastexpb.2807:15|
 :skolemid |476|
 :pattern ( ($IsAlloc f@@39 (Tclass._System.___hFunc1 t0@@55 t1@@31) h@@39))
)))
(assert (forall ((f@@40 T@U) (t0@@56 T@U) (t1@@32 T@U) (h@@40 T@U) ) (!  (=> (and (and (and (and (= (type f@@40) HandleTypeType) (= (type t0@@56) TyType)) (= (type t1@@32) TyType)) (= (type h@@40) (MapType1Type refType))) (and ($IsGoodHeap h@@40) ($IsAlloc f@@40 (Tclass._System.___hFunc1 t0@@56 t1@@32) h@@40))) (forall ((bx0@@30 T@U) ) (!  (=> (= (type bx0@@30) BoxType) (=> (and ($IsAllocBox bx0@@30 t0@@56 h@@40) (Requires1 t0@@56 t1@@32 h@@40 f@@40 bx0@@30)) ($IsAllocBox (Apply1 t0@@56 t1@@32 h@@40 f@@40 bx0@@30) t1@@32 h@@40)))
 :qid |fastexpb.2821:18|
 :skolemid |477|
 :pattern ( (Apply1 t0@@56 t1@@32 h@@40 f@@40 bx0@@30))
)))
 :qid |fastexpb.2818:15|
 :skolemid |478|
 :pattern ( ($IsAlloc f@@40 (Tclass._System.___hFunc1 t0@@56 t1@@32) h@@40))
)))
(assert (forall ((arg0@@156 T@U) (arg1@@73 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1 arg0@@156 arg1@@73)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1|
 :pattern ( (Tclass._System.___hPartialFunc1 arg0@@156 arg1@@73))
)))
(assert (forall ((|#$T0@@31| T@U) (|#$R@@35| T@U) ) (!  (=> (and (= (type |#$T0@@31|) TyType) (= (type |#$R@@35|) TyType)) (= (Tag (Tclass._System.___hPartialFunc1 |#$T0@@31| |#$R@@35|)) Tagclass._System.___hPartialFunc1))
 :qid |fastexpb.2829:15|
 :skolemid |479|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@31| |#$R@@35|))
)))
(assert (forall ((arg0@@157 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_0 arg0@@157)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_0|
 :pattern ( (Tclass._System.___hPartialFunc1_0 arg0@@157))
)))
(assert (forall ((|#$T0@@32| T@U) (|#$R@@36| T@U) ) (!  (=> (and (= (type |#$T0@@32|) TyType) (= (type |#$R@@36|) TyType)) (= (Tclass._System.___hPartialFunc1_0 (Tclass._System.___hPartialFunc1 |#$T0@@32| |#$R@@36|)) |#$T0@@32|))
 :qid |fastexpb.2837:15|
 :skolemid |480|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@32| |#$R@@36|))
)))
(assert (forall ((arg0@@158 T@U) ) (! (= (type (Tclass._System.___hPartialFunc1_1 arg0@@158)) TyType)
 :qid |funType:Tclass._System.___hPartialFunc1_1|
 :pattern ( (Tclass._System.___hPartialFunc1_1 arg0@@158))
)))
(assert (forall ((|#$T0@@33| T@U) (|#$R@@37| T@U) ) (!  (=> (and (= (type |#$T0@@33|) TyType) (= (type |#$R@@37|) TyType)) (= (Tclass._System.___hPartialFunc1_1 (Tclass._System.___hPartialFunc1 |#$T0@@33| |#$R@@37|)) |#$R@@37|))
 :qid |fastexpb.2845:15|
 :skolemid |481|
 :pattern ( (Tclass._System.___hPartialFunc1 |#$T0@@33| |#$R@@37|))
)))
(assert (forall ((|#$T0@@34| T@U) (|#$R@@38| T@U) (bx@@56 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@34|) TyType) (= (type |#$R@@38|) TyType)) (= (type bx@@56) BoxType)) ($IsBox bx@@56 (Tclass._System.___hPartialFunc1 |#$T0@@34| |#$R@@38|))) (and (= ($Box ($Unbox HandleTypeType bx@@56)) bx@@56) ($Is ($Unbox HandleTypeType bx@@56) (Tclass._System.___hPartialFunc1 |#$T0@@34| |#$R@@38|))))
 :qid |fastexpb.2853:15|
 :skolemid |482|
 :pattern ( ($IsBox bx@@56 (Tclass._System.___hPartialFunc1 |#$T0@@34| |#$R@@38|)))
)))
(assert (forall ((|#$T0@@35| T@U) (|#$R@@39| T@U) (|f#0@@7| T@U) ) (!  (=> (and (and (= (type |#$T0@@35|) TyType) (= (type |#$R@@39|) TyType)) (= (type |f#0@@7|) HandleTypeType)) (and (=> ($Is |f#0@@7| (Tclass._System.___hPartialFunc1 |#$T0@@35| |#$R@@39|)) (and ($Is |f#0@@7| (Tclass._System.___hFunc1 |#$T0@@35| |#$R@@39|)) (forall ((|x0#0@@3| T@U) ) (!  (=> (and (= (type |x0#0@@3|) BoxType) ($IsBox |x0#0@@3| |#$T0@@35|)) (|Set#Equal| (Reads1 |#$T0@@35| |#$R@@39| $OneHeap |f#0@@7| |x0#0@@3|) (|Set#Empty| BoxType)))
 :qid |fastexpb.2864:19|
 :skolemid |483|
 :no-pattern (type |x0#0@@3|)
 :no-pattern (U_2_int |x0#0@@3|)
 :no-pattern (U_2_bool |x0#0@@3|)
)))) (=> (and ($Is |f#0@@7| (Tclass._System.___hFunc1 |#$T0@@35| |#$R@@39|)) (forall ((|x0#0@@4| T@U) ) (!  (=> (and (= (type |x0#0@@4|) BoxType) ($IsBox |x0#0@@4| |#$T0@@35|)) (|Set#Equal| (Reads1 |#$T0@@35| |#$R@@39| $OneHeap |f#0@@7| |x0#0@@4|) (|Set#Empty| BoxType)))
 :qid |fastexpb.2864:19|
 :skolemid |483|
 :no-pattern (type |x0#0@@4|)
 :no-pattern (U_2_int |x0#0@@4|)
 :no-pattern (U_2_bool |x0#0@@4|)
))) ($Is |f#0@@7| (Tclass._System.___hPartialFunc1 |#$T0@@35| |#$R@@39|)))))
 :qid |fastexpb.2860:15|
 :skolemid |484|
 :pattern ( ($Is |f#0@@7| (Tclass._System.___hPartialFunc1 |#$T0@@35| |#$R@@39|)))
)))
(assert (forall ((|#$T0@@36| T@U) (|#$R@@40| T@U) (|f#0@@8| T@U) ($h@@14 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@36|) TyType) (= (type |#$R@@40|) TyType)) (= (type |f#0@@8|) HandleTypeType)) (= (type $h@@14) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc1 |#$T0@@36| |#$R@@40|) $h@@14) ($IsAlloc |f#0@@8| (Tclass._System.___hFunc1 |#$T0@@36| |#$R@@40|) $h@@14)) (=> ($IsAlloc |f#0@@8| (Tclass._System.___hFunc1 |#$T0@@36| |#$R@@40|) $h@@14) ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc1 |#$T0@@36| |#$R@@40|) $h@@14))))
 :qid |fastexpb.2869:15|
 :skolemid |485|
 :pattern ( ($IsAlloc |f#0@@8| (Tclass._System.___hPartialFunc1 |#$T0@@36| |#$R@@40|) $h@@14))
)))
(assert (forall ((arg0@@159 T@U) (arg1@@74 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1 arg0@@159 arg1@@74)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1|
 :pattern ( (Tclass._System.___hTotalFunc1 arg0@@159 arg1@@74))
)))
(assert (forall ((|#$T0@@37| T@U) (|#$R@@41| T@U) ) (!  (=> (and (= (type |#$T0@@37|) TyType) (= (type |#$R@@41|) TyType)) (= (Tag (Tclass._System.___hTotalFunc1 |#$T0@@37| |#$R@@41|)) Tagclass._System.___hTotalFunc1))
 :qid |fastexpb.2877:15|
 :skolemid |486|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@37| |#$R@@41|))
)))
(assert (forall ((arg0@@160 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_0 arg0@@160)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_0|
 :pattern ( (Tclass._System.___hTotalFunc1_0 arg0@@160))
)))
(assert (forall ((|#$T0@@38| T@U) (|#$R@@42| T@U) ) (!  (=> (and (= (type |#$T0@@38|) TyType) (= (type |#$R@@42|) TyType)) (= (Tclass._System.___hTotalFunc1_0 (Tclass._System.___hTotalFunc1 |#$T0@@38| |#$R@@42|)) |#$T0@@38|))
 :qid |fastexpb.2884:15|
 :skolemid |487|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@38| |#$R@@42|))
)))
(assert (forall ((arg0@@161 T@U) ) (! (= (type (Tclass._System.___hTotalFunc1_1 arg0@@161)) TyType)
 :qid |funType:Tclass._System.___hTotalFunc1_1|
 :pattern ( (Tclass._System.___hTotalFunc1_1 arg0@@161))
)))
(assert (forall ((|#$T0@@39| T@U) (|#$R@@43| T@U) ) (!  (=> (and (= (type |#$T0@@39|) TyType) (= (type |#$R@@43|) TyType)) (= (Tclass._System.___hTotalFunc1_1 (Tclass._System.___hTotalFunc1 |#$T0@@39| |#$R@@43|)) |#$R@@43|))
 :qid |fastexpb.2892:15|
 :skolemid |488|
 :pattern ( (Tclass._System.___hTotalFunc1 |#$T0@@39| |#$R@@43|))
)))
(assert (forall ((|#$T0@@40| T@U) (|#$R@@44| T@U) (bx@@57 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@40|) TyType) (= (type |#$R@@44|) TyType)) (= (type bx@@57) BoxType)) ($IsBox bx@@57 (Tclass._System.___hTotalFunc1 |#$T0@@40| |#$R@@44|))) (and (= ($Box ($Unbox HandleTypeType bx@@57)) bx@@57) ($Is ($Unbox HandleTypeType bx@@57) (Tclass._System.___hTotalFunc1 |#$T0@@40| |#$R@@44|))))
 :qid |fastexpb.2899:15|
 :skolemid |489|
 :pattern ( ($IsBox bx@@57 (Tclass._System.___hTotalFunc1 |#$T0@@40| |#$R@@44|)))
)))
(assert (forall ((|#$T0@@41| T@U) (|#$R@@45| T@U) (|f#0@@9| T@U) ) (!  (=> (and (and (= (type |#$T0@@41|) TyType) (= (type |#$R@@45|) TyType)) (= (type |f#0@@9|) HandleTypeType)) (and (=> ($Is |f#0@@9| (Tclass._System.___hTotalFunc1 |#$T0@@41| |#$R@@45|)) (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc1 |#$T0@@41| |#$R@@45|)) (forall ((|x0#0@@5| T@U) ) (!  (=> (and (= (type |x0#0@@5|) BoxType) ($IsBox |x0#0@@5| |#$T0@@41|)) (Requires1 |#$T0@@41| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@5|))
 :qid |fastexpb.2910:19|
 :skolemid |490|
 :no-pattern (type |x0#0@@5|)
 :no-pattern (U_2_int |x0#0@@5|)
 :no-pattern (U_2_bool |x0#0@@5|)
)))) (=> (and ($Is |f#0@@9| (Tclass._System.___hPartialFunc1 |#$T0@@41| |#$R@@45|)) (forall ((|x0#0@@6| T@U) ) (!  (=> (and (= (type |x0#0@@6|) BoxType) ($IsBox |x0#0@@6| |#$T0@@41|)) (Requires1 |#$T0@@41| |#$R@@45| $OneHeap |f#0@@9| |x0#0@@6|))
 :qid |fastexpb.2910:19|
 :skolemid |490|
 :no-pattern (type |x0#0@@6|)
 :no-pattern (U_2_int |x0#0@@6|)
 :no-pattern (U_2_bool |x0#0@@6|)
))) ($Is |f#0@@9| (Tclass._System.___hTotalFunc1 |#$T0@@41| |#$R@@45|)))))
 :qid |fastexpb.2906:15|
 :skolemid |491|
 :pattern ( ($Is |f#0@@9| (Tclass._System.___hTotalFunc1 |#$T0@@41| |#$R@@45|)))
)))
(assert (forall ((|#$T0@@42| T@U) (|#$R@@46| T@U) (|f#0@@10| T@U) ($h@@15 T@U) ) (!  (=> (and (and (and (= (type |#$T0@@42|) TyType) (= (type |#$R@@46|) TyType)) (= (type |f#0@@10|) HandleTypeType)) (= (type $h@@15) (MapType1Type refType))) (and (=> ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc1 |#$T0@@42| |#$R@@46|) $h@@15) ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc1 |#$T0@@42| |#$R@@46|) $h@@15)) (=> ($IsAlloc |f#0@@10| (Tclass._System.___hPartialFunc1 |#$T0@@42| |#$R@@46|) $h@@15) ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc1 |#$T0@@42| |#$R@@46|) $h@@15))))
 :qid |fastexpb.2914:15|
 :skolemid |492|
 :pattern ( ($IsAlloc |f#0@@10| (Tclass._System.___hTotalFunc1 |#$T0@@42| |#$R@@46|) $h@@15))
)))
(assert (= (type |#_System._tuple#0._#Make0|) DatatypeTypeType))
(assert (= (DatatypeCtorId |#_System._tuple#0._#Make0|) |##_System._tuple#0._#Make0|))
(assert (forall ((d@@6 T@U) ) (!  (=> (= (type d@@6) DatatypeTypeType) (and (=> (_System.Tuple0.___hMake0_q d@@6) (= (DatatypeCtorId d@@6) |##_System._tuple#0._#Make0|)) (=> (= (DatatypeCtorId d@@6) |##_System._tuple#0._#Make0|) (_System.Tuple0.___hMake0_q d@@6))))
 :qid |fastexpb.2932:15|
 :skolemid |493|
 :pattern ( (_System.Tuple0.___hMake0_q d@@6))
)))
(assert (forall ((d@@7 T@U) ) (!  (=> (and (= (type d@@7) DatatypeTypeType) (_System.Tuple0.___hMake0_q d@@7)) (= d@@7 |#_System._tuple#0._#Make0|))
 :qid |fastexpb.2938:15|
 :skolemid |494|
 :pattern ( (_System.Tuple0.___hMake0_q d@@7))
)))
(assert (= (type Tclass._System.Tuple0) TyType))
(assert (= (Tag Tclass._System.Tuple0) Tagclass._System.Tuple0))
(assert (forall ((bx@@58 T@U) ) (!  (=> (and (= (type bx@@58) BoxType) ($IsBox bx@@58 Tclass._System.Tuple0)) (and (= ($Box ($Unbox DatatypeTypeType bx@@58)) bx@@58) ($Is ($Unbox DatatypeTypeType bx@@58) Tclass._System.Tuple0)))
 :qid |fastexpb.2950:15|
 :skolemid |495|
 :pattern ( ($IsBox bx@@58 Tclass._System.Tuple0))
)))
(assert ($Is |#_System._tuple#0._#Make0| Tclass._System.Tuple0))
(assert (forall (($h@@16 T@U) ) (!  (=> (and (= (type $h@@16) (MapType1Type refType)) ($IsGoodHeap $h@@16)) ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@16))
 :qid |fastexpb.2960:15|
 :skolemid |496|
 :pattern ( ($IsAlloc |#_System._tuple#0._#Make0| Tclass._System.Tuple0 $h@@16))
)))
(assert (= |#_System._tuple#0._#Make0| (Lit |#_System._tuple#0._#Make0|)))
(assert (forall ((d@@8 T@U) ) (!  (=> (and (= (type d@@8) DatatypeTypeType) (|$IsA#_System.Tuple0| d@@8)) (_System.Tuple0.___hMake0_q d@@8))
 :qid |fastexpb.2972:15|
 :skolemid |497|
 :pattern ( (|$IsA#_System.Tuple0| d@@8))
)))
(assert (forall ((d@@9 T@U) ) (!  (=> (and (= (type d@@9) DatatypeTypeType) ($Is d@@9 Tclass._System.Tuple0)) (_System.Tuple0.___hMake0_q d@@9))
 :qid |fastexpb.2977:15|
 :skolemid |498|
 :pattern ( (_System.Tuple0.___hMake0_q d@@9) ($Is d@@9 Tclass._System.Tuple0))
)))
(assert (forall ((a@@99 T@U) (b@@60 T@U) ) (!  (=> (and (and (= (type a@@99) DatatypeTypeType) (= (type b@@60) DatatypeTypeType)) true) (and (=> (|_System.Tuple0#Equal| a@@99 b@@60) true) (=> true (|_System.Tuple0#Equal| a@@99 b@@60))))
 :qid |fastexpb.2985:15|
 :skolemid |499|
 :pattern ( (|_System.Tuple0#Equal| a@@99 b@@60))
)))
(assert (forall ((a@@100 T@U) (b@@61 T@U) ) (!  (=> (and (= (type a@@100) DatatypeTypeType) (= (type b@@61) DatatypeTypeType)) (and (=> (|_System.Tuple0#Equal| a@@100 b@@61) (= a@@100 b@@61)) (=> (= a@@100 b@@61) (|_System.Tuple0#Equal| a@@100 b@@61))))
 :qid |fastexpb.2990:15|
 :skolemid |500|
 :pattern ( (|_System.Tuple0#Equal| a@@100 b@@61))
)))
(assert (= (type Tclass._module.__default) TyType))
(assert (= (Tag Tclass._module.__default) Tagclass._module.__default))
(assert (forall ((bx@@59 T@U) ) (!  (=> (and (= (type bx@@59) BoxType) ($IsBox bx@@59 Tclass._module.__default)) (and (= ($Box ($Unbox refType bx@@59)) bx@@59) ($Is ($Unbox refType bx@@59) Tclass._module.__default)))
 :qid |fastexpb.3004:15|
 :skolemid |501|
 :pattern ( ($IsBox bx@@59 Tclass._module.__default))
)))
(assert (forall (($o@@7 T@U) ) (!  (=> (= (type $o@@7) refType) (and (=> ($Is $o@@7 Tclass._module.__default) (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default))) (=> (or (= $o@@7 null) (= (dtype $o@@7) Tclass._module.__default)) ($Is $o@@7 Tclass._module.__default))))
 :qid |fastexpb.3010:15|
 :skolemid |502|
 :pattern ( ($Is $o@@7 Tclass._module.__default))
)))
(assert (forall (($o@@8 T@U) ($h@@17 T@U) ) (!  (=> (and (= (type $o@@8) refType) (= (type $h@@17) (MapType1Type refType))) (and (=> ($IsAlloc $o@@8 Tclass._module.__default $h@@17) (or (= $o@@8 null) (U_2_bool (MapType1Select $h@@17 $o@@8 alloc)))) (=> (or (= $o@@8 null) (U_2_bool (MapType1Select $h@@17 $o@@8 alloc))) ($IsAlloc $o@@8 Tclass._module.__default $h@@17))))
 :qid |fastexpb.3016:15|
 :skolemid |503|
 :pattern ( ($IsAlloc $o@@8 Tclass._module.__default $h@@17))
)))
(assert (forall (($ly T@U) (|x#0@@1| Int) (|n#0| Int) ) (!  (=> (= (type $ly) LayerTypeType) (= (_module.__default.exp ($LS $ly) |x#0@@1| |n#0|) (_module.__default.exp $ly |x#0@@1| |n#0|)))
 :qid |fastexpb.3027:15|
 :skolemid |504|
 :pattern ( (_module.__default.exp ($LS $ly) |x#0@@1| |n#0|))
)))
(assert  (and (forall ((arg0@@162 T@U) ) (! (= (type (AsFuelBottom arg0@@162)) LayerTypeType)
 :qid |funType:AsFuelBottom|
 :pattern ( (AsFuelBottom arg0@@162))
)) (= (type $LZ) LayerTypeType)))
(assert (forall (($ly@@0 T@U) (|x#0@@2| Int) (|n#0@@0| Int) ) (!  (=> (= (type $ly@@0) LayerTypeType) (= (_module.__default.exp $ly@@0 |x#0@@2| |n#0@@0|) (_module.__default.exp $LZ |x#0@@2| |n#0@@0|)))
 :qid |fastexpb.3033:15|
 :skolemid |505|
 :pattern ( (_module.__default.exp (AsFuelBottom $ly@@0) |x#0@@2| |n#0@@0|))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@1 T@U) (|x#0@@3| Int) (|n#0@@1| Int) ) (!  (=> (and (= (type $ly@@1) LayerTypeType) (or (|_module.__default.exp#canCall| |x#0@@3| |n#0@@1|) (and (not (= 0 $FunctionContextHeight)) (>= |n#0@@1| (LitInt 0))))) true)
 :qid |fastexpb.3039:16|
 :skolemid |506|
 :pattern ( (_module.__default.exp $ly@@1 |x#0@@3| |n#0@@1|))
))))
(assert (forall (($ly@@2 T@U) (|x#0@@4| Int) (|n#0@@2| Int) ) (!  (=> (= (type $ly@@2) LayerTypeType) (and (=> (|_module.__default.exp#requires| $ly@@2 |x#0@@4| |n#0@@2|) (>= |n#0@@2| (LitInt 0))) (=> (>= |n#0@@2| (LitInt 0)) (|_module.__default.exp#requires| $ly@@2 |x#0@@4| |n#0@@2|))))
 :qid |fastexpb.3048:15|
 :skolemid |507|
 :pattern ( (|_module.__default.exp#requires| $ly@@2 |x#0@@4| |n#0@@2|))
)))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@3 T@U) (|x#0@@5| Int) (|n#0@@3| Int) ) (!  (=> (and (= (type $ly@@3) LayerTypeType) (or (|_module.__default.exp#canCall| |x#0@@5| |n#0@@3|) (and (not (= 0 $FunctionContextHeight)) (>= |n#0@@3| (LitInt 0))))) (and (=> (not (= |n#0@@3| (LitInt 0))) (|_module.__default.exp#canCall| |x#0@@5| (- |n#0@@3| 1))) (= (_module.__default.exp ($LS $ly@@3) |x#0@@5| |n#0@@3|) (ite (= |n#0@@3| (LitInt 0)) 1 (Mul |x#0@@5| (_module.__default.exp $ly@@3 |x#0@@5| (- |n#0@@3| 1)))))))
 :qid |fastexpb.3054:16|
 :skolemid |508|
 :pattern ( (_module.__default.exp ($LS $ly@@3) |x#0@@5| |n#0@@3|))
))))
(assert  (=> (<= 0 $FunctionContextHeight) (forall (($ly@@4 T@U) (|x#0@@6| Int) (|n#0@@4| Int) ) (!  (=> (and (= (type $ly@@4) LayerTypeType) (or (|_module.__default.exp#canCall| (LitInt |x#0@@6|) (LitInt |n#0@@4|)) (and (not (= 0 $FunctionContextHeight)) (>= (LitInt |n#0@@4|) (LitInt 0))))) (and (=> (not (= (LitInt |n#0@@4|) (LitInt 0))) (|_module.__default.exp#canCall| (LitInt |x#0@@6|) (LitInt (- |n#0@@4| 1)))) (= (_module.__default.exp ($LS $ly@@4) (LitInt |x#0@@6|) (LitInt |n#0@@4|)) (ite (= (LitInt |n#0@@4|) (LitInt 0)) 1 (Mul (LitInt |x#0@@6|) (LitInt (_module.__default.exp ($LS $ly@@4) (LitInt |x#0@@6|) (LitInt (- |n#0@@4| 1)))))))))
 :qid |fastexpb.3066:16|
 :weight 3
 :skolemid |509|
 :pattern ( (_module.__default.exp ($LS $ly@@4) (LitInt |x#0@@6|) (LitInt |n#0@@4|)))
))))
(assert  (and (and (and (and (and (and (and (forall ((arg0@@163 T@T) (arg1@@75 T@T) ) (! (= (Ctor (MapType4Type arg0@@163 arg1@@75)) 23)
 :qid |ctor:MapType4Type|
)) (forall ((arg0@@164 T@T) (arg1@@76 T@T) ) (! (= (MapType4TypeInv0 (MapType4Type arg0@@164 arg1@@76)) arg0@@164)
 :qid |typeInv:MapType4TypeInv0|
 :pattern ( (MapType4Type arg0@@164 arg1@@76))
))) (forall ((arg0@@165 T@T) (arg1@@77 T@T) ) (! (= (MapType4TypeInv1 (MapType4Type arg0@@165 arg1@@77)) arg1@@77)
 :qid |typeInv:MapType4TypeInv1|
 :pattern ( (MapType4Type arg0@@165 arg1@@77))
))) (forall ((arg0@@166 T@U) (arg1@@78 T@U) (arg2@@32 T@U) ) (! (let ((aVar1@@4 (MapType4TypeInv1 (type arg0@@166))))
(= (type (MapType4Select arg0@@166 arg1@@78 arg2@@32)) aVar1@@4))
 :qid |funType:MapType4Select|
 :pattern ( (MapType4Select arg0@@166 arg1@@78 arg2@@32))
))) (forall ((arg0@@167 T@U) (arg1@@79 T@U) (arg2@@33 T@U) (arg3@@12 T@U) ) (! (let ((aVar1@@5 (type arg3@@12)))
(let ((aVar0@@3 (type arg1@@79)))
(= (type (MapType4Store arg0@@167 arg1@@79 arg2@@33 arg3@@12)) (MapType4Type aVar0@@3 aVar1@@5))))
 :qid |funType:MapType4Store|
 :pattern ( (MapType4Store arg0@@167 arg1@@79 arg2@@33 arg3@@12))
))) (forall ((m@@37 T@U) (x0@@15 T@U) (x1@@12 T@U) (val@@16 T@U) ) (! (let ((aVar1@@6 (MapType4TypeInv1 (type m@@37))))
 (=> (= (type val@@16) aVar1@@6) (= (MapType4Select (MapType4Store m@@37 x0@@15 x1@@12 val@@16) x0@@15 x1@@12) val@@16)))
 :qid |mapAx0:MapType4Select|
 :weight 0
))) (and (and (forall ((val@@17 T@U) (m@@38 T@U) (x0@@16 T@U) (x1@@13 T@U) (y0@@11 T@U) (y1@@9 T@U) ) (!  (or (= x0@@16 y0@@11) (= (MapType4Select (MapType4Store m@@38 x0@@16 x1@@13 val@@17) y0@@11 y1@@9) (MapType4Select m@@38 y0@@11 y1@@9)))
 :qid |mapAx1:MapType4Select:0|
 :weight 0
)) (forall ((val@@18 T@U) (m@@39 T@U) (x0@@17 T@U) (x1@@14 T@U) (y0@@12 T@U) (y1@@10 T@U) ) (!  (or (= x1@@14 y1@@10) (= (MapType4Select (MapType4Store m@@39 x0@@17 x1@@14 val@@18) y0@@12 y1@@10) (MapType4Select m@@39 y0@@12 y1@@10)))
 :qid |mapAx1:MapType4Select:1|
 :weight 0
))) (forall ((val@@19 T@U) (m@@40 T@U) (x0@@18 T@U) (x1@@15 T@U) (y0@@13 T@U) (y1@@11 T@U) ) (!  (or true (= (MapType4Select (MapType4Store m@@40 x0@@18 x1@@15 val@@19) y0@@13 y1@@11) (MapType4Select m@@40 y0@@13 y1@@11)))
 :qid |mapAx2:MapType4Select|
 :weight 0
)))) (forall ((arg0@@168 T@U) (arg1@@80 T@U) (arg2@@34 T@U) (arg3@@13 Bool) ) (! (= (type (|lambda#0| arg0@@168 arg1@@80 arg2@@34 arg3@@13)) (MapType4Type refType boolType))
 :qid |funType:lambda#0|
 :pattern ( (|lambda#0| arg0@@168 arg1@@80 arg2@@34 arg3@@13))
))))
(assert (forall (($o@@9 T@U) ($f T@U) (|l#0| T@U) (|l#1| T@U) (|l#2| T@U) (|l#3| Bool) ) (! (let ((alpha@@6 (FieldTypeInv0 (type $f))))
 (=> (and (and (and (and (= (type $o@@9) refType) (= (type $f) (FieldType alpha@@6))) (= (type |l#0|) refType)) (= (type |l#1|) (MapType1Type refType))) (= (type |l#2|) (FieldType boolType))) (= (U_2_bool (MapType4Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@9 $f))  (=> (and (not (= $o@@9 |l#0|)) (U_2_bool (MapType1Select |l#1| $o@@9 |l#2|))) |l#3|))))
 :qid |fastexpb.3095:31|
 :skolemid |516|
 :pattern ( (MapType4Select (|lambda#0| |l#0| |l#1| |l#2| |l#3|) $o@@9 $f))
)))
(assert (forall ((arg0@@169 T@U) (arg1@@81 T@U) (arg2@@35 T@U) (arg3@@14 Bool) ) (! (= (type (|lambda#1| arg0@@169 arg1@@81 arg2@@35 arg3@@14)) (MapType4Type refType boolType))
 :qid |funType:lambda#1|
 :pattern ( (|lambda#1| arg0@@169 arg1@@81 arg2@@35 arg3@@14))
)))
(assert (forall (($o@@10 T@U) ($f@@0 T@U) (|l#0@@0| T@U) (|l#1@@0| T@U) (|l#2@@0| T@U) (|l#3@@0| Bool) ) (! (let ((alpha@@7 (FieldTypeInv0 (type $f@@0))))
 (=> (and (and (and (and (= (type $o@@10) refType) (= (type $f@@0) (FieldType alpha@@7))) (= (type |l#0@@0|) refType)) (= (type |l#1@@0|) (MapType1Type refType))) (= (type |l#2@@0|) (FieldType boolType))) (= (U_2_bool (MapType4Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))  (=> (and (not (= $o@@10 |l#0@@0|)) (U_2_bool (MapType1Select |l#1@@0| $o@@10 |l#2@@0|))) |l#3@@0|))))
 :qid |fastexpb.3104:35|
 :skolemid |517|
 :pattern ( (MapType4Select (|lambda#1| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0|) $o@@10 $f@@0))
)))
(assert (forall ((arg0@@170 T@U) (arg1@@82 T@U) (arg2@@36 T@U) (arg3@@15 Bool) ) (! (= (type (|lambda#2| arg0@@170 arg1@@82 arg2@@36 arg3@@15)) (MapType4Type refType boolType))
 :qid |funType:lambda#2|
 :pattern ( (|lambda#2| arg0@@170 arg1@@82 arg2@@36 arg3@@15))
)))
(assert (forall (($o@@11 T@U) ($f@@1 T@U) (|l#0@@1| T@U) (|l#1@@1| T@U) (|l#2@@1| T@U) (|l#3@@1| Bool) ) (! (let ((alpha@@8 (FieldTypeInv0 (type $f@@1))))
 (=> (and (and (and (and (= (type $o@@11) refType) (= (type $f@@1) (FieldType alpha@@8))) (= (type |l#0@@1|) refType)) (= (type |l#1@@1|) (MapType1Type refType))) (= (type |l#2@@1|) (FieldType boolType))) (= (U_2_bool (MapType4Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))  (=> (and (not (= $o@@11 |l#0@@1|)) (U_2_bool (MapType1Select |l#1@@1| $o@@11 |l#2@@1|))) |l#3@@1|))))
 :qid |fastexpb.3154:31|
 :skolemid |518|
 :pattern ( (MapType4Select (|lambda#2| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1|) $o@@11 $f@@1))
)))
(assert (forall ((arg0@@171 T@U) (arg1@@83 T@U) (arg2@@37 T@U) (arg3@@16 Bool) ) (! (= (type (|lambda#3| arg0@@171 arg1@@83 arg2@@37 arg3@@16)) (MapType4Type refType boolType))
 :qid |funType:lambda#3|
 :pattern ( (|lambda#3| arg0@@171 arg1@@83 arg2@@37 arg3@@16))
)))
(assert (forall (($o@@12 T@U) ($f@@2 T@U) (|l#0@@2| T@U) (|l#1@@2| T@U) (|l#2@@2| T@U) (|l#3@@2| Bool) ) (! (let ((alpha@@9 (FieldTypeInv0 (type $f@@2))))
 (=> (and (and (and (and (= (type $o@@12) refType) (= (type $f@@2) (FieldType alpha@@9))) (= (type |l#0@@2|) refType)) (= (type |l#1@@2|) (MapType1Type refType))) (= (type |l#2@@2|) (FieldType boolType))) (= (U_2_bool (MapType4Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))  (=> (and (not (= $o@@12 |l#0@@2|)) (U_2_bool (MapType1Select |l#1@@2| $o@@12 |l#2@@2|))) |l#3@@2|))))
 :qid |fastexpb.3230:31|
 :skolemid |519|
 :pattern ( (MapType4Select (|lambda#3| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2|) $o@@12 $f@@2))
)))
(declare-fun $Heap () T@U)
(declare-fun $_Frame@1 () T@U)
(declare-fun $_Frame@0 () T@U)
(declare-fun %lbl%+0 () Bool)
(declare-fun %lbl%@1 () Bool)
(declare-fun |b$reqreads#0@1| () Bool)
(declare-fun %lbl%+2 () Bool)
(declare-fun |n#0@@5| () Int)
(declare-fun |x#0@@7| () Int)
(declare-fun |##n#0@0| () Int)
(declare-fun %lbl%@3 () Bool)
(declare-fun |b$reqreads#0@0| () Bool)
(declare-fun %lbl%@4 () Bool)
(declare-fun %lbl%@5 () Bool)
(declare-fun %lbl%@6 () Bool)
(declare-fun %lbl%+7 () Bool)
(declare-fun %lbl%+8 () Bool)
(declare-fun %lbl%+9 () Bool)
(declare-fun %lbl%+10 () Bool)
(declare-fun %lbl%+11 () Bool)
(declare-fun $IsHeapAnchor (T@U) Bool)
(assert  (and (and (= (type $Heap) (MapType1Type refType)) (= (type $_Frame@1) (MapType4Type refType boolType))) (= (type $_Frame@0) (MapType4Type refType boolType))))
(push 1)
(set-info :boogie-vc-id CheckWellformed$$_module.__default.exp)
(assert (not
(let ((anon5_correct  (=> (! (and %lbl%+0 true) :lblpos +0) (! (or %lbl%@1 |b$reqreads#0@1|) :lblneg @1))))
(let ((anon7_Else_correct  (=> (! (and %lbl%+2 true) :lblpos +2) (=> (and (and (not (= |n#0@@5| (LitInt 0))) ($IsAlloc (int_2_U |x#0@@7|) TInt $Heap)) (and (= |##n#0@0| (- |n#0@@5| 1)) ($IsAlloc (int_2_U |##n#0@0|) TInt $Heap))) (and (! (or %lbl%@3 (>= |##n#0@0| (LitInt 0))) :lblneg @3) (=> (>= |##n#0@0| (LitInt 0)) (=> (and (=> |b$reqreads#0@0| (forall (($o@@13 T@U) ($f@@3 T@U) ) (! (let ((alpha@@10 (FieldTypeInv0 (type $f@@3))))
 (=> (and (and (= (type $o@@13) refType) (= (type $f@@3) (FieldType alpha@@10))) false) (U_2_bool (MapType4Select $_Frame@1 $o@@13 $f@@3))))
 :qid |fastexpb.3123:44|
 :skolemid |510|
 :no-pattern (type $o@@13)
 :no-pattern (type $f@@3)
 :no-pattern (U_2_int $o@@13)
 :no-pattern (U_2_bool $o@@13)
 :no-pattern (U_2_int $f@@3)
 :no-pattern (U_2_bool $f@@3)
))) (=> (forall (($o@@14 T@U) ($f@@4 T@U) ) (! (let ((alpha@@11 (FieldTypeInv0 (type $f@@4))))
 (=> (and (and (= (type $o@@14) refType) (= (type $f@@4) (FieldType alpha@@11))) false) (U_2_bool (MapType4Select $_Frame@1 $o@@14 $f@@4))))
 :qid |fastexpb.3123:44|
 :skolemid |510|
 :no-pattern (type $o@@14)
 :no-pattern (type $f@@4)
 :no-pattern (U_2_int $o@@14)
 :no-pattern (U_2_bool $o@@14)
 :no-pattern (U_2_int $f@@4)
 :no-pattern (U_2_bool $f@@4)
)) |b$reqreads#0@0|)) (and (! (or %lbl%@4  (or (<= 0 |x#0@@7|) (= |x#0@@7| |x#0@@7|))) :lblneg @4) (=> (or (<= 0 |x#0@@7|) (= |x#0@@7| |x#0@@7|)) (and (! (or %lbl%@5  (or (or (<= 0 |n#0@@5|) (< |x#0@@7| |x#0@@7|)) (= |##n#0@0| |n#0@@5|))) :lblneg @5) (=> (or (or (<= 0 |n#0@@5|) (< |x#0@@7| |x#0@@7|)) (= |##n#0@0| |n#0@@5|)) (and (! (or %lbl%@6  (or (< |x#0@@7| |x#0@@7|) (and (= |x#0@@7| |x#0@@7|) (< |##n#0@0| |n#0@@5|)))) :lblneg @6) (=> (or (< |x#0@@7| |x#0@@7|) (and (= |x#0@@7| |x#0@@7|) (< |##n#0@0| |n#0@@5|))) (=> (and (|_module.__default.exp#canCall| |x#0@@7| (- |n#0@@5| 1)) (= (_module.__default.exp ($LS $LZ) |x#0@@7| |n#0@@5|) (Mul |x#0@@7| (_module.__default.exp ($LS $LZ) |x#0@@7| (- |n#0@@5| 1))))) (=> (and (and (|_module.__default.exp#canCall| |x#0@@7| (- |n#0@@5| 1)) ($Is (int_2_U (_module.__default.exp ($LS $LZ) |x#0@@7| |n#0@@5|)) TInt)) (and (=> |b$reqreads#0@1| |b$reqreads#0@0|) (=> |b$reqreads#0@0| |b$reqreads#0@1|))) anon5_correct)))))))))))))))
(let ((anon7_Then_correct  (=> (! (and %lbl%+7 true) :lblpos +7) (=> (= |n#0@@5| (LitInt 0)) (=> (and (and (= (_module.__default.exp ($LS $LZ) |x#0@@7| |n#0@@5|) (LitInt 1)) ($Is (int_2_U (_module.__default.exp ($LS $LZ) |x#0@@7| |n#0@@5|)) TInt)) (and (=> |b$reqreads#0@1| true) (=> true |b$reqreads#0@1|))) anon5_correct)))))
(let ((anon6_Else_correct  (=> (! (and %lbl%+8 true) :lblpos +8) (=> (= $_Frame@1 (|lambda#1| null $Heap alloc false)) (and anon7_Then_correct anon7_Else_correct)))))
(let ((anon6_Then_correct  (=> (! (and %lbl%+9 true) :lblpos +9) true)))
(let ((anon0_correct  (=> (! (and %lbl%+10 true) :lblpos +10) (=> (and (= $_Frame@0 (|lambda#0| null $Heap alloc false)) (>= |n#0@@5| (LitInt 0))) (and anon6_Then_correct anon6_Else_correct)))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+11 true) :lblpos +11) (=> (and (and ($IsGoodHeap $Heap) ($IsHeapAnchor $Heap)) (= 0 $FunctionContextHeight)) anon0_correct))))
PreconditionGeneratedEntry_correct)))))))
))
(push 1)
(check-sat)