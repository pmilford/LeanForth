\ The guard table of Lean 4.35.0's default simprocs whose action is not
\ ported (review of simp group 4, B1): one row for each simproc of Init's
\ default set that has neither a port (simprocs/core.fs, simprocs/nat.fs)
\ nor a named guard (simp/simprocs.fs), with Lean's declaration (src/lean/
\ Lean/Meta/Tactic/Simp/BuiltinSimprocs/FILE:LINE, and the macro's use for
\ UInt.lean's and SInt.lean's) and the helper its body is (body: its own).
\ Each body was read for this table (2026-11-26):
\ - sp-lit-...: the body answers .continue unless every explicit operand
\   that is no proof passes its family's fromExpr? (getNatValue?,
\   getOfNatValue?, getIntValue?, getFinValue?, getBitVecValue?,
\   getCharValue?, getStringValue?, Meta/LitValues.lean): reduceUnary,
\   reduceBin, reduceBinPred, reduceBoolPred, reduceBinIntNatOp,
\   reduceNatCore, reduceNatOp, reduceOp, reduceExtend, reduceGetBit,
\   reduceShift and the bodies read so; a body that also reads an
\   implicit argument (Fin.castLT's n, castLE's m, setWidth''s w,
\   BitVec.ofFin's w) fires on fewer terms, which the guard answers
\   unsupported too. BitVec.reduceOfNat fires on a non-literal width only
\   when bitVecOfNat is false (not by-simp's setting); Int.reduceNeg and
\   the Int8-64 reduceNeg fire on any OfNat.ofNat operand, a literal's
\   head.
\ - sp-crude-...: the body fires where an explicit operand has no
\   literal's form: unsupported whenever the keys match.
\ The phase and kind (d a dsimproc, s a simproc, pre the arrow) are the
\ declaration's; a record of another phase or kind is unsupported
\ (simprocs.fs's sp-fitting). tests/front/tactics/simp-procs/test.fs
\ checks the rows against tests/front/simp-data/init-simprocs.txt, Init's
\ 341 simproc records, each with one row; make reference-simp-init checks
\ that list against the data it writes. Untrusted, as simprocs.fs; no
\ state but the rows, laid while loading.

require ../simprocs.fs

\ ---- Array.lean
sp-crude-d: Array.reduceGetElem          \ Array.lean:18 getArrayLit?: an array
sp-crude-d: Array.reduceGetElem!         \ Array.lean:35 getArrayLit?: an array
sp-crude-d: Array.reduceGetElem?         \ Array.lean:26 getArrayLit?: an array

\ ---- BitVec.lean
sp-lit-d: BitVec.isValue                 \ BitVec.lean:313 body
sp-lit-d: BitVec.reduceAbs               \ BitVec.lean:135 reduceUnary
sp-lit-d: BitVec.reduceAdd               \ BitVec.lean:147 reduceBin
sp-lit-d: BitVec.reduceAllOnes           \ BitVec.lean:425 body
sp-lit-d: BitVec.reduceAnd               \ BitVec.lean:138 reduceBin
sp-lit-d: BitVec.reduceAppend            \ BitVec.lean:242 body
sp-lit-d: BitVec.reduceBEq               \ BitVec.lean:329 reduceBoolPred
sp-lit-d: BitVec.reduceBNe               \ BitVec.lean:333 reduceBoolPred
sp-lit-d: BitVec.reduceBitVecOfFin       \ BitVec.lean:431 body
sp-lit-d: BitVec.reduceBitVecToFin       \ BitVec.lean:438 body
sp-lit-d: BitVec.reduceCast              \ BitVec.lean:250 body
sp-lit-d: BitVec.reduceClz               \ BitVec.lean:189 reduceUnary
sp-lit-d: BitVec.reduceCpop              \ BitVec.lean:192 reduceUnary
sp-lit-d: BitVec.reduceDiv               \ BitVec.lean:156 reduceBin
sp-lit-s: BitVec.reduceEq                \ BitVec.lean:323 reduceBinPred
sp-lit-d: BitVec.reduceExtractLsb        \ BitVec.lean:396 body
sp-lit-d: BitVec.reduceExtractLsb'       \ BitVec.lean:387 body
sp-lit-s: BitVec.reduceGE                \ BitVec.lean:347 reduceBinPred
sp-lit-s: BitVec.reduceGT                \ BitVec.lean:344 reduceBinPred
sp-lit-d: BitVec.reduceGetElem           \ BitVec.lean:196 body
sp-lit-d: BitVec.reduceGetLsb            \ BitVec.lean:183 reduceGetBit
sp-lit-d: BitVec.reduceGetMsb            \ BitVec.lean:186 reduceGetBit
sp-lit-d: BitVec.reduceHShiftLeft        \ BitVec.lean:217 reduceShift
sp-lit-d: BitVec.reduceHShiftRight       \ BitVec.lean:225 reduceShift
sp-lit-s: BitVec.reduceLE                \ BitVec.lean:341 reduceBinPred
sp-lit-s: BitVec.reduceLT                \ BitVec.lean:338 reduceBinPred
sp-lit-d: BitVec.reduceMod               \ BitVec.lean:159 reduceBin
sp-lit-d: BitVec.reduceMul               \ BitVec.lean:150 reduceBin
sp-lit-s: BitVec.reduceNe                \ BitVec.lean:326 reduceBinPred
sp-lit-d: BitVec.reduceNeg               \ BitVec.lean:128 reduceUnary
sp-lit-d: BitVec.reduceNot               \ BitVec.lean:131 reduceUnary
sp-lit-d: BitVec.reduceOfInt             \ BitVec.lean:272 body
sp-lit-d: BitVec.reduceOfNat             \ BitVec.lean:288 body
sp-lit-d: BitVec.reduceOfNatClamp        \ BitVec.lean:280 body
sp-lit-d: BitVec.reduceOr                \ BitVec.lean:141 reduceBin
sp-lit-d: BitVec.reduceReplicate         \ BitVec.lean:405 body
sp-lit-d: BitVec.reduceRotateLeft        \ BitVec.lean:233 reduceShift
sp-lit-d: BitVec.reduceRotateRight       \ BitVec.lean:237 reduceShift
sp-lit-d: BitVec.reduceSDiv              \ BitVec.lean:177 reduceBin
sp-lit-d: BitVec.reduceSLE               \ BitVec.lean:363 reduceBoolPred
sp-lit-d: BitVec.reduceSLT               \ BitVec.lean:359 reduceBoolPred
sp-lit-d: BitVec.reduceSMTSDiv           \ BitVec.lean:180 reduceBin
sp-lit-d: BitVec.reduceSMTUDiv           \ BitVec.lean:168 reduceBin
sp-lit-d: BitVec.reduceSMod              \ BitVec.lean:171 reduceBin
sp-lit-d: BitVec.reduceSRem              \ BitVec.lean:174 reduceBin
sp-lit-d: BitVec.reduceSShiftRight       \ BitVec.lean:213 reduceShift
sp-lit-d: BitVec.reduceSetWidth          \ BitVec.lean:413 reduceExtend
sp-lit-d: BitVec.reduceSetWidth'         \ BitVec.lean:368 body
sp-lit-d: BitVec.reduceShiftLeft         \ BitVec.lean:205 reduceShift
sp-lit-d: BitVec.reduceShiftLeftZeroExtend \ BitVec.lean:379 body
sp-lit-d: BitVec.reduceSignExtend        \ BitVec.lean:421 reduceExtend
sp-lit-d: BitVec.reduceSub               \ BitVec.lean:153 reduceBin
sp-lit-d: BitVec.reduceToInt             \ BitVec.lean:265 body
sp-lit-d: BitVec.reduceToNat             \ BitVec.lean:258 body
sp-lit-d: BitVec.reduceUDiv              \ BitVec.lean:165 reduceBin
sp-lit-d: BitVec.reduceULE               \ BitVec.lean:355 reduceBoolPred
sp-lit-d: BitVec.reduceULT               \ BitVec.lean:351 reduceBoolPred
sp-lit-d: BitVec.reduceUMod              \ BitVec.lean:162 reduceBin
sp-lit-d: BitVec.reduceUShiftRight       \ BitVec.lean:209 reduceShift
sp-lit-d: BitVec.reduceXOr               \ BitVec.lean:144 reduceBin
sp-lit-d: BitVec.reduceZeroExtend        \ BitVec.lean:417 reduceExtend

\ ---- Char.lean
sp-lit-d-pre: Char.isValue               \ Char.lean:95 body
sp-lit-d: Char.reduceBEq                 \ Char.lean:81 reduceBoolPred
sp-lit-d: Char.reduceBNe                 \ Char.lean:83 reduceBoolPred
sp-crude-d: Char.reduceDefault           \ Char.lean:106 no explicit operand
sp-lit-s: Char.reduceEq                  \ Char.lean:77 reduceBinPred
sp-lit-s: Char.reduceGE                  \ Char.lean:75 reduceBinPred
sp-lit-s: Char.reduceGT                  \ Char.lean:73 reduceBinPred
sp-lit-d: Char.reduceIsAlpha             \ Char.lean:55 reduceUnary
sp-lit-d: Char.reduceIsAlphaNum          \ Char.lean:59 reduceUnary
sp-lit-d: Char.reduceIsDigit             \ Char.lean:57 reduceUnary
sp-lit-d: Char.reduceIsLower             \ Char.lean:53 reduceUnary
sp-lit-d: Char.reduceIsUpper             \ Char.lean:51 reduceUnary
sp-lit-d: Char.reduceIsWhitespace        \ Char.lean:49 reduceUnary
sp-lit-s: Char.reduceLE                  \ Char.lean:71 reduceBinPred
sp-lit-s: Char.reduceLT                  \ Char.lean:69 reduceBinPred
sp-lit-s: Char.reduceNe                  \ Char.lean:79 reduceBinPred
sp-lit-d: Char.reduceOfNatAux            \ Char.lean:100 body
sp-lit-d: Char.reduceToLower             \ Char.lean:43 reduceUnary
sp-lit-d: Char.reduceToNat               \ Char.lean:47 reduceUnary
sp-lit-d: Char.reduceToString            \ Char.lean:61 reduceUnary
sp-lit-d: Char.reduceToUpper             \ Char.lean:45 reduceUnary
sp-lit-d: Char.reduceVal                 \ Char.lean:63 body

\ ---- Fin.lean
sp-lit-d: Fin.isValue                    \ Fin.lean:120 body
sp-lit-d: Fin.reduceAdd                  \ Fin.lean:73 reduceBin
sp-lit-d: Fin.reduceAddNat               \ Fin.lean:162 body
sp-lit-d: Fin.reduceAnd                  \ Fin.lean:90 reduceBin
sp-lit-d: Fin.reduceBEq                  \ Fin.lean:114 reduceBoolPred
sp-lit-d: Fin.reduceBNe                  \ Fin.lean:116 reduceBoolPred
sp-lit-d: Fin.reduceCastAdd              \ Fin.lean:155 body
sp-lit-d: Fin.reduceCastLE               \ Fin.lean:186 body
sp-lit-d: Fin.reduceCastLT               \ Fin.lean:176 body
sp-lit-d: Fin.reduceCastSucc             \ Fin.lean:149 body
sp-lit-d: Fin.reduceDiv                  \ Fin.lean:79 reduceBin
sp-lit-s: Fin.reduceEq                   \ Fin.lean:110 reduceBinPred
sp-lit-d: Fin.reduceFinMk                \ Fin.lean:131 body
sp-lit-s: Fin.reduceGE                   \ Fin.lean:108 reduceBinPred
sp-lit-s: Fin.reduceGT                   \ Fin.lean:106 reduceBinPred
sp-lit-s: Fin.reduceLE                   \ Fin.lean:104 reduceBinPred
sp-lit-s: Fin.reduceLT                   \ Fin.lean:102 reduceBinPred
sp-lit-d: Fin.reduceLast                 \ Fin.lean:70 reduceNatOp
sp-lit-d: Fin.reduceMod                  \ Fin.lean:81 reduceBin
sp-lit-d: Fin.reduceMul                  \ Fin.lean:75 reduceBin
sp-lit-d: Fin.reduceNatAdd               \ Fin.lean:169 body
sp-lit-s: Fin.reduceNe                   \ Fin.lean:112 reduceBinPred
sp-lit-d: Fin.reduceOfNat                \ Fin.lean:142 body
sp-lit-d: Fin.reduceOr                   \ Fin.lean:92 reduceBin
sp-lit-d: Fin.reducePow                  \ Fin.lean:83 body
sp-lit-d: Fin.reducePred                 \ Fin.lean:208 body
sp-lit-d: Fin.reduceRev                  \ Fin.lean:68 reduceOp
sp-lit-d: Fin.reduceShiftLeft            \ Fin.lean:97 reduceBin
sp-lit-d: Fin.reduceShiftRight           \ Fin.lean:99 reduceBin
sp-lit-d: Fin.reduceSub                  \ Fin.lean:77 reduceBin
sp-lit-d: Fin.reduceSubNat               \ Fin.lean:198 body
sp-lit-d: Fin.reduceSucc                 \ Fin.lean:66 reduceOp
sp-lit-d: Fin.reduceXor                  \ Fin.lean:94 reduceBin

\ ---- Int.lean
sp-lit-d: Int.reduceAbs                  \ Int.lean:128 reduceNatCore
sp-lit-d: Int.reduceAdd                  \ Int.lean:74 reduceBin
sp-lit-d: Int.reduceBEq                  \ Int.lean:118 reduceBoolPred
sp-lit-d: Int.reduceBNe                  \ Int.lean:120 reduceBoolPred
sp-lit-d: Int.reduceBdiv                 \ Int.lean:92 reduceBinIntNatOp
sp-lit-d: Int.reduceBmod                 \ Int.lean:94 reduceBinIntNatOp
sp-lit-d: Int.reduceDiv                  \ Int.lean:80 reduceBin
sp-lit-s: Int.reduceDvd                  \ Int.lean:145 body
sp-lit-s: Int.reduceEq                   \ Int.lean:114 reduceBinPred
sp-lit-d: Int.reduceFDiv                 \ Int.lean:88 reduceBin
sp-lit-d: Int.reduceFMod                 \ Int.lean:90 reduceBin
sp-lit-s: Int.reduceGE                   \ Int.lean:112 reduceBinPred
sp-lit-s: Int.reduceGT                   \ Int.lean:110 reduceBinPred
sp-lit-s: Int.reduceLE                   \ Int.lean:108 reduceBinPred
sp-lit-s: Int.reduceLT                   \ Int.lean:106 reduceBinPred
sp-lit-d: Int.reduceMod                  \ Int.lean:82 reduceBin
sp-lit-d: Int.reduceMul                  \ Int.lean:76 reduceBin
sp-lit-d: Int.reduceNatCast              \ Int.lean:161 body
sp-lit-d: Int.reduceNatCast'             \ Int.lean:166 body
sp-lit-s: Int.reduceNe                   \ Int.lean:116 reduceBinPred
sp-lit-d: Int.reduceNeg                  \ Int.lean:58 body
sp-lit-d: Int.reduceNegSucc              \ Int.lean:133 body
sp-lit-d: Int.reduceOfNat                \ Int.lean:139 body
sp-lit-d: Int.reducePow                  \ Int.lean:97 body
sp-lit-d: Int.reduceSub                  \ Int.lean:78 reduceBin
sp-lit-d: Int.reduceTDiv                 \ Int.lean:84 reduceBin
sp-lit-d: Int.reduceTMod                 \ Int.lean:86 reduceBin
sp-lit-d: Int.reduceToNat                \ Int.lean:130 reduceNatCore

\ ---- List.lean
sp-crude-d: List.reduceReplicate         \ List.lean:20 only n read: x any

\ ---- Nat.lean
sp-lit-s: Nat.reduceDvd                  \ Nat.lean:401 body
sp-lit-d: Nat.reduceLog2                 \ Nat.lean:54 reduceUnary
sp-lit-d: Nat.reducePowMod               \ Nat.lean:83 body

\ ---- SInt.lean
sp-lit-s: ISize.reduceToInt              \ SInt.lean:153 body
sp-lit-s: ISize.reduceToNatClampNeg      \ SInt.lean:135 body
sp-lit-d: Int16.reduceAdd                \ SInt.lean:62 (122) reduceBin
sp-lit-d: Int16.reduceBEq                \ SInt.lean:74 (122) reduceBoolPred
sp-lit-d: Int16.reduceBNe                \ SInt.lean:75 (122) reduceBoolPred
sp-lit-d: Int16.reduceDiv                \ SInt.lean:65 (122) reduceBin
sp-lit-s: Int16.reduceEq                 \ SInt.lean:72 (122) reduceBinPred
sp-lit-s: Int16.reduceGE                 \ SInt.lean:71 (122) reduceBinPred
sp-lit-s: Int16.reduceGT                 \ SInt.lean:70 (122) reduceBinPred
sp-lit-s: Int16.reduceLE                 \ SInt.lean:69 (122) reduceBinPred
sp-lit-s: Int16.reduceLT                 \ SInt.lean:68 (122) reduceBinPred
sp-lit-d: Int16.reduceMod                \ SInt.lean:66 (122) reduceBin
sp-lit-d: Int16.reduceMul                \ SInt.lean:63 (122) reduceBin
sp-lit-s: Int16.reduceNe                 \ SInt.lean:73 (122) reduceBinPred
sp-lit-d: Int16.reduceNeg                \ SInt.lean:53 (122) body
sp-lit-d: Int16.reduceOfInt              \ SInt.lean:89 (122) body
sp-lit-d: Int16.reduceOfIntLE            \ SInt.lean:77 (122) body
sp-lit-d: Int16.reduceOfNat              \ SInt.lean:83 (122) body
sp-lit-d: Int16.reduceSub                \ SInt.lean:64 (122) reduceBin
sp-lit-d: Int16.reduceToInt              \ SInt.lean:95 (122) body
sp-lit-d: Int16.reduceToNatClampNeg      \ SInt.lean:101 (122) body
sp-lit-d: Int32.reduceAdd                \ SInt.lean:62 (124) reduceBin
sp-lit-d: Int32.reduceBEq                \ SInt.lean:74 (124) reduceBoolPred
sp-lit-d: Int32.reduceBNe                \ SInt.lean:75 (124) reduceBoolPred
sp-lit-d: Int32.reduceDiv                \ SInt.lean:65 (124) reduceBin
sp-lit-s: Int32.reduceEq                 \ SInt.lean:72 (124) reduceBinPred
sp-lit-s: Int32.reduceGE                 \ SInt.lean:71 (124) reduceBinPred
sp-lit-s: Int32.reduceGT                 \ SInt.lean:70 (124) reduceBinPred
sp-lit-s: Int32.reduceLE                 \ SInt.lean:69 (124) reduceBinPred
sp-lit-s: Int32.reduceLT                 \ SInt.lean:68 (124) reduceBinPred
sp-lit-d: Int32.reduceMod                \ SInt.lean:66 (124) reduceBin
sp-lit-d: Int32.reduceMul                \ SInt.lean:63 (124) reduceBin
sp-lit-s: Int32.reduceNe                 \ SInt.lean:73 (124) reduceBinPred
sp-lit-d: Int32.reduceNeg                \ SInt.lean:53 (124) body
sp-lit-d: Int32.reduceOfInt              \ SInt.lean:89 (124) body
sp-lit-d: Int32.reduceOfIntLE            \ SInt.lean:77 (124) body
sp-lit-d: Int32.reduceOfNat              \ SInt.lean:83 (124) body
sp-lit-d: Int32.reduceSub                \ SInt.lean:64 (124) reduceBin
sp-lit-d: Int32.reduceToInt              \ SInt.lean:95 (124) body
sp-lit-d: Int32.reduceToNatClampNeg      \ SInt.lean:101 (124) body
sp-lit-d: Int64.reduceAdd                \ SInt.lean:62 (126) reduceBin
sp-lit-d: Int64.reduceBEq                \ SInt.lean:74 (126) reduceBoolPred
sp-lit-d: Int64.reduceBNe                \ SInt.lean:75 (126) reduceBoolPred
sp-lit-d: Int64.reduceDiv                \ SInt.lean:65 (126) reduceBin
sp-lit-s: Int64.reduceEq                 \ SInt.lean:72 (126) reduceBinPred
sp-lit-s: Int64.reduceGE                 \ SInt.lean:71 (126) reduceBinPred
sp-lit-s: Int64.reduceGT                 \ SInt.lean:70 (126) reduceBinPred
sp-lit-s: Int64.reduceLE                 \ SInt.lean:69 (126) reduceBinPred
sp-lit-s: Int64.reduceLT                 \ SInt.lean:68 (126) reduceBinPred
sp-lit-d: Int64.reduceMod                \ SInt.lean:66 (126) reduceBin
sp-lit-d: Int64.reduceMul                \ SInt.lean:63 (126) reduceBin
sp-lit-s: Int64.reduceNe                 \ SInt.lean:73 (126) reduceBinPred
sp-lit-d: Int64.reduceNeg                \ SInt.lean:53 (126) body
sp-lit-d: Int64.reduceOfInt              \ SInt.lean:89 (126) body
sp-lit-d: Int64.reduceOfIntLE            \ SInt.lean:77 (126) body
sp-lit-d: Int64.reduceOfNat              \ SInt.lean:83 (126) body
sp-lit-d: Int64.reduceSub                \ SInt.lean:64 (126) reduceBin
sp-lit-d: Int64.reduceToInt              \ SInt.lean:95 (126) body
sp-lit-d: Int64.reduceToNatClampNeg      \ SInt.lean:101 (126) body
sp-lit-d: Int8.reduceAdd                 \ SInt.lean:62 (120) reduceBin
sp-lit-d: Int8.reduceBEq                 \ SInt.lean:74 (120) reduceBoolPred
sp-lit-d: Int8.reduceBNe                 \ SInt.lean:75 (120) reduceBoolPred
sp-lit-d: Int8.reduceDiv                 \ SInt.lean:65 (120) reduceBin
sp-lit-s: Int8.reduceEq                  \ SInt.lean:72 (120) reduceBinPred
sp-lit-s: Int8.reduceGE                  \ SInt.lean:71 (120) reduceBinPred
sp-lit-s: Int8.reduceGT                  \ SInt.lean:70 (120) reduceBinPred
sp-lit-s: Int8.reduceLE                  \ SInt.lean:69 (120) reduceBinPred
sp-lit-s: Int8.reduceLT                  \ SInt.lean:68 (120) reduceBinPred
sp-lit-d: Int8.reduceMod                 \ SInt.lean:66 (120) reduceBin
sp-lit-d: Int8.reduceMul                 \ SInt.lean:63 (120) reduceBin
sp-lit-s: Int8.reduceNe                  \ SInt.lean:73 (120) reduceBinPred
sp-lit-d: Int8.reduceNeg                 \ SInt.lean:53 (120) body
sp-lit-d: Int8.reduceOfInt               \ SInt.lean:89 (120) body
sp-lit-d: Int8.reduceOfIntLE             \ SInt.lean:77 (120) body
sp-lit-d: Int8.reduceOfNat               \ SInt.lean:83 (120) body
sp-lit-d: Int8.reduceSub                 \ SInt.lean:64 (120) reduceBin
sp-lit-d: Int8.reduceToInt               \ SInt.lean:95 (120) body
sp-lit-d: Int8.reduceToNatClampNeg       \ SInt.lean:101 (120) body

\ ---- Simproc.lean
sp-crude-d: Lean.Meta.Grind.Arith.normPowRatInt \ Grind/Arith/Simproc.lean:190 a / b

\ ---- String.lean
sp-lit-d: String.reduceAppend            \ String.lean:21 body
sp-lit-d: String.reduceBEq               \ String.lean:103 reduceBoolPred
sp-lit-d: String.reduceBNe               \ String.lean:105 reduceBoolPred
sp-lit-s: String.reduceEq                \ String.lean:90 body
sp-lit-s: String.reduceGE                \ String.lean:87 reduceBinPred
sp-lit-s: String.reduceGT                \ String.lean:85 reduceBinPred
sp-lit-s: String.reduceLE                \ String.lean:83 reduceBinPred
sp-lit-s: String.reduceLT                \ String.lean:81 reduceBinPred
sp-lit-s: String.reduceNe                \ String.lean:97 body
sp-lit-d: String.reduceOfList            \ String.lean:37 body
sp-lit-d: String.reducePush              \ String.lean:48 body
sp-lit-d: String.reduceSingleton         \ String.lean:55 body
sp-lit-d: String.reduceToList            \ String.lean:42 body

\ ---- UInt.lean
sp-lit-d: UInt16.reduceAdd               \ UInt.lean:48 (96) reduceBin
sp-lit-d: UInt16.reduceBEq               \ UInt.lean:60 (96) reduceBoolPred
sp-lit-d: UInt16.reduceBNe               \ UInt.lean:61 (96) reduceBoolPred
sp-lit-d: UInt16.reduceDiv               \ UInt.lean:51 (96) reduceBin
sp-lit-s: UInt16.reduceEq                \ UInt.lean:58 (96) reduceBinPred
sp-lit-s: UInt16.reduceGE                \ UInt.lean:57 (96) reduceBinPred
sp-lit-s: UInt16.reduceGT                \ UInt.lean:56 (96) reduceBinPred
sp-lit-s: UInt16.reduceLE                \ UInt.lean:55 (96) reduceBinPred
sp-lit-s: UInt16.reduceLT                \ UInt.lean:54 (96) reduceBinPred
sp-lit-d: UInt16.reduceMod               \ UInt.lean:52 (96) reduceBin
sp-lit-d: UInt16.reduceMul               \ UInt.lean:49 (96) reduceBin
sp-lit-s: UInt16.reduceNe                \ UInt.lean:59 (96) reduceBinPred
sp-lit-d: UInt16.reduceOfNat             \ UInt.lean:69 (96) body
sp-lit-d: UInt16.reduceOfNatLT           \ UInt.lean:63 (96) body
sp-lit-d: UInt16.reduceSub               \ UInt.lean:50 (96) reduceBin
sp-lit-d: UInt16.reduceToNat             \ UInt.lean:75 (96) body
sp-lit-d: UInt32.reduceAdd               \ UInt.lean:48 (98) reduceBin
sp-lit-d: UInt32.reduceBEq               \ UInt.lean:60 (98) reduceBoolPred
sp-lit-d: UInt32.reduceBNe               \ UInt.lean:61 (98) reduceBoolPred
sp-lit-d: UInt32.reduceDiv               \ UInt.lean:51 (98) reduceBin
sp-lit-s: UInt32.reduceEq                \ UInt.lean:58 (98) reduceBinPred
sp-lit-s: UInt32.reduceGE                \ UInt.lean:57 (98) reduceBinPred
sp-lit-s: UInt32.reduceGT                \ UInt.lean:56 (98) reduceBinPred
sp-lit-s: UInt32.reduceLE                \ UInt.lean:55 (98) reduceBinPred
sp-lit-s: UInt32.reduceLT                \ UInt.lean:54 (98) reduceBinPred
sp-lit-d: UInt32.reduceMod               \ UInt.lean:52 (98) reduceBin
sp-lit-d: UInt32.reduceMul               \ UInt.lean:49 (98) reduceBin
sp-lit-s: UInt32.reduceNe                \ UInt.lean:59 (98) reduceBinPred
sp-lit-d: UInt32.reduceOfNat             \ UInt.lean:69 (98) body
sp-lit-d: UInt32.reduceOfNatLT           \ UInt.lean:63 (98) body
sp-lit-d: UInt32.reduceSub               \ UInt.lean:50 (98) reduceBin
sp-lit-d: UInt32.reduceToNat             \ UInt.lean:75 (98) body
sp-lit-d: UInt64.reduceAdd               \ UInt.lean:48 (100) reduceBin
sp-lit-d: UInt64.reduceBEq               \ UInt.lean:60 (100) reduceBoolPred
sp-lit-d: UInt64.reduceBNe               \ UInt.lean:61 (100) reduceBoolPred
sp-lit-d: UInt64.reduceDiv               \ UInt.lean:51 (100) reduceBin
sp-lit-s: UInt64.reduceEq                \ UInt.lean:58 (100) reduceBinPred
sp-lit-s: UInt64.reduceGE                \ UInt.lean:57 (100) reduceBinPred
sp-lit-s: UInt64.reduceGT                \ UInt.lean:56 (100) reduceBinPred
sp-lit-s: UInt64.reduceLE                \ UInt.lean:55 (100) reduceBinPred
sp-lit-s: UInt64.reduceLT                \ UInt.lean:54 (100) reduceBinPred
sp-lit-d: UInt64.reduceMod               \ UInt.lean:52 (100) reduceBin
sp-lit-d: UInt64.reduceMul               \ UInt.lean:49 (100) reduceBin
sp-lit-s: UInt64.reduceNe                \ UInt.lean:59 (100) reduceBinPred
sp-lit-d: UInt64.reduceOfNat             \ UInt.lean:69 (100) body
sp-lit-d: UInt64.reduceOfNatLT           \ UInt.lean:63 (100) body
sp-lit-d: UInt64.reduceSub               \ UInt.lean:50 (100) reduceBin
sp-lit-d: UInt64.reduceToNat             \ UInt.lean:75 (100) body
sp-lit-d: UInt8.reduceAdd                \ UInt.lean:48 (94) reduceBin
sp-lit-d: UInt8.reduceBEq                \ UInt.lean:60 (94) reduceBoolPred
sp-lit-d: UInt8.reduceBNe                \ UInt.lean:61 (94) reduceBoolPred
sp-lit-d: UInt8.reduceDiv                \ UInt.lean:51 (94) reduceBin
sp-lit-s: UInt8.reduceEq                 \ UInt.lean:58 (94) reduceBinPred
sp-lit-s: UInt8.reduceGE                 \ UInt.lean:57 (94) reduceBinPred
sp-lit-s: UInt8.reduceGT                 \ UInt.lean:56 (94) reduceBinPred
sp-lit-s: UInt8.reduceLE                 \ UInt.lean:55 (94) reduceBinPred
sp-lit-s: UInt8.reduceLT                 \ UInt.lean:54 (94) reduceBinPred
sp-lit-d: UInt8.reduceMod                \ UInt.lean:52 (94) reduceBin
sp-lit-d: UInt8.reduceMul                \ UInt.lean:49 (94) reduceBin
sp-lit-s: UInt8.reduceNe                 \ UInt.lean:59 (94) reduceBinPred
sp-lit-d: UInt8.reduceOfNat              \ UInt.lean:69 (94) body
sp-lit-d: UInt8.reduceOfNatLT            \ UInt.lean:63 (94) body
sp-lit-d: UInt8.reduceSub                \ UInt.lean:50 (94) reduceBin
sp-lit-d: UInt8.reduceToNat              \ UInt.lean:75 (94) body
sp-lit-s: USize.reduceToNat              \ UInt.lean:113 body
