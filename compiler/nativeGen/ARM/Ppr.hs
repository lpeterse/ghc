{-# OPTIONS_GHC -fno-warn-orphans #-}
module ARM.Ppr (pprNatCmmDecl) where

import           GhcPrelude

import           Data.Bits
import           Data.Int
import           Data.Word

import           BlockId
import           CLabel
import           Cmm               hiding (topInfoTable)
import           DynFlags
import           FastString
import           Format
import           Hoopl.Collections
import           Hoopl.Label
import           Instruction
import           Outputable
import           Platform
import           PprBase
import           Reg
import           RegClass
import           TargetReg
import           Unique            (pprUniqueAlways)

import           ARM.Cond
import           ARM.Instr         (Instr (..))
import           ARM.Regs

pprInstr :: Instr -> SDoc
pprInstr (ADD  rd rn op2) =
  pprMnmRegRegOp2 (sLit "ADD")  rd rn op2
pprInstr (ADC  rd rn op2) =
  pprMnmRegRegOp2 (sLit "ADC")  rd rn op2
pprInstr (SUB  rd rn op2) =
  pprMnmRegRegOp2 (sLit "SUB")  rd rn op2
pprInstr (SBC  rd rn op2) =
  pprMnmRegRegOp2 (sLit "SBC")  rd rn op2
pprInstr (MUL  rd rn rm) =
  pprMnmRegRegReg (sLit "MUL")  rd rn rm
pprInstr (SDIV rd rn rm) =
  pprMnmRegRegReg (sLit "SDIV") rd rn rm
pprInstr (UDIV rd rn rm) =
  pprMnmRegRegReg (sLit "UDIV") rd rn rm
pprInstr (MOV  rd op2) =
  pprMnmRegOp2    (sLit "MOV")  rd op2
pprInstr (MOVS rd op2) =
  pprMnmRegOp2    (sLit "MOVS") rd op2
pprInstr (MVN  rd op2) =
  pprMnmRegOp2    (sLit "MVN")  rd op2
pprInstr (MVNS rd op2) =
  pprMnmRegOp2    (sLit "MVNS") rd op2
pprInstr (CMP  rn op2) =
  pprMnmRegOp2    (sLit "CMP")  rn op2
pprInstr (CMN  rn op2) =
  pprMnmRegOp2    (sLit "CMN")  rn op2
pprInstr (TST  rn op2) =
  pprMnmRegOp2    (sLit "TST")  rn op2
pprInstr (TEQ  rn op2) =
  pprMnmRegOp2    (sLit "TEQ")  rn op2
pprInstr (AND  rd rn op2) =
  pprMnmRegRegOp2 (sLit "AND")  rd rn op2
pprInstr (EOR  rd rn op2) =
  pprMnmRegRegOp2 (sLit "EOR")  rd rn op2
pprInstr (ORR  rd rn op2) =
  pprMnmRegRegOp2 (sLit "ORR")  rd rn op2
pprInstr (ORN  rd rn op2) =
  pprMnmRegRegOp2 (sLit "ORN")  rd rn op2
pprInstr (BIC  rd rn op2) =
  pprMnmRegRegOp2 (sLit "BIC")  rd rn op2
pprInstr (LDR  cd rd ad) =
  char '\t' <> sLit "LDR" <> pprCond cd <> char '\t' <>
  pprReg rd <> pprAddress ad
pprInstr (LDRB cd rd ad) =
  char '\t' <> sLit "LDR" <> pprCond cd <> text "B\t" <>
  pprReg rd <> pprAddress ad
pprInstr (STR  cd rd ad) =
  char '\t' <> sLit "STR" <> pprCond cd <> char '\t' <>
  pprReg rd <> pprAddress ad
pprInstr (STRB cd rd ad) =
  char '\t' <> sLit "STR" <> pprCond cd <> text "B\t" <>
  pprReg rd <> pprAddress ad
pprInstr (SWP cd rd rm rn) =
  char '\t' <> sLit "SWP" <> pprCond cd <> char '\t' <>
  pprReg rd <> text ", " <> pprReg rm <> text ", [" <> pprReg rn <> char ']'
pprInstr (SWPB cd rd rm rn) =
  char '\t' <> sLit "SWP" <> pprCond cd <> text "B\t" <>
  pprReg rd <> text ", " <> pprReg rm <> text ", [" <> pprReg rn <> char ']'
pprInstr (SWI  cd im) =
  char '\t' <> sLit "SWI" <> pprCond cd <> char '\t' <> pprImm im


-- Like `\tADD\trd, rn, rm, LSL #23`.
pprMnmRegRegOp2 :: LitString -> Rd -> Rn -> Op2 -> SDoc
pprMnmRegRegOp2 mnm rd rn op2 = hcat
  [ char '\t', ptext mnm, char '\t', pprReg rd
  , text ", ", pprReg rn, text ", ", pprOp2 op2 ]

-- Like `\tNUL\trd, rm, rs`.
pprMnmRegRegReg :: LitString -> Rd -> Reg -> Reg -> SDoc
pprMnmRegRegReg mnm rd rn rm = hcat
  [ char '\t', ptext mnm, char '\t', pprReg rd
  , text ", ", pprReg rn, text ", ", pprReg rm ]

-- Like `\tMOV\trd, rm, LSL #23`.
pprMnmRegOp2 :: LitString -> Rd -> Op2 -> SDoc
pprMnmRegOp2 mnm rd op2 = hcat
  [ char '\t', ptext mnm, char '\t', pprReg rd
  , text ", ", pprOp2 op2 ]

pprReg :: Reg -> SDoc
pprReg r
  | r == r0   = sLit "r0"
  | r == r1   = sLit "r1"
  | r == r2   = sLit "r2"
  | r == r3   = sLit "r3"
  | r == r4   = sLit "r4"
  | r == r5   = sLit "r5"
  | r == r6   = sLit "r6"
  | r == r7   = sLit "r7"
  | r == r8   = sLit "r8"
  | r == r9   = sLit "r9"
  | r == r10  = sLit "r10"
  | r == r11  = sLit "r11"
  | r == r12  = sLit "r12"
  | r == sp   = sLit "sp"
  | r == lr   = sLit "lr"
  | r == pc   = sLit "pc"
  | r == cpsr = sLit "cpsr"
  | otherwise = panic "ARM.pprReg: unknown register"

pprImm :: Imm -> SDoc
pprImm (ImmInt i)      = char '#' <> int i

pprOp2 :: Op2 -> SDoc
pprOp2 (Op2     rm)    = pprReg rm
pprOp2 (Op2     im)    = pprImm im
pprOp2 (Op2LSL  rm rn) = pprReg rm <> text ", LSL " <> pprReg rn
pprOp2 (Op2LSL' rm im) = pprReg rm <> text ", LSL " <> pprImm im
pprOp2 (Op2LSR  rm rn) = pprReg rm <> text ", LSR " <> pprReg rn
pprOp2 (Op2LSR' rm im) = pprReg rm <> text ", LSR " <> pprImm im
pprOp2 (Op2ASR  rm rn) = pprReg rm <> text ", ASR " <> pprReg rn
pprOp2 (Op2ASR' rm im) = pprReg rm <> text ", ASR " <> pprImm im
pprOp2 (Op2ROR  rm rn) = pprReg rm <> text ", ROR " <> pprReg rn
pprOp2 (Op2ROR' rm im) = pprReg rm <> text ", ROR " <> pprImm im

pprCond :: Cond -> SDoc
pprCond EQ = sLit "EQ"
pprCond NE = sLit "NE"
pprCond CS = sLit "CS"
pprCond CC = sLit "CC"
pprCond MI = sLit "MI"
pprCond PL = sLit "PL"
pprCond VS = sLit "VS"
pprCond VC = sLit "VC"
pprCond HI = sLit "HI"
pprCond LS = sLit "LS"
pprCond GE = sLit "GE"
pprCond LT = sLit "LT"
pprCond GT = sLit "GT"
pprCond LE = sLit "LE"
pprCond AL = empty

pprSize :: Size -> SDoc
pprSize B  = sLit "B"
pprSize SB = sLit "SB"
pprSize H  = sLit "H"
pprSize SH = sLit "SH"

pprAddress :: Address -> SDoc
pprAddress (ZeroOffset rn) =
  char '[' <> pprReg rn <> ']'
pprAddress (PreIndexedRegister rn rm) =
  char '[' <> pprReg rn <> text ", " <> pprRegOffset rm <> char ']'
pprAddress (PreIndexedImmediate n im) =
  char '[' <> pprReg rn <> text ", " <> pprImmOffset im <> char ']'
pprAddress (PostIndexedRegister rn rm) =
  char '[' <> pprReg rn <> text "], " <> pprRegOffset rm
pprAddress (PostIndexedImmediate rn im) =
  char '[' <> pprReg rn <> text "], " <> pprImmOffset im

pprRegOffset :: RegOffset -> SDoc
pprRegOffset (PlusReg rn)  =             pprReg rn
pprRegOffset (MinusReg rn) = char '-' <> pprReg rn

pprImmOffset :: ImmOffset -> SDoc
pprImmOffset (PlusImm (ImmInt i))  = char '#' <> int i
pprImmOffset (MinusImm (ImmInt i)) = char '#' <> int (negate i)
